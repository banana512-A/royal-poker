const express  = require('express');
const http     = require('http');
const { Server } = require('socket.io');
const path     = require('path');

const app    = express();
const server = http.createServer(app);
const io     = new Server(server, { cors: { origin: '*' } });

app.use(express.static(path.join(__dirname, 'public')));

// ─── CONFIG ───────────────────────────────────────────────
const SMALL_BLIND    = 25000;
const BIG_BLIND      = 50000;
const MAX_SEATS      = 6;
const TIMER_SECONDS  = 30;   // وقت كل لاعب
const MIN_RAISE      = 2000; // أقل رهان ممكن

const TABLES_CFG = {
  rookie: { name:'ROOKIE TABLE', sb:25000,  bb:50000,  minBuy:50000,   maxBuy:1000000 },
  vip:    { name:'VIP TABLE',    sb:250000, bb:500000, minBuy:500000,  maxBuy:5000000 },
};

// ─── DATA ─────────────────────────────────────────────────
const rooms = {};   // roomId -> Room
const players_db = {}; // socketId -> { name, history: [] }

// ─── DECK ─────────────────────────────────────────────────
const SUITS  = ['S','H','D','C'];
const VALUES = ['2','3','4','5','6','7','8','9','T','J','Q','K','A'];
const VAL_MAP = Object.fromEntries(VALUES.map((v,i) => [v, i+2]));

function buildDeck() {
  const d = [];
  for (const s of SUITS) for (const v of VALUES) d.push({ v, s, n: VAL_MAP[v] });
  for (let i = d.length-1; i > 0; i--) {
    const j = Math.floor(Math.random()*(i+1));
    [d[i],d[j]] = [d[j],d[i]];
  }
  return d;
}

// ─── HAND EVALUATOR ───────────────────────────────────────
function evalFive(cards) {
  const vals  = cards.map(c=>c.n).sort((a,b)=>b-a);
  const suits = cards.map(c=>c.s);
  const counts = {};
  vals.forEach(v => counts[v] = (counts[v]||0)+1);
  const freq = Object.values(counts).sort((a,b)=>b-a);
  const flush = suits.every(s=>s===suits[0]);
  const uq = [...new Set(vals)].sort((a,b)=>a-b);
  let straight=false, highS=0;
  for (let i=0; i<=uq.length-5; i++)
    if (uq[i+4]-uq[i]===4 && new Set(uq.slice(i,i+5)).size===5)
      { straight=true; highS=uq[i+4]; }
  if (!straight && uq.includes(14)&&uq.includes(2)&&uq.includes(3)&&uq.includes(4)&&uq.includes(5))
    { straight=true; highS=5; }

  let score, name;
  if (straight&&flush)       { score=8e7+highS;  name=highS===14?'Royal Flush':'Straight Flush'; }
  else if (freq[0]===4)      { const q=+Object.keys(counts).find(k=>counts[k]===4); score=7e7+q*100+vals.find(v=>v!==q); name='Four of a Kind'; }
  else if (freq[0]===3&&freq[1]===2) { const t=+Object.keys(counts).find(k=>counts[k]===3),p=+Object.keys(counts).find(k=>counts[k]===2); score=6e7+t*100+p; name='Full House'; }
  else if (flush)            { score=5e7+vals[0]*1e6+vals[1]*1e4+vals[2]*100+vals[3]*10+vals[4]; name='Flush'; }
  else if (straight)         { score=4e7+highS; name='Straight'; }
  else if (freq[0]===3)      { const t=+Object.keys(counts).find(k=>counts[k]===3),ks=vals.filter(v=>v!==t); score=3e7+t*1e4+ks[0]*100+ks[1]; name='Three of a Kind'; }
  else if (freq[0]===2&&freq[1]===2) { const ps=Object.keys(counts).filter(k=>counts[k]===2).map(Number).sort((a,b)=>b-a),k=vals.find(v=>v!==ps[0]&&v!==ps[1]); score=2e7+ps[0]*1e4+ps[1]*100+k; name='Two Pair'; }
  else if (freq[0]===2)      { const p=+Object.keys(counts).find(k=>counts[k]===2),ks=vals.filter(v=>v!==p); score=1e7+p*1e5+ks[0]*1e3+ks[1]*10+ks[2]; name='One Pair'; }
  else                       { score=vals[0]*1e6+vals[1]*1e4+vals[2]*100+vals[3]*10+vals[4]; name='High Card'; }
  return { score, name };
}

function bestHand(hole, community) {
  const all = [...hole, ...community];
  if (all.length < 5) return { score:0, name:'—' };
  let best = null;
  for (let i=0;i<all.length-4;i++) for (let j=i+1;j<all.length-3;j++)
    for (let k=j+1;k<all.length-2;k++) for (let l=k+1;l<all.length-1;l++)
      for (let m=l+1;m<all.length;m++) {
        const ev = evalFive([all[i],all[j],all[k],all[l],all[m]]);
        if (!best || ev.score > best.score) best = ev;
      }
  return best || { score:0, name:'—' };
}

// ─── ROOM FACTORY ─────────────────────────────────────────
function createRoom(id, tableKey) {
  const cfg = TABLES_CFG[tableKey] || TABLES_CFG.rookie;
  return {
    id, tableKey, cfg,
    players: [],      // { socketId, name, chips, seat, cards, bet, totalBet, folded, allIn, handName, handScore, history }
    deck: [], community: [], pot: 0,
    street: -1,       // -1=lobby, 0=preflop, 1=flop, 2=turn, 3=river
    dealerSeat: 0, currentSeat: -1,
    currentBet: 0, minRaise: MIN_RAISE,
    lastAggressor: -1,
    handOver: true, started: false,
    round: 0,
    actionTimer: null, timerEnd: 0,
  };
}

function getRoom(id, tableKey) {
  if (!rooms[id]) rooms[id] = createRoom(id, tableKey||'rookie');
  return rooms[id];
}

// ─── BROADCAST ────────────────────────────────────────────
function broadcast(room) {
  room.players.forEach(p => {
    const state = buildState(room, p.socketId);
    io.to(p.socketId).emit('state', state);
  });
}

function buildState(room, socketId) {
  const me = room.players.find(p=>p.socketId===socketId);
  const now = Date.now();
  return {
    players: room.players.map(p => ({
      seat: p.seat, name: p.name, chips: p.chips,
      bet: p.bet, folded: p.folded, allIn: p.allIn,
      isDealer: p.seat === room.dealerSeat,
      isActive: p.seat === room.currentSeat && !room.handOver,
      cards: p.socketId===socketId
        ? p.cards
        : (room.handOver && !p.folded ? p.cards : p.cards.map(()=>null)),
      handName: room.handOver ? p.handName : '',
    })),
    community:    room.community,
    pot:          room.pot,
    street:       room.street,
    currentBet:   room.currentBet,
    minRaise:     Math.max(room.minRaise, MIN_RAISE),
    myTurn:       me && room.currentSeat===me.seat && !room.handOver,
    handOver:     room.handOver,
    started:      room.started,
    playerCount:  room.players.length,
    round:        room.round,
    tableName:    room.cfg.name,
    timerEnd:     room.timerEnd,   // timestamp when current timer expires
    timerSeconds: TIMER_SECONDS,
    myHistory:    me ? me.history.slice(-5) : [],  // آخر 5 رهانات
  };
}

// ─── GAME LOGIC ───────────────────────────────────────────
function startHand(room) {
  if (room.players.length < 2) return;
  room.handOver = false;
  room.deck = buildDeck();
  room.community = [];
  room.pot = 0;
  room.street = 0; // preflop
  room.currentBet = room.cfg.bb;
  room.minRaise   = Math.max(room.cfg.bb * 2, MIN_RAISE * 2);
  room.started    = true;
  room.round++;

  room.players.forEach(p => {
    p.cards    = [room.deck.pop(), room.deck.pop()];
    p.bet      = 0;
    p.totalBet = 0;
    p.folded   = false;
    p.allIn    = false;
    p.handName = '';
    p.handScore= 0;
  });

  // Rotate dealer
  const seats = room.players.map(p=>p.seat).sort((a,b)=>a-b);
  const di = seats.indexOf(room.dealerSeat);
  room.dealerSeat = seats[(di+1) % seats.length];

  // Post blinds
  const sbSeat = nextSeat(room, room.dealerSeat, false);
  const bbSeat = nextSeat(room, sbSeat, false);
  postBlind(room, sbSeat, room.cfg.sb, 'SB');
  postBlind(room, bbSeat, room.cfg.bb, 'BB');
  room.lastAggressor = bbSeat;
  room.currentSeat   = nextSeat(room, bbSeat, false);

  broadcast(room);
  io.to(room.id).emit('log', `── جولة ${room.round} | SB ${fmt(room.cfg.sb)} BB ${fmt(room.cfg.bb)} ──`);
  scheduleTimer(room);
}

function postBlind(room, seat, amount, label) {
  const p = room.players.find(p=>p.seat===seat);
  if (!p) return;
  const a = Math.min(amount, p.chips);
  p.chips -= a; p.bet += a; p.totalBet += a; room.pot += a;
  if (p.chips === 0) p.allIn = true;
  io.to(room.id).emit('log', `${p.name} ${label} ${fmt(a)}`);
}

function nextSeat(room, fromSeat, skipCurrent=true) {
  const eligible = room.players
    .filter(p => !p.folded && !p.allIn)
    .map(p=>p.seat).sort((a,b)=>a-b);
  if (!eligible.length) return -1;
  const next = eligible.find(s => s > fromSeat);
  return next !== undefined ? next : eligible[0];
}

function activePlayers(room) { return room.players.filter(p=>!p.folded&&!p.allIn); }
function notFolded(room)     { return room.players.filter(p=>!p.folded); }

function isBettingDone(room) {
  const active = activePlayers(room);
  if (!active.length) return true;
  return active.every(p => p.bet === room.currentBet)
      && room.lastAggressor !== room.currentSeat;
}

// ─── APPLY ACTION ─────────────────────────────────────────
function applyAction(room, seat, action, amount) {
  clearTimeout(room.actionTimer);
  const p = room.players.find(p=>p.seat===seat);
  if (!p || p.seat!==room.currentSeat || room.handOver) return false;

  const callAmt = room.currentBet - p.bet;

  switch(action) {
    case 'fold':
      p.folded = true;
      io.to(room.id).emit('log', `${p.name} // FOLD`);
      break;

    case 'check':
      if (callAmt > 0) return applyAction(room, seat, 'call', 0);
      io.to(room.id).emit('log', `${p.name} // CHECK`);
      break;

    case 'call': {
      const a = Math.min(callAmt, p.chips);
      p.chips -= a; p.bet += a; p.totalBet += a; room.pot += a;
      if (p.chips===0) { p.allIn=true; io.to(room.id).emit('log',`${p.name} // CALL ALL-IN`); }
      else io.to(room.id).emit('log',`${p.name} // CALL ${fmt(a)}`);
      break;
    }

    case 'raise': {
      // amount = total bet player wants to put in (not just the raise)
      const raiseTotal = Math.min(amount, p.chips + p.bet);
      const added = raiseTotal - p.bet;
      if (added < Math.max(MIN_RAISE, room.cfg.bb)) {
        // raise too small — treat as call
        return applyAction(room, seat, 'call', 0);
      }
      p.chips -= added; room.pot += added;
      room.minRaise = Math.max(raiseTotal - room.currentBet, MIN_RAISE);
      room.currentBet = raiseTotal;
      p.bet = raiseTotal; p.totalBet += added;
      room.lastAggressor = seat;
      if (p.chips===0) { p.allIn=true; io.to(room.id).emit('log',`${p.name} // RAISE ALL-IN → ${fmt(raiseTotal)}`); }
      else io.to(room.id).emit('log', `${p.name} // RAISE → ${fmt(raiseTotal)}`);
      break;
    }

    case 'allin': {
      const a = p.chips;
      const nb = p.bet + a;
      p.chips=0; room.pot+=a; p.totalBet+=a;
      if (nb > room.currentBet) {
        room.minRaise = Math.max(nb-room.currentBet, MIN_RAISE);
        room.currentBet = nb;
        room.lastAggressor = seat;
      }
      p.bet = nb; p.allIn = true;
      io.to(room.id).emit('log',`${p.name} // ALL-IN ${fmt(a)}`);
      break;
    }

    default: return false;
  }
  return true;
}

// ─── ADVANCE ──────────────────────────────────────────────
function advance(room) {
  if (notFolded(room).length === 1) { endHand(room); return; }
  if (isBettingDone(room))           { nextStreet(room); return; }

  // Find next eligible seat
  let seat = room.currentSeat;
  let tries = 0;
  do {
    const seats = room.players.map(p=>p.seat).sort((a,b)=>a-b);
    const idx   = seats.indexOf(seat);
    seat        = seats[(idx+1) % seats.length];
    tries++;
    if (tries > MAX_SEATS * 2) { nextStreet(room); return; }
  } while (room.players.find(p=>p.seat===seat)?.folded ||
           room.players.find(p=>p.seat===seat)?.allIn);

  room.currentSeat = seat;
  broadcast(room);
  scheduleTimer(room);
}

// ─── STREETS — betting opens on each one ──────────────────
function nextStreet(room) {
  // Reset street bets
  room.players.forEach(p => { p.bet = 0; });
  room.currentBet  = 0;
  room.minRaise    = Math.max(room.cfg.bb, MIN_RAISE);
  room.lastAggressor = -1;
  room.street++;

  if (room.street === 1) {
    room.community.push(room.deck.pop(), room.deck.pop(), room.deck.pop());
    io.to(room.id).emit('log', '── FLOP ──');
  } else if (room.street === 2) {
    room.community.push(room.deck.pop());
    io.to(room.id).emit('log', '── TURN ──');
  } else if (room.street === 3) {
    room.community.push(room.deck.pop());
    io.to(room.id).emit('log', '── RIVER ──');
  } else {
    endHand(room); return;
  }

  // First to act = left of dealer
  room.currentSeat = nextSeat(room, room.dealerSeat, false);
  broadcast(room);
  scheduleTimer(room);
}

// ─── SHOWDOWN ─────────────────────────────────────────────
function endHand(room) {
  clearTimeout(room.actionTimer);
  room.handOver = true;
  room.timerEnd = 0;

  const contestants = notFolded(room);
  contestants.forEach(p => {
    const ev = bestHand(p.cards, room.community);
    p.handScore = ev.score;
    p.handName  = ev.name;
  });

  const maxScore = Math.max(...contestants.map(p=>p.handScore));
  const winners  = contestants.filter(p=>p.handScore===maxScore);
  const share    = Math.floor(room.pot / winners.length);
  winners.forEach(p => { p.chips += share; });

  // Save to history for each player
  room.players.forEach(p => {
    const isWinner = winners.includes(p);
    const entry = {
      round:    room.round,
      result:   isWinner ? 'WIN' : (p.folded ? 'FOLD' : 'LOSE'),
      amount:   isWinner ? share : -p.totalBet,
      handName: p.handName || '—',
      pot:      room.pot,
      ts:       Date.now(),
    };
    if (!p.history) p.history = [];
    p.history.unshift(entry);
    if (p.history.length > 5) p.history = p.history.slice(0,5);
  });

  broadcast(room);
  io.to(room.id).emit('handResult', {
    winners: winners.map(p=>({ name:p.name, seat:p.seat, handName:p.handName, won:share })),
    pot: room.pot,
  });
  io.to(room.id).emit('log', `✓ ${winners.map(p=>p.name).join(' & ')} يفوز ${fmt(share)} — ${winners[0].handName}`);

  // Remove bust players
  room.players = room.players.filter(p => p.chips > 0);

  if (room.players.length >= 2)
    setTimeout(() => startHand(room), 4500);
}

// ─── TIMER ────────────────────────────────────────────────
// المؤقت يعمل على السيرفر ويُبث لجميع اللاعبين
function scheduleTimer(room) {
  clearTimeout(room.actionTimer);
  room.timerEnd = Date.now() + TIMER_SECONDS * 1000;

  // Broadcast timerEnd so all clients can show countdown
  broadcast(room);

  room.actionTimer = setTimeout(() => {
    const p = room.players.find(p=>p.seat===room.currentSeat);
    if (p && !p.folded && !p.allIn && !room.handOver) {
      io.to(room.id).emit('log', `${p.name} // TIMEOUT → AUTO-FOLD`);
      applyAction(room, room.currentSeat, 'fold', 0);
      broadcast(room);
      advance(room);
    }
  }, TIMER_SECONDS * 1000);
}

// ─── SOCKET.IO ────────────────────────────────────────────
io.on('connection', socket => {
  let myRoom = null;
  let mySeat = null;

  socket.on('join', ({ roomId, tableKey, name, buyIn }) => {
    const room = getRoom(roomId || 'public', tableKey || 'rookie');

    if (room.players.length >= MAX_SEATS) {
      socket.emit('error', 'الغرفة ممتلئة'); return;
    }

    const cfg = room.cfg;
    const safeBI = Math.max(cfg.minBuy, Math.min(buyIn || cfg.minBuy, cfg.maxBuy));

    // Assign seat
    const taken = room.players.map(p=>p.seat);
    let seat = 0; while (taken.includes(seat)) seat++;

    const playerData = {
      socketId: socket.id,
      name:     name || `Player${seat+1}`,
      chips:    safeBI,
      seat,
      cards:    [], bet:0, totalBet:0,
      folded:   false, allIn:false,
      handName:'', handScore:0,
      history:  [],
    };
    room.players.push(playerData);
    myRoom = room;
    mySeat = seat;

    socket.join(room.id);
    io.to(room.id).emit('log', `${playerData.name} انضم (مقعد ${seat+1})`);
    broadcast(room);

    if (room.players.length >= 2 && !room.started) {
      setTimeout(() => startHand(room), 2000);
    }
  });

  socket.on('action', ({ action, amount }) => {
    if (!myRoom || mySeat === null) return;
    if (applyAction(myRoom, mySeat, action, amount)) {
      broadcast(myRoom);
      advance(myRoom);
    }
  });

  socket.on('emoji', ({ emoji }) => {
    if (!myRoom) return;
    const p = myRoom.players.find(p=>p.socketId===socket.id);
    if (!p) return;
    io.to(myRoom.id).emit('reaction', { seat: p.seat, emoji });
  });

  socket.on('disconnect', () => {
    if (!myRoom) return;
    const p = myRoom.players.find(p=>p.socketId===socket.id);
    if (p) io.to(myRoom.id).emit('log', `${p.name} غادر`);
    myRoom.players = myRoom.players.filter(p=>p.socketId!==socket.id);
    if (myRoom.players.length < 2) {
      clearTimeout(myRoom.actionTimer);
      myRoom.handOver = true;
      myRoom.started  = false;
    }
    broadcast(myRoom);
  });
});

// ─── HELPERS ──────────────────────────────────────────────
function fmt(n) {
  if (n >= 1000000) return (n/1000000).toFixed(1).replace('.0','')+'M';
  if (n >= 1000)    return Math.round(n/1000)+'K';
  return n+'';
}

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log(`🃏 Poker server on port ${PORT}`));
