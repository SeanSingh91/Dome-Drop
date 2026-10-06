const http=require('http'),fs=require('fs'),path=require('path'),crypto=require('crypto');
const PORT=process.env.PORT||3000,rooms=new Map();
const W=1200,H=700,TABLE_Y=600,GRAVITY=1250,STEP=1/480,AIR_DRAG=1-0.12*STEP,BALL_R=8;
const DOME={cx:880,cy:380,r:260,openingDeg:-142,halfWidthDeg:11};
const SUPPORTS=[{x1:630,x2:740,y:476},{x1:725,x2:780,y:438},{x1:1010,x2:1090,y:300},{x1:1085.4,x2:1125,y:486}];
const GAP_BARRIERS=[{x1:630,x2:660,y1:476,y2:600}];
const STILL_SPEED=18,STILL_TIME=0.35,STILL_AREA=20,STILL_AREA_TIME=1,MAX_THROW_TIME=10;
const CUPS=[
{name:'floor 10',cx:790,rim:556,w:54,h:44,points:10},{name:'floor 50',cx:880,rim:556,w:38,h:44,points:50},{name:'floor 20',cx:960,rim:556,w:48,h:44,points:20},
{name:'shelf 20',cx:700,rim:438,w:44,h:38,points:20},{name:'shelf 30',cx:752,rim:400,w:38,h:38,points:30},{name:'back 50',cx:1040,rim:250,w:40,h:40,points:50},{name:'side 100',cx:1099,rim:450,w:40,h:36,points:100}
];
const uid=()=>crypto.randomBytes(10).toString('hex');
const code=()=>{let c;do{c='';for(let i=0;i<4;i++)c+='ABCDEFGHJKLMNPQRSTUVWXYZ'[crypto.randomInt(24)]}while(rooms.has(c));return c};
const json=(res,obj,status=200)=>{res.writeHead(status,{'Content-Type':'application/json','Cache-Control':'no-store'});res.end(JSON.stringify(obj))};
const send=(p,m)=>{if(p.res)try{p.res.write(`data:${JSON.stringify(m)}\n\n`)}catch{p.res=null}};
const broadcast=(r,m)=>r.players.forEach(p=>send(p,m));
const publicState=r=>({type:'state',room:r.code,hostId:r.hostId,status:r.status,round:r.round,currentPlayerId:r.currentPlayerId,turnDeadline:r.turnDeadline,throwSetup:r.throwSetup,players:r.players.map(p=>({id:p.id,name:p.name,host:p.id===r.hostId,connected:p.connected,disconnectDeadline:p.disconnectDeadline||null,score:p.score,throws:p.throws}))});
const state=r=>broadcast(r,publicState(r));
const byId=(r,id)=>r?.players.find(p=>p.id===id);
const connectedPlayers=r=>r.players.filter(p=>p.connected);
function chooseHost(r){const old=byId(r,r.hostId);if(old?.connected)return;const n=connectedPlayers(r)[0];if(n)r.hostId=n.id}
function clearDisconnect(p){if(p.disconnectTimer){clearTimeout(p.disconnectTimer);p.disconnectTimer=null}}
function clamp(v,a,b){return Math.max(a,Math.min(b,v))}
function randomInt(a,b){return crypto.randomInt(a,b+1)}
function makeThrowSetup(r,p){return{round:r.round,throwNo:p.throws.length+1,playerId:p.id,x:randomInt(70,240),y:randomInt(380,480),angleSweepMs:randomInt(2600,3200),powerSweepMs:randomInt(2200,2800),createdAt:Date.now()}}
function rad(d){return d*Math.PI/180}
function angleDiff(a,b){return Math.abs(((a-b+180)%360)-180)}
function opening(t){return angleDiff(t,DOME.openingDeg)<=DOME.halfWidthDeg}
function circlePoint(deg){return{x:DOME.cx+DOME.r*Math.cos(rad(deg)),y:DOME.cy+DOME.r*Math.sin(rad(deg))}}
function cupGeom(c){const bw=c.w*.68;return{topL:c.cx-c.w/2,topR:c.cx+c.w/2,botL:c.cx-bw/2,botR:c.cx+bw/2,bottom:c.rim+c.h}}
function reflect(vx,vy,nx,ny,e){const d=vx*nx+vy*ny;if(d<0){vx-=(1+e)*d*nx;vy-=(1+e)*d*ny}return[vx,vy]}
function segHit(px,py,ax,ay,bx,by){const dx=bx-ax,dy=by-ay,l=dx*dx+dy*dy;if(!l)return[Math.hypot(px-ax,py-ay),ax,ay];const t=clamp(((px-ax)*dx+(py-ay)*dy)/l,0,1),x=ax+t*dx,y=ay+t*dy;return[Math.hypot(px-x,py-y),x,y]}
function collideSupport(b,support){
  if(b.y+BALL_R<support.y||b.y-BALL_R>support.y||b.x<support.x1-BALL_R||b.x>support.x2+BALL_R)return false;
  if(b.vy>=0){b.y=support.y-BALL_R;b.vy=-Math.abs(b.vy)*.35;return true}
  return false;
}
function officialThrow(startX,startY,angle,power){
  const s=power,a=rad(angle);const b={x:startX,y:startY,vx:s*Math.cos(a),vy:-s*Math.sin(a),bounced:false,entered:false,stillTime:0,stillAreaTime:0,areaMinX:startX,areaMaxX:startX,areaMinY:startY,areaMaxY:startY};
  for(let stepNo=1;stepNo<=MAX_THROW_TIME/STEP;stepNo++){
    b.vy+=GRAVITY*STEP;b.vx*=AIR_DRAG;b.vy*=AIR_DRAG;b.x+=b.vx*STEP;b.y+=b.vy*STEP;
    const speed=Math.hypot(b.vx,b.vy);
    b.stillTime=speed<STILL_SPEED?b.stillTime+STEP:0;
    b.areaMinX=Math.min(b.areaMinX,b.x);b.areaMaxX=Math.max(b.areaMaxX,b.x);b.areaMinY=Math.min(b.areaMinY,b.y);b.areaMaxY=Math.max(b.areaMaxY,b.y);if(b.areaMaxX-b.areaMinX<=STILL_AREA&&b.areaMaxY-b.areaMinY<=STILL_AREA){b.stillAreaTime+=STEP}else{b.areaMinX=b.areaMaxX=b.x;b.areaMinY=b.areaMaxY=b.y;b.stillAreaTime=0}
    if(b.stillTime>=STILL_TIME||b.stillAreaTime>=STILL_AREA_TIME)return{points:0,label:'Missed',duration:stepNo*STEP};
    if(b.y+BALL_R>=TABLE_Y){
      if(!b.bounced&&!b.entered){b.bounced=true;b.y=TABLE_Y-BALL_R;b.vy=-Math.abs(b.vy)*.8}
      else if(!b.entered)return{points:0,label:'Bounced twice',duration:stepNo*STEP};
      else{b.y=TABLE_Y-BALL_R;b.vy=-Math.abs(b.vy)*.8}
    }
    let dx=b.x-DOME.cx,dy=b.y-DOME.cy,d=Math.hypot(dx,dy)||1,theta=Math.atan2(dy,dx)*180/Math.PI;
    if(!b.entered&&b.bounced&&d<DOME.r&&opening(theta)&&b.y<DOME.cy)b.entered=true;
    if(!opening(theta)){
      if(b.entered&&d+BALL_R>DOME.r){const nx=dx/d,ny=dy/d;b.x=DOME.cx+nx*(DOME.r-BALL_R);b.y=DOME.cy+ny*(DOME.r-BALL_R);[b.vx,b.vy]=reflect(b.vx,b.vy,nx,ny,.62)}
      else if(!b.entered&&d<DOME.r+BALL_R){const nx=dx/d,ny=dy/d;b.x=DOME.cx+nx*(DOME.r+BALL_R);b.y=DOME.cy+ny*(DOME.r+BALL_R);[b.vx,b.vy]=reflect(b.vx,b.vy,nx,ny,.62)}
    }
    if(!b.entered){for(const deg of [DOME.openingDeg-DOME.halfWidthDeg,DOME.openingDeg+DOME.halfWidthDeg]){const p=circlePoint(deg),q=segHit(b.x,b.y,p.x,p.y,p.x,p.y);if(q[0]<BALL_R){const dd=q[0]||1,nx=(b.x-p.x)/dd,ny=(b.y-p.y)/dd;b.x=p.x+nx*BALL_R;b.y=p.y+ny*BALL_R;[b.vx,b.vy]=reflect(b.vx,b.vy,nx,ny,.62)}}}
    for(const c of CUPS){const g=cupGeom(c);if(b.entered&&b.y>=c.rim&&b.y<=g.bottom){const t=(b.y-c.rim)/c.h,l=g.topL+t*(g.botL-g.topL),r=g.topR+t*(g.botR-g.topR);const scoreR=r;if(b.x>=l&&b.x<=scoreR)return{points:c.points,label:`+${c.points}!`,duration:stepNo*STEP}}
      if(b.entered){for(const[ax,ay,bx,by]of [[g.topL,c.rim,g.botL,g.bottom],[g.topR,c.rim,g.botR,g.bottom]]){const q=segHit(b.x,b.y,ax,ay,bx,by);if(q[0]<BALL_R){const dd=q[0]||1,nx=(b.x-q[1])/dd,ny=(b.y-q[2])/dd;b.x=q[1]+nx*BALL_R;b.y=q[2]+ny*BALL_R;[b.vx,b.vy]=reflect(b.vx,b.vy,nx,ny,.35)}}if(b.y+BALL_R>g.bottom&&b.x>=g.botL-BALL_R&&b.x<=g.botR+BALL_R){b.y=g.bottom-BALL_R;b.vy=-Math.abs(b.vy)*.2}}
    }
    if(b.entered){for(const support of SUPPORTS)collideSupport(b,support);for(const g of GAP_BARRIERS){if(b.x>=g.x1-BALL_R&&b.x<=g.x2+BALL_R&&b.y>=g.y1-BALL_R&&b.y<=g.y2+BALL_R){const dl=Math.abs(b.x-(g.x1-BALL_R)),dr=Math.abs(b.x-(g.x2+BALL_R)),dt=Math.abs(b.y-(g.y1-BALL_R)),db=Math.abs(b.y-(g.y2+BALL_R)),m=Math.min(dl,dr,dt,db);if(m===dl){b.x=g.x1-BALL_R;b.vx=-Math.abs(b.vx)*.35}else if(m===dr){b.x=g.x2+BALL_R;b.vx=Math.abs(b.vx)*.35}else if(m===dt){b.y=g.y1-BALL_R;b.vy=-Math.abs(b.vy)*.35}else{b.y=g.y2+BALL_R;b.vy=Math.abs(b.vy)*.35}}}}
    if(b.y>760||b.x>1300||b.x<-100)return{points:0,label:b.bounced?'Missed':'No bounce, doesn’t count',duration:stepNo*STEP};
  }
  return{points:0,label:'Missed',duration:MAX_THROW_TIME};
}
function clearAllTimers(r){r.players.forEach(clearDisconnect);if(r.officialTimer){clearTimeout(r.officialTimer);r.officialTimer=null}}
function markDisconnected(r,p){p.connected=false;p.res=null;p.disconnectDeadline=Date.now()+20000;clearDisconnect(p);if(r.hostId===p.id)chooseHost(r);if(r.status==='playing'&&r.currentPlayerId===p.id&&!p.pending){p.disconnectTimer=setTimeout(()=>{if(!p.connected&&r.status==='playing'&&r.currentPlayerId===p.id&&!p.pending){p.disconnectTimer=null;p.disconnectDeadline=null;broadcast(r,{type:'disconnectSkip',playerId:p.id,player:p.name});recordSkipped(r,p)}},20000)}state(r)}
function recordSkipped(r,p){if(r.currentPlayerId!==p.id||p.pending)return;p.throws.push(0);p.pending=null;broadcast(r,{type:'throwResult',playerId:p.id,player:p.name,points:0,label:'Disconnected — skipped',throwNo:p.throws.length,score:p.score,official:true});nextTurn(r)}
function nextTurn(r){const active=connectedPlayers(r);if(!active.length){r.currentPlayerId=null;state(r);return}const idx=r.players.findIndex(p=>p.id===r.currentPlayerId);let found=null;for(let k=1;k<=r.players.length;k++){const p=r.players[(idx+k+r.players.length)%r.players.length];if(p?.connected){found=p;break}}if(!found)found=active[0];const nextIdx=r.players.findIndex(p=>p.id===found.id);if(nextIdx<=r.turnIndex)r.round++;r.turnIndex=nextIdx;if(r.round>5){finish(r);return}r.currentPlayerId=found.id;r.turnDeadline=null;r.throwSetup=makeThrowSetup(r,found);broadcast(r,{type:'throwSetup',...r.throwSetup,playerId:found.id,player:found.name});state(r)}
function finish(r,winner=null){clearAllTimers(r);r.status='finished';r.currentPlayerId=null;r.turnDeadline=null;const max=winner?winner.score:Math.max(...r.players.map(p=>p.score),0);r.winners=winner?[winner.name]:r.players.filter(p=>p.score===max).map(p=>p.name);broadcast(r,{type:'gameOver',winnerNames:r.winners,winningScore:max,scores:r.players.map(p=>({id:p.id,name:p.name,score:p.score,throws:p.throws,connected:p.connected}))});state(r)}
function recordOfficial(r,p,official){if(!p.pending||r.status!=='playing')return;const no=p.pending.throwNo;p.throws[no-1]=official.points;p.score+=official.points;p.pending=null;r.turnDeadline=null;if(r.officialTimer){clearTimeout(r.officialTimer);r.officialTimer=null}broadcast(r,{type:'throwResult',playerId:p.id,player:p.name,points:official.points,label:official.label,throwNo:no,score:p.score,official:true});if(p.score>=250){finish(r,p);return}if(r.round>=5&&r.players.filter(x=>x.connected).every(x=>x.throws.length>=5)){finish(r);return}nextTurn(r)}
function scheduleOfficial(r,p,official){const delay=Math.max(0,Math.round(official.duration*1000));r.officialTimer=setTimeout(()=>{r.officialTimer=null;recordOfficial(r,p,official)},delay)}
function resetGame(r){clearAllTimers(r);r.status='lobby';r.round=1;r.turnIndex=0;r.currentPlayerId=null;r.turnDeadline=null;r.throwSetup=null;r.winners=[];r.players.forEach(p=>{p.score=0;p.throws=[];p.pending=null;p.disconnectDeadline=null});state(r)}
function body(req){return new Promise(resolve=>{let b='';req.on('data',x=>b+=x);req.on('end',()=>{try{resolve(JSON.parse(b||'{}'))}catch{resolve({})}})})}
async function action(req,res,m){const id=req.headers['x-player-id'];if(m.type==='create'){const pid=uid(),name=String(m.name||'Player').trim().slice(0,20)||'Player';const r={code:code(),hostId:pid,status:'lobby',round:1,turnIndex:0,currentPlayerId:null,turnDeadline:null,throwSetup:null,officialTimer:null,players:[{id:pid,name,connected:true,res:null,score:0,throws:[],pending:null,disconnectTimer:null,disconnectDeadline:null}],winners:[]};rooms.set(r.code,r);json(res,{ok:true,room:r.code,playerId:pid});return}
 const r=rooms.get(String(m.room||'').toUpperCase());if(!r)return json(res,{error:'That room code does not exist.'},404);const p=byId(r,id);if(!p)return json(res,{error:'Player session not found. Rejoin with the same name and code.'},400);
 if(m.type==='start'){if(r.hostId!==id)return json(res,{error:'Only the host can start.'},403);const first=r.players.findIndex(x=>x.connected);if(first<0)return json(res,{error:'At least one connected player is required.'},400);r.status='playing';r.round=1;r.turnIndex=first;r.currentPlayerId=r.players[first].id;r.throwSetup=makeThrowSetup(r,r.players[first]);broadcast(r,{type:'throwSetup',...r.throwSetup,playerId:r.players[first].id,player:r.players[first].name});state(r);return json(res,{ok:true})}
 if(m.type==='aiming'){if(r.status==='playing'&&r.currentPlayerId===id&&p.connected&&!p.pending)broadcast(r,{type:'aiming',player:p.name,value:!!m.value});return json(res,{ok:true})}
 if(m.type==='throw'){if(r.status!=='playing'||r.currentPlayerId!==id||!p.connected)return json(res,{error:'Not your turn.'},403);if(p.throws.length>=5)return json(res,{error:'Five throws used.'},400);if(p.pending)return json(res,{error:'Throw already pending.'},400);const angle=Number(m.angle),power=Number(m.power);if(!Number.isFinite(angle)||!Number.isFinite(power))return json(res,{error:'Invalid throw.'},400);if(!r.throwSetup||r.throwSetup.playerId&&r.throwSetup.playerId!==id)return json(res,{error:'Throw setup is not ready.'},400);const a=clamp(angle,-86,-48),pw=clamp(power,1100,1950),setup=r.throwSetup,official=officialThrow(setup.x,setup.y,a,pw);p.pending={round:r.round,throwNo:p.throws.length+1,angle:a,power:pw,startX:setup.x,startY:setup.y};r.turnDeadline=Date.now()+Math.max(20000,Math.ceil(official.duration*1000)+1000);broadcast(r,{type:'throw',player:p.name,playerId:id,angle:a,power:pw,startX:setup.x,startY:setup.y,round:r.round,throwNo:p.pending.throwNo});scheduleOfficial(r,p,official);return json(res,{ok:true})}
 if(m.type==='playAgain'){if(r.status!=='finished'||r.hostId!==id)return json(res,{error:'Only the host can play again.'},403);resetGame(r);return json(res,{ok:true})}
 if(m.type==='leave'){markDisconnected(r,p);return json(res,{ok:true})}
 return json(res,{error:'Unknown action.'},400)}
const server=http.createServer(async(req,res)=>{if(req.method==='GET'&&req.url.startsWith('/events/')){const id=req.url.split('/')[2],r=[...rooms.values()].find(x=>byId(x,id)),p=byId(r,id);if(!r||!p){res.writeHead(404);return res.end()}clearDisconnect(p);p.connected=true;p.disconnectDeadline=null;p.res=res;res.writeHead(200,{'Content-Type':'text/event-stream','Cache-Control':'no-cache','Connection':'keep-alive','X-Accel-Buffering':'no'});send(p,publicState(r));state(r);req.on('close',()=>{if(p.res===res){p.res=null;markDisconnected(r,p)}});return}
 if(req.method==='POST'&&req.url==='/api/create'){const m=await body(req);return action(req,res,{...m,type:'create'})}
 if(req.method==='POST'&&req.url==='/api/join'){const m=await body(req),r=rooms.get(String(m.room||'').toUpperCase());if(!r)return json(res,{error:'That room code does not exist.'},404);const name=String(m.name||'Player').trim().slice(0,20)||'Player';const p=r.players.find(x=>x.name.toLowerCase()===name.toLowerCase()&&!x.connected&&x.disconnectDeadline&&x.disconnectDeadline>Date.now());if(p){p.connected=true;p.disconnectDeadline=null;clearDisconnect(p);p.res=null;json(res,{ok:true,room:r.code,playerId:p.id,rejoined:true});state(r);return}if(r.status!=='lobby')return json(res,{error:'The game has already started. Only a disconnected player can rejoin.'},400);if(r.players.filter(x=>x.connected).length>=6)return json(res,{error:'Room is full.'},400);if(r.players.some(x=>x.connected&&x.name.toLowerCase()===name.toLowerCase()))return json(res,{error:'That name is already in use.'},400);const id=uid();r.players.push({id,name,connected:true,res:null,score:0,throws:[],pending:null,disconnectTimer:null,disconnectDeadline:null});state(r);json(res,{ok:true,room:r.code,playerId:id,rejoined:false});return}
 if(req.method==='POST'&&req.url==='/api/action')return action(req,res,await body(req));let f=req.url==='/'?'/index.html':req.url,root=path.join(__dirname,'public'),fp=path.normalize(path.join(root,f));if(!fp.startsWith(root)){res.writeHead(403);return res.end()}fs.readFile(fp,(e,d)=>{if(e){res.writeHead(404);return res.end('Not found')}res.writeHead(200,{'Content-Type':path.extname(fp)==='.html'?'text/html':'text/javascript','Cache-Control':'no-store'});res.end(d)})});server.listen(PORT,'0.0.0.0',()=>console.log(`Dome Drop Phase 3: http://0.0.0.0:${PORT}`));
