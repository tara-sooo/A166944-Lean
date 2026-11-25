// First projected contact: whole-pair slab energy, recent-high reverse keys.
// Run node research/min_clock_projected_recent_audit.mjs 1024 4096 16384 65536
function audit(X,mode='diagnostic'){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,ell=Math.log(Math.log(B)),S=Math.max(1,Math.log(ell)),U=7*X+2;
 const ok=(b,m)=>{if(!b)throw Error(m);};
 ok(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(U+4);
 for(let p=2;p<spf.length;p++)if(!spf[p]){
  spf[p]=p;if(p*p<spf.length)for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 }
 let L=2,y=2;for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>6*S**.25)break;L*=p;y=p;}
 const T=mode==='degree'?4:mode==='diagnostic'?6:Math.ceil(20*ell),g=Math.max(2,T*L),
  kg=mode==='analytic'?Math.floor(1.5*ell/Math.log(g)):5,
  k=mode==='analytic'?Math.floor(ell/(8*Math.log(g))):3,
  P=mode==='analytic'?Math.ceil(B/Math.log(B)**.125):Math.ceil(B/4),
  tau=mode==='analytic'?Math.log(B)**1.5:12,
  Z=mode==='analytic'?Math.log(B)**1.5:12,
  near=mode==='analytic'?Math.floor(4*Math.log(B)):Math.max(2,Math.floor(B/64));
 const lo=X,hi=7*X/2-1,len=hi+1,r=new Int32Array(len),d=new Uint8Array(len),paths=[],horizons=new Map();
 const gBound=(L/2)*Array.from({length:kg+1},(_,i)=>(T*L/2)**i).reduce((s,v)=>s+v,0),
  kBound=(L/2)*Array.from({length:k+1},(_,i)=>(T*L/2)**i).reduce((s,v)=>s+v,0)*Math.floor(2*Math.log(U)/Math.log(P));
 function fac(n,cb){while(n>1){const p=spf[n];if(p>B)break;if(p>2)cb(p);while(n%p===0)n/=p;}}
 for(let j=lo;j<=hi;j++){
  for(const x of [2*j,2*j+2])fac(x,p=>{if(p>y)d[j]++;});
  const q=Math.min(spf[2*j-1],spf[2*j+1]);if(q<=B)r[j]=q;
 }
 function hit(t,C,K){
  let u=K+1,p=0;for(const sign of [-1,1])fac(C+sign,q=>{
   const m=2*q,rs=sign===-1?0:q+2,v=t+1+(rs-(t+1)%m+m)%m;
   if(v<u||(v===u&&v<=K&&q<p)){u=v;p=q;}
  });return [u,p];
 }
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a;};
 const get=C=>{let x=horizons.get(C);if(!x){x={list:[],good:0,recent:0,groups:new Map()};horizons.set(C,x);}return x;};
 let R=0,RK=0,removed=0,events=0,literal=0,finished=0,keptFinished=0,kept=0,goodVisits=0,recentVisits=0,regVisits=0,highHits=0,rootGoodVisitsMax=0,rootRecentVisitsMax=0,maxDeep=0;
 const fullW=new Float64Array(len),keptW=new Float64Array(len);
 for(let M=X+1;M<2*X;M+=2){
  const i=(M-X-1)/2,s=M+2,C0=2*M-2,K=Math.floor((7*M-1)/4),path=[];
  let t=s,C=C0,depth=0,inc=0,J=0,qHigh=0,depHigh=-1,regular=true,lowGain=0,flag=false,cost=0,twin=false,nh=0;
  for(;;){
   const j=C/2;
   ok(C<=2*t&&C>=C0&&C-C0<=2*H+B+6,'prefix invariant');
   if(depth<=kg&&d[j]>T)flag=true;
   const recent=!!qHigh&&depth-depHigh<=k;
   const e={i,M,C,t,inc,depth,good:depth<=kg,recent,recentDepth:recent?depth-depHigh:-1,regular:recent&&regular,J:recent?J:0,q:recent?qHigh:0,w:0,cost:0,tail:0,end:0};
   path.push(e);
   if(t>=s+H)break;
   const [u,p]=hit(t,C,K);
   if(X<=1024){let uu=K+1,pp=0;for(let v=t+1;v<=K;v++){
    const z=gcd(v%2?v-2:v,v%2?C+1:C-1);
    if(z>1&&spf[z]<=B){uu=v;pp=spf[z];break;}
   }ok(uu===u&&pp===p,'literal clock');literal++;}
   if(!p){ok(!r[j]&&spf[C-1]===C-1&&spf[C+1]===C+1,'twin');finished++;twin=true;break;}
   const q=r[j],dur=Math.max(0,Math.min(u-s,H)-Math.max(t-s,a));
   ok(q>0&&q<=p&&u-t<=2*q,'wait bound');
   e.w=dur/(2*q);e.cost=dur/2;cost+=e.cost;R+=e.cost;fullW[j]+=e.w;
   t=u;C+=p-1;inc=p;events++;
   if(p>y){depth++;lowGain=0;ok(C%p===0||(C+2)%p===0,'post divisor');
    if(p>=P){qHigh=p;J=C;depHigh=depth;regular=true;nh++;}
    else if(d[C/2]>T)regular=false;
   }else{lowGain+=p-1;ok(lowGain<L,'LOW barrier');}
  }
  ok(cost<=B&&nh*(P-1)<=2*H+B+6,'root budgets');
  maxDeep=Math.max(maxDeep,depth);
  if(flag){removed++;continue;}
  kept++;if(twin)keptFinished++;RK+=cost;highHits+=nh;
  let tail=0,gv=0,rv=0;
  for(let z=path.length-1;z>=0;z--){let e=path[z];tail+=e.cost;e.tail=tail;e.end=C;}
  for(const e of path){
   const x=get(e.C);x.list.push(e);
   if(e.good){gv++;goodVisits++;x.good++;}
   if(e.recent){rv++;recentVisits++;x.recent++;
    ok(e.J<=e.C&&e.q>=P&&(e.J%e.q===0||(e.J+2)%e.q===0),'recent key');
    if(e.regular){regVisits++;const key=e.J+':'+e.q;x.groups.set(key,(x.groups.get(key)||0)+1);}
   }
   keptW[e.C/2]+=e.w;
  }
  ok(gv<=(kg+1)*L/2&&rv<=nh*(k+1)*L/2,'visit caps');
  rootGoodVisitsMax=Math.max(rootGoodVisitsMax,gv);rootRecentVisitsMax=Math.max(rootRecentVisitsMax,rv);
  paths.push(path);
 }
 ok(R-RK<=B*removed,'root deletion budget');
 let maxGood=0,maxGroups=0,maxGroupMass=0,maxMass=0,S0=0,E=0,EK=0,diag=0;
 for(let j=lo;j<=hi;j++){S0+=r[j];E+=r[j]*fullW[j]**2;EK+=r[j]*keptW[j]**2;}
 for(const x of horizons.values()){
  maxGood=Math.max(maxGood,x.good);maxGroups=Math.max(maxGroups,x.groups.size);maxMass=Math.max(maxMass,x.list.length);
  for(const m of x.groups.values())maxGroupMass=Math.max(maxGroupMass,m);
  ok(x.good<=gBound&&x.groups.size<=kBound,'reverse leaf/key caps');
 }
 const names=['near','shortTail','bothGood','recentGood','recentThin','remaining'],counts=Array(6).fill(0),energy=Array(6).fill(0),sameEnergy=Array(6).fill(0),budget=Array(6).fill(0),ind={short:0,gg:0,rg:0,rt:0,regularBoth:0,deepThin:0,deepThinExtended:0,deepThinNonlow:0,deepRecentGood:0,deepRecentGoodNonlow:0};
 let pairs=0,physicalFirst=0,asyncFirst=0,rootContact=0,nonrootContact=0,laterSync=0,sameKey=0,totalPairVisits=0;
 // Only O(B) active pair records per current original root, not a global pair hash.
 for(const path of paths){
  const M=path[0].M,seen=new Map();
  for(const e of path){
   const x=get(e.C),q=r[e.C/2];diag+=q*e.w**2;
   for(const b of x.list){
    if(b.M>=M)break;
    const dist=M-b.M;ok(dist<=H+B/2+4,'final state root support');
    let v=seen.get(b.i);
    if(!v){
     pairs++;
     if(e.t===b.t)physicalFirst++;else asyncFirst++;
     if(!e.inc||!b.inc){rootContact++;ok(e.inc||b.inc,'distinct roots');}
     else{nonrootContact++;ok(e.inc!==b.inc,'first projected contact different incoming');}
     const short=Math.min(e.tail,b.tail)<=Z,gg=e.good&&b.good,
      rg=(e.recent&&b.good)||(b.recent&&e.good),rr=e.recent&&b.recent;
     const ke=e.J+':'+e.q,kb=b.J+':'+b.q;
     let rt=false;
     if(rr){ok(ke!==kb,'first contact distinct high keys');
      rt=(e.regular&&x.groups.get(ke)<=tau)||(b.regular&&x.groups.get(kb)<=tau);
      if(e.regular&&b.regular)ind.regularBoth++;
     }
     if(short)ind.short++;if(gg)ind.gg++;if(rg){ind.rg++;if(!gg){ind.deepRecentGood++;if((e.recentDepth>0&&b.good)||(b.recentDepth>0&&e.good))ind.deepRecentGoodNonlow++;}}
     if(rt){ind.rt++;if(!e.good&&!b.good){ind.deepThin++;if(e.depth>0&&b.depth>0&&(e.C!==e.J||b.C!==b.J))ind.deepThinExtended++;if(e.recentDepth>0||b.recentDepth>0)ind.deepThinNonlow++;}}
     const cls=dist<=near?0:short?1:gg?2:rg?3:rt?4:5;
     const cap=2*Math.min(e.tail,b.tail,1.5*(e.end-e.C),1.5*(b.end-b.C));
     v={cls,cap,w:0,phys:e.t===b.t,first:e.C};seen.set(b.i,v);counts[cls]++;budget[cls]+=cap;
    }
    if(!v.phys&&e.t===b.t){v.phys=true;laterSync++;}
    const w=2*q*e.w*b.w;v.w+=w;energy[v.cls]+=w;if(e.t===b.t)sameEnergy[v.cls]+=w;
    if(w)totalPairVisits++;
    ok(v.w<=v.cap+1e-7*Math.max(1,v.cap),'whole pair suffix bound');
   }
  }
 }
 ok(2*ind.gg<=goodVisits*Math.max(0,maxGood-1),'good-good count');
 ok(ind.rg<=maxGood*recentVisits,'recent-good count');
 ok(ind.rt<=maxGroups*tau*recentVisits,'recent-thin count');
 ok(energy.every((v,i)=>v<=budget[i]+1e-7*Math.max(1,budget[i])),'class bound');
 ok(Math.abs(EK-diag-energy.reduce((s,x)=>s+x,0))<=1e-7*Math.max(1,EK),'independent energy identity');
 ok(pairs===counts.reduce((s,x)=>s+x,0)&&pairs===physicalFirst+asyncFirst&&pairs===rootContact+nonrootContact,'pair partition');
 const named=a=>Object.fromEntries(names.map((n,i)=>[n,a[i]]));
 return {X,B,mode,N,L,y,T,P,kg,k,tau,Z,near,gBound,kBound,removed,kept,finished,keptFinished,events,literal,maxDeep,R,RK,E,EK,S0,diag,goodVisits,recentVisits,regVisits,highHits,rootGoodVisitsMax,rootRecentVisitsMax,maxGood,maxGroups,maxGroupMass,maxMass,pairs,physicalFirst,asyncFirst,rootContact,nonrootContact,laterSync,totalPairVisits,ind,counts:named(counts),energy:named(energy),sameEnergy:named(sameEnergy),budget:named(budget)};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','degree'])console.log(JSON.stringify(audit(X,mode)));
