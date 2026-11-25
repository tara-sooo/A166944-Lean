// First heavy crossing, moving reverse ancestry windows.
// Run node research/min_clock_first_heavy_audit.mjs 1024 4096 16384 65536
function audit(X,mode='diagnostic'){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,ell=Math.log(Math.log(B)),S=Math.max(1,Math.log(ell)),U=7*X+2;
 const ok=(b,m)=>{if(!b)throw Error(m);};
 ok(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(U+4);
 for(let p=2;p<spf.length;p++)if(!spf[p]){
  spf[p]=p;if(p*p<spf.length)for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 }
 let L=2,y=2;for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>6*S**.25)break;L*=p;y=p;}
 const T=mode==='degree'?4:(mode==='diagnostic'||(mode==='wide'||mode==='clock'))?6:Math.ceil(20*ell),g=Math.max(2,T*L),
  kg=mode==='analytic'?Math.floor(1.5*ell/Math.log(g)):5,
  k=mode==='analytic'?Math.floor(ell/(8*Math.log(g))):3,
  P=mode==='analytic'?Math.ceil(B/Math.log(B)**.125):Math.ceil(B/((mode==='wide'||mode==='clock')?8:4)),
  tau=mode==='analytic'?Math.log(B)**1.5:12,
  Z=mode==='analytic'?Math.log(B)**1.5:12,
  near=mode==='analytic'?Math.floor(4*Math.log(B)):Math.max(2,Math.floor(B/64));
 const A=mode==='analytic'?Math.floor(Math.log(B)**.125):Math.max(2,Math.floor(P/((mode==='wide'||mode==='clock')?2:8))), capDiff=mode==='analytic'?Math.log(B)**3.5:256,capSame=mode==='analytic'?Math.log(B)**2.5:144;
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
 const get=C=>{let x=horizons.get(C);if(!x){x={list:[],good:0,recent:0,groups:new Map(),physical:new Map(),regPhysical:new Map(),occupation:new Map()};horizons.set(C,x);}return x;};
 let R=0,RK=0,removed=0,events=0,literal=0,finished=0,keptFinished=0,kept=0,goodVisits=0,recentVisits=0,regVisits=0,highHits=0,rootGoodVisitsMax=0,rootRecentVisitsMax=0,maxDeep=0;
 const fullW=new Float64Array(len),keptW=new Float64Array(len),anchorMap=new Map();
 for(let M=X+1;M<2*X;M+=2){
  const i=(M-X-1)/2,s=M+2,C0=2*M-2,K=Math.floor((7*M-1)/4),path=[];
  let t=s,C=C0,depth=0,inc=0,J=0,uHigh=0,qHigh=0,depHigh=-1,regular=true,lowGain=0,flag=false,cost=0,twin=false,nh=0;
  for(;;){
   const j=C/2;
   ok(C<=2*t&&C>=C0&&C-C0<=2*H+B+6,'prefix invariant');
   if(depth<=kg&&d[j]>T)flag=true;
   const recent=!!qHigh&&depth-depHigh<=k;
   const e={i,M,C,t,inc,depth,good:depth<=kg,recent,recentDepth:recent?depth-depHigh:-1,regular:recent&&regular,J:recent?J:0,q:recent?qHigh:0,anchor:qHigh?uHigh+':'+J+':'+qHigh:'',anchorJ:J,anchorT:uHigh,anchorP:qHigh,anchorDepth:qHigh?depth-depHigh:-1,w:0,cost:0,tail:0,end:0};
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
    if(p>=P){qHigh=p;J=C;uHigh=t;depHigh=depth;regular=true;nh++;}
    else if(d[C/2]>T)regular=false;
   }else{lowGain+=p-1;ok(lowGain<L,'LOW barrier');}
  }
  ok(cost<=B&&nh*(P-1)<=2*H+B+6,'root budgets');
  maxDeep=Math.max(maxDeep,depth);
  if(flag){removed++;continue;}
  kept++;if(twin)keptFinished++;RK+=cost;highHits+=nh;
  let tail=0,gv=0,rv=0;
  for(let z=path.length-1;z>=0;z--){let e=path[z];tail+=e.cost;e.tail=tail;e.end=C;}
  const past=[];for(let ix=0;ix<path.length;ix++){
   const e=path[ix];e.ix=ix;if(e.anchor&&e.C===e.anchorJ)past.push(e.anchor);
   const x=get(e.C);if(e.w)for(const id of past)x.occupation.set(id,(x.occupation.get(id)||0)+e.w);x.list.push(e);
   if(e.good){gv++;goodVisits++;x.good++;}
   if(e.recent){rv++;recentVisits++;x.recent++;
    ok(e.J<=e.C&&e.q>=P&&(e.J%e.q===0||(e.J+2)%e.q===0),'recent key');
    if(e.regular){regVisits++;const key=e.J+':'+e.q;x.groups.set(key,(x.groups.get(key)||0)+1);x.regPhysical.set(e.anchor,(x.regPhysical.get(e.anchor)||0)+1);}
   }
   if(e.anchor){
    if(!anchorMap.has(e.anchor))anchorMap.set(e.anchor,{t:e.anchorT,J:e.anchorJ,p:e.anchorP,n:0,tags:[]});
    const an=anchorMap.get(e.anchor);if(e.C===e.anchorJ){an.n++;an.tags.push({M:e.M,tail:e.tail});}
    const group=x.physical.get(e.anchor)||{n:0,R:0,t:e.t,tails:[]};ok(group.t===e.t,'physical anchor deterministic replay');group.n++;group.R+=e.tail;group.tails.push(e.tail);x.physical.set(e.anchor,group);
    const p=e.anchorP,t=e.anchorT,J=e.anchorJ;ok(t%2===0?t%(2*p)===0&&J%p===0:(t-(p+2))%(2*p)===0&&(J+2)%p===0,'anchor clock residues');
    ok(2*t-J>=0&&2*t-J<=2*(H+2*B)+6,'anchor deficit strip');ok(e.t-t<=3*(e.C-J),'suffix elapsed');
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




 const u=Math.log(B),tauP=mode==='analytic'?Math.floor(u**2.5):12,tauS=mode==='analytic'?Math.floor(u**2.25):8,
 k0=mode==='analytic'?Math.floor(ell/(4*Math.log(g))):3,k1=k0+1;
 const exceptional=new Uint8Array(len);let nD=0,Dedge=0;
 for(let j=lo;j<=hi;j++)if(d[j]>T){exceptional[j]=1;nD++;Dedge+=d[j];}
 let cur=exceptional,curN=nD,reverse=new Uint8Array(len),layers=[nD];
 for(let k=0;k<=k1;k++){
  const J=new Uint8Array(len);let n=0;
  for(let x=lo;x<=hi;x++)if(cur[x])for(let e=0;e<L/2&&x-e>=lo;e++){if(!J[x-e]){J[x-e]=1;n++;}reverse[x-e]=1;}
  ok(n<=L/2*curN,'low offset set cap');
  if(k===k1)break;
  const next=new Uint8Array(len);let nn=0,edges=0;
  for(let j=lo;j<=hi;j++)if(J[j])for(const a0 of [2*j,2*j+2])fac(a0,p=>{if(p<=y)return;edges++;const v=j-(p-1)/2;if(v>=lo&&!next[v]){next[v]=1;nn++;}});
  ok(nn<=edges&&edges<=T*n+Dedge,'exception edge recurrence');cur=next;curN=nn;layers.push(nn);
 }
 const leaf=(L/2)*Array.from({length:k1+1},(_,i)=>(T*L/2)**i).reduce((s,v)=>s+v,0);
 const physicalKeyCap=kBound*2*(Math.floor((2*(H+2*B)+6)/(4*P))+2);
 const startCap=tauP+tauS*physicalKeyCap+gBound+1;
 let startMax=0,reverseStartMass=0,reverseHorizons=0,referencePhysicalMax=0;
 for(const [C,x] of horizons){
  x.states=new Map();x.P=x.list.length;x.starts=0;x.projectedGood=0;x.extended=0;
  for(const e of x.list){const v=x.states.get(e.t)||{n:0,g:0,e:0};v.n++;x.states.set(e.t,v);}
  let regularTimes=new Set();
  for(const e of x.list){
   e.pLight=x.P<=tauP;e.sLight=x.states.get(e.t).n<=tauS;
   e.cert=e.ix===0||e.sLight&&(e.regular||e.good);
   e.start=e.ix===0||e.pLight||e.cert;
   if(e.regular)regularTimes.add(e.t);
   if(e.start)x.starts++;
   referencePhysicalMax=Math.max(referencePhysicalMax,x.states.get(e.t).n);
  }
  ok(regularTimes.size<=physicalKeyCap&&x.starts<=startCap,'certified start count');
  startMax=Math.max(startMax,x.starts);
  if(reverse[C/2]){reverseHorizons++;reverseStartMass+=x.starts;}
 }
 let cut=0,cutR=0,retained=[],crossP=0,crossS=0,extendedS=0,neverP=0,neverS=0,deepP=0,deepS=0,maxDepthBeforeP=0,postPVisits=0,postSVisits=0,prePVisits=0,preSVisits=0,cutAtDeep=0;
 const W=new Float64Array(len),WP=new Float64Array(len),WX=new Float64Array(len);
 const state=(e)=>horizons.get(e.C).states.get(e.t);
 for(const path of paths){
  let last=null,flag=false,deepFlag=false;
  for(const e of path){
   if(e.start)last=e;
   if(last&&e.depth-last.depth<=k1&&d[e.C/2]>T){
    ok(reverse[last.C/2]===1,'actual starting horizon in reverse exceptional union');flag=true;if(e.depth>kg)deepFlag=true;
   }
  }
  if(flag){cut++;cutAtDeep+=+deepFlag;cutR+=path.reduce((s,e)=>s+e.cost,0);continue;}
  retained.push(path);
  const ip=path.findIndex(e=>!e.pLight),is=path.findIndex(e=>!e.sLight);
  if(ip>=0){crossP++;maxDepthBeforeP=Math.max(maxDepthBeforeP,path[ip].depth);if(path[ip].depth>kg)deepP++;}
  else neverP++;
  if(is>=0){crossS++;if(path[is].depth>kg)deepS++;}
  else neverS++;
  const extendS=is===0||is>0&&path[is-1].cert;
  if(extendS&&is>=0)extendedS++;
  let lastGood=null,goodEnded=false;
  for(const e of path){
   const x=horizons.get(e.C),j=e.C/2;
   e.gp=ip<0||e.ix<ip||e.depth-path[ip].depth<=k0;
   e.freshP=ip>=0&&e.ix>=ip&&e.gp;
   e.gs=is<0||e.ix<is||extendS&&e.depth-path[is].depth<=k0;
   e.freshS=is>=0&&e.ix>=is&&e.gs;
   e.gu=e.gp||e.gs;
   if(e.gu){ok(!goodEnded,'union good prefix');lastGood=e;}else goodEnded=true;
   if(e.gp){x.projectedGood++;WP[j]+=e.w;if(e.freshP)postPVisits++;else prePVisits++;}
   if(e.freshS){x.extended++;WX[j]+=e.w;postSVisits++;}else if(e.gs)preSVisits++;
   for(const ip0 of [e.freshP?Math.max(0,ip-1):-1,e.freshS?Math.max(0,is-1):-1])if(ip0>=0){
    ok(path[ip0].start&&e.depth-path[ip0].depth<=k1,'fresh crossing start');
    for(let l=ip0+1;l<=e.ix;l++)if(path[l].inc>y)ok(d[path[l].C/2]<=T,'regular actual fresh suffix');
   }
   if(e.gu)state(e).g++;
   W[j]+=e.w;
  }
  ok(lastGood,'root good at start');state(lastGood).e++;
 }
 ok(cut<=reverseStartMass&&cutR<=cut*B,'exception root deletion');
 const cap=tauP+startCap*leaf,pcap=tauS+cap+startCap*leaf;
 let E2=0,R2=0,diag2=0,Rgood=0,EgCurrent=0,ExCurrent=0,maxGP=0,maxExt=0,maxPhysGood=0,expiry=0;
 for(let j=lo;j<=hi;j++){const q=r[j];E2+=q*W[j]**2;R2+=q*W[j];Rgood+=q*WP[j];EgCurrent+=q*(2*W[j]*WP[j]-WP[j]**2);ExCurrent+=q*(2*W[j]*WX[j]-WX[j]**2);}
 for(const x of horizons.values()){
  maxGP=Math.max(maxGP,x.projectedGood);maxExt=Math.max(maxExt,x.extended);
  ok(x.projectedGood<=cap&&x.extended<=startCap*leaf,'moving reverse leaf mass');
  for(const v of x.states.values()){ok(v.e<=v.g&&v.g<=pcap,'physical prefix cap');maxPhysGood=Math.max(maxPhysGood,v.g);expiry+=v.e*(v.g-v.e)+v.e*(v.e-1)/2;}
 }
 ok(Math.abs(RK-R2-cutR)<=1e-7*Math.max(1,RK),'linear deletion identity');
 ok(EgCurrent<=2*cap*R2+1e-6*Math.max(1,E2)&&ExCurrent<=2*startCap*leaf*R2+1e-6*Math.max(1,E2),'current energy caps');
 const classEnergy=[0,0,0],classPairs=[0,0,0];
 let ggPhysical=0,sharedGG=0,firstProjected=0,firstPhysical=0,freshPhysicalDeep=0,freshProjectedDeep=0,mixedRecentDeep=0,currentGG=0,physicalFreshGood=0;
 for(const path of retained){const seen=new Map();
  for(const e of path){const x=horizons.get(e.C),q=r[e.C/2];diag2+=q*e.w**2;
   for(const b of x.list){if(b.M>=e.M)break;if(b.gu===undefined)continue;
    let v=seen.get(b.i);
    if(!v){firstProjected++;const fresh=(e.freshP&&b.gp)||(b.freshP&&e.gp),recent=(e.gp&&b.recent)||(b.gp&&e.recent);
     const cls=fresh?0:recent?1:2;
     if(fresh&&(!e.good||!b.good))freshProjectedDeep++;
     if(recent&&(!e.good||!b.good))mixedRecentDeep++;
     classPairs[cls]++;v={cls,met:false,gg:false};seen.set(b.i,v);
    }
    if(!v.met&&e.t===b.t){v.met=true;firstPhysical++;v.gg=e.gu&&b.gu;if(v.gg){ggPhysical++;if(!e.good||!b.good)freshPhysicalDeep++;if(e.freshS||b.freshS||e.freshP||b.freshP)physicalFreshGood++;}}
    const w=2*q*e.w*b.w;classEnergy[v.cls]+=w;if(v.gg&&e.t===b.t)sharedGG+=w;if(e.gu&&b.gu&&e.t===b.t)currentGG+=w;
   }
  }
 }
 ok(ggPhysical===expiry&&ggPhysical<=retained.length*Math.max(0,maxPhysGood-1),'physical expiry exact');
 ok(sharedGG<=2*B*ggPhysical+1e-6*Math.max(1,E2),'whole same state suffix cap');
 ok(Math.abs(E2-diag2-classEnergy.reduce((s,v)=>s+v,0))<=1e-7*Math.max(1,E2),'energy oracle');
 ok(classPairs[0]<=postPVisits*cap,'fresh projected pair cap');
 ok(classPairs[1]<=recentVisits*cap,'recent projected pair cap');
 return {X,B,mode,tauP,tauS,k0,k1,T,L,P,reference:kept,referencePhysicalMax,removed,cut,cutR,cutAtDeep,nD,Dedge,layers,reverseHorizons,reverseStartMass,startMax,startCap,leaf,cap,pcap,retained:retained.length,R2,E2,EK,S0,diag:diag2,events,literal,crossP,crossS,neverP,neverS,extendedS,deepP,deepS,maxDepthBeforeP,postPVisits,postSVisits,prePVisits,preSVisits,maxGP,maxExt,maxPhysGood,Rgood,EgCurrent,ExCurrent,firstProjected,firstPhysical,ggPhysical,expiry,sharedGG,currentGG,physicalFreshGood,freshPhysicalDeep,freshProjectedDeep,mixedRecentDeep,classPairs,classEnergy};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','degree','wide'])console.log(JSON.stringify(audit(X,mode)));
