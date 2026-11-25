// Last-high physical anchor pair CRT and weighted tail caps.
// Run node research/min_clock_anchor_pair_audit.mjs 1024 4096 16384 65536
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
 const A=mode==='analytic'?Math.floor(Math.log(B)**.125):Math.max(2,Math.floor(P/8)), capDiff=mode==='analytic'?Math.log(B)**3.5:256,capSame=mode==='analytic'?Math.log(B)**2.5:144;
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
 const get=C=>{let x=horizons.get(C);if(!x){x={list:[],good:0,recent:0,groups:new Map(),physical:new Map(),regPhysical:new Map()};horizons.set(C,x);}return x;};
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
  for(const e of path){
   const x=get(e.C);x.list.push(e);
   if(e.good){gv++;goodVisits++;x.good++;}
   if(e.recent){rv++;recentVisits++;x.recent++;
    ok(e.J<=e.C&&e.q>=P&&(e.J%e.q===0||(e.J+2)%e.q===0),'recent key');
    if(e.regular){regVisits++;const key=e.J+':'+e.q;x.groups.set(key,(x.groups.get(key)||0)+1);x.regPhysical.set(e.anchor,(x.regPhysical.get(e.anchor)||0)+1);}
   }
   if(e.anchor){
    if(!anchorMap.has(e.anchor))anchorMap.set(e.anchor,{t:e.anchorT,J:e.anchorJ,p:e.anchorP,n:0});
    const an=anchorMap.get(e.anchor);if(e.C===e.anchorJ)an.n++;
    const group=x.physical.get(e.anchor)||{n:0,R:0,t:e.t};ok(group.t===e.t,'physical anchor deterministic replay');group.n++;group.R+=e.tail;x.physical.set(e.anchor,group);
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

 const plist=[];for(let p=Math.max(3,P);p<=B;p++)if(spf[p]===p)plist.push(p);
 const maxDelta=2*(H+2*B)+6, tLo=X+3,tHi=2*X+2+H+2*B;
 let envelopeDiff=0,envelopeSame=0;
 for(const p of plist){
  const nC=Math.floor(5*X/(2*p))+2,nT=Math.floor((tHi-tLo)/(2*p))+2,
   cTime=Math.floor(maxDelta/(4*p))+2,cHor=Math.floor(maxDelta/(2*p))+2;
  envelopeSame+=8*(nC*cTime*cTime+nT*cHor*cHor);
  for(const q of plist)if(p!==q){
   const m=p*q, nnC=Math.floor(5*X/(2*m))+2,nnT=Math.floor((tHi-tLo)/m)+2,
     cTq=Math.floor(maxDelta/(4*q))+2,cHq=Math.floor(maxDelta/(2*q))+2;
   envelopeDiff+=4*((2*A+1)*nnC*cTime*cTq+(2*A+1)*nnT*cHor*cHq);
  }
 }
 const names=['near','shortTail','bothGood','recentGood','recentThin','physicalThin','anchorDiff','anchorSame','remaining'];
 const counts=Array(names.length).fill(0),energy=counts.slice(),sameEnergy=counts.slice(),budget=counts.slice();
 const ind={physicalThin:0,physicalThinExtra:0,anchorDiff:0,anchorSame:0,anchorDiffExtra:0,anchorSameExtra:0,diffBothThick:0,diffDeep:0,diffLongSuffix:0,diffWeightedExtra:0,closeH:0,closeT:0,sameNearH:0,sameNearT:0};
 const contactMap=new Map();let pairs=0,physicalFirst=0,asyncFirst=0,rootContact=0,laterSync=0,nearAnchorDiffRecords=0,nearAnchorSameRecords=0,nearAnchorDiffBound=0,nearAnchorSameBound=0,thinKeyMax=0,physicalAnchorPairMaxMass=0;
 const maxAnchorTimeChoices=2*(Math.floor(maxDelta/(4*P))+2);
 for(const x of horizons.values()){thinKeyMax=Math.max(thinKeyMax,x.regPhysical.size);ok(x.regPhysical.size<=kBound*maxAnchorTimeChoices,'regular physical key cap');}
 function pairKey(a,b){return a<b?a+'|'+b:b+'|'+a;}
 for(const path of paths){
  const M=path[0].M,seen=new Map();
  for(const e of path){
   const x=get(e.C),q=r[e.C/2];diag+=q*e.w**2;
   for(const b of x.list){
    if(b.M>=M)break;
    const dist=M-b.M;ok(dist<=H+B/2+4,'pair support');
    let v=seen.get(b.i);
    if(!v){
     pairs++;if(e.t===b.t)physicalFirst++;else asyncFirst++;
     if(!e.inc||!b.inc){rootContact++;ok(e.inc||b.inc,'distinct roots');}else ok(e.inc!==b.inc,'different incoming at first projected contact');
     const short=Math.min(e.tail,b.tail)<=Z,gg=e.good&&b.good,rg=(e.recent&&b.good)||(b.recent&&e.good),rr=e.recent&&b.recent;
     const ke=e.J+':'+e.q,kb=b.J+':'+b.q;
     const rt=rr&&((e.regular&&x.groups.get(ke)<=tau)||(b.regular&&x.groups.get(kb)<=tau));
     const pt=rr&&((e.regular&&x.regPhysical.get(e.anchor)<=tau)||(b.regular&&x.regPhysical.get(b.anchor)<=tau));
     if(rt)ok(pt,'projected thin subset physical thin');
     if(pt){ind.physicalThin++;if(!rt)ind.physicalThinExtra++;}
     let ad=false,as=false,lagFloor=0,record=null;
     if(e.anchor&&b.anchor){
      ok(e.anchor!==b.anchor,'same physical anchor impossible at first projected contact');
      ok(e.anchorJ!==b.anchorJ||e.anchorP!==b.anchorP,'same projected anchor impossible at first contact');
      const dh=Math.abs(e.anchorJ-b.anchorJ),dt=Math.abs(e.anchorT-b.anchorT),ch=dh<=A,ct=dt<=A;
      if(ch||ct){
       const ge=x.physical.get(e.anchor),gb=x.physical.get(b.anchor),nk=pairKey(e.anchor,b.anchor),prev=contactMap.get(nk);
       if(prev)ok(prev.C===e.C,'unique first suffix intersection');
       const p=e.anchorP,p2=b.anchorP,different=p!==p2;
       const weighted=Math.min(ge.n*gb.R,gb.n*ge.R)/B,prod=ge.n*gb.n;
       ok(weighted<=prod+1e-9,'tail product cap');
       physicalAnchorPairMaxMass=Math.max(physicalAnchorPairMaxMass,prod);
       if(different){
        ad=weighted<=capDiff;
        if(ch)ind.closeH++;if(ct)ind.closeT++;
        if(ad){
         ind.anchorDiff++;
         if(!pt)ind.anchorDiffExtra++;
         if(ge.n>tau&&gb.n>tau)ind.diffBothThick++;
         if(!e.good&&!b.good)ind.diffDeep++;
         if(e.anchorDepth>k||b.anchorDepth>k)ind.diffLongSuffix++;
         if(prod>capDiff)ind.diffWeightedExtra++;
        }
       }else{
        ok(A<p-2,'near same-label cutoff');
        if(ch){ok(dh===2,'same prime near horizon opposite sides');ok(dt>=p-2,'same prime opposite clock gap');ind.sameNearH++;}
        if(ct){ok(dt===0&&dh>=2*p,'same prime near time equal clock distinct horizons');ind.sameNearT++;}
        ok(!(ch&&ct),'same prime cannot be close in both');
        if(ch)lagFloor=Math.max(0,dt-3*Math.max(e.C-e.anchorJ,b.C-b.anchorJ));
        if(lagFloor)ok(Math.abs(e.t-b.t)>=lagFloor,'anchor lag lower bound');
        as=weighted<=capSame;if(as){ind.anchorSame++;if(!pt)ind.anchorSameExtra++;}
       }
       if(!prev){
        record={C:e.C,different,n:0,w:0,cap:2*B*weighted,eligible:different?ad:as,prod};contactMap.set(nk,record);
        if(different){nearAnchorDiffRecords++;if(ad)nearAnchorDiffBound+=record.cap;}
        else{nearAnchorSameRecords++;if(as)nearAnchorSameBound+=record.cap;}
       }else{record=prev;ok(record.eligible===(different?ad:as),'group classification stable');}
       record.n++;
      }
     }
     const cls=dist<=near?0:short?1:gg?2:rg?3:rt?4:pt?5:ad?6:as?7:8;
     const cap=2*Math.min(e.tail,b.tail,1.5*(e.end-e.C),1.5*(b.end-b.C));
     v={cls,cap,w:0,phys:e.t===b.t,first:e.C,record,lagFloor};seen.set(b.i,v);counts[cls]++;budget[cls]+=cap;
    }
    if(!v.phys&&e.t===b.t){v.phys=true;laterSync++;ok(3*(e.C-v.first)>=v.lagFloor,'minimum synchronization gain');}
    const w=2*q*e.w*b.w;v.w+=w;energy[v.cls]+=w;if(e.t===b.t)sameEnergy[v.cls]+=w;
    if(v.record)v.record.w+=w;
    ok(v.w<=v.cap+1e-7*Math.max(1,v.cap),'whole pair tail bound');
   }
  }
 }
 let measuredDiff=0,measuredSame=0;
 for(const rec of contactMap.values()){
  ok(rec.n<=rec.prod&&rec.w<=rec.cap+1e-7*Math.max(1,rec.cap),'aggregate actual anchor pair bound');
  if(rec.eligible){if(rec.different)measuredDiff+=rec.w;else measuredSame+=rec.w;}
 }
 ok(nearAnchorDiffRecords<=envelopeDiff&&nearAnchorSameRecords<=envelopeSame,'CRT arithmetic envelope');
 ok(measuredDiff<=nearAnchorDiffBound+1e-6*Math.max(1,E)&&measuredSame<=nearAnchorSameBound+1e-6*Math.max(1,E),'weighted aggregate cap');
 ok(ind.physicalThin<=recentVisits*thinKeyMax*tau,'physical thin bound');
 ok(Math.abs(EK-diag-energy.reduce((s,v)=>s+v,0))<=1e-7*Math.max(1,EK),'exact E decomposition');
 ok(pairs===counts.reduce((s,n)=>s+n,0),'pair partition');
 const named=a=>Object.fromEntries(names.map((n,i)=>[n,a[i]]));
 return {X,B,mode,P,A,kg,k,L,T,tau,capDiff,capSame,removed,kept,events,literal,RK,E,EK,diag,pairs,physicalFirst,asyncFirst,laterSync,highHits,recentVisits,regVisits,maxGroups,maxGroupMass,thinKeyMax,anchorCount:anchorMap.size,nearAnchorDiffRecords,nearAnchorSameRecords,envelopeDiff,envelopeSame,physicalAnchorPairMaxMass,nearAnchorDiffBound,nearAnchorSameBound,measuredDiff,measuredSame,ind,counts:named(counts),energy:named(energy),sameEnergy:named(sameEnergy)};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','degree'])console.log(JSON.stringify(audit(X,mode)));
