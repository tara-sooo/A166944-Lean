// Reproduce: node research/min_prime_root_exit_phase_audit.mjs
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),ell=Math.log(u),analytic=mode==="analytic",T=analytic?Math.floor(X/u**.25):mode==="short"?B:4*B,Q=analytic?Math.ceil(B/u):mode==="wide"?7:Math.max(5,Math.ceil(B/8)),D=analytic?4*B:mode==="short"?Math.max(1,Math.floor(B/4)):4*B,m=analytic?Math.max(1,Math.floor(u**1.75/(1+ell))):1,I=analytic?u*u:3,cd=analytic?X*Math.sqrt(u)/(D+1):16,cs=analytic?X*u**1.5/(D+1):16;
 const lim=7*X+5,spf=new Int32Array(lim+1),ok=(v,s)=>{if(!v)throw Error(s);},mod=(a,n)=>((a%n)+n)%n,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c;}return a;};
 for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)spf[j]=spf[j]||n;}
 const fs=n=>{let a=[];while(n>1){let p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const all=new Map(),roots=new Map();let N=0,R=0,G=0,events=0,visits=0,cross=0,twins=0,literal=0,hiR=0,hiHits=0;
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){N++;let C=2*M-2,t=M+2,cut=Math.floor((7*M-1)/4),a=[],cost=0;
  while(true){const e={M,C,t,p:0,r:0,s:0,high:false,keep:false};a.push(e);if(!all.has(C))all.set(C,[]);all.get(C).push(e);visits++;
   if(C-(2*M-2)>=T){cross++;break;}
   let tt=Infinity,p=Infinity;for(const sg of [-1,1])for(const q of fs(C+sg)){let tick=t+1+mod((sg===-1?0:q+2)-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;}}
   if(X<=1024){let lt=Infinity,lp=Infinity;for(let w=t+1;w<=cut;w++){let f=fs(gcd(w%2?w-2:w,C+(w%2?1:-1)));if(f.length){lt=w;lp=f[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal");literal++;}
   if(tt>cut){if(spf[C-1]===C-1&&spf[C+1]===C+1)twins++;break;}
   const r=Math.min(...fs(C-1),...fs(C+1));ok(r<=p&&tt-t<=2*r,"clock");e.p=p;e.r=r;e.s=tt;cost+=r;events++;if(p>=Q&&r>p/(analytic?Math.sqrt(Math.log(p)):2)){e.high=true;hiR+=r;hiHits++;}
   C+=p-1;t=tt;ok(C<=2*t,"invariant");
  }
  const gain=C-(2*M-2);G+=gain;R+=cost;ok(gain<T+B&&2*cost<=3*gain,"gain");roots.set(M,a);
 }
 const firstPhys=new Set(),mergeExit=new Set(),syncSeen=new Set(),classes=["physical","immediate","nearCappedSame","nearCappedDistinct","nearImbalanced","nearBalancedLarge","far"],energy=Array(7).fill(0),count=Array(7).fill(0);
 let E0=0,E=0,diag=0,thinR=0,thinHits=0,groupCount=0,thinGroups=0,support=0,groupBound=0,degMax=0,eligibleMax=0,closeSame=0,closeDistinct=0,cappedSame=0,cappedDistinct=0,imbalancedEdges=0,edgeEnergy=0,imbEdgeEnergy=0,internal=0,incLag=0,decLag=0,flatLag=0,lagExamples={},smallIn=0,smallInFar=0,lagChecks=0,orderedNext=0,immediateCount=0,physicalChecks=0,allPairs=new Set(),crtChecks=0;
 const pairKey=(a,b)=>(Math.min(a.M,b.M)-X)*X+Math.max(a.M,b.M)-X;
 for(const C of [...all.keys()].sort((a,b)=>a-b)){
  const es=all.get(C);
  for(let i=0;i<es.length;i++)for(let j=i+1;j<es.length;j++){const a=es[i],b=es[j],id=pairKey(a,b);allPairs.add(id);if(syncSeen.has(id)){ok(a.t===b.t,"physical suffix");physicalChecks++;}else if(a.t===b.t){syncSeen.add(id);firstPhys.add(id);}if(a.p&&b.p){
    const d=Math.abs(a.t-b.t),d1=Math.abs(a.s-b.s);ok((a.t-b.t)*(a.s-b.s)>=0&&Math.abs(d1-d)<2*a.r,"monotone next and lag variation");orderedNext++;
    if(a.s===b.s)ok(a.p===b.p,"tie unique");
    if(a.p===b.p){ok(d1%(2*a.p)===0&&(d1===2*a.p*Math.floor(d/(2*a.p))||d1===2*a.p*Math.ceil(d/(2*a.p))),"same prime rounding");lagChecks++;if(d>0&&d1>0){const typ=d1>d?"up":d1<d?"down":"flat";if(typ==="up")incLag++;else if(typ==="down")decLag++;else flatLag++;if(!lagExamples[typ])lagExamples[typ]={M:a.M,Mp:b.M,C,p:a.p,t:a.t,tp:b.t,s:a.s,sp:b.s,d,d1};}}
    if(d&&a.s===b.s){ok(!mergeExit.has(id),"unique immediate synchronization");mergeExit.add(id);}
  }}
  const high=es.filter(e=>e.high);if(!high.length)continue;const r=high[0].r;E0+=r*high.length**2;support++;const mm=new Map(),key=e=>e.s+":"+e.p;
  for(const e of high){const k=key(e);if(!mm.has(k))mm.set(k,[]);mm.get(k).push(e);}
  const elig=[...fs(C-1),...fs(C+1)];eligibleMax=Math.max(eligibleMax,elig.length);
  if(r**3>C+1)ok(elig.length<=4,"at most four eligible primes");
  const span=3*(T+B)+2*B+6;let bound=0;for(const p of elig)if(p>=Q)bound+=Math.floor(span/(2*p))+1;
  ok(mm.size<=bound,"exit group support");groupBound+=bound;groupCount+=mm.size;
  const kept=[];for(const v of mm.values())if(v.length<=m){thinGroups++;thinR+=r*v.length;thinHits+=v.length;}else{for(const e of v){e.keep=true;kept.push(e);}}
  if(!kept.length)continue;
  E+=r*kept.length**2;diag+=r*kept.length;const groups=[...mm.values()].filter(v=>v.length>m).sort((a,b)=>a[0].s-b[0].s);let deg=Array(groups.length).fill(0);for(const g of groups)internal+=r*g.length**2;
  for(let i=0;i<groups.length;i++)for(let j=i+1;j<groups.length&&groups[j][0].s-groups[i][0].s<=D;j++){
   const a=groups[i],b=groups[j],p=a[0].p,q=b[0].p,h=b[0].s-a[0].s;ok(h>0,"unique exit time");deg[i]++;deg[j]++;
   if(p===q){ok(h%(2*p)===0,"same label period");closeSame++;if(a.length*b.length<=cs)cappedSame++;}
   else{closeDistinct++;if(a.length*b.length<=cd)cappedDistinct++;const sg=(C-1)%p===0?-1:1,sh=(C-1)%q===0?-1:1;ok((C+sg)%p===0&&(C+sh)%q===0&&mod(a[0].s,2*p)===(sg===-1?0:mod(p+2,2*p))&&mod(b[0].s,2*q)===(sh===-1?0:mod(q+2,2*q)),"distinct CRT residues");crtChecks++;}
   edgeEnergy+=2*r*a.length*b.length;if(Math.min(a.length,b.length)*I<=Math.max(a.length,b.length)){imbalancedEdges++;imbEdgeEnergy+=2*r*a.length*b.length;}
  }
  const degreeLimit=elig.filter(p=>p>=Q).reduce((s,p)=>s+Math.floor(D/p)+1,0);ok(deg.every(d=>d<=degreeLimit),"close graph degree");degMax=Math.max(degMax,...deg);
  for(let i=0;i<kept.length;i++)for(let j=i+1;j<kept.length;j++){
   const a=kept[i],b=kept[j],d=Math.abs(a.t-b.t),d1=Math.abs(a.s-b.s),ma=mm.get(key(a)).length,mb=mm.get(key(b)).length;let cl;
   if(!d)cl=0;else if(!d1){cl=1;immediateCount++;}else if(d1>D)cl=6;else if(ma*mb<=(a.p===b.p?cs:cd))cl=a.p===b.p?2:3;else if(Math.min(ma,mb)*I<=Math.max(ma,mb))cl=4;else cl=5;
   if(d>0&&d<=Math.max(0,D-2*B)){smallIn++;if(d1>D)smallInFar++;}
   energy[cl]+=2*r;count[cl]++;
  }
 }
 ok(E===diag+energy.reduce((a,b)=>a+b,0)&&E<=E0&&diag===hiR-thinR,"energy/linear partition");
 ok(thinHits<=m*groupCount&&immediateCount<=mergeExit.size&&smallInFar===0,"charge and small lag");
 ok(energy[2]+energy[3]+energy[4]+energy[5]===edgeEnergy&&energy[4]<=imbEdgeEnergy&&imbEdgeEnergy<=2*degMax*internal/I+1e-6,"imbalance bound");
 return {mode,X,B,T,Q,D,m,I,cd,cs,N,R,G,events,visits,cross,twins,literal,hiHits,hiR,E0,E,diag,thinR,thinHits,support,groupCount,groupBound,thinGroups,degMax,eligibleMax,closeSame,closeDistinct,cappedSame,cappedDistinct,imbalancedEdges,edgeEnergy,imbEdgeEnergy,internal,incLag,decLag,flatLag,lagExamples,smallIn,smallInFar,lagChecks,orderedNext,immediateCount,physicalChecks,allPairs:allPairs.size,mergeExit:mergeExit.size,crtChecks,energy:Object.fromEntries(classes.map((s,i)=>[s,energy[i]])),count:Object.fromEntries(classes.map((s,i)=>[s,count[i]]))};
}
const xs=process.argv.slice(2).map(Number);for(const mode of ['short','wide','analytic'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
