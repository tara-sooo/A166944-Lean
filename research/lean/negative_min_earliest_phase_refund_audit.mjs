// Earliest-phase cap-one policy, exact refund identity, and weighted roughness field.
// Run: node research/lean/negative_min_earliest_phase_refund_audit.mjs
// Finite proxy parameters; no asymptotic inference from sample counts.
function audit() {
 const check=(b,m)=>{if(!b)throw Error(m)},mod=(x,p)=>(x%p+p)%p;
 const maxR=48000,sp=new Int32Array(2*maxR+3);
 for(let p=2;p<sp.length;p++)if(!sp[p]){sp[p]=p;if(p*p<sp.length)for(let n=p*p;n<sp.length;n+=p)if(!sp[n])sp[n]=p}
 function fac(n){let a=[];while(n>1){let p=sp[n];check(p>0,"factor range");a.push(p);while(n%p===0)n/=p}return a}
 const cache=new Map();
 function info(x){if(!cache.has(x)){let c=[...fac(x+1).map(p=>[p,0]),...fac(x-1).map(p=>[p,p+2])];cache.set(x,{c,q:Math.min(...c.map(a=>a[0])),twin:sp[x-1]===x-1&&sp[x+1]===x+1})}return cache.get(x)}
 function next(x,n){let f=Infinity,p0=0;for(let [p,c] of info(x).c){let w=mod(c-n,2*p)||2*p;if(n+w<f||(n+w===f&&p<p0)){f=n+w;p0=p}}return {f,p:p0}}
 const rows=[];
 for(const [R,T,K] of [[3000,72,5],[12000,144,11],[48000,312,19]]){
  const W=6*Math.floor(T/6),lo=Math.ceil(R/6)*6,S=Math.ceil(Math.sqrt(2*R+1)),windows=Math.floor((2*R-lo)/W)+1;
  let roots=0,fullTicks=0,uniqueTicks=0,roughTicks=0,terminalNonrough=0,earliestValue=0,optimum=0,firstIdle=0,phaseCount=0,eventCount=0,actualWaitChecks=0,netChecks=0,twinRoots=0,weighted=0,weightedTwin=0,weightedNonTwin=0,weightedBirth=0,binChecks=0,mergers=0;
  let sites=new Map();
  for(let J=0;J<windows;J++){
   const a0=lo+J*W,a1=Math.min(2*R,a0+W-6),obs=3-a0/2,end=obs+T,first=3-a1/2;
   const phases=new Map(),births=new Map(),paths=[];
   for(let A=a0;A<=a1;A+=6){
    roots++;const b=3-A/2;births.set(b,A);if(info(A).twin)twinRoots++;
    let x=A,n=b,word=[];
    while(n<end){
     let {f,p}=next(x,n),e=Math.min(f,end),key=x+","+f,v=phases.get(key);
     if(!v)phases.set(key,v={x,f,p,a:n,e,arrivals:0});else v.a=Math.min(v.a,n);
     v.arrivals++;word.push({x,n,f,p,e,key});
     if(word.length===1){const idle=Math.min(end-n,f-n-1);firstIdle+=idle;weightedBirth+=Math.min(S,info(x).q)*Math.min(end-n,f-n);check(f-n>=(info(x).q-7)/2,"canonical first wait height bound")}
     fullTicks+=e-n;
     if(f<=end){eventCount++;n=f;x-=p-1}else break;
    }
    paths.push({A,b,word});
   }
   const all=new Map(),profits=new Map();
   for(let ph of phases.values()){
    phaseCount++;let {x,a,e,f}=ph,q=info(x).q,len=e-a;
    if(q>=K)roughTicks+=len;
    else if(f>end)terminalNonrough+=len;
    uniqueTicks+=len;
    let w=Math.min(S,q);weighted+=w*len;if(info(x).twin)weightedTwin+=w*len;else weightedNonTwin+=w*len;
    sites.set(x,(sites.get(x)||0)+len);
    for(let n=a;n<e;n++){let k=x+","+n;check(!all.has(k),"disjoint phase bins");all.set(k,ph)}
   }
   // Literal individual root profit; actual gap cost is fixed in the full graph.
   for(let {word} of paths){
    let net=0,peak=0,debt=0;
    for(let z of word){
     const ph=phases.get(z.key),q=info(z.x).q;
     if(z.f<=end){check(z.f-z.n<=z.f-ph.a,"earliest actual gap");actualWaitChecks++}
     for(let n=z.n;n<z.e;n++){
      let c=(q<K&&n+1===z.f)?z.f-ph.a:0,inc=1-c,p=Math.max(0,inc-debt);
      net+=inc;debt=Math.max(0,debt-inc);check(p===Math.max(0,net-peak),"root record");peak=Math.max(peak,net);
      let key=z.x+","+n;if(p)profits.set(key,Math.max(p,profits.get(key)||0));
     }
    }
   }
   const exact=[...profits.values()].reduce((a,b)=>a+b,0);optimum+=exact;
   // Earliest-arrival cap-one policy. Retain resident on ties with later arrivals.
   let live=new Map(),ledger=new Map(),seen=new Set(),value=0,rMass=0,tMass=0,N=paths.length;
   function insert(r,n){if(live.has(r.x)){mergers++;return}r.a=n;const z=next(r.x,n);r.f=z.f;r.p=z.p;live.set(r.x,r)}
   for(let n=first;n<end;n++){
    if(births.has(n)){let A=births.get(n);const l={A,net:0,rough:0,terminal:0};ledger.set(A,l);insert({x:A,l},n)}
    let arrivals=[];
    for(let [x,r] of live){
     let key=x+","+n,ph=all.get(key);check(ph&&!seen.has(key)&&r.a===ph.a,"earliest representative");seen.add(key);binChecks++;
     const q=info(x).q,fire=r.f===n+1,c=fire&&q<K?r.f-ph.a:0;r.l.net+=1-c;value+=1-c;
     if(q>=K){r.l.rough++;rMass++}
     if(q<K&&r.f>end){r.l.terminal++;tMass++}
     if(fire){check(r.f-r.a===r.f-ph.a,"paid full actual wait");live.delete(x);arrivals.push({x:x-r.p+1,l:r.l})}
    }
    if(n+1<end)for(let r of arrivals)insert(r,n+1);
   }
   check(seen.size===all.size,"full reachability realized");
   for(let l of ledger.values()){check(l.net===l.rough+l.terminal,"per-root exact refund identity");netChecks++}
   check(value===rMass+tMass,"total refund identity");earliestValue+=value;
   check(exact>=value&&exact<=rMass+2*K*N,"optimum sandwich");
  }
  let siteWeighted=0,siteWeightedNonTwin=0,siteTwin=0,bands=new Map(),maxSiteTicks=0;
  const windowBound=Math.ceil((3*T+6)/W)+2;
  for(let x=R-3*T-6+(R%2);x<=2*R;x+=2){
   if(x<=2)continue;const q=info(x).q,w=Math.min(S,q);siteWeighted+=w;if(info(x).twin)siteTwin++;else{siteWeightedNonTwin+=w;check(q<=S,"non-twin least factor");let i=Math.floor(Math.log2(S/q));bands.set(i,(bands.get(i)||0)+1)}
  }
  for(let [x,n] of sites){check(n<=windowBound*Math.ceil(1.5*T),"constant window overlap");maxSiteTicks=Math.max(maxSiteTicks,n)}
  check(weighted===weightedTwin+weightedNonTwin&&weighted>=weightedBirth&&weightedTwin>=S*T*twinRoots,"weighted field lower");
  check(weightedNonTwin<=windowBound*Math.ceil(1.5*T)*siteWeightedNonTwin,"weighted field upper");
  check(earliestValue===roughTicks+terminalNonrough&&optimum<=roughTicks+2*K*roots&&optimum>=firstIdle,"all controls");
  rows.push({R,T,K,S,roots,windows,fullTicks,uniqueTicks,phaseCount,eventCount,actualWaitChecks,binChecks,netChecks,mergers,roughTicks,terminalNonrough,earliestValue,optimum,firstIdle,weighted,weightedTwin,weightedNonTwin,weightedBirth,siteWeighted,siteWeightedNonTwin,siteTwin,twinRoots,maxSiteTicks,bands:[...bands].sort((a,b)=>a[0]-b[0])})
 }
 return rows;
}
console.log(JSON.stringify(audit(),null,2));
