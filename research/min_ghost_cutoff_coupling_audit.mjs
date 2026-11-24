// Common CRT cutoff coupling and finite-time forbidden-pair audit.
function audit(Y,V,N=4096){
 const ps=[];for(let p=3;p<V;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const k=ps.findIndex(p=>p>=Y);if(k<0)throw Error("no added primes");
 const T=Math.floor(Y*Math.sqrt(Math.log(Y))),U=T+2*Y;
 let rng=(0x7f43a9bd^Y^V)>>>0;
 function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let m=4294967296-4294967296%p,x;do{x=u32()}while(x>=m);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),mod=(a,b)=>(a%b+b)%b;
 function run(k){
  let g=0,e=0,d=0,events=[],terminal=null,gap=null;
  for(;;){let w=Infinity,p0=0;
   for(let i=0;i<k;i++){let p=ps[i],cc=(c[i]+g)%p;if(cc!==1&&cc!==p-1)continue;let ph=cc===1?0:p+2,f=2*p-mod(t[i]+e-ph,2*p);if(f<w||(f===w&&p<p0)){w=f;p0=p}}
   if(w>2*Y&&gap===null)gap=e;
   if(!p0){terminal=e;break}
   if(e+w>U)break;
   e+=w;g+=p0-1;d=Math.max(d,2*e-g);events.push([e,p0,g]);
   if(events.length>U)throw Error("time monotonicity");
  }
  return {events,terminal,gap,d};
 }
 let divergence=0,divT=0,lowLong=0,largeGapLate=0,agree=0,earlyTerminal=0,check=0,maxDistinct=0,repeatBound=0,largeSeen=0;
 const firstSeen=new Map(),inc=new Map();let totalClockPairs=0,conditional=0,conditionalN=0;
 const ck=(b,m)=>{if(!b)throw Error(m)};
 for(let j=0;j<N;j++){
  let parity=uni(2);for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let v=uni(p);t[i]=v%2===parity?v:v+p}
  let a=run(k),b=run(ps.length),eq=JSON.stringify(a.events)===JSON.stringify(b.events);
  let ea=a.events.filter(v=>v[0]<=T),eb=b.events.filter(v=>v[0]<=T);
  if(JSON.stringify(ea)!==JSON.stringify(eb))divT++;
  if(!eq)divergence++;else{agree++;ck((a.terminal!==null&&a.terminal<=T)===(b.gap!==null&&b.gap<=T),"gap equivalence");check++;}
  if(a.terminal===null||a.terminal>T)lowLong++;else earlyTerminal++;
  if(b.gap===null||b.gap>T)largeGapLate++;
  let counts=new Map();for(let [e,p] of eb){counts.set(p,(counts.get(p)||0)+1);inc.set(p,(inc.get(p)||0)+1)}
  for(let [p,m] of counts){ck(m<=1+Math.floor(T/(p-2)),"repeat clock spacing");repeatBound++;firstSeen.set(p,(firstSeen.get(p)||0)+1)}
  maxDistinct=Math.max(maxDistinct,counts.size);if([...counts.keys()].some(p=>p>=Y))largeSeen++;
  ck((JSON.stringify(ea)!==JSON.stringify(eb))===[...counts.keys()].some(p=>p>=Y),"first divergence");
  // Exact forbidden union conditional on the entire lower history, including frozen tail.
  // For 128 deterministic initial samples, enumerate all high prime pairs of residues.
  if(j<128){
   let product=1;
   for(let i=k;i<ps.length;i++){
    let p=ps[i],set=new Set(),g=0,idx=0;
    for(let u=1;u<=U;u++){
     // At a tied lower clock the smaller lower label wins; skip that time.
     if(idx<a.events.length&&a.events[idx][0]===u){g=a.events[idx++][2];continue}
     let even=(parity+u)%2===0,s=even?1:-1,ph=even?0:p+2;
     let cp=mod(s-g,p),tp=mod(ph-u,p);set.add(cp*p+tp);
    }
    ck(set.size<=U&&set.size<=p*p,"forbidden size");
    product*=1-set.size/(p*p);totalClockPairs+=set.size;
    // Actual inserted prime residues hit exactly this set iff there is some eligible earlier clock on lower trace.
    let hit=set.has(c[i]*p+mod(t[i],p));
    if(ps.length-k===1)ck(hit===!eq,"single insertion");
   }
   conditional+=1-product;conditionalN++;
  }
 }
 let reciprocal=ps.slice(k).reduce((s,p)=>s+1/p**2,0);
 return {Y,V,N,T,U,extraPrimes:ps.length-k,divT,divergence,agree,lowLong,largeGapLate,earlyTerminal,check,maxDistinct,repeatBound,largeSeen,unionT:Math.min(1,T*reciprocal),unionU:Math.min(1,U*reciprocal),conditionalMean:conditional/conditionalN,conditionalN,totalClockPairs,selected:[...firstSeen].sort((a,b)=>a[0]-b[0]).map(([p,n])=>({p,n,inc:inc.get(p)}))};
}
function exact(Y,p){
 let ps=[];for(let q=3;q<Y;q+=2)if(!ps.some(r=>q%r===0))ps.push(q);
 let L=2*ps.reduce((a,b)=>a*b,1),U=2*Y+Math.floor(Y*Math.sqrt(Math.log(Y))),mod=(a,b)=>(a%b+b)%b;
 if(p<Y||ps.some(q=>p%q===0))throw Error("extra");
 const ck=(b,m)=>{if(!b)throw Error(m)};
 function trace(C,t,alphabet){let e=0,g=0,events=[];for(;;){let w=Infinity,q0=0;for(let q of alphabet){let cc=mod(C+g,q);if(cc!==1&&cc!==q-1)continue;let ph=cc===1?0:q+2,f=2*q-mod(t+e-ph,2*q);if(f<w||(f===w&&q<q0)){w=f;q0=q}}if(e+w>U)break;e+=w;g+=q0-1;events.push([e,q0,g]);}return events}
 // CRT representatives of original even C and clock t at prescribed extra residues.
 function lift(v,m,target,p){let x=v;while(mod(x,p)!==target)x+=m;return x}
 let states=0,cases=0,div=0,forbidden=0;
 for(let C=0;C<L;C+=2)for(let t=0;t<L;t++){
  let a=trace(C,t,ps),set=new Set(),g=0,i=0;
  for(let u=1;u<=U;u++){if(i<a.length&&a[i][0]===u){g=a[i++][2];continue}
   let even=(t+u)%2===0;set.add(mod((even?1:-1)-g,p)*p+mod((even?0:p+2)-u,p))}
  states++;forbidden+=set.size;
  for(let cp=0;cp<p;cp++)for(let tp=0;tp<p;tp++){
   let b=trace(lift(C,L,cp,p),lift(t,L,tp,p),[...ps,p]),different=JSON.stringify(a)!==JSON.stringify(b);
   ck(different===set.has(cp*p+tp),"exact forbidden equivalence");div+=different;cases++;
  }
 }
 ck(div===forbidden,"exact total");return {Y,p,L,U,states,cases,div,prob:div/cases,union:Math.min(1,U/p**2)};
}
for(const y of [5,7,11])console.log(JSON.stringify(exact(y,y)));
for(const y of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(y,8*y,2048)));
