// Full relaxed barrier sets for Negative MIN: CRT gaps, pair/multipoint correlations, actual variable cells.
// node research/min_local_negative_relaxed_barrier_gap_audit.mjs
function audit(){
 const mod=(a,p)=>(a%p+p)%p,ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 const primes=[3,5,7,11,13,17,19,23],f=x=>x?x*Math.log(x):0;
 let P=1,B=[0],sets=[],checks=0;
 function barrier(t,ps){return ps.every(p=>mod(-t,p)<=(p-3)/2)}
 function local(p,ds){let a=[...new Set(ds.map(x=>mod(x,p)))].sort((a,b)=>a-b),sum=0;
  for(let i=0;i<a.length;i++){let d=(i===a.length-1?a[0]+p:a[i+1])-a[i];sum+=Math.max(0,d-(p+1)/2)}
  return sum;
 }
 for(let p of primes){
  let oldP=P,old=B;P*=p;B=[];
  for(let b of old)for(let k=0;k<p;k++){let t=b+k*oldP;if(mod(-t,p)<=(p-3)/2)B.push(t)}
  B.sort((a,b)=>a-b);
  let ps=primes.filter(q=>q<=p),n=B.length,expected=ps.reduce((a,q)=>a*(q-1)/2,1);ck(n===expected,"CRT cardinality");
  const count=new Map();let min=Infinity,max=0,meanLog=0,meanRootM=0,short=0;
  for(let i=0;i<n;i++){
   let d=(i===n-1?B[0]+P:B[i+1])-B[i];ck(d%3===0&&d>0,"canonical spacing");
   ck(ps.every(q=>mod(2*d-1,q)!==0&&mod(2*d+1,q)!==0),"rough difference");
   if(2*d<=p*p-1){ck(2*d-1>p&&2*d+1>p,"near gap");short++}
   count.set(d,(count.get(d)||0)+1);min=Math.min(min,d);max=Math.max(max,d);meanLog+=d/P*Math.log(d/3);meanRootM+=d*d/(3*P);checks++;
  }
  ck([...count].reduce((s,[d,m])=>s+d*m,0)===P,"gap sum");
  let hist=[...count].sort((a,b)=>a[0]-b[0]),q=(u)=>{let s=0;for(let [d,m] of hist){s+=d*m/P;if(s>=u)return 2*d}return 2*max;};
  let pairChecks=0,multiChecks=0,firstRough=null;
  // Formula for all small differences, and explicit CRT period intersections on small sets.
  let cap=Math.min(2000,P);
  let membership=p<=17?new Set(B):null;
  for(let d=1;d<=cap;d++){
   let predicted=ps.reduce((a,q)=>a*local(q,[0,d]),1);
   let rough=ps.every(q=>mod(2*d-1,q)!==0&&mod(2*d+1,q)!==0);
   ck((predicted>0)===rough,"pair equivalence");
   if(predicted>0&&firstRough===null)firstRough=2*d;
   if(membership&&d<=300){let actual=0;for(let b of B)actual+=+membership.has(mod(b+d,P));ck(actual===predicted,"explicit pair count");pairChecks++;}
   checks++;
  }
  ck(firstRough===null||firstRough===2*min,"minimum difference");
  for(let d=0;d<=12;d++)for(let e=d;e<=18;e++){
   let pred=ps.reduce((a,q)=>a*local(q,[0,d,e]),1);
   for(let q of ps){let actual=0;for(let t=0;t<q;t++)actual+=+([0,d,e].every(x=>mod(-(t+x),q)<=(q-3)/2));ck(actual===local(q,[0,d,e]),"local multipoint");multiChecks++;}
   if(membership&&p<=13){let actual=0;for(let b of B)actual+=+(membership.has(mod(b+d,P))&&membership.has(mod(b+e,P)));ck(actual===pred,"global triple");multiChecks++;}
  }
  // Direct enumeration of relaxed downward crossing at every local residue.
  for(let q of ps)for(let t=0;t<q;t++){
   let possible=false;for(let j=0;j<=q-3;j+=2)if(mod(2*t+j-1,q)===0||mod(2*t+j+1,q)===0)possible=true;
   ck(!possible===barrier(t,[q]),"relaxed boundary");checks++;
  }
  sets.push({p,P,B,ps});
  checks+=pairChecks+multiChecks;
  sets.at(-1).row={z:p,halfPeriod:P,barriers:n,canonicalDensity:3*n/P,meanGap:2*P/n,minGap:2*min,maxGap:2*max,rootMedianGap:q(.5),root90Gap:q(.9),root99Gap:q(.99),rootMeanLogM:meanLog,rootMeanM:meanRootM,primorialLogM:Math.log(P/3),shortTwinGaps:short,pairChecks,multiChecks};
 }
 // Actual trajectories, variable barrier cells, using per-root elapsed T.
 const R=480000,T=Math.ceil(Math.sqrt(2*R+1)),S=Math.sqrt(2*R+1),L=Math.log(S),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1,spf=new Int32Array(2*R+5);
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const q=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1),weight=p=>{let t=Math.log(Math.max(3,Math.min(S,p))),d=L-t;return (t/L)**2/((1+d)*(1+Math.log1p(d))**2)};
 function bounds(t,set){let k=Math.floor(t/set.P),u=t-k*set.P,a=set.B,l=0,r=a.length;
  while(l<r){let m=(l+r)>>1;if(a[m]<=u)l=m+1;else r=m}
  return [2*(k*set.P+(l?a[l-1]:a.at(-1)-set.P)),2*(k*set.P+(l<a.length?a[l]:set.P+a[0]))];
 }
 let stats=sets.filter(s=>s.p<=19).map(set=>({set,z:set.p,roots:N,exit:0,high:0,terminal:0,meanLogM:0,meanLogActualM:0,proxy:0,exact:0,cells:new Map(),pre:new Map(),end:new Map(),initial:new Map(),barrierChecks:0,checks:0}));
 for(let A=lo;A<=hi;A+=6){
  let n=3-A/2,birth=n,end=n+T,a=A,G=0,live=stats.map(s=>{let [l,r]=bounds(A/2,s.set),M=(r-l)/6,Ma=Math.max(0,Math.min(hi,r-6)-Math.max(lo,l))/6+1;
   s.meanLogM+=Math.log(M);s.meanLogActualM+=Math.log(Ma);s.initial.set(l,(s.initial.get(l)||0)+1);return {s,l,r,M,Ma,best:A,done:false}});
  for(;;){
   let e=next(a,n),fire=n+e.w,b=a-e.p+1;
   for(let v of live)if(!v.done){
    let {s,l,r,M,Ma}=v;ck(a>=l&&a<r&&A-a===G,"initial variable cell");
    if(q(a)>q(v.best))v.best=a;
    let exit=fire<=end&&b<l,terminal=fire>end;
    if(exit||terminal){
     v.done=true;let lower,age=n-birth;ck(age<=3*G,"age");
     if(exit){ck(e.p>s.z,"variable barrier");s.barrierChecks++;s.exit++;s.high+=+(e.p>=S/4);lower=Math.max(3,(e.p-1)/4-1.25*G-1.5)}
     else{s.terminal++;lower=Math.max(3,(T-3*G)/2)}
     ck(q(a)>=lower-1e-8,"wait");
     s.proxy+=weight(lower)/Ma;s.exact+=weight(q(v.best))/Ma;s.cells.set(l,Math.max(s.cells.get(l)||0,weight(q(v.best))));
     s.pre.set(a,(s.pre.get(a)||0)+1);s.checks++;
    }
   }
   if(fire>end)break;
   for(let s of stats){let [l]=bounds(a/2,s.set);if(e.p<=s.z){ck(b>=l,"all-path barrier");s.barrierChecks++;}}
   a=b;G+=e.p-1;n=fire;
  }
  for(let s of stats){let [l]=bounds(a/2,s.set);s.end.set(l,(s.end.get(l)||0)+1)}
 }
 let cap=0;for(let a=2*Math.ceil((lo-2*T-6)/2);a<=hi;a+=2)if(q(a)<=S)cap+=weight(q(a));
 const actual=stats.map(s=>{
  let support=0;for(let [a,m] of s.pre){let [l,r]=bounds(a/2,s.set);ck(m<=(r-l)/6,"pre multiplicity");support+=weight(q(a))}
  let cellCert=[...s.cells.values()].reduce((t,x)=>t+x,0);ck(s.proxy<=s.exact+1e-7&&s.exact<=cellCert+1e-7,"weighted cell certificate");
  return {z:s.z,R,N,meanLogM:s.meanLogM/N,meanLogActualM:s.meanLogActualM/N,initialEntropy:[...s.initial.values()].reduce((t,m)=>t+f(m),0)/N,finalEntropy:[...s.end.values()].reduce((t,m)=>t+f(m),0)/N,exit:s.exit/N,terminal:s.terminal/N,largeGood:(s.high+s.terminal)/N,proxy:s.proxy,exact:s.exact,cellCert,preSupport:support,cap,checks:s.checks,barrierChecks:s.barrierChecks};
 });
 return {checks,periods:sets.map(s=>s.row),actual};
}
console.log(JSON.stringify(audit(),null,2));
