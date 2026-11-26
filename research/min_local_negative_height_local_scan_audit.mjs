// Height-local candidate scan, adaptive modulus cap transfer, and formal CRT height controls.
function audit(){
 const ck=(b,m)=>{if(!b)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=600000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let x=p*p;x<=N+2;x+=p)if(!spf[x])spf[x]=p;
 function fs(n){let a=[];n=Math.abs(n);while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 let iv=new Int32Array(N+3);function inv3(p){if(!iv[p])iv[p]=(p%3===1?(2*p+1):(p+1))/3;return iv[p]}
 function next(a,v){let p=Infinity,w=Infinity,e=0;for(let [d,s] of [[a+1,-1],[a-1,1]])for(let r of fs(d)){let t=mod((s===-1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e}}
 function tick(t,h,par,query){
  let b=h+1,e=mod(3-3*par+t,2)===0?-1:1,n=e===-1?2*b+1:2*b-5,p=0;
  for(let q of fs(n)){let c=e===-1?0:q+2;
   if(q===3){if(mod(3+t-c,3)===0){p=q;break}}else{
    let r=mod((3+t-c)*inv3(q),q);
    if(query(q,r)){p=q;break}
   }
  }
  return {h:b-(p?(p-1)/2:0),p,e,n}
 }
 let s={actualRoots:0,actualTicks:0,actualEvents:0,queries:0,clockChecks:0,heightChecks:0,cutoffChecks:0,firstWaitChecks:0,firstWaitPeriodChecks:0,firstWaitRows:[],cappedControls:0,cappedLeaves:0,cappedQueries:0,cappedFullChecks:0,intervalChecks:0,maxTVRatio:0,formalRows:[],actualRows:[]};
 for(let A=120;A<=240000;A+=198){
  let j=A/6,par=j%2,a=A,v=3-A/2,t=0,h=3,stop=Math.min(1500,A/2-4),ev=next(a,v),due=ev.w,Q=1n,seen=new Set();
  for(t=1;t<=stop&&a>A/2;t++){
   let out=tick(t,h,par,(q,r)=>{s.queries++;if(!seen.has(q)){seen.add(q);Q*=BigInt(q)}return j%q===r});
   ck(out.p===(t===due?ev.p:0),"tick vs event");
   if(out.p){ck(out.e===ev.e,"side");a-=out.p-1;v+=ev.w;s.actualEvents++;if(a>A/2){ev=next(a,v);due=t+ev.w}}
   h=out.h;ck(h===a/2+3-A/2+t&&h>=0,"height");ck(h<=3+t,"height cap");ck(Math.abs(out.n)<=2*t+7,"factor cutoff");s.heightChecks++;s.cutoffChecks++;s.actualTicks++;s.clockChecks++;
  }s.actualRoots++;
 }
 function capped(par,K,Qmax){
  let leaves=[],nodeCount=0;
  function walk(t,h,sets,Q,prob){
   if(t>K){leaves.push({sets,Q,prob,t,h,stop:"horizon"});return}
   let b=h+1,e=mod(3-3*par+t,2)===0?-1:1,ps=fs(e===-1?2*b+1:2*b-5);
   function scan(i,C,P,mass){
    if(i===ps.length){walk(t+1,b,C,P,mass);return}
    let q=ps[i],c=e===-1?0:q+2;
    if(q===3){if(mod(3+t-c,3)===0)walk(t+1,b-1,C,P,mass);else scan(i+1,C,P,mass);return}
    let r=mod((3+t-c)*inv3(q),q),old=C.get(q);
    if(!old&&P*q>Qmax){leaves.push({sets:C,Q:P,prob:mass,t,h,stop:"cap"});return}
    let V=old||Array.from({length:q},(_,i)=>i),PP=old?P:P*q,node=new Map(C);
    nodeCount++;if(!V.includes(r)){node.set(q,V);scan(i+1,node,PP,mass);return}
    let yes=new Map(node);yes.set(q,[r]);walk(t+1,b-(q-1)/2,yes,PP,mass/V.length);
    if(V.length>1){let no=new Map(node);no.set(q,V.filter(x=>x!==r));scan(i+1,no,PP,mass*(V.length-1)/V.length)}
   }scan(0,sets,Q,prob)
  }walk(1,3,new Map(),1,1);
  let total=leaves.reduce((a,x)=>a+x.prob,0);ck(Math.abs(total-1)<1e-9,"partition");
  for(let l of leaves){let m=[...l.sets.values()].reduce((a,v)=>a*v.length,1);ck(l.Q<=Qmax&&Math.abs(l.prob-m/l.Q)<1e-12,"leaf exact mass")}
  let rows=[];
  for(let [start,n] of [[17,1000],[113,10000],[5001,30000]]){
   let count=new Uint32Array(leaves.length);
   for(let j0=start;j0<start+n;j0++){let j=2*j0+par,k=0;
    for(let i=0;i<leaves.length;i++){let x=leaves[i];if([...x.sets].every(([q,v])=>v.includes(j%q))){count[i]++;k++}}
    ck(k===1,"exact disjoint leaves");s.cappedFullChecks++;
   }
   let tv=0,done=0,pdone=0,mean=0,emean=0;
   for(let i=0;i<leaves.length;i++){let x=leaves[i],p=count[i]/n;ck(Math.abs(p-x.prob)<=x.Q/n*x.prob+1e-12,"relative error");tv+=Math.abs(p-x.prob)/2;
    if(x.stop==="horizon"){done+=p;pdone+=x.prob;mean+=p*x.h;emean+=x.prob*x.h}
   }ck(tv<=Qmax/(2*n)+1e-9,"TV");s.intervalChecks+=leaves.length;s.maxTVRatio=Math.max(s.maxTVRatio,tv/(Qmax/(2*n)));
   rows.push({n,tv,done,pdone,mean,emean})
  }
  s.cappedControls++;s.cappedLeaves+=leaves.length;s.cappedQueries+=nodeCount;
  return {par,K,Qmax,leaves:leaves.length,capLeaves:leaves.filter(x=>x.stop==="cap").length,probHorizon:leaves.filter(x=>x.stop==="horizon").reduce((a,x)=>a+x.prob,0),rows}
 }
 for(let par of [0,1])for(let [K,Q] of [[8,35],[12,385],[18,1155],[22,5005]])s.actualRows.push(capped(par,K,Q));
 // Exact first-wait survival on each parity: along a stationary
 // source, only two possible residues of each prime can be queried.
 for(let K of [4,6,8,12,20,100,1000,10000,100000])for(let par of [0,1]){
  let C=new Map();
  for(let t=1;t<=K;t++){
   let b=3+t,e=mod(3-3*par+t,2)===0?-1:1;
   for(let q of fs(e===-1?2*b+1:2*b-5)){
    let c=e===-1?0:q+2;if(q===3){ck(mod(3+t-c,3)!==0,"stationary 3");continue}
    let r=mod((3+t-c)*inv3(q),q),a=C.get(q)||new Set();a.add(r);C.set(q,a);
    ck(a.size<=2&&[...a].every(x=>mod(6*x-e,q)===0||mod(6*x+e,q)===0),"stationary residues");s.firstWaitChecks++;
   }
  }
  let log=0,low=0,up=0,Q=1n;for(let q=5;q<=2*K+7;q+=2)if(!spf[q]){
   let m=C.get(q)?.size||0;log+=Math.log1p(-m/q);low+=Math.log1p(-2/q);if(2*q<=K){up+=Math.log1p(-2/q);ck(m===2,"both sides tested")}
   if(m)Q*=BigInt(q);
  }
  ck(low<=log+1e-10&&log<=up+1e-10,"first wait sandwich");
  if(Q<=500000n){let cnt=0,qq=Number(Q);for(let l=0;l<qq;l++){let j=2*l+par;if([...C].every(([p,a])=>!a.has(j%p)))cnt++;s.firstWaitPeriodChecks++}
   ck(Math.abs(cnt/qq-Math.exp(log))<1e-10,"first wait product")}
  s.firstWaitRows.push({K,par,primes:C.size,prob:Math.exp(log),lower:Math.exp(low),upper:Math.exp(up),normalized:Math.exp(log)*Math.log(K)**2});
 }
 let rng=123456789;function random(){rng=(Math.imul(rng,1664525)+1013904223)>>>0;return rng/4294967296}
 for(let K of [100,1000,10000,100000]){
  let row={K,runs:K===100000?80:240,meanHeightRatio:0,minHeightRatio:Infinity,maxHeightRatio:0,meanMaxHeightRatio:0,meanGainRatio:0,meanSelected:0,meanQueries:0,meanLogQ:0,meanLastEventRatio:0,meanEscapeTime:{8:0,16:0,32:0,64:0},escapeCount:{8:0,16:0,32:0,64:0}};
  for(let i=0;i<row.runs;i++){let par=i%2,C=new Map(),used=new Set(),h=3,maxh=h,G=0,queries=0,last=0,logQ=0,esc={};
   for(let t=1;t<=K;t++){let x=tick(t,h,par,(q,r)=>{queries++;if(!C.has(q)){C.set(q,Math.floor(random()*q));logQ+=Math.log(q)}return C.get(q)===r});
    h=x.h;ck(h>=0&&h<=t+3,"formal height");if(x.p){used.add(x.p);G+=x.p-1;last=t}
    ck(h===3+t-G/2,"formal invariant");maxh=Math.max(maxh,h);
    for(let H of [8,16,32,64])if(h>=H&&esc[H]===undefined){esc[H]=t}
   }
   for(let H of [8,16,32,64])if(esc[H]!==undefined){row.meanEscapeTime[H]+=esc[H];row.escapeCount[H]++}
   row.meanHeightRatio+=h/K;row.minHeightRatio=Math.min(row.minHeightRatio,h/K);row.maxHeightRatio=Math.max(row.maxHeightRatio,h/K);row.meanMaxHeightRatio+=maxh/K;row.meanGainRatio+=G/K;row.meanSelected+=used.size;row.meanQueries+=queries;row.meanLogQ+=logQ;row.meanLastEventRatio+=last/K;
  }
  for(let k of ["meanHeightRatio","meanMaxHeightRatio","meanGainRatio","meanSelected","meanQueries","meanLogQ","meanLastEventRatio"])row[k]/=row.runs;
  for(let H of [8,16,32,64])if(row.escapeCount[H])row.meanEscapeTime[H]/=row.escapeCount[H];s.formalRows.push(row)
 }
 return s
}
console.log(JSON.stringify(audit(),null,2));
