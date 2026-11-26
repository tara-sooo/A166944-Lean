// Negative-time exact inverse suffix and small-prime erasure certificates.
function audit(){
 const ck=(c,m)=>{if(!c)throw Error(m)},mod=(a,p)=>(a%p+p)%p,N=300000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)if(!spf[n])spf[n]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p!==2)a.push(p);while(n%p===0)n/=p}return a}
 const Kmax=768,times=Array.from({length:Kmax+1},(_,k)=>k?fs(k%2===0?k:k+2):[]);
 function sign(k){return k%2===0?-1:1}
 function step(a,k){let p=times[k].find(p=>mod(a-sign(k),p)===0);return p===undefined?a:a-p+1}
 let s={primeTargets:0,compositeTargets:0,twinTargets:0,extinct:0,alive:0,reverseTicks:0,inverseChecks:0,forwardWitnessChecks:0,twinStationaryChecks:0,extentChecks:0,maxWidth:0,maxDeath:0,aliveExamples:[],longest:[],qSmallChecks:0,canonicalChecks:0,canonicalEvents:0,nonzeroPhases:0,periodControls:[],byQ:{},byRange:{}};
 function back(a,K,witness=false){
  let S=new Set([a]),max=1,cap=0;
  for(let k=1;k<=K;k++){
   let ps=times[k],V=new Set();cap+=ps.length?ps[ps.length-1]-1:0;
   for(let b of S){
    if(step(b,k)===b){V.add(b);s.inverseChecks++}
    for(let p of ps){let x=b+p-1;if(step(x,k)===b){V.add(x);s.inverseChecks++}}
   }
   for(let x of V)ck(x>=a&&x<=a+cap&&x%2===0,"reverse extent");
   ck(V.size<=1+cap/2,"width");s.extentChecks++;s.reverseTicks++;S=V;max=Math.max(max,S.size);
   if(!S.size)return {dead:k,max,size:0};
  }
  if(witness){let x=S.values().next().value,b=x;for(let k=K;k>=1;k--)b=step(b,k);ck(b===a,"forward witness");s.forwardWitnessChecks++}
  return {dead:0,max,size:S.size};
 }
 // Exact image of a full small-prime suffix, periodic modulo twice the product.
 for(let [q,K] of [[3,1],[5,3],[7,5],[7,7],[11,9],[13,11]]){
  let ps=[];for(let p=3;p<=K+2;p+=2)if(!spf[p])ps.push(p);
  let Q=2*ps.reduce((a,b)=>a*b,1),img=new Uint8Array(Q/2);
  for(let a=0;a<Q;a+=2){let b=a;for(let k=K;k>=1;k--)b=step(b,k);img[mod(b,Q)/2]=1}
  let n=0,live=0,liveResidues=[],inverseMatches=0;
  for(let a=0;a<Q;a+=2){
   // a+1 prime outside the small prime set, a-1 has least factor q
   if(mod(a-1,q)!==0||ps.some(p=>mod(a+1,p)===0||p<q&&mod(a-1,p)===0))continue;
   n++;let x=back(a+Q,K,true);ck(!!img[a/2]===!x.dead,"period inverse comparison");inverseMatches++;
   if(!x.dead){live++;if(liveResidues.length<8)liveResidues.push(a)}
  }
  if(q<=5||q===7&&K===7)ck(live===0,"small q erasure");
  s.periodControls.push({q,K,Q,candidates:n,live,liveResidues,inverseMatches});
 }
 // All primes in a substantial range, not merely actual terminal labels.
 for(let p=1009;p<=N;p+=2)if(!spf[p]){
  s.primeTargets++;let a=p-1,K=Math.min(Kmax,a/2-4);
  if(!spf[p-2]){
   s.twinTargets++;for(let k=1;k<=K;k++){ck(step(a,k)===a,"stationary twin");s.twinStationaryChecks++}continue;
  }
  s.compositeTargets++;let q=spf[p-2],b=back(a,K,true);
  let key=q<=19?String(q):q<=97?"23..97":"101+",r=s.byQ[key]??={n:0,extinct:0,alive:0,maxDeath:0,maxWidth:0};
  let range=p<=10000?"1009..10000":p<=100000?"10001..100000":"100001..300000",rr=s.byRange[range]??={n:0,extinct:0,alive:0,maxDeath:0};
  r.n++;rr.n++;r.maxWidth=Math.max(r.maxWidth,b.max);s.maxWidth=Math.max(s.maxWidth,b.max);
  if(b.dead){s.extinct++;r.extinct++;rr.extinct++;r.maxDeath=Math.max(r.maxDeath,b.dead);rr.maxDeath=Math.max(rr.maxDeath,b.dead);s.maxDeath=Math.max(s.maxDeath,b.dead);s.longest.push({p,q,dead:b.dead,width:b.max});}
  else{s.alive++;r.alive++;rr.alive++;if(s.aliveExamples.length<20)s.aliveExamples.push({p,q,K,...b})}
  if(q<=7){ck(b.dead>0&&b.dead<=(q===7?7:q-2),"small q universal");s.qSmallChecks++}
 }
 s.longest.sort((a,b)=>b.dead-a.dead);s.longest=s.longest.slice(0,10);
 // independent canonical clock simulation for a sparse set and literal negative suffix check
 for(let A=6;A<=N;A+=198){
  let a=A,v=-A/2+3,last=0,prezero=null;
  while(a){
   let p=Infinity,w=Infinity;
   for(let [d,e] of [[a+1,1],[a-1,-1]])for(let r of fs(d)){let j=mod((e===1?0:r+2)-v,2*r)||2*r;if(j<w||j===w&&r<p){p=r;w=j}}
   ck(Number.isFinite(p),"event");if(v+w===0)prezero=a;
   a-=p-1;v+=w;last=p;s.canonicalEvents++;
  }
  if(v===0){ck(prezero===last-1,"zero source");let K=Math.min(Kmax,A/2-4);if(K>=1){let b=back(last-1,K,true);ck(!b.dead,"actual zero-phase has ancestor");s.canonicalChecks++;}}
  else s.nonzeroPhases++;
 }
 return s
}
console.log(JSON.stringify(audit(),null,2));
