// Square-root high band added to a fixed low alphabet: CRT one/two pin counts and first gap-clock law.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=2100000,spf=new Uint32Array(N+1),pr=[];
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)spf[a]=p;
 for(let p=3;p<=N;p+=2)if(!spf[p])pr.push(p);
 function fs(n){let a=[];n=Math.abs(n);while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n,P){let p=Infinity,w=Infinity,sign=0;
  for(let s of [-1,1])for(let q of P){if(mod(a-s,q)!==0)continue;let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){w=d;p=q;sign=s}}return {p,w,sign}}
 function absorb(A,P){let a=A,n=3-A/2,h=3,maxH=3,W=0;
  for(;;){let e=next(a,n,P);if(!Number.isFinite(e.p))return {a,h,maxH,W,G:A-a};maxH=Math.max(maxH,h+e.w);a-=e.p-1;n+=e.w;h+=e.w-(e.p-1)/2;W+=e.w;ck(h>=0,"height")}
 }
 let z={periodRoots:0,actualRoots:0,eligibilityChecks:0,independentRaceChecks:0,crtSingleChecks:0,crtPairChecks:0,bonferroniChecks:0,rows:[]};
 for(let P of [[3,5],[3,5,7],[3,5,7,11]]){
  let M=2*P.filter(p=>p>=5).reduce((s,p)=>s*p,1),profiles=[],maxHeight=0,maxW=0,maxGain=0;
  for(let j=0;j<M;j++){let r=absorb(6*j,P);profiles.push(r);maxHeight=Math.max(maxHeight,r.maxH,r.h);maxW=Math.max(maxW,r.W);maxGain=Math.max(maxGain,r.G);z.periodRoots++}
  for(let R of [48000,192000,480000,1000000]){
   let T=Math.ceil(8*Math.sqrt(2*R+1)),Y=Math.ceil(T/8),U=Math.floor(T/4),Q=pr.filter(p=>p>=Y&&p<=U),qs=new Set(Q),j0=Math.ceil(R/6),j1=Math.floor(2*R/6),nr=j1-j0+1;
   if((Y-1)/2<=maxHeight||maxW+2*U>T)continue;
   let sum=0,events=0,pairs=0,maxMatches=0,actualCounts=new Map(),pairCounts=new Map(),modelGain=0,fullGain=0;
   for(let j=j0;j<=j1;j++){let A=6*j,r=profiles[mod(j,M)],a=A-r.G,n=3-A/2+r.W,found=[];
    for(let s of [-1,1])for(let p of fs(a-s))if(qs.has(p)){let w=mod((s===-1?0:p+2)-n,2*p)||2*p;ck(r.W+w<=T,"all gap clocks fit");found.push({p,w,s});actualCounts.set(p,(actualCounts.get(p)||0)+1);z.eligibilityChecks++}
    found.sort((a,b)=>a.w-b.w||a.p-b.p);sum+=found.length;events+=+(found.length>0);pairs+=found.length*(found.length-1)/2;maxMatches=Math.max(maxMatches,found.length);
    for(let i=0;i<found.length;i++)for(let k=i+1;k<found.length;k++){let x=Math.min(found[i].p,found[k].p),y=Math.max(found[i].p,found[k].p),key=x+":"+y;pairCounts.set(key,(pairCounts.get(key)||0)+1)}
    // independent full gap-alphabet event simulation for a subsample.
    if((j-j0)%97===0){
     let b=A,t=3-A/2,end=t+T,first=null;
     for(;;){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(b-s))if(P.includes(q)||qs.has(q)){let v=mod((s===-1?0:q+2)-t,2*q)||2*q;if(v<w||v===w&&q<p){p=q;w=v}}
      if(t+w>end)break;if(qs.has(p)){first={p,t:t+w};break}b-=p-1;t+=w;
     }ck((first===null)===(found.length===0),"gap event existence");if(first)ck(first.p===found[0].p&&first.t===n+found[0].w,"gap event clock");z.independentRaceChecks++;
    }z.actualRoots++;
   }
   let expected=2*Q.reduce((s,p)=>s+1/p,0),maxSingleErr=0,maxPairErr=0;
   for(let p of Q){let err=Math.abs((actualCounts.get(p)||0)-2*nr/p);ck(err<=2*M+1e-8,"single CRT error");maxSingleErr=Math.max(maxSingleErr,err);z.crtSingleChecks++}
   for(let i=0;i<Q.length;i++)for(let k=i+1;k<Q.length;k++){let p=Q[i],q=Q[k],err=Math.abs((pairCounts.get(p+":"+q)||0)-4*nr/(p*q));ck(err<=4*M+1e-8,"pair CRT error");maxPairErr=Math.max(maxPairErr,err);z.crtPairChecks++}
   ck(sum-pairs<=events&&events<=sum,"Bonferroni");z.bonferroniChecks++;
   z.rows.push({P,M,R,T,Y,U,primes:Q.length,roots:nr,maxHeight,maxW,maxGain,expected,firstMoment:sum/nr,prob:events/nr,pairMoment:pairs/nr,maxMatches,maxSingleErr,maxPairErr});
  }
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
