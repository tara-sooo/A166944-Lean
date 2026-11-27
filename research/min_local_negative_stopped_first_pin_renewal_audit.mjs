// Event-to-event first-pin renewal at a common height with gain-budget stopping.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p;
 const P=[3,5,7,11,13,17],M=2*P.filter(p=>p>3).reduce((a,b)=>a*b,1);
 let z={fullRoots:0,deletedRoots:0,activated:0,affordable:0,overBudget:0,blocks:0,pinChecks:0,fullComparisons:0,repeatChecks:0,eventChecks:0,rows:[]};
 function next(a,n,Q){let p=1,w=Infinity,s=0;for(let q of Q)for(let e of [-1,1])if(mod(a-e,q)===0){let d=mod((e===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d;s=e}}return {p,w,s}}
 function finish(A,state,Q,H,J,hook){
  let {a,n,h,G,N,labels}=state;labels=labels.slice();
  for(;;){let v=next(a,n,Q),lim=H-h;
   if(hook)hook({a,n,h,G,N,labels:labels.slice(),v,lim});
   if(v.w>lim)return {a,h:H,G,N,labels,reason:"height"};
   if(G+v.p-1>J)return {a,h:h+v.w-1,G,N,labels,reason:"gain"};
   a-=v.p-1;n+=v.w;h+=v.w-(v.p-1)/2;G+=v.p-1;N++;labels.push(v.p);ck(h<H&&h>=0,"height");
  }
 }
 function initial(A){return {a:A,n:3-A/2,h:3,G:0,N:0,labels:[]}}
 function same(x,y,L){return mod(x.a,L)===mod(y.a,L)&&x.h===y.h&&x.G===y.G&&x.N===y.N&&x.reason===y.reason&&x.labels.join(",")===y.labels.join(",")}
 for(let [H,J] of [[24,18],[48,30],[64,60]])for(let p of [5,7,11,13,17]){
  const old=P.filter(q=>q!==p),m=M/p,l=6*m,L=6*M;let stats={H,J,p,M,m,deletedMean:0,fullMean:0,firstFraction:0,blockedFraction:0,pMean:0,pUpper:0,changedMean:0,selectedFraction:0,selectedMean:0,selectedFirst:0,selectedP:0,selectedPUpper:0,avgBlocks:0,avgPins:0,avgAffordablePins:0,repeatMean:0,positiveDelta:0,negativeDelta:0};
  for(let j=0;j<m;j++){
   let A=6*j,seen=new Map();
   const base=finish(A,initial(A),old,H,J,v=>{
    z.blocks++;stats.avgBlocks++;
    for(let s of [-1,1]){
     let r=mod(v.G+s,p);if(seen.has(r))continue;
     let k=0;while(mod(v.a+k*l-s,p))k++;ck(k<p,"unique");
     let n=v.n-k*l/2,w=mod((s===-1?0:p+2)-n,2*p)||2*p;
     if(w>v.lim||w>v.v.w||w===v.v.w&&p>v.v.p)continue;
     const ok=v.G+p-1<=J;
     let st={a:v.a+k*l,n,h:v.h,G:v.G,N:v.N,labels:v.labels};
     let x=ok?finish(A+k*l,{a:st.a-p+1,n:n+w,h:v.h+w-(p-1)/2,G:v.G+p-1,N:v.N+1,labels:[...v.labels,p]},P,H,J):{a:st.a,h:v.h+w-1,G:v.G,N:v.N,labels:v.labels,reason:"gain"};
     ck(mod(A+k*l,p)===r,"pin");z.pinChecks++;seen.set(r,{k,x,ok});z.activated++;stats.avgPins++;
     if(ok){z.affordable++;stats.avgAffordablePins++}else z.overBudget++;
    }
   });
   z.deletedRoots++;stats.deletedMean+=base.N;
   let sumDelta=0,first=0,blocked=0;
   for(let k=0;k<p;k++){
    let B=A+k*l,v=seen.get(mod(B,p)),x=v?v.x:{...base,a:base.a+k*l};
    let y=finish(B,initial(B),P,H,J);
    ck(same(x,y,L),{H,J,p,B,x,y});z.fullComparisons++;z.fullRoots++;
    let pc=y.labels.filter(q=>q===p).length,firstUse=pc>0;
    ck(firstUse===!!(v&&v.ok),"first affordable");z.eventChecks++;
    let cap=firstUse?Math.floor((y.G/(p-1)+1)/2):0;
    ck(pc<=cap,"repeat gain bound");if(firstUse)z.repeatChecks++;
    stats.pMean+=pc;stats.pUpper+=cap;stats.repeatMean+=Math.max(0,pc-1);
    if(y.reason==="height"){stats.selectedFraction++;stats.selectedMean+=y.N;stats.selectedFirst+=+firstUse;stats.selectedP+=pc;stats.selectedPUpper+=cap}
    stats.fullMean+=y.N;sumDelta+=y.N-base.N;
    first+=+firstUse;blocked+=+(!!v&&!v.ok);
   }
   let delta=[...seen.values()].reduce((s,v)=>s+v.x.N-base.N,0);
   ck(delta===sumDelta&&first===[...seen.values()].filter(v=>v.ok).length,"insertion mean identity");
   stats.firstFraction+=first;stats.blockedFraction+=blocked;stats.changedMean+=delta;
   for(let v of seen.values()){let d=v.x.N-base.N;if(d>0)stats.positiveDelta+=d;else stats.negativeDelta+=d}
  }
  let sel=stats.selectedFraction;
  for(let k of ["deletedMean","avgBlocks","avgPins","avgAffordablePins"])stats[k]/=m;
  for(let k of ["fullMean","firstFraction","blockedFraction","pMean","pUpper","changedMean","selectedFraction","positiveDelta","negativeDelta","repeatMean"])stats[k]/=M;
  for(let k of ["selectedMean","selectedFirst","selectedP","selectedPUpper"])stats[k]/=sel;
  ck(Math.abs(stats.fullMean-stats.deletedMean-stats.changedMean)<1e-10,"mean");
  z.rows.push(stats)
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
