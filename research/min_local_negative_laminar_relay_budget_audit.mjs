// Prefix stopping criterion and laminar weighted multiband relay packing.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(x,p)=>(x%p+p)%p,N=400000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)spf[n]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
 function event(a,v){let p=Infinity,w=Infinity,e=0,q=Infinity;for(let [x,s] of [[a+1,-1],[a-1,1]])for(let r of fs(x)){q=Math.min(q,r);let t=mod((s===-1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e,q}}
 let s={canonical:0,canonicalEvents:0,half:0,time:0,twinVisited:0,nonTwin:0,nonTwinLowerChecks:0,smallWaitWitness:0,blocks:0,controls:0,intervals:0,empty:0,same:0,groups:0,laminarChecks:0,overlapLowEvents:0,maxDepth:0,weightChecks:0,weightedPackingChecks:0,residualChecks:0,positiveGroup:0,positiveCertificate:0,maxCertificate:0,maxRatio:0,unweightedOvercharge:0,syntheticPermutations:0,syntheticControls:0,rows:[]};
 function check(arr,T0,row){
  if(!arr.length)return;
  let n=arr.length,lev=arr.map(x=>x.p<T0?-1:Math.floor(Math.log2(x.p/T0)));
  let H=Array(n+1).fill(0),G=Array(n+1).fill(0);
  for(let i=0;i<n;i++){H[i+1]=H[i]+(lev[i]>=0?arr[i].p-1:0);G[i+1]=G[i]+(lev[i]<0?arr[i].p-1:0)}
  let max=Math.max(...lev),I=[],groups=new Map();
  for(let j=0;j<=max;j++){
   let last=-1;
   for(let i=0;i<n;i++){if(lev[i]>j){last=-1;continue}if(lev[i]!==j)continue;
    if(last>=0){
     let a=arr[last],b=arr[i],E=H[i]-H[last+1]+G[i]-G[last+1],h=H[i]-H[last+1],g=G[i]-G[last+1];
     ck(E===a.a-a.p+1-b.a,"relay gain");
     let x={l:last+1,r:i,level:j,a:a.a,p:a.p,rp:b.p,e:a.e,f:b.e,E,h,g,weight:0};
     I.push(x);s.intervals++;if(x.l===x.r)s.empty++;
     if(x.p===x.rp){ck(E>=x.p-1,"same");s.same++}
     else{ck(mod(a.a-a.e,a.p)===0&&mod(a.a-(a.p-1+E+b.e),b.p)===0,"CRT");let key=[j,a.p,b.p,a.e,b.e].join(":");let z=groups.get(key)||[];z.push(x);groups.set(key,z)}
    }last=i
   }
  }
  let dep=Array(n).fill(0);for(let x of I)for(let j=x.l;j<x.r;j++)dep[j]++;
  for(let i=0;i<I.length;i++)for(let j=0;j<i;j++){let a=I[i],b=I[j];if(a.l>=a.r||b.l>=b.r)continue;
   ck(a.r<=b.l||b.r<=a.l||a.l<=b.l&&b.r<=a.r||b.l<=a.l&&a.r<=b.r,"laminar");s.laminarChecks++}
  let lowG=G[n];s.maxDepth=Math.max(s.maxDepth,...dep);let raw=0;
  for(let j=0;j<n;j++)if(lev[j]<0){raw+=dep[j]*(arr[j].p-1);if(dep[j]>1)s.overlapLowEvents++}
  if(raw>lowG)s.unweightedOvercharge++;
  // Three allocations: uniform inverse global depth, local inverse max depth,
  // and deepest-relay-only with unit weights on minimal intervals.
  for(let mode=0;mode<3;mode++){
   let gd=Math.max(1,...dep);
   for(let x of I){
    let d=0;for(let j=x.l;j<x.r;j++)if(lev[j]<0)d=Math.max(d,dep[j]);
    x.weight=d===0?0:mode===0?1/gd:mode===1?1/d:(!I.some(y=>y!==x&&y.l>=x.l&&y.r<=x.r&&y.level<x.level&&y.g>0)?1:0);
   }
   for(let j=0;j<n;j++)if(lev[j]<0){let w=I.reduce((w,x)=>w+(x.l<=j&&j<x.r?x.weight:0),0);ck(w<=1+1e-9,"weight overlap");s.weightChecks++}
   let cert=0,actual=0;
   for(let x of I){actual+=x.weight*x.g;if(x.p===x.rp)cert+=Math.max(0,x.weight*(x.p-1-x.h))}
   for(let list of groups.values()){
    let {p,rp}=list[0],span=Math.max(...list.map(x=>x.a))-Math.min(...list.map(x=>x.a)),c=Math.floor(span/(2*p*rp))+1,counts=new Map();
    for(let x of list)counts.set(x.E,(counts.get(x.E)||0)+1);
    ck([...counts.values()].every(v=>v<=c),"capacity");
    let weights=list.map(x=>x.weight).sort((a,b)=>b-a),pack=weights.reduce((sum,w,j)=>sum+2*Math.floor(j/c)*w,0),wE=list.reduce((a,x)=>a+x.weight*x.E,0),known=list.reduce((a,x)=>a+x.weight*x.h,0),rem=list.reduce((a,x)=>a+x.weight*x.g,0);
    ck(pack<=wE+1e-8,"weighted packing");ck(Math.max(0,pack-known)<=rem+1e-8,"group residual");s.weightedPackingChecks++;if(pack>known+1e-8)s.positiveGroup++;cert+=Math.max(0,pack-known);
   }
   ck(cert<=actual+1e-7&&actual<=lowG+1e-7,"certificate total");s.residualChecks++;if(cert>1e-8)s.positiveCertificate++;s.maxCertificate=Math.max(s.maxCertificate,cert);if(lowG)s.maxRatio=Math.max(s.maxRatio,cert/lowG);
   row.maxCertificate=Math.max(row.maxCertificate,cert);
  }
  s.groups+=groups.size;s.controls++;
 }
 // Brute force weighted packing by permutations of the cheapest multiset.
 function perm(a,i,fn){if(i===a.length){fn(a);return}for(let j=i;j<a.length;j++){[a[i],a[j]]=[a[j],a[i]];perm(a,i+1,fn);[a[i],a[j]]=[a[j],a[i]]}}
 for(let c=1;c<=3;c++)for(let n=1;n<=7;n++)for(let mode=0;mode<3;mode++){
  let weights=Array.from({length:n},(_,j)=>((7*j+3*mode)%11)/10).sort((a,b)=>b-a),E=Array.from({length:n},(_,j)=>2*Math.floor(j/c)),lo=weights.reduce((a,w,j)=>a+w*E[j],0),mn=Infinity;
  perm(E,0,x=>{mn=Math.min(mn,x.reduce((a,v,j)=>a+v*weights[j],0));s.syntheticPermutations++});ck(Math.abs(mn-lo)<1e-8,"rearrangement");s.syntheticControls++
 }
 // Exact prefix stopping criterion on every canonical seed up to 120000.
 for(let A=12;A<=120000;A+=6){
  let a=A,v=-A/2+3,W=0,seen=false,reason,arr=[];
  while(true){if(a<=A/2){reason="half";break}let x=event(a,v);if(x.q>Math.sqrt(a+1))seen=true;
   if(v+x.w>-1){reason="time";break}arr.push({a,v,...x});W+=x.w;a-=x.p-1;v+=x.w;s.canonicalEvents++;ck(v+a/2>=0,"height")}
  s.canonical++;s[reason]++;if(seen)s.twinVisited++;else{s.nonTwin++;if(reason==="half")ck(W>=A/4-3,"half bound");else ck(W>=A/2-4-2*Math.sqrt(A+1),"time bound");s.nonTwinLowerChecks++}
  if(W<Math.min(A/4-3,A/2-4-2*Math.sqrt(A+1))){ck(seen,"twin witness");s.smallWaitWitness++}
 }
 // Longer noncanonical paths supply additional overlapping relay controls.
 for(let R of [10000,40000,100000,180000]){
  let row={R,blocks:0,maxCertificate:0};
  for(let mode of [0,1,2,3])for(let A=2*R-150+(6-((2*R-150)%6))%6;A<2*R;A+=6){
   let a=A,v=mode===0?-A/2+3:mode===1?0:mode===2?17:Math.floor(A/5),arr=[];
   function flush(){if(!arr.length)return;for(let T0 of [5,7,11,17,23])check(arr,T0,row);row.blocks++;s.blocks++;arr=[]}
   while(a>=R){let x=event(a,v);if(mode===0&&v+x.w>-1)break;if(x.q>Math.sqrt(a+1))flush();else arr.push({a,v,...x});v+=x.w;a-=x.p-1}flush();
  }s.rows.push(row)
 }
 return s
}
console.log(JSON.stringify(audit(),null,2));
