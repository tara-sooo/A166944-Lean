// One-prime insertion: exact internal low-prefix certificate and excess packing bound.
function audit(){
 const mod=(a,p)=>(a%p+p)%p,ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},pr=[3,5,7,11,13,17];
 let out={states:0,prefixes:0,internal:0,congruences:0,directChecks:0,packingChecks:0,chainPackingChecks:0,rows:[]};
 for(let K of [5,7,11]){
  let P=pr.filter(q=>q<=K),p=pr.find(q=>q>K),Q=P.reduce((a,b)=>a*b,1),L=2*Q,s=(p-1)/2,modes=[5,7].filter(z=>z<=K).flatMap(z=>[0,1,2].map(m=>({z,m})));
  let opts=Array.from({length:Q},()=>modes.map(()=>new Map([[0,[0,0,0,-1,-1,-1,-1]]]))),eligible=Array.from({length:Q},(_,x)=>P.flatMap(q=>[-1,1].filter(e=>mod(2*x-e,q)===0).map(e=>[q,e===-1?0:q+2])));
  let nInt=0,maxD=0,minD=Infinity,sideCounts=[0,0],bestInt=modes.map(()=>0),statesInt=new Uint32Array(Q);
  function next(x,n){let q0=0,w=Infinity;for(let [q,c] of eligible[x]){let t=mod(c-n,2*q)||2*q;if(t<w||t===w&&q<q0){q0=q;w=t}}return [q0,w]}
  for(let x=0;x<Q;x++)for(let n0=0;n0<L;n0++){
   let a=x,n=n0,c0=n0%2?p+2:0,a0=n0%2?2:0,alive=true,intD=-1,intSide=0,ds=modes.map(()=>new Map()),total=modes.map(()=>0),exc=modes.map(()=>0);
   for(;;){
    let [q,w]=next(a,n),d=x-a;
    if(alive){let r=mod(a0-2*d,p);if(r===1||r===p-1){let wp=mod((r===1?p+2:0)-c0-(n-n0),2*p)||2*p;if(wp<w){alive=false;intD=d;intSide=r===1?1:-1;ck(d>=s&&[s,s+1,s+2].includes(mod(d,p)),"internal congruence");out.congruences++;out.internal++;nInt++;statesInt[x]++;maxD=Math.max(maxD,d);minD=Math.min(minD,d);sideCounts[+(intSide===1)]++;for(let i=0;i<modes.length;i++){let v=opts[x][i].get(d)||[0,0,0,-1,-1,-1,-1];v[2]=Math.max(v[2],total[i]);let slot=3+2*(n0%2)+ +(intSide===1);v[slot]=Math.max(v[slot],total[i]);opts[x][i].set(d,v);bestInt[i]=Math.max(bestInt[i],total[i])}}}}
    for(let i=0;i<modes.length;i++){let v=opts[x][i].get(d)||[0,0,0,-1,-1,-1,-1];v[0]=Math.max(v[0],exc[i]);if([s,s+1,s+2].includes(mod(d,p)))v[1]=Math.max(v[1],total[i]);opts[x][i].set(d,v)}
    if(!q)break;
    let b=n+w-n0+a-x,k=(q-1)/2;
    for(let i=0;i<modes.length;i++)if(q<=modes[i].z)for(let h=b+1-k;h<b;h++){let m=(ds[i].get(h)||0)+1;ds[i].set(h,m);total[i]++;if(m>modes[i].m)exc[i]++}
    a-=k;n+=w;ck(a>=0,"wall");out.prefixes++;
   }
   if((x*L+n0)%997===0){
    let A=2*x,N=n0;while(mod(A,p)!==a0)A+=2*Q;while(mod(N,2*p)!==c0)N+=L;
    let u=A,v=N,d=-1,side=0;
    for(;;){let q0=0,w=Infinity,e0=0;for(let q of [...P,p])for(let e of [-1,1])if(mod(u-e,q)===0){let t=mod((e===-1?0:q+2)-v,2*q)||2*q;if(t<w||t===w&&q<q0){q0=q;w=t;e0=e}}
     if(!q0)break;if(q0===p){d=(A-u)/2;side=e0;break}u-=q0-1;v+=w;
    }ck(d===intD&&side===intSide,{K,x,n0,d,intD,side,intSide});out.directChecks++;
   }
   out.states++;
  }
  for(let i=0;i<modes.length;i++){
   let {z,m}=modes[i],F=Array.from({length:3},()=>new Int32Array(Q+1));
   for(let x=0;x<Q;x++)for(let j=0;j<3;j++){F[j][x+1]=F[j][x];for(let [d,v] of opts[x][i]){F[j][x+1]=Math.max(F[j][x+1],Math.max(v[0],v[j])+F[j][Math.max(0,x-d-s+1)]);out.packingChecks++}}
   ck(F[0][Q]<=F[2][Q]&&F[2][Q]<=F[1][Q],"packing ordering");
   const Qnew=Q*p,sNew=(pr.find(q=>q>p)-1)/2,H=new Int32Array(Qnew+1),B=[new Int32Array(Qnew),new Int32Array(Qnew)];
   for(let x=0;x<Qnew;x++){
    let x0=x%Q,phase=mod(x,p),post=phase===0?0:phase===1?1:-1,best=0,begin=0;
    for(let [d,v] of opts[x0][i]){
     let end=x-d,after=end-s,j=mod(2*end,p),target=j===1?1:j===p-1?0:-1,exit=v[0]+H[Math.max(0,end-sNew+1)];
     begin=Math.max(begin,exit);
     if(post>=0)best=Math.max(best,exit);
     if(target>=0){
      let tail=after<0?0:B[target][after];
      begin=Math.max(begin,v[0]+tail);
      if(post>=0&&v[3+2*post+target]>=0)best=Math.max(best,v[3+2*post+target]+tail);
     }
     out.chainPackingChecks++;
    }
    if(post>=0)B[post][x]=best;
    H[x+1]=Math.max(H[x],begin);
   }
   ck(H[Qnew]<=p*F[2][Q],"chain relaxation tighter");
   if(m===1&&p===7&&z===5)ck(H[Qnew]>=0,"known exact bound");
   if(m===1&&p===11&&z===7)ck(H[Qnew]>=31,"known exact bound");
   
   out.rows.push({K,p,z,m,Q,states:Q*L,internal:nInt,internalFraction:nInt/(Q*L),internalSpatialClasses:statesInt.filter(x=>x>0).length,minD,maxD,sideCounts,bestInt:bestInt[i],base:F[0][Q],congruence:F[1][Q],exactInternal:F[2][Q],rhoBase:F[0][Q]/Q,rhoCongruence:F[1][Q]/Q,rhoExactInternal:F[2][Q]/Q,chain:H[Qnew],rhoChain:H[Qnew]/Qnew})
  }
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
