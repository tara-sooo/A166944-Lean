// Void probability and size-biased gap entropy bounds from exact barrier pair correlations.
// node research/min_local_negative_barrier_void_moment_audit.mjs
function audit(){
 const primes=[5,7,11,13,17,19,23,29,31,37,41,43,47,53],mod=(a,p)=>(a%p+p)%p,ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 let P=1n,delta=1,ps=[],rows=[],checks=0;
 for(let p of primes){
  ps.push(p);P*=BigInt(p);delta*=((p-1)/2)/p;
  if(![7,13,19,23,31,43,53].includes(p))continue;
  const tables=ps.map(q=>{let l=(q-1)/2;return Array.from({length:q},(_,d)=>{let r=mod(3*d,q);return q*Math.max(0,l-Math.min(r,q-r))/(l*l)})});
  let base=Math.max(1,Math.ceil(1/delta)),Hs=[1,2,4,8,16,32].map(k=>Math.ceil(k*base)),maxH=Hs.at(-1);
  const logPeriod=Math.log(Number(P));
  let sum=0,weighted=0,hIndex=0,ms=[];
  for(let d=1;d<maxH;d++){
   let c=1;for(let i=0;i<ps.length;i++){c*=tables[i][d%ps[i]];if(c===0)break}
   sum+=c;weighted+=d*c;
   let H=d+1;if(H===Hs[hIndex]){
    let r=1/(H*delta)+2*(H*sum-weighted)/(H*H)-1;
    ck(r>=-1e-8,"variance nonnegative");r=Math.max(0,r);
    let voidBound=r/(1+r),tailBound=Math.min(1,2*voidBound);
    let entropyBound=Math.min(logPeriod,Math.log(2*H)+tailBound*Math.max(0,logPeriod-Math.log(2*H)));
    ms.push({H,relativeVariance:r,voidBound,tailBound,entropyBound});hIndex++;checks++;
   }
  }
  ck(ms.length===Hs.length,"all moments");
  // Enumerate exact cyclic gaps for p<=23, in canonical coordinate k=b/6.
  let exact=null;
  if(p<=23){
   let M=1,B=[0];
   for(let q of ps){let C=[];for(let b of B)for(let j=0;j<q;j++){let k=b+j*M;if(mod(-3*k,q)<=(q-3)/2)C.push(k)}M*=q;B=C.sort((a,b)=>a-b)}
   let gaps=B.map((b,i)=>(i===B.length-1?B[0]+M:B[i+1])-b),meanLog=gaps.reduce((s,g)=>s+g/M*Math.log(g),0);
   ck(BigInt(M)===P&&Math.abs(B.length/M-delta)<1e-12,"CRT set");
   for(let row of ms){let H=row.H,v=gaps.reduce((s,g)=>s+Math.max(0,g-H),0)/M,tail=gaps.reduce((s,g)=>s+(g>2*H?g:0),0)/M;
    ck(v<=row.voidBound+1e-8&&tail<=row.tailBound+1e-8&&meanLog<=row.entropyBound+1e-8,"exact void and entropy");
    row.exactVoid=v;row.exactTail=tail;checks++;
   }
   // Direct count second moments independently on small periods.
   if(p<=13){
    let arr=new Uint8Array(M);for(let b of B)arr[b]=1;
    for(let row of ms){let H=row.H,C=0;for(let i=0;i<H;i++)C+=arr[mod(-i,M)];
     let sq=0;for(let i=0;i<M;i++){sq+=(C-H*delta)**2;C+=arr[(i+1)%M]-arr[mod(i-H+1,M)];}
     ck(Math.abs(sq/M/(H*delta)**2-row.relativeVariance)<1e-8,"literal window variance");checks++;
    }
   }
   exact={barriers:B.length,meanLog};
  }
  let best=ms.reduce((a,b)=>a.entropyBound<b.entropyBound?a:b);
  rows.push({z:p,period:P.toString(),delta,meanGap:1/delta,logMeanGap:Math.log(1/delta),logPeriod,exact,best,ms,terms:maxH-1});
 }
 return {checks,rows};
}
console.log(JSON.stringify(audit(),null,2));
