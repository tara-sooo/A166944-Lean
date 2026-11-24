// Terminal frozen-state high-clock product: exact residue checks and omitted-tail bounds.
function gapAudit(){
 const ck=(b,m)=>{if(!b)throw Error(m)};
 let exact=[];
 for(let q of [3,5,7,11,13,17,19,23])for(let parity of [0,1])for(let S of [0,1,2,q-1,q,q+1,2*q-1,2*q,2*q+1,3*q]){
  let count=0;for(let c=0;c<q;c++)for(let t=0;t<q;t++){
   let tt=t%2===parity?t:t+q,hit=false;for(let j=1;j<=S;j++){
    if(((tt+j)%2===0&&c===1&&(tt+j)%q===0)||((tt+j)%2===1&&c===q-1&&(tt+j-2)%q===0)){hit=true;break}
   }if(hit)count++
  }let expected=Math.min(q,Math.floor(S/2))+Math.min(q,Math.ceil(S/2));ck(count===expected,"gap count");exact.push({q,parity,S,count})
 }
 const Q=10000000,sieve=new Uint8Array(Q+1),primes=[];
 for(let p=2;p<=Q;p++)if(!sieve[p]){primes.push(p);if(p*p<=Q)for(let j=p*p;j<=Q;j+=p)sieve[j]=1}
 let rows=[];
 for(let Y of [13,53,101,397,1597,10007]){
  let cuts=[{type:"Y",S:Y},{type:"YlogY",S:Math.floor(Y*Math.log(Y))},{type:"Y^1.5",S:Math.floor(Y**1.5)},{type:"Y^2",S:Y*Y}].filter(z=>z.S<=Q);
  for(let z of cuts){
   let lp=0, count=0;for(let q of primes)if(q>=Y){let b=Math.min(q,Math.floor(z.S/2))+Math.min(q,Math.ceil(z.S/2));lp+=Math.log1p(-b/q**2);count++}
   let upper=Math.exp(lp);
   // All primes beyond Q are coprime to 30. For each full 30-block after Q,
   // use its left endpoint as a majorant, including the first partial block.
   let b0=Math.floor(Q/30),tailBound=z.S*8/900*(1/b0**2+1/b0);
   let lower=upper*Math.max(0,1-tailBound);ck(lower<=upper&&tailBound<=z.S/Q*1.001,"tail");
   rows.push({Y,...z,Q,primeCount:count,truncated:upper,tailBound,lower,upper,limit:z.type==="Y^1.5"?4/9:z.type==="Y^2"?.25:1});
  }
 }
 return {exactChecks:exact.length,exact,rows}
}
console.log(JSON.stringify(gapAudit()));
