function audit(){
 const mod=(a,b)=>(a%b+b)%b;
 function isPrime(p){if(p===2)return true;if(p<2||p%2===0)return false;for(let q=3;q*q<=p;q+=2)if(p%q===0)return false;return true}
 function primes(B){let a=[];for(let p=3;p<=B;p+=2)if(isPrime(p))a.push(p);return a}
 function compressed(events,T,primeRoot=true){
  let N=events.length,labels=new Set(events.map(e=>e[1])),qs=[...new Set([...labels,...primes(2*N+(primeRoot?3:2))])].sort((a,b)=>a-b),dead=[],forced=[];
  const hit=(lo,hi,res,par,q)=>{if(hi<lo)return false;let b=mod(res,q);if(b%2!==par)b+=q;return lo+mod(b-lo,2*q)<=hi};
  for(let q of qs){let A=new Set(Array.from({length:q},(_,i)=>i).filter(i=>!primeRoot||i)),E=0,a=0;
   for(let [b,p] of [...events,[T+1,0]]){for(let e of [-1,1]){
    // modular division by 2 without unsafe multiplication for large selected labels
    let c=mod(2-E+e,q);if(c%2)c+=q;c/=2;let r=-c-(e===1?2:0),par=e===1?1:0;
    if(hit(a+1,b-1,r,par,q)||(p>q&&hit(b,b,r,par,q)))A.delete(c);
   }if(p===q){let c=mod(2-E+(b%2?1:-1),q);if(c%2)c+=q;c/=2;let r=-c-(b%2?2:0);if(!hit(b,b,r,b%2,q))A.clear();else for(let v of A)if(v!==c)A.delete(v)}
   if(p){a=b;E+=p-1}}
   if(!A.size)dead.push(q);else if(![...A].some(x=>{let r=mod(2*x-2+E,q);return r!==1&&r!==q-1}))forced.push(q);
  }
  return {dead,forced}
 }
 let escapes=[];
 for(let seed of [{events:[],T:0,E:0},{events:[[4,3],[5,3]],T:6,E:4}])for(let side of [-1,1]){
  let {events,T,E}=seed;events=events.map(e=>e.slice());let chain=[];
  for(let i=0;i<2;i++){
   let Q=[...new Set([...events.map(e=>e[1]),...primes(2*events.length+5)])].reduce((a,b)=>a*b,1),p=Q+1;while(p<=2*T+7||!isPrime(p))p+=Q;if(p>2e6)throw Error("audit size");
   let k=p%4===mod(1-E,4)?1:3,j=(k*p+E-(side===1?7:1))/2;if(j<=T||j>T+2*p||!Number.isInteger(j))throw Error("time");events.push([j,p]);E+=p-1;T=j;
   let c=compressed(events,T);if(c.dead.length||c.forced.length)throw Error("escape renewal");chain.push({p,j,E,Q})
  }escapes.push({seed:seed.T,side,chain})
 }
 function choose(n,k){n=BigInt(n);let r=1n;for(let i=1;i<=k;i++)r=r*(n-BigInt(i)+1n)/BigInt(i);return r}
 function bound(B,k){let v=1n;for(let i=1;i<=k;i++)v*=BigInt(2*i);for(let j=1;j<k;j++)v*=choose(B[j]+BigInt(j),j);return B[k-1]+v}
 let bounds={};for(let [key,base] of [["relaxed",[0n,2n,6n,18n]],["clock",[0n,2n,5n,11n]],["generalOdd",[0n,2n]]]){for(let k=base.length;k<=5;k++)base.push(bound(base,k));bounds[key]=base.map(String)}
 let paths=0,signatures=0,gaps=0;
 function check(S){let Q=S.reduce((a,b)=>a*b,1),D=new Uint16Array(Q+1);let j0=0;for(let j=Q-1;j>=0;j--){for(let p of S){let r=2*j%p;if(r===1||r===p-1){let J=j+(p-1)/2;if(J>Q)throw Error("barrier");D[j]=Math.max(D[j],1+D[J])}}if(D[j]>D[j0])j0=j}
 let w=[],j=j0,last=new Map(),seen=new Set(),used=new Set();while(D[j]){let p=S.find(p=>{let r=2*j%p;return (r===1||r===p-1)&&D[j+(p-1)/2]+1===D[j]});let e=2*j%p===1?1:-1;last.set(p,w.length);used.add(p);w.push({p,e});j+=(p-1)/2;if(used.size!==S.length)continue;
 let order=[...last].sort((a,b)=>a[1]-b[1]),sig=order.map(([p,i])=>[p,w[i].e]),counts=[];for(let a=0;a+1<order.length;a++){let v=order.slice(a+1).map(([q])=>w.slice(order[a][1]+1,order[a+1][1]).filter(x=>x.p===q).length);let len=v.reduce((a,b)=>a+b,0);if(len!==order[a+1][1]-order[a][1]-1||len>Number(bounds.relaxed[v.length]))throw Error("gap");counts.push(v);gaps++}
 let key=JSON.stringify([sig,counts]);if(seen.has(key))throw Error("signature repeats");seen.add(key);
 for(let a=0;a<order.length;a++){let [p,i]=order[a],R=w[i].e-1;for(let b=a;b<order.length-1;b++){for(let c=0;c<counts[b].length;c++)R+=counts[b][c]*(order[b+1+c][0]-1);R+=order[b+1][0]-1}if(mod(R,p)!==2*j%p)throw Error("signature residue")}
 signatures++;
 }paths++}
 let ps=primes(59);for(let i=0;i<ps.length;i++){check([ps[i]]);for(let j=i+1;j<ps.length;j++){check([ps[i],ps[j]]);for(let k=j+1;k<ps.length;k++)check([ps[i],ps[j],ps[k]])}}for(let S of [[3,5,7,11],[3,5,7,17],[3,5,17,19]])check(S)
 return {escapes,bounds,paths,signatures,gaps}
}

console.log(JSON.stringify(audit(),null,2));
