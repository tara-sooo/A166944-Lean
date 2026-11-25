// Exact selected-clock CRT controls of overlapping last-exit corridors (relaxed, not MIN first-hit).
function audit(){
 const cap=100000,spf=new Int32Array(cap),ps=[];
 for(let i=2;i<cap;i++)if(!spf[i]){spf[i]=i;if(i%2)ps.push(i);if(i*i<cap)for(let j=i*i;j<cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b,assert=(v,m)=>{if(!v)throw Error(m)};
 const results=[];
 for(let p of [2551,3391,8431,12007]){
  if(spf[p]!==p||p%4!==3)continue;
  const R=p-2,used=new Set([p]),rows=[];let d=6,tpar=1;
  function push(s,w){let dp=d+2*w-s+1;assert(w>=1&&w<=2*s&&mod(tpar+w,2)===0&&dp>=0&&dp%(2*s)===0,"clock geometry");rows.push({p:s,w,d,dp,I:0});used.add(s);d=dp;tpar=0}
  push(p,(3*p-7)/2);
  function descend(target,low){
   while(d+3>target){
    let best=null;
    for(let s of ps){if(s>R)break;if(used.has(s))continue;let w=mod((-d-1)*((s+1)/2),s);if(w%2)w+=s;if(!w)w=2*s;
     let dp=d+2*w-s+1;if(dp>=d||dp<low||dp===0)continue;
     if(!best||dp<best.dp)best={s,w,dp}
    }assert(best,"descending clock "+p+" d"+d+" low"+low);push(best.s,best.w)
   }
  }
  descend(.7*p,.48*p);
  let q=ps.find(q=>q>3.7*p&&q<3.95*p&&q>=5*(d+3)&&mod(3*q-d-1,4)===0);assert(q,"second mark");push(q,(3*q-d-1)/2);
  descend(.38*p,.26*p);
  // CRT fixes the chosen horizon congruence for every distinct label; not a MIN first-hit test.
  let H0=0n,P=4n,g=0;
  for(let z of rows){let s=z.p,r=mod(1-g,s),a=Number(P%BigInt(s)),b=s,u=1,v=0;while(b){let k=Math.floor(a/b);[a,b]=[b,a-k*b];[u,v]=[v,u-k*v]}assert(a===1,"inverse");H0+=P*BigInt(mod(u*(r-Number(H0%BigInt(s))),s));P*=BigInt(s);g+=s-1}
  while(H0<BigInt(q*q+8))H0+=P;
  let H=H0,t=H0/2n+3n,checks=0;
  for(let z of rows){let n=t+BigInt(z.w),s=BigInt(z.p);assert((H-1n)%s===0n&&n%s===0n&&n%2n===0n&&s*s<=H+1n&&2n*t-H===BigInt(z.d),"absolute clock");H+=s-1n;t=n;assert(2n*t-H===BigInt(z.dp),"post");checks++}
  const xs=[...rows.map(z=>z.d+3),rows.at(-1).dp+3],corr=[];
  for(let [i,T] of [[0,p],[rows.findIndex(z=>z.p===q),2*p]]){
   assert(rows[i].p>=T&&rows[i].p<2*T&&rows[i].p>=5*xs[i]&&rows[i].dp===2*rows[i].p,"A1");
   let b=i+1;while(b<xs.length&&5*xs[b]>2*T)b++;assert(b<xs.length,"complete");
   let a=b-1;while(10*xs[a]<19*T)a--;
   assert(a>i&&a<b&&rows.slice(a,b).every(z=>z.p<=R),"good");
   corr.push({a,b,T,startX:xs[a],endX:xs[b],gain:rows.slice(a,b).reduce((s,z)=>s+z.p-1,0),labels:rows.slice(a,b).map(z=>z.p)})
  }
  let overlap=Math.min(corr[0].b,corr[1].b)-Math.max(corr[0].a,corr[1].a);
  assert(overlap>0,"actual overlap in relaxed timed path");results.push({p,q,R,events:rows.length,absoluteClockChecks:checks,rootDigits:(H0/2n+1n).toString().length,overlap,corr})
 }
 assert(results.length===4,"controls");return results
}
console.log(JSON.stringify(audit(),null,2));
