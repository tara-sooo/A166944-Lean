// Exact reverse-clock ancestry in the absorbing process; LOW7 prefix-gain relaxation.
function reverseAudit(X) {
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,L=210,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const check=b=>{if(!b)throw Error("assertion failed")},mod=(a,m)=>((a%m)+m)%m;
 function primes(v,max=B){let a=[];while(v>1){let p=spf[v];if(p>max)break;a.push(p);while(v%p===0)v/=p}return a}
 function hit(t,C,K){let u=K+1,q=0;for(let s of [-1,1])for(let p of primes(C+s)){let h=t+1+mod((s===-1?0:p+2)-t-1,2*p);if(h<u||(h===u&&p<q)){u=h;q=p}}return [u,q]}
 function prev(n,C){let a=X+3;for(let s of [-1,1])for(let p of primes(C+s)){let z=n-1-mod(n-1-(s===-1?0:p+2),2*p);a=Math.max(a,z)}return a}
 function root(i){return 2*X+4*i}
 function cutoff(i){return Math.floor((7*(X+2*i+1)-1)/4)}
 const Kmax=cutoff(N-1),caps=[Math.max(2,Math.floor(B/8)),Math.max(2,Math.floor(B/4)),Math.max(2,Math.floor(B/2))];
 const back=Array.from({length:L},()=>new Set());
 for(let c=0;c<L;c+=2)for(let t=0;t<L;t++){
  let C=c,u=t;back[C%L].add(0);for(;;){let a=Infinity,q=0;for(let p of [3,5,7])for(let s of [-1,1])if((C+s)%p===0){let v=u+1+mod((s===-1?0:p+2)-u-1,2*p);if(v<a||(v===a&&p<q)){a=v;q=p}}if(!q)break;u=a;C+=q-1;check(C-c<L);back[C%L].add(C-c)}
 }
 const maxLow=Math.max(...back.map(s=>s.size)),maxGain=Math.max(...back.flatMap(s=>[...s]));
 function run(cap){
  const buckets=new Map(),put=(i,t,C,h)=>{if(!buckets.has(C))buckets.set(C,[]);buckets.get(C).push({i,t,h})};
  for(let i=0;i<N;i++)put(i,X+2*i+3,root(i),0);
  const stops=new Map(),key=(p,C)=>`${p},${C}`;
  for(let C=2*X;C<7*X;C+=2){let a=buckets.get(C);if(!a)continue;buckets.delete(C);let g=new Map();
   for(let e of a){let [n,p]=hit(e.t,C,cutoff(e.i));if(!p)continue;if(p<=7)put(e.i,n,C+p-1,e.h);else{if(!g.has(p))g.set(p,[]);g.get(p).push({...e,n})}}
   for(let [p,z] of g)if(z.length>=cap)stops.set(key(p,C),{p,C,z});else for(let e of z)put(e.i,e.n,C+p-1,e.h+1)
  }
  const memo=new Map(),relaxMemo=new Map();let queryTimes=0,exactChecks=0,rows=[];
  function arrivals(D,lo,hi){let a=new Set(),t0=(D+6)/2;if(t0%2===1&&t0>=lo&&t0<hi)a.add(t0);for(let p of primes(D))for(let t=lo+mod(-lo,2*p);t<hi;t+=2*p)a.add(t);for(let p of primes(D+2))for(let t=lo+mod(p+2-lo,2*p);t<hi;t+=2*p)a.add(t);return a}
  function F(t,H){if(H<2*X||H>2*t||t<X+3)return new Map();let k=t*(7*X+4)+H;if(memo.has(k))return memo.get(k);let a=new Map();
   if(t%2===1&&H===2*t-6){let i=(H-2*X)/4;if(Number.isInteger(i)&&i>=0&&i<N&&cutoff(i)>=t)a.set(i,0)}
   for(let q of primes(t%2?H+2:H)){
    if(t%2?mod(t-(q+2),2*q)!==0: t%(2*q)!==0)continue;
    let D=H-q+1;if(D<2*X||stops.has(key(q,D))||hit(t-1,D,t)[1]!==q)continue;
    for(let u of arrivals(D,prev(t,D),t))for(let [i,h] of F(u,D))if(cutoff(i)>=t){check(!a.has(i));a.set(i,h+ +(q>7))}
   }memo.set(k,a);return a
  }
  function relaxed(C,h){if(C<2*X)return new Set();let k=C*10+h;if(relaxMemo.has(k))return relaxMemo.get(k);let a=new Set();for(let g of back[C%L]){let D=C-g;if(D>=2*X&&D<4*X&&(D-2*X)%4===0)a.add((D-2*X)/4);if(h>0){for(let q of [...new Set([...primes(D),...primes(D+2)])])if(q>7&&D-q+1>=2*X)for(let i of relaxed(D-q+1,h-1))a.add(i)}}relaxMemo.set(k,a);return a}
  let selected=[...stops.values()].sort((a,b)=>b.z.length-a.z.length).slice(0,X<=1024?100:1);
  for(let {p,C,z} of selected){
   let actual=new Map(z.map(e=>[e.i,e.h])),found=new Map(),side=(C-1)%p===0?-1:1,phase=side===-1?0:p+2;
   for(let n=X+4+mod(phase-X-4,2*p);n<=Kmax;n+=2*p){
    if(hit(n-1,C,n)[1]!==p)continue;queryTimes++;
    for(let t of arrivals(C,prev(n,C),n))for(let [i,h] of F(t,C))if(cutoff(i)>=n){check(!found.has(i));found.set(i,h)}
   }
   check(actual.size===found.size);for(let [i,h] of actual)check(found.get(i)===h);exactChecks+=found.size;
   let depths=[];for(let h=0;h<=4;h++){let r=relaxed(C,h),a=[...actual].filter(([i,k])=>k<=h);for(let [i,k] of a)check(r.has(i));depths.push({h,actual:a.length,relaxed:r.size})}
   rows.push({p,C,m:z.length,depths});
  }
  return {cap,sinks:stops.size,checked:rows.length,exactChecks,memoNodes:memo.size,queryTimes,top:rows.slice(0,3),all:rows}
 }
 return {X,B,maxLow,maxGain,runs:caps.map(run)};
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(reverseAudit(Number(a))));
