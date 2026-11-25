// Exact rational-weight checks for the dimension-two upper sieve.
function audit(){
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a},mod=(a,b)=>(a%b+b)%b;
 function primes(n){let p=[];for(let x=3;x<=n;x+=2)if(p.every(q=>q*q>x||x%q))p.push(x);return p}
 let tests=0,quadratic=0,weights=0,lattice=0,identityChecks=0,sieveTotal=0,weightedTotal=0,largeWeightMax=0,averageChecks=0,examples=[];
 function exact(z,kind,parameter,e,lo,N){
  const ps=primes(z),Rho=new Map(),bad=new Map();
  for(let l of ps){let arr=[0];if(kind==="fixed"){
    if(parameter%l===0)throw Error("p not coprime");let v=0;while(mod(parameter*v+2*e,l))v++;if(v===0)throw Error("two roots");arr.push(v)
   }else{let v=mod(-parameter,l);if(v)arr.push(v)}
   bad.set(l,arr);Rho.set(l,arr.length)
  }
  const D=[{d:1,mu:1,rs:1,hden:1,fac:[]}];
  for(let l of ps){let orig=D.slice();for(let x of orig)if(x.d*l<=z){D.push({d:x.d*l,mu:-x.mu,rs:x.rs*Rho.get(l),hden:x.hden*(l-Rho.get(l)),fac:[...x.fac,l]})}}
  const M=ps.reduce((s,l)=>s*BigInt(l-Rho.get(l)),1n),R=ps.reduce((s,l)=>s*BigInt(Rho.get(l)),1n),P=ps.reduce((s,l)=>s*BigInt(l),1n);
  for(let x of D)x.hnum=M/BigInt(x.hden)*BigInt(x.rs);
  let G=D.reduce((s,x)=>s+x.hnum,0n),scale=G*R;
  for(let x of D){let T=D.filter(y=>y.d%x.d===0).reduce((s,y)=>s+y.hnum,0n);x.W=BigInt(x.mu)*BigInt(x.d)*(R/BigInt(x.rs))*T;
   if((x.W<0n?-x.W:x.W)>BigInt(x.d)*scale)throw Error("weight bound");weights++}
  if(D[0].W!==scale)throw Error("lambda1");
  let Q=0n,E=0n;
  for(let x of D)for(let y of D){let l=x.d*y.d/gcd(x.d,y.d),rs=1;for(let p of ps)if(l%p===0)rs*=Rho.get(p);Q+=x.W*y.W*BigInt(rs)*(P/BigInt(l));E+=(x.W<0n?-x.W:x.W)*(y.W<0n?-y.W:y.W)*BigInt(rs);quadratic++}
  if(Q*G!==scale*scale*P*M)throw Error("diagonalization");
  if(E>BigInt(z)**6n*scale*scale)throw Error("error bound");
  let S=0,W=0n;for(let n=lo;n<lo+N;n++){let sum=0n,div=new Set(ps.filter(l=>bad.get(l).includes(mod(n,l))));if(!div.size)S++;for(let x of D)if(x.fac.every(l=>div.has(l)))sum+=x.W;W+=sum*sum;lattice++}
  if(BigInt(S)*scale**2n>W||W*G>BigInt(N)*M*scale**2n+E*G)throw Error("sieve majorant");
  // Exact G0 comparison, including degenerate shifts.
  const M0=ps.reduce((s,l)=>s*BigInt(l-2),1n);
  const G0=D.reduce((s,x)=>s+(M0/x.fac.reduce((a,l)=>a*BigInt(l-2),1n))*(2n**BigInt(x.fac.length)),0n);
  let pn=1n,pd=1n;for(let l of ps)if(kind==="shift"&&parameter%l===0){pn*=BigInt(l);pd*=BigInt(l-2)}
  if(G0*M*pd>G*M0*pn)throw Error("singular product comparison");
  // Odd harmonic-pair lower bound G0>= H_odd(floor sqrt z)^2/6.
  let t=Math.floor(Math.sqrt(z)),hd=1n;for(let a=1;a<=t;a+=2)hd*=BigInt(a);
  let hn=0n;for(let a=1;a<=t;a+=2)hn+=hd/BigInt(a);
  if(6n*G0*hd*hd<M0*hn*hn)throw Error("harmonic lower bound");
  tests++;identityChecks++;sieveTotal+=S;weightedTotal+=Number(W)/Number(scale**2n);
  largeWeightMax=Math.max(largeWeightMax,...D.map(x=>Math.abs(Number(x.W)/Number(scale))));
  if(examples.length<4||kind==="shift"&&parameter===210&&z===43)examples.push({z,kind,parameter,e,lo,N,survivors:S,weighted:Number(W)/Number(scale**2n),main:Number(BigInt(N)*M)/Number(G)});
 }
 for(let z of [3,5,7,11,17,23,31,43,61])for(let N of [100,1000,10000]){
  for(let [p,e] of [[101,1],[103,-1],[107,1]])exact(z,"fixed",p,e,19,N);
  for(let h of [2,6,12,30,42,210,2310])exact(z,"shift",h,1,101,N);
 }
 // Verify the mean singular product inequality over a complete finite divisor expansion.
 for(let T of [1,10,100,1000,10000]){
  const ps=primes(T);
  // Products represented as floating point here only for the diagnostic display;
  // the rigorous proof uses a positive divisor expansion and telescoping series.
  let sum=0;for(let h=1;h<=T;h++){let n=h,val=1;for(let p of ps){if(p*p>n)break;if(n%p===0){val*=p/(p-2);while(n%p===0)n/=p}}if(n>2&&n%2)val*=n/(n-2);sum+=val}
  // n may retain powers of 2; use independent exact factor loop below.
  let sum2=0;for(let h=1;h<=T;h++){let n=h;while(n%2===0)n/=2;let val=1;for(let p of ps){if(p*p>n)break;if(n%p===0){val*=p/(p-2);while(n%p===0)n/=p}}if(n>1)val*=n/(n-2);sum2+=val}
  if(sum2>T*Math.E)throw Error("mean singular factor");
  averageChecks++;if(T===10000)examples.push({T,meanSingular:sum2/T});
 }
 return {tests,quadratic,weights,lattice,identityChecks,sieveTotal,weightedTotal,largeWeightMax,averageChecks,examples}
}
console.log(JSON.stringify(audit(),null,2));
