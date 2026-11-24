// Reproduce: node research/min_prime_root_repeat_energy_audit.mjs
function audit(X, diagnostic=false) {
  const B=Math.ceil(Math.sqrt(7*X)), Q=diagnostic?Math.max(5,Math.floor(B/8)):Math.ceil(B/Math.log(B)), J=diagnostic?12:Math.floor(Math.pow(Math.log(B),.25)), k=Math.max(1,Math.floor(Math.sqrt(Math.log(B)))), T=B;
  const lim=7*X+5, spf=new Int32Array(lim+1), ps=[];
  for(let n=2;n<=lim;n++) if(!spf[n]) {spf[n]=n;if(n<=B && n%2)ps.push(n);if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)if(!spf[j])spf[j]=n;}
  const factors=n=>{let a=[];while(n>1){let p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
  const mod=(a,m)=>((a%m)+m)%m;
  const gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c;}return a;};
  const inv=(a,m)=>{let x=0,y=1,b=m;while(a){let q=Math.floor(b/a);[b,a]=[a,b-q*a];[x,y]=[y,x-q*y];}if(b!==1)throw Error("inverse");return mod(x,m);};
  const ok=(b,msg)=>{if(!b)throw Error(msg);};
  const bad=new Set();
  for(const p of ps)if(p>=Q)for(const q of ps)if(q!==p) {
    let congr=false;for(let c=-J;c<=4;c++)if(c%2===0&&mod(q-c,p)===0){congr=true;break;}if(!congr)continue;
    const pq=p*q, ip=inv(p,q);
    for(let e=0;e<=J;e+=2)for(const sigma of [-1,1])for(const tau of [-1,1]){
      let a=mod(-sigma,p), b=mod(e-1-tau,q), r=a+p*mod((b-a)*ip,q);
      let C=r+pq*Math.ceil((2*X-r)/pq);if(C%2)C+=pq;
      for(;C<7*X;C+=2*pq)bad.add(C);
    }
  }
  const rcache=new Int32Array(lim+1);
  function least(C){if(rcache[C])return rcache[C]-1;let v=0;for(const n of [C-1,C+1])for(const p of factors(n))if(!v||p<v)v=p;rcache[C]=v+1;return v;}
  let S0=0,Sbad=0;for(let C=2*X;C<7*X;C+=2){let r=least(C);S0+=r;if(bad.has(C))Sbad+=r;}
  let N=0,H=0,R=0,base=0,deleted=0,small=0,high=0,Z=0,light=0,lightCost=0,events=0,literal=0,nontwin=0, maxCount=0;
  const W=new Map(),Wlate=new Map(),Wall=new Map();
  function add(m,C){m.set(C,(m.get(C)||0)+1);}
  for(let M=X+(X%2===0?1:0);M<2*X;M+=2)if(spf[M]===M){
    N++;let t=M+2,C=2*M-2,K=Math.floor((7*M-1)/4);H+=K-t;
    let a=[],last=new Map(),counts=new Map(),smallCounts=new Map(), elapsed=0;
    while(true){
      let tt=Infinity,p=Infinity,sg=0;
      for(const sigma of [-1,1])for(const q of factors(C+sigma)){
        let residue=sigma===-1?0:q+2, tick=t+1+mod(residue-(t+1),2*q);
        if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;sg=sigma;}
      }
      if(X<=1024){let lt=Infinity,lp=Infinity;for(let n=t+1;n<=K;n++){let d=gcd(n%2?n-2:n,C+(n%2?1:-1));let fs=factors(d);if(fs.length){lt=n;lp=fs[0];break;}}ok((tt>K&&lt===Infinity)||(tt===lt&&p===lp),"literal parity gcd");literal++;}
      if(tt>K)break;
      let r=least(C), w=tt-t;ok(r>0&&r<=p&&w<=2*r&&C<=2*t,"clock invariant");
      events++;R+=r;elapsed+=w;add(Wall,C);
      let idx=a.length, prev=last.get(p), count=(counts.get(p)||0)+1;counts.set(p,count);
      if(prev!==undefined && p>=Q){
        let E=C-a[prev].C-(p-1), max=-1, j=-1;
        for(let i=prev+1;i<idx;i++)if(a[i].p-1>max){max=a[i].p-1;j=i;}
        if(j>=0&&E-max<=J){
          let q=a[j].p, e2=C-(a[j].C+q-1), e1=E-max-e2;
          ok(q!==p&&e1>=0&&e2>=0&&e1%2===0&&e2%2===0,"light gain");
          ok(mod(q-(2-e1-e2+a[prev].sg-sg),p)===0,"return congruence");
          ok(mod(C+1-e2+a[j].sg,q)===0&&bad.has(C),"return CRT coverage");
          light++;lightCost+=r;
        }
      }
      if(count<=k)base+=r;
      else if(bad.has(C))deleted+=r;
      else if(p<Q){small+=r;smallCounts.set(p,(smallCounts.get(p)||0)+1);}
      else {high+=r;add(W,C);if(C-(2*M-2)>T)add(Wlate,C);}
      last.set(p,idx);a.push({C,p,sg});t=tt;C+=p-1;ok(C<=2*t,"post invariant");
    }
    for(const n of smallCounts.values())Z+=n*n;
    for(const n of counts.values())maxCount=Math.max(maxCount,n);
    if(spf[C-1]!==C-1||spf[C+1]!==C+1){nontwin++;ok(K-(M+2)<=2*a.reduce((s,x)=>s+least(x.C),0)+2*B,"no twin clock");}
  }
  ok(R===base+deleted+small+high,"disjoint R");ok(deleted<=N*Sbad&&lightCost<=N*Sbad,"bad weight");ok(base<=N*k*ps.reduce((s,p)=>s+p,0),"baseline");
  let P2=ps.filter(p=>p<Q).reduce((s,p)=>s+p*p,0);
  ok(BigInt(small)**2n<=BigInt(N)*BigInt(P2)*BigInt(Z),"small Cauchy");
  const energy=m=>{let e=0n;for(const [C,n] of m)e+=BigInt(least(C))*BigInt(n)**2n;return e;};
  let e=energy(W),el=energy(Wlate),ea=energy(Wall);
  ok(BigInt(high)**2n<=BigInt(S0)*e&&e<=ea&&el<=e,"energy");
  return {X,B,Q,J,k,N,events,literal,nontwin,R,base,deleted,small,high,Z,P2,light,lightCost,Sbad,badHorizons:bad.size,E:e.toString(),Elate:el.toString(),Eall:ea.toString(),maxCount,H,S0};
}
const xs=process.argv.slice(2).map(Number); const windows=xs.length?xs:[256,1024,4096,16384,65536,262144]; for(const X of windows) console.log(JSON.stringify({mode:'asymptotic',...audit(X)})); for(const X of windows) console.log(JSON.stringify({mode:'diagnostic',...audit(X,true)}));
