// Prime-root subset of canonical MIN full-horizon energy.
// Run: node research/min_prime_root_energy_audit.mjs 256 1024 4096 16384 65536 262144
function audit(X){
  const B=Math.ceil(Math.sqrt(7*X)), T=Math.floor(B*Math.pow(Math.log(B),1.5));
  const spf=new Int32Array(7*X+4);
  for(let p=2;p<spf.length;p++)if(!spf[p]){
    spf[p]=p;if(p*p<spf.length)for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
  }
  const check=(v,m)=>{if(!v)throw Error(m)};
  const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a};
  function hit(t,C,K){
    let T=K+1,P=0;
    for(const s of [-1,1]){
      let v=C+s;
      while(v>1){let p=spf[v];if(p>B)break;
        const m=2*p,r=s===-1?0:p+2,u=t+1+(r-(t+1)%m+m)%m;
        if(p>2&&(u<T||(u===T&&u<=K&&p<P))){T=u;P=p;}
        while(v%p===0)v/=p;
      }
    }
    return [T,P];
  }
  const Q=Math.ceil(B/Math.pow(Math.log(B),1/8)), y=Math.ceil(Math.sqrt(B));
  const verts=new Map(), totalCost=new Map();
  const key=(t,C)=>t*(7*X+4)+C;
  const vertex=(t,C)=>{const k=key(t,C);if(!verts.has(k))verts.set(k,{t,C,edges:new Map(),root:0,r:0,p:0});return verts.get(k)};
  const len=7*X/2+1, W=new Int32Array(len), WP=new Int32Array(len),
        WL=new Int32Array(len), WB=new Int32Array(len);
  let roots=0,all=0,primeEvents=0,bad=0,primeBad=0,travel=0,primeElapsed=0,
      literal=0,rootChecks=0,largestGain=0;
  for(let M=X+1;M<2*X;M+=2){
    let prime=spf[M]===M,t=M+2,C=2*M-2,K=Math.floor((7*M-1)/4);
    let cost=0;
    if(prime){roots++;travel+=K-t;check(M>B,'prime root above B');vertex(t,C).root=M;}
    for(;;){
      const [u,p]=hit(t,C,K);
      if(X<=1024){
        let a=K+1,b=0;
        for(let j=t+1;j<=K;j++){
          let g=gcd(j%2?j-2:j,j%2?C+1:C-1);
          if(g>1&&spf[g]<=B){a=j;b=spf[g];break}
        }
        check(a===u&&b===p,'literal MIN');literal++;
      }
      if(!p){
        if(spf[C-1]!==C-1||spf[C+1]!==C+1){
          bad++;if(prime)primeBad++;
          check(K-t<2*B,'terminal quiet bound');
        }
        if(prime){largestGain=Math.max(largestGain,C-(2*M-2));totalCost.set(M,cost);}
        break;
      }
      const r=Math.min(spf[C-1],spf[C+1]);
      check(u-t<=2*r,'wait bound');
      W[C/2]++;all++;
      if(prime){WP[C/2]++;primeEvents++;primeElapsed+=u-t;
        if(C-(2*M-2)>T)WL[C/2]++;
        if(C-(2*M-2)>B)WB[C/2]++;
        cost+=r;const v=vertex(t,C);v.r=r;v.p=p;
        vertex(u,C+p-1).edges.set(key(t,C),{M,p,cost});
      }
      t=u;C+=p-1;
      check(C<=2*t,'horizon invariant');
      if(t%2===1&&C===2*t-6&&t-2>=X&&t-2<2*X){
        rootChecks++;check((t-2)%p===0&&spf[t-2]!==t-2,'no incoming prime root');
      }
    }
  }
  const pref=new Int32Array(2*X+1);
  for(let i=1;i<pref.length;i++)pref[i]=pref[i-1]+(i>=2&&spf[i]===i?1:0);
  function maxNear(T){
    let m=0;
    for(let C=2*X;C<7*X;C+=2){
      const hi=Math.min(2*X-1,Math.floor((C+2)/2));
      const lo=Math.max(X+1,Math.ceil((C+2-T)/2));
      if(lo<=hi)m=Math.max(m,pref[hi]-pref[lo-1]);
    }return m;
  }
  let R=0,E=0,RP=0,EP=0,EL=0,EB=0,S0=0,mass=0;
  // Exact integer BigInt cross-products, even for larger windows.
  for(let C=2*X;C<7*X;C+=2){
    let r=Math.min(spf[C-1],spf[C+1]),n=W[C/2],p=WP[C/2],l=WL[C/2],b=WB[C/2];
    if(r>B){check(n===0,'eligible');continue}
    S0+=r;R+=r*n;E+=r*n*n;RP+=r*p;EP+=r*p*p;EL+=r*l*l;EB+=r*b*b;mass=Math.max(mass,p);
  }
  let same=0,big=0,mixed=0,sameCost=0,bigCost=0,mixedCost=0,rootLineCost=0,rootLineDemotions=0,rep=0,repHigh=0;
  const demoted=new Set();
  function demote(v,e,kind){
    check(!demoted.has(e.M),'single demotion');demoted.add(e.M);
    const c=totalCost.get(e.M)-e.cost;check(c>=0,'suffix cost');
    if(kind==='same'){same++;sameCost+=c}
    else if(kind==='big'){big++;bigCost+=c}
    else{mixed++;mixedCost+=c}
    if(v.t%2===1&&v.C===2*v.t-6&&v.t-2>=X&&v.t-2<2*X){rootLineDemotions++;rootLineCost+=c}
  }
  for(const v of verts.values()){
    if(v.r){rep+=v.r;if(v.p>=y)repHigh+=v.r}
    check(!v.root||v.edges.size===0,'prime injected root no predecessors');
    const groups=new Map();
    for(const e of v.edges.values()){
      if(!groups.has(e.p))groups.set(e.p,[]);
      groups.get(e.p).push(e);
    }
    let winners=[];
    for(const a of groups.values()){
      a.sort((b,c)=>c.M-b.M);winners.push(a[0]);
      for(const e of a.slice(1))demote(v,e,'same');
    }
    const large=winners.filter(e=>e.p>=Q).sort((a,b)=>b.M-a.M);
    for(const e of large.slice(1))demote(v,e,'big');
    winners=winners.filter(e=>e.p<Q||e===large[0]).sort((a,b)=>b.M-a.M);
    for(const e of winners.slice(1))demote(v,e,'mixed');
  }
  check(rep+sameCost+bigCost+mixedCost===RP,'exact prime representative ledger');
  for(const n of [R,E,RP,EP,EL,EB,S0,travel,primeElapsed])check(Number.isSafeInteger(n),'integer overflow');
  const nearT=maxNear(T),nearB=maxNear(B);
  check(EP-EL<=2*nearT*RP,'prime late split T');
  check(EP-EB<=2*nearB*RP,'prime late split B');
  check(BigInt(RP)**2n<=BigInt(S0)*BigInt(EP),'Cauchy');
  check(primeElapsed<=2*RP,'elapsed');
  const H2=travel-2*B*roots;
  if(H2>0&&4n*BigInt(S0)*BigInt(EP)<BigInt(H2)**2n)check(primeBad<roots,'finite energy cert');
  return {X,B,T,Q,y,roots,same,big,mixed,rep,repHigh,sameCost,bigCost,mixedCost,rootLineDemotions,rootLineCost,all,primeEvents,rootChecks,literal,bad,primeBad,travel,RP,EP,EL,EB,nearT,nearB,S0,largestGain,mass,R,E,energyRatio:EP/(X*X*B),cert:H2>0&&4n*BigInt(S0)*BigInt(EP)<BigInt(H2)**2n};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[256,1024,4096,16384,65536,262144])console.log(JSON.stringify(audit(X)));
