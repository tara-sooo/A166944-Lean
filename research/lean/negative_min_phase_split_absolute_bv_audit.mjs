// Exact log bounds and finite structural proxies; not an asymptotic proof.
function audit() {
  const assert=(b,msg)=>{if(!b)throw Error(msg)};
  const S=10n**22n;
  const ceil=(a,b)=>(a+b-1n)/b;
  function logI(n,d){
    if(n<d){const [l,h]=logI(d,n);return [-h,-l]}
    const a=n-d,b=n+d;let lo=0n,hi=0n;
    for(let j=0;j<70;j++){const k=BigInt(2*j+1),num=2n*S*a**k,den=k*b**k;lo+=num/den;hi+=ceil(num,den)}
    const k=141n;hi+=ceil(2n*S*a**k*b*b,k*b**k*(b*b-a*a));return [lo,hi]
  }
  function divI([l,h],n,d){const fl=(a,b)=>a>=0n?a/b:-ceil(-a,b);return [fl(l*d,n),-fl(-h*d,n)]}
  const scale=10000n,d=6246n,e=4990n,a=3000n,c=3128n,b=3130n;
  const F=x=>divI(logI(d-x,x),d,scale);
  const J=divI(logI(c*(e-a),a*(e-c)),2n*e,scale);
  const Fa=F(a),Fc=F(c),Fb=F(b);
  const margin=[Fa[0]-Fc[1]-J[1]+2n*Fb[0],Fa[1]-Fc[0]-J[0]+2n*Fb[1]];
  assert(margin[0]>846n*S/100000n,"positive margin > .00846");
  assert(margin[0]-2n*S/1000n-4n*S/5000n-S/2000n>4n*S/1000n,"high population > .004");
  assert(2n*a>e && e>c && c<b && b<3749n,"exponent conditions");
  assert((d-a)+6n<3n*a,"variable cutoff below a");
  const details=[];let totalTicks=0,phaseCases=0,highCases=0,exactCases=0,crtCases=0;
  function spf(N){let f=new Int32Array(N+1);for(let p=2;p<=N;p++)if(!f[p]){f[p]=p;if(p*p<=N)for(let n=p*p;n<=N;n+=p)if(!f[n])f[n]=p}return f}
  const mod=(a,b)=>((a%b)+b)%b;
  for(const R of [100000,400000,1000000]){
    const f=spf(2*R+3),factors=n=>{const r=[];while(n>1){const p=f[n];r.push(p);n/=p}return r};
    const A0=R**.16,A=R**.18,C=R**.27,B=R**.34;
    let all=0,sa0=0,sa=0,sc=0,sb=0,base=0,corr=0,reset=0,repeated=0,isolatedHigh=0,low=0,multi=0;
    for(let n=R+1;n<=2*R+1;n++){
      const p=f[n],v=n/p;
      if(p<R**.30||p>R**.44||v<=p||f[v]!==v)continue;
      all++;const fs=factors(n-2),r=fs[0],qs=[...new Set(fs)];if(r>=A0)sa0++;if(r>=A)sa++;if(r>=C)sc++;if(r>=B)sb++;
      for(const q of qs)if(q>=A0&&q<B){
        const cut=R**((.6246-Math.log(q)/Math.log(R))/3+.0002);
        if(r>=cut)base++;
        if(r>=cut&&r<q)corr++;
      }
      if(r<A||r>=C)continue;
      low++;const u=(n-2)/r;
      const resetPhase=u%4===3;
      assert(resetPhase===(mod(r*3+2,4)===n%4),"phase class");
      phaseCases++;
      if(resetPhase)reset++;
      const repeat=fs.some((q,i)=>i>0&&q===fs[i-1]&&q>=A);
      const otherLow=qs.some(q=>q!==r&&q<B);
      if(repeat)repeated++;
      if(otherLow)multi++;
      if(!repeat&&!otherLow&&!resetPhase){isolatedHigh++;highCases++}
      if(repeat||otherLow)continue;
      const root=n-1; if(root%6!==0)continue;
      const other=Math.min(p,...fs.slice(1));
      if(other<=3*r+7)continue;
      const wait=resetPhase?(r-1)/2:(3*r-1)/2;
      let winner=0, t=0;
      for(t=1;t<=wait;t++){
        const clock=3-root/2+t,plus=clock%2===0;
        for(const l of factors(root+(plus?1:-1))){
          if(l===2)continue;
          if(mod(clock,2*l)===(plus?0:l+2)){winner=l;break}
        }
        totalTicks++;
        if(winner)break;
      }
      assert(t===wait&&winner===r,"literal isolated first winner");
      assert(3+t-(r-1)/2===(resetPhase?3:r+3),"postheight");
      exactCases++;
    }
    assert(sa0-base+corr===sb,"variable Buchstab identity");
    assert(sa-sc===low,"partition");
    assert(isolatedHigh>=sa-sc-reset-corr-repeated,"counting lower");
    assert(multi<=corr,"multiple low primes charged");
    // Independent small-grid check of the correction for induced characters:
    // when the source prime band starts at P and d<P^2, d contains at most one such prime.
    for(let k=3;k<Math.min(15000,R**.499);k+=2){
      const fac=[...new Set(factors(k))].filter(p=>p>=R**.30);
      assert(fac.length<=1,"at most one excluded large source prime");crtCases++;
    }
    details.push({R,source:all,sa0,sa,sc,sb,base,corr,reset,repeated,multi,isolatedHigh});
  }
  assert(highCases>0&&exactCases>0&&totalTicks>0,"nonvacuous finite checks");
  return {marginScaled:margin.map(String),scale:String(S),phaseCases,highCases,exactCases,totalTicks,crtCases,details};
}
console.log(JSON.stringify(audit(),null,2));
