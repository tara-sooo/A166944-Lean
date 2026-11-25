// Literal per-tick all-odd canonical MIN audit. No external dependencies.
function audit(X, stress=false, full=false) {
  const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,u=Math.log(B),D=Math.max(1,Math.floor(B/u**2)),eps=stress?0.125:u**(-0.25),zeta=stress?0.5:u**(-0.125),limit=H+2*B,stride=16*X+100;
  const assert=(x,msg)=>{if(!x)throw Error(msg)};
  const close=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b));
  const spf=new Int32Array(8*X+100);
  for(let i=2;i<spf.length;i++)if(!spf[i])for(let j=i;j<spf.length;j+=i)if(!spf[j])spf[j]=i;
  function gcd(a,b){while(b){let c=a%b;a=b;b=c}return a}
  function eligible(C){let p=Math.min(spf[C-1]||Infinity,spf[C+1]||Infinity);return p<=B?p:0}
  const counts=new Map(), groups=new Map(); let unstable=0,growth=0,referenceCost=0,activeTicks=0,maskedTicks=0,rawTicks=0,rootChecks=0;
  const paths=[];
  for(let M=2*X-1;M>=X;M-=2){
    const s=M+2,K=Math.floor((7*M-1)/4),cap=Math.min(limit,K-s);
    assert(H<=cap,"original cutoff gate");
    let C=2*M-2,t=0,trace=[],records=[];
    while(t<cap){
      let r=eligible(C);if(!r)break;
      let lo=t,p=0;
      while(t<cap){
        trace.push(C);
        t++;
        let n=s+t,par=n%2,g=gcd(n-2*par,C+2*par-1);
        p=spf[g]||0;if(p>B)p=0;
        if(p)break;
      }
      assert(t-lo<=2*r,"clock wait bound");
      records.push({C,r,lo,hi:t,p});
      if(p){C+=p-1;assert(C<=2*(s+t),"invariant")}
    }
    const n=new Int32Array(trace.length),stable=new Uint8Array(trace.length);
    for(let i=0;i<trace.length;i++){
      const key=(s+i)*stride+trace[i]; n[i]=1+(counts.get(key)||0);
      assert(i===0?n[i]===1:n[i]>=n[i-1],"ordered persistence");
      counts.set(key,n[i]); 
    }
    let localBad=0;
    for(let i=0;i<trace.length;i++){
      const old=i>=D?n[i-D]:1;
      stable[i]=Math.log(n[i]/old)<=eps+1e-12?1:0;
      localBad+=1-stable[i];
    }
    const g=trace.length?Math.log(n[trace.length-1]):0;
    assert(localBad<=D*g/eps+1e-7,"Fubini budget");
    unstable+=localBad;growth+=g;activeTicks+=trace.length;rootChecks++;
    const path={M,s,trace,n,stable}; paths.push(path);
    for(const rec of records){
      const {C,r,lo,hi,p}=rec; let group=groups.get(C);
      if(!group){group={r,A:0,entries:[]};groups.set(C,group)}
      group.A++;referenceCost+=r;
      let low,high;
      if(full){if(!(lo<H&&p&&2*(hi-lo)>p-1))continue;low=lo;high=hi;}
      else{if(!(p>Math.ceil(B**.25)))continue;low=Math.max(a,lo);high=Math.min(H,hi);}
      if(low>=high)continue;
      const raw=high-low;rawTicks+=raw; const kept=[];
      for(let i=low;i<high;i++){
        if(stress&&(M+i)%7===0){maskedTicks++;continue}
        if(stable[i])kept.push(i);
      }
      if(kept.length)group.entries.push({path,lo,hi,kept,w:kept.length/(2*r)});
    }
  }
  let E=0,diag=0,recent=0,old=0,notYet=0,gateTicks=0,keptTicks=0,preGateTicks=0,keptGroups=0,pairCount=0,oracleChecks=0,olderPairs=0;
  const beta=2*(1-Math.exp(-eps))/zeta;
  for(const [C,g] of groups){
    let {r,A,entries}=g,U=entries.reduce((v,e)=>v+e.w,0);
    preGateTicks+=Math.round(2*r*U);
    if(U<zeta*A){gateTicks+=Math.round(2*r*U);continue}
    if(!entries.length)continue;
    keptGroups++; keptTicks+=Math.round(2*r*U);E+=r*U*U;
    let localRecent=0,localOld=0,localNot=0,localDiag=0;
    for(let i=0;i<entries.length;i++){
      const b=entries[i];localDiag+=r*b.w*b.w;
      for(let j=i+1;j<entries.length;j++){
        const f=entries[j]; // larger M was inserted first
        assert(f.path.M<b.path.M,"ordered roots");
        pairCount++;
        const P=f.path,Q=b.path;
        const left=Math.max(P.s+f.lo,Q.s+b.lo),right=Math.min(P.s+f.hi,Q.s+b.hi);
        let meet=Infinity;
        const equal=t=>t>=P.s&&t>=Q.s&&t-P.s<P.trace.length&&t-Q.s<Q.trace.length&&P.trace[t-P.s]===Q.trace[t-Q.s];
        if(left<right){
          assert(equal(left),"overlap is physical meeting");
          let l=Q.s,h=left;
          while(l<h){const m=Math.floor((l+h)/2);if(equal(m))h=m;else l=m+1}
          meet=l;
          if(X<=1024||oracleChecks<64){
            let first=Q.s;while(first<left&&!equal(first))first++;
            assert(first===meet,"independent first meeting");oracleChecks++;
          }
        }
        for(const tick of f.kept){
          const t=P.s+tick;
          if(t<meet||!equal(t)){localNot+=b.w;continue}
          if(t-D<meet){localRecent+=b.w;assert(P.stable[tick],"recent focal stable")}
          else{localOld+=b.w;olderPairs++;assert(equal(t-D),"old common tick")}
        }
      }
    }
    assert(close(r*U*U,localDiag+localRecent+localOld+localNot),"energy partition");
    assert(localRecent<=beta*r*U*U+1e-6,"relative bound per horizon");
    diag+=localDiag;recent+=localRecent;old+=localOld;notYet+=localNot;
  }
  assert(gateTicks<=2*zeta*referenceCost+1e-6,"density loss bound");
  assert(rawTicks-preGateTicks<=unstable+maskedTicks,"unstable/holes budget");
  assert(close(E,diag+recent+old+notYet),"global energy partition");
  assert(recent<=beta*E+1e-6,"global relative bound");
  assert(unstable<=D*growth/eps+1e-6,"global Fubini");
  return {X,B,N,D,eps,zeta,beta,stress,full,rootChecks,activeTicks,growth,unstable,referenceCost,rawTicks,maskedTicks,preGateTicks,gateTicks,keptTicks,keptGroups,E,diag,recent,old,notYet,pairCount,oracleChecks,olderPairs};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384]))for(const full of [false,true])for(const stress of [false,true])console.log(JSON.stringify(audit(X,stress,full)));
