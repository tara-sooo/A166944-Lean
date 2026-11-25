// Exact local clock phase counts, maximum waits and factor-gap obstruction.
function audit(Hmax=2000){
 const mod=(a,b)=>(a%b+b)%b;
 function fac(n){let fs=[];for(let d=3;d*d<=n;d+=2)if(n%d===0){fs.push(d);while(n%d===0)n/=d}if(n>1)fs.push(n);return fs}
 function gcd(a,b){while(b)[a,b]=[b,a%b];return a}
 function next(t,H){let best=null;for(let e of [1,-1])for(let p of fac(H-e)){if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}return best}
 let s={Hmax,plateaus:0,labels:0,waitTests:0,possible:0,impossible:0,phaseChecks:0,crtExamples:0,exactMaxChecks:0,localResidueChecks:0,literalTicks:0,nearFactorChecks:0,nearFactorBlocked:0,nearFactorAllowed:0,maxPeriod:0,example:null,nearExample:null,largeExample:null};
 for(let H=8;H<=Hmax;H+=2){
  let clocks=[1,-1].flatMap(e=>fac(H-e).filter(p=>p*p<=H+1).map(p=>({p,e})));
  if(!clocks.length)continue;s.plateaus++;
  for(let {p,e} of clocks){
   s.labels++;let I=(1-e)/2,q=(H-e)/p,h0=mod(I-(q+1)/2,2),n0=p*((q+1)/2+h0)+2*I;
   let others=clocks.filter(v=>v.p!==p),P=others.reduce((a,v)=>a*v.p,1);
   // The small finite plateau bound keeps all n in the exact Number range.
   if(!Number.isSafeInteger(n0+2*p*P))throw Error("range");
   s.maxPeriod=Math.max(s.maxPeriod,P);
   let maxW=Math.min(2*p,...others.map(v=>v.e===e?(v.p<p?2*v.p-2:2*v.p):2*v.p-1));
   let observed=0;
   for(let w=1;w<=2*p;w++){
    let expected=1,allow=[];
    for(let {p:f,e:ef} of others){
     let count=0,first=-1;
     let bad=ef===e?Math.floor((w-1)/2)+(f<p?1:0):Math.floor(w/2);
     let target=Math.max(0,f-bad);
     for(let j=0;j<f;j++){
      let n=n0+2*p*j,lag=mod(n-(ef===1?0:f+2),2*f);
      let ok=lag===0?f>p&&w<=2*f:lag>=w;
      if(ef!==e&&lag===0)throw Error("parity");
      if(ok){count++;if(first<0)first=j;}
      s.localResidueChecks++;
     }
     if(count!==target)throw Error("factor count");
     expected*=target;allow.push({f,first});
    }
    if((expected>0)!==(w<=maxW))throw Error("max");
    let actual=0,first=-1;
    for(let j=0;j<P;j++){
     let n=n0+2*p*j;
     // Shift by a complete phase period to keep the envelope, without altering clocks.
     if(n-w<H/2)n+=2*p*P*Math.ceil((H/2+w-n)/(2*p*P));
     let r=next(n-w,H),ok=r?.p===p&&r.e===e&&r.w===w;
     if(ok){actual++;if(first<0)first=n;observed=Math.max(observed,w)}
     s.phaseChecks++;
    }
    if(actual!==expected)throw Error("product");
    s.waitTests++;if(expected){s.possible++;
     let j=0,m=1;for(let {f,first} of allow){while(j%f!==first)j+=m;m*=f}
     let n=n0+2*p*j;if(n-w<H/2)n+=2*p*P*Math.ceil((H/2+w-n)/(2*p*P));
     let r=next(n-w,H);if(r?.p!==p||r.e!==e||r.w!==w)throw Error("crt");
     s.crtExamples++;
     if(s.crtExamples<=2000){for(let i=1;i<=w;i++){let z=n-w+i,ee=z%2?-1:1,g=gcd(ee===1?z:z-2,H-ee),f=g===1?0:fac(g)[0],active=f&&f*f<=H+1;if(i<w&&active||i===w&&(!active||f!==p))throw Error("literal");s.literalTicks++}}
     if(others.length>=2&&w===maxW&&!s.example)s.example={H,p,e,w,period:P,count:expected,n,t:n-w,others};
    }else s.impossible++;
   }
   if(observed!==maxW)throw Error("observed max");s.exactMaxChecks++;
   // Verify the exact congruence and small-gap obstruction for post-phase h.
   for(let j=0;j<12;j++){
    let h=h0+2*j,n=n0+2*p*j;
    for(let {p:f,e:ef} of others){
     let lag=mod(n-(ef===1?0:f+2),2*f),v=(2*h+1)*p-(ef===e?0:6*e);
     if(mod(2*lag-v,f)!==0||2*lag%4!==(ef===e?0:2))throw Error("lag");
     if(f<p&&f%4===p%4){let gap=p-f,z=(2*h+1)*gap-(ef===e?0:6*e);
      if(z>0&&z<4*f){if(2*lag!==z)throw Error("near factor");s.nearFactorChecks++;
       let w=Math.ceil((p-1)/4);if(z<2*w){s.nearFactorBlocked++;if(!s.nearExample)s.nearExample={H,p,e,f,ef,h,gap,lag,w}}else s.nearFactorAllowed++;
      }
     }
    }
   }
  }
 }
 // Large previously verified all-distinct type III plateau. Test all phases
 // for each eligible rival separately and construct a simultaneous CRT phase.
 let H=125876515620,p=5003,e=-1,w=1251,I=1,q=(H-e)/p,h0=mod(I-(q+1)/2,2),n0=p*((q+1)/2+h0)+2*I,others=[1,-1].flatMap(ef=>fac(H-ef).filter(f=>f!==p&&f*f<=H+1).map(f=>({f,ef})));
 let j=0n,M=1n,counts=[];
 for(let {f,ef} of others){let count=0,first=-1;
  for(let k=0;k<f;k++){let n=n0+2*p*k,lag=mod(n-(ef===1?0:f+2),2*f),ok=lag===0?f>p&&w<=2*f:lag>=w;if(ok){count++;if(first<0)first=k}}
  let target=Math.max(0,f-(ef===e?Math.floor((w-1)/2)+(f<p?1:0):Math.floor(w/2)));
  if(count!==target||first<0)throw Error("large phase");
  let F=BigInt(f);while(j%F!==BigInt(first))j+=M;M*=F;counts.push({f,ef,count});
 }
 let period=2n*BigInt(p)*M,n=BigInt(n0)+2n*BigInt(p)*j,min=BigInt(H/2+w);if(n<min)n+=period*((min-n+period-1n)/period);
 let t=n-BigInt(w);
 for(let i=1;i<=w;i++){let z=t+BigInt(i),ee=z%2n?-1:1,A=ee===1?z:z-2n,B=BigInt(H-ee);while(B)[A,B]=[B,A%B];let f=A===1n?0:fac(Number(A))[0],active=f&&f*f<=H+1;if(i<w&&active||i===w&&(!active||f!==p))throw Error("large literal");s.literalTicks++}
 s.largeExample={H,p,e,w,counts,phasePeriod:M.toString(),allowedPhases:counts.reduce((a,v)=>a*BigInt(v.count),1n).toString(),n:n.toString(),t:t.toString()};
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||2000)),null,2));
