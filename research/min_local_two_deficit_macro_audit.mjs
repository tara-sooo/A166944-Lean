// Two-deficit short-clock macro audit; standard integer MIN, no asymptotic claim.
function audit(limit=1000000){
 const a=new Uint32Array(2*limit+3);
 for(let p=3;p*p<a.length;p+=2)if(!a[p])for(let n=p*p;n<a.length;n+=2*p)if(!a[n])a[n]=p;
 function factors(n){let f=[];while(n>1){let p=a[n]||n;f.push(p);n/=p}return f}
 const mod=(a,b)=>(a%b+b)%b;
 const gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return Math.abs(a)};
 function ck(x,m){if(!x)throw Error(m)}
 function ev(u,v){let fm=factors(u-1),fp=factors(u+1),p=Infinity,w=Infinity,e=0;
   for(let [f,s] of [[fm,1],[fp,-1]])for(let q of f){
    let z=mod((s===1?0:q+2)-v,2*q)||2*q;
    if(z<w||z===w&&q<p){w=z;p=q;e=s}
   }return {p,w,e,dm:2*v+2*w-u-p+1,twin:fm.length===1&&fp.length===1,fm,fp}
 }
 let exceptions=new Set(),literalTicks=0;
 function macro(u,d){
  let v=(u+d)/2,z=ev(u,v),{p,w,e,dm,twin}=z;
  if(p<13||dm!==(e===1?0:6))return null;
  ck(u%6===0&&(d===0||d===6),"macro domain");
  ck(u%4===mod(p-1,4),"orientation source class");
  ck(2*w===p-1+dm-d,"short clock");
  ck((u-e)/p%4===(e===1?3:1),"short cofactor class");
  if(!twin){if(p>=37)ck(p*p<=3*(u+1),"cap");else if(p*p>3*(u+1))exceptions.add(JSON.stringify({u,d,p,w,e}))}
  let U=u+p-1,V=v+w,relay=[],E=0;
  if(p%6===5){
    ck(U%12===4,"relay entry");
    let d0=2*V-U;
    let expected=d0===6?[[3,1]]:((U-1)%5===0?[[5,2],[3,1],[3,1]]:[[3,4]]);
    for(let [r,s] of expected){let j=ev(U,V);ck(j.p===r&&j.w===s,"relay mismatch "+U+" "+V);relay.push([r,s]);U+=r-1;V+=s;E+=r-1}
  }
  ck(U%6===0&&(2*V-U===0||2*V-U===6),"return");
  ck(E===0||E===2||E===8,"relay gain");
  return {...z,u,d,U,D:2*V-U,E,relay};
 }
 let controls=0,macroCount=0,nonTwin=0,near=0,nearPairs=0,allPairs=0,repeat=0,relayCounts={},orientCounts={},pCapMax={ratio:0},exampleRelay={},examplePair=null,nearExamples=[],roughChecks=0,localDensityChecks=0,resetRoots=0,rootMacro=0,rootNear=0,rootNearPair=0,rootNearPairNonTwin=0;
 const eta=.25;
 for(let u=12;u<=limit;u+=6)for(let d of [0,6]){
   let z=macro(u,d);controls++;
   if(d===6)resetRoots++;
   if(!z)continue;
   macroCount++;if(d===6)rootMacro++;
   if(u<3000){let v=(u+d)/2;for(let t=1;t<=z.w;t++){let n=v+t,g=gcd(n%2?n-2:n,n%2?u+1:u-1);ck(t===z.w?(a[g]||g)===z.p:g===1,"literal");literalTicks++}}
   if(z.twin)continue;
   nonTwin++;let key=z.p%12+":"+z.e+":"+d+":"+z.E;
   orientCounts[key]=(orientCounts[key]||0)+1;
   relayCounts[z.E]=(relayCounts[z.E]||0)+1;
   if(z.E&&!exampleRelay[z.E])exampleRelay[z.E]={u,d,p:z.p,w:z.w,e:z.e,relay:z.relay,U:z.U,D:z.D};
   let ratio=z.p/Math.sqrt(u+1);if(ratio>pCapMax.ratio)pCapMax={u,d,p:z.p,e:z.e,ratio};
   let high=z.p>=eta*Math.sqrt(u);if(high){near++;if(d===6)rootNear++}
   if(z.U>limit)continue;
   let y=macro(z.U,z.D);
   if(!y)continue;
   allPairs++;ck(z.p!==y.p,"adjacent repeat");
   let highPair=high&&y.p>=eta*Math.sqrt(u);
   if(highPair&&d===6){rootNearPair++;if(!y.twin)rootNearPairNonTwin++}
   if(y.twin)continue;
   let m=(u-z.e)/z.p,n=(y.u-y.e)/y.p,b=z.E+z.e-1-y.e;
   ck(y.p*n===z.p*(m+1)+b,"pair product");ck(b!==0&&Math.abs(b)<z.p,"nonzero");
   if(!examplePair)examplePair={u,d,p:z.p,m,e:z.e,E:z.E,r:y.p,n,f:y.e};
   if(highPair){
     nearPairs++;
     if(nearExamples.length<8)nearExamples.push({u,d,p:z.p,m,e:z.e,E:z.E,r:y.p,n,f:y.e});
     for(let l of [5,7,11,13,17,19,23,29,31]){
       if(2*l>=Math.min(z.w,y.w)||l>=Math.min(z.p,y.p))continue;
       ck(y.p%l!==0&&n%l!==0,"axes");
       for(let c of [z.p+b,z.p+b-2*z.e,-2*y.e])ck(mod(y.p*n-c,l)!==0,"rough form");
       roughChecks++;
     }
   }
   let q=macro(y.U,y.D);if(q&&q.p===z.p){
     repeat++;let drift=q.u-u;ck(drift%12===0&&mod(drift,z.p)===mod(q.e-z.e,z.p),"repeat congruence");
   }
 }
 for(let l of [5,7,11,13,17,19,23,29,31])for(let p of [37,61,97,109,157])for(let e of [-1,1])for(let f of [-1,1])for(let E of [0,2,8]){
   if(p===l)continue;let b=E+e-1-f,c=[p+b,p+b-2*e,-2*f];
   let nz=new Set(c.map(x=>mod(x,l)).filter(x=>x!==0)).size;
   let rho=0;for(let r=0;r<l;r++)for(let n=0;n<l;n++)if(!r||!n||c.some(x=>mod(r*n-x,l)===0))rho++;
   ck(rho===2*l-1+nz*(l-1),"local density");localDensityChecks++;
 }
 return {limit,controls,macroCount,nonTwin,near,nearPairs,allPairs,repeat,relayCounts,pCapMax,exampleRelay,examplePair,nearExamples,roughChecks,localDensityChecks,resetRoots,rootMacro,rootNear,rootNearPair,rootNearPairNonTwin,orientCounts,literalTicks,exceptions:[...exceptions].map(JSON.parse)}
}
console.log(JSON.stringify(audit(Number(process.argv[2]||1000000)),null,2));
