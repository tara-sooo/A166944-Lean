// Exact CRT lift of restricted-clock paths under one-prime alphabet extensions.
function audit(){
 const mod=(x,m)=>(x%m+m)%m,ck=(v,m)=>{if(!v)throw Error(m)};
 function next(u,v,A){let p=Infinity,w=Infinity,e=0;for(let r of A){let s=mod(u,r)===1?1:mod(u,r)===r-1?-1:0;if(!s)continue;let z=mod((s===1?0:r+2)-v,2*r)||2*r;if(z<w||z===w&&r<p){p=r;w=z;e=s}}return {p,w,e}}
 function gcd(a,b){while(b){let z=a%b;a=b;b=z}return Math.abs(a)}
 function walk(x,v,A){let a=[],u=x,t=v;for(;;){let z=next(u,t,A);if(!isFinite(z.p))return {a,u,t,G:u-x};a.push({u,t,...z});u+=z.p-1;t+=z.w;ck(a.length<200000,"termination")}}
 let rows=[];
 for(let [A,p] of [[[3],5],[[3,5],7],[[3,5,7],11],[[3,5,7,11],13],[[3,5,7,11,13],17],[[3,5],101],[[3,5,7],293],[[3,5,7,11],907]]){
  let Q=2*A.reduce((a,b)=>a*b,1),P=2*Q,base=P*p,N=P/6,F=new Int32Array(Q+2);
  for(let u=Q-2;u>=0;u-=2)for(let r of A)if(mod(u,r)===1||mod(u,r)===r-1){ck(u+r-1<=Q,"wall");F[u]=Math.max(F[u],r-1+F[u+r-1])}
  let L=Math.max(...F),s={A,p,Q,L,baseRoots:N,liftRoots:N*p,baseGain:0,newGain:0,baseGain2:0,preemptUpper:0,changed:0,preempt:0,terminalOnly:0,negative:0,maxNewP:0,repeatChecks:0,unionChecks:0,literalTicks:0,dirtyRoots:0,lossCharge:0,actualLossCharge:0,firstOnly:0,exampleNegative:null,examplePreempt:null,exclusiveRootCount:0};
  let sparse=p>6*L+5;
  for(let X=base;X<base+P;X+=6){
   let old=walk(X,X/2+3,A),G=old.G,W=old.t-(X/2+3);s.baseGain+=G;s.baseGain2+=G*G;
   ck(G<=L&&W<=3*G,"old gain");let susceptible=old.a.filter(z=>p+1<=2*z.t-z.u+2*z.w).length; // strict preemption requires p+1 <= d+2w_low
   s.preemptUpper+=2*susceptible;if(susceptible)s.dirtyRoots++;
   let predicted=new Set(),predPre=new Set(),eligible=new Map();
   // Enumerate exact residue classes by translating the original restricted prefix.
   // The p-adic class is fixed by each source/side, even when the phase changes.
   let inv=0;for(let k=1;k<p;k++)if(mod(2*Q*k,p)===1){inv=k;break}ck(inv>0,"inverse");
   function test(u,v,w,isEnd){
    for(let e of [1,-1]){
     let k=mod((e-u)*inv,p),U=u+P*k,V=v+Q*k,z=next(U,V,[p]);ck(z.e===e,"CRT eligibility");
     if(isEnd||z.w<w){predicted.add(k);if(!isEnd){predPre.add(k);if(!eligible.has(k))eligible.set(k,{u:U,v:V,w:z.w});}}
    }
   }
   for(let z of old.a)test(z.u,z.t,z.w,false);test(old.u,old.t,Infinity,true);
   ck(predicted.size>=2&&predPre.size<=2*susceptible,"union bounds");
   if(sparse)ck(predicted.size===2&&predPre.size===0,"sparse prediction");
   for(let k=0;k<p;k++){
    let x=X+P*k,v=x/2+3,nu=walk(x,v,A.concat(p)),hits=nu.a.filter(z=>z.p===p),G1=nu.G;
    s.newGain+=G1;ck((hits.length>0)===predicted.has(k),"changed exact");s.unionChecks++;
    if(!hits.length){ck(G1===G,"unchanged");continue}
    s.changed++;s.maxNewP=Math.max(s.maxNewP,hits.length);
    const f=hits[0],isPre=f.u!==old.u+P*k;
    // An old path could include a later offset equal to old terminal only there.
    ck(isPre===predPre.has(k),"preemption exact");
    if(isPre){s.preempt++;s.actualLossCharge+=G;if(!s.examplePreempt)s.examplePreempt={x,p,oldEnd:old.u+P*k,newEnd:nu.u,first:f};ck(G>=(p-5)/6,"preempt gain threshold");}
    else {s.terminalOnly++;ck(G1>=G+p-1,"terminal extension");}
    if(G1<G){s.negative++;ck(isPre,"negative only preempt");if(!s.exampleNegative)s.exampleNegative={x,p,old:old.a.map(z=>[z.u+P*k,z.p,z.w]),new:nu.a.map(z=>[z.u,z.p,z.w]),oldEnd:old.u+P*k,newEnd:nu.u};}
    for(let i=1;i<hits.length;i++){let E=hits[i].u-(hits[i-1].u+p-1);ck(E>=p-1&&E<=L,"repeat relay");s.repeatChecks++}
    if(sparse)ck(hits.length===1&&G1-G>=p-1&&G1-G<=p-1+L,"sparse increment");
    if(X<base+18&&k<5){for(let z of nu.a)for(let j=1;j<=z.w;j++){let n=z.t+j,g=gcd(n%2?n-2:n,n%2?z.u+1:z.u-1),q=A.concat(p).find(q=>g%q===0);ck(j===z.w?q===z.p:q===undefined,"literal");s.literalTicks++}}
   }
   s.lossCharge+=G*2*susceptible;
  }
  ck(s.changed>=2*N&&s.preempt<=s.preemptUpper,"population");
  ck(s.newGain-p*s.baseGain>=2*N*(p-1)-s.actualLossCharge,"mean lower");
  if(sparse)ck(s.changed===2*N&&s.newGain-p*s.baseGain<=2*N*(p-1+L),"sparse mean upper");
  s.sparse=sparse;s.meanBase=s.baseGain/N;s.meanNew=s.newGain/(N*p);s.meanDelta=s.meanNew-s.meanBase;rows.push(s)
 }
 return rows;
}
console.log(JSON.stringify(audit(),null,2));
