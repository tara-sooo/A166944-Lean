// Restricted low-alphabet maximum net-credit capacity, exact phase averages and finite diagnostics.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p;
 const N=2000000,sp=new Uint8Array(N+1),pr=[];for(let p=2;p*p<=N;p++)if(!sp[p])for(let x=p*p;x<=N;x+=p)sp[x]=1;for(let p=3;p<=N;p+=2)if(!sp[p])pr.push(p);
 let out={periodStates:0,periodTransitionChecks:0,periodDirectChecks:0,phaseSamples:0,sampleEvents:0,sampleTruncated:0,capacityPrimeChecks:0,exact:[],sample:[]};
 // Exact distribution of the least neighbor prime conditional on
 // a pin p|a+-1, with other prime coordinates unrestricted.
 let prob=[],C0=[0],C1=[0],V=1,highSum=[0],inv2=[0],cut=0;
 for(let [i,p] of pr.entries()){
  while(cut<i&&8*pr[cut]<=p-1)cut++;
  let h=(8*(C1[i]-C1[cut])-(p-1)*(C0[i]-C0[cut]))+(7*p+1)*V;
  ck(h>=0&&h<=7*p+1+1e-9,"credit cap");
  if(i<30){let e=0;for(let j=0;j<i;j++)e+=Math.max(0,8*pr[j]-p+1)*prob[j];e+=(7*p+1)*V;ck(Math.abs(e-h)<1e-10,"independent expectation");out.capacityPrimeChecks++}
  highSum.push(highSum.at(-1)+h/p**2);inv2.push(inv2.at(-1)+1/p**2);
  let u=2*V/p;prob.push(u);C0.push(C0.at(-1)+u);C1.push(C1.at(-1)+p*u);V*=1-2/p;
  ck(Math.abs(C0.at(-1)+V-1)<1e-10,"probability mass")
 }
 function tail(z){let i=pr.findIndex(p=>p>z);return {sumH:highSum.at(-1)-highSum[i],sumInv2:inv2.at(-1)-inv2[i]}}
 function next(a,n,P){let p0=0,w0=Infinity;
  for(let p of P)for(let e of [-1,1])if(mod(a-e,p)===0){let w=mod((e===-1?0:p+2)-n,2*p)||2*p;if(w<w0||w===w0&&p<p0){p0=p;w0=w}}
  return {p:p0,w:w0}
 }
 for(let z of [3,5,7,11]){
  let P=pr.filter(p=>p<=z),Q=P.reduce((a,b)=>a*b,1),C=2*Q,gs=new Int32Array(Q*C),bs=new Int32Array(Q*C),sumG=[0,0],sumB=[0,0],maxG=0,maxB=0;
  for(let i=0;i<Q;i++){
   let E=P.flatMap(p=>[-1,1].filter(e=>mod(2*i-e,p)===0).map(e=>[p,e===-1?0:p+2]));
   for(let n=0;n<C;n++){
    let p0=0,w0=Infinity;
    for(let [p,c] of E){let w=mod(c-n,2*p)||2*p;if(w<w0||w===w0&&p<p0){p0=p;w0=w}}
    let idx=i*C+n,g=0,B=0;if(p0){let b=i-(p0-1)/2;ck(b>=0,"wall");let k=b*C+mod(n+w0,C);g=p0-1+gs[k];B=Math.max(0,4*w0-p0+1+bs[k]);out.periodTransitionChecks++}
    gs[idx]=g;bs[idx]=B;sumG[n%2]+=g;sumB[n%2]+=B;maxG=Math.max(maxG,g);maxB=Math.max(maxB,B);out.periodStates++;
   }
  }
  for(let i=0;i<Q;i+=Math.max(1,Math.floor(Q/29)))for(let n=0;n<C;n+=Math.max(1,Math.floor(C/31))){let a=2*i,v=n,G=0,W=0,B=0;
   while(true){let e=next(a,v,P);if(!e.p)break;G+=e.p-1;W+=e.w;B=Math.max(B,4*W-G);a-=e.p-1;v+=e.w}
   ck(G===gs[i*C+n]&&B===bs[i*C+n],"direct restricted replay");out.periodDirectChecks++;
  }
  let meanG=sumG.map(a=>a/(Q*Q)),meanB=sumB.map(a=>a/(Q*Q)),t=tail(z);
  out.exact.push({z,Q,states:Q*C,meanG,meanB,maxG,maxB,...t,partialCoefficient:1.5*((meanB[0]+meanB[1])*t.sumInv2+2*t.sumH)});
 }
 let seed=0x81ab3e35;function u32(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0}function rnd(n){let m=Math.floor(4294967296/n)*n,x;do{x=u32()}while(x>=m);return x%n}
 for(let z of [11,31,127,511,2047,8191]){
  let P=pr.filter(p=>p<=z),cap=64*z,Ns=z<=511?2048:512,sums=[{n:0,absorb:0,G:0,B:0,max:0},{n:0,absorb:0,G:0,B:0,max:0}];
  for(let k=0;k<Ns;k++){
   let par=rnd(2),a=P.map(p=>rnd(p)),n=P.map(p=>2*rnd(p)+par),G=0,W=0,B=0,success=false;
   while(true){
    let p0=0,w0=Infinity;
    for(let i=0;i<P.length;i++){let p=P[i],r=mod(a[i]-G,p);if(r!==1&&r!==p-1)continue;let w=mod((r===p-1?0:p+2)-n[i]-W,2*p)||2*p;if(w<w0||w===w0&&p<p0){p0=p;w0=w}}
    if(!p0){success=true;break}if(G+p0-1>cap)break;
    G+=p0-1;W+=w0;B=Math.max(B,4*W-G);out.sampleEvents++;
   }
   let s=sums[par];s.n++;s.absorb+=+success;s.G+=G;s.B+=B;s.max=Math.max(s.max,G);out.phaseSamples++;if(!success)out.sampleTruncated++;
  }
  let meanG=sums.map(s=>s.G/s.n),meanB=sums.map(s=>s.B/s.n),t=tail(z);
  out.sample.push({z,Ns,cap,sums,meanG,meanB,ratio:(meanB[0]+meanB[1])/(z*Math.log(z)),partialCoefficient:1.5*((meanB[0]+meanB[1])*t.sumInv2+2*t.sumH),...t});
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
