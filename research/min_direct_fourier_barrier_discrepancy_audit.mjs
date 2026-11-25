// Fourier discrepancy of horizon/deficit CRT barriers; finite diagnostics.
function audit(){
 const primes=[];for(let p=3;p<=2000;p+=2){if(!primes.some(q=>q*q<=p&&p%q===0))primes.push(p)}
 const mod=(x,p)=>(x%p+p)%p;
 const local=(j,p,kind)=>kind==="H"?j<=(p-3)/2:p===3?true:[0,1].every(I=>{let r=mod(2*j-6*I,2*p);return !(r>=2&&r<=p-3)});
 const s={localChecks:0,coefficientChecks:0,crtFrequencyChecks:0,divisorChecks:0,intervalChecks:0,roundChecks:0,tailChecks:0,periods:[],large:[]};
 for(let p of primes.filter(p=>p<=199)){
  let a=(p-3)/2,k=p>=11?1/(a*Math.sin(Math.PI/p)):1;
  for(let kind of ["H","d"]){
   let rs=Array.from({length:p},(_,j)=>j).filter(j=>local(j,p,kind));
   if(rs.length!==(kind==="H"?(p-1)/2:p<=7?3:a))throw Error("local count");
   s.localChecks++;
   for(let f=1;f<p;f++){
    let re=0,im=0;for(let r of rs){re+=Math.cos(2*Math.PI*f*r/p);im+=Math.sin(2*Math.PI*f*r/p)}
    if(Math.hypot(re,im)/rs.length>k+1e-10)throw Error("local coeff");s.coefficientChecks++;
   }
  }
 }
 let seed=12345;const rand=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n};
 for(let S of [5,7,11,13,17,19]){
  const ps=primes.filter(p=>p<=S),P=ps.reduce((a,p)=>a*p,1),large=ps.filter(p=>p>=11);
  const ks=large.map(p=>1/(((p-3)/2)*Math.sin(Math.PI/p))),Lambda=ks.reduce((a,k)=>a*k,1),D=ks.reduce((a,k,i)=>a*(1+(1/k-1)/large[i]),1);
  let E=Math.min(P,P*Lambda*D*(1+Math.log(P))),B=2*Math.ceil(E)+4;
  // Enumerate divisor weights and their average (up to min(P,100000)).
  let sum=0;for(let k=1;k<=Math.min(P,100000);k++){let f=1;large.forEach((p,i)=>{if(k%p===0)f/=ks[i]});sum+=f;if(sum>D*k+1e-7)throw Error("divisor avg");s.divisorChecks++}
  for(let kind of ["H","d"]){
   const sets=ps.map(p=>Array.from({length:p},(_,j)=>j).filter(j=>local(j,p,kind)));
   let pre=new Uint32Array(P+1),cuts=[];
   for(let j=0;j<P;j++){let ok=ps.every((p,i)=>sets[i].includes(j%p));pre[j+1]=pre[j]+(ok?1:0);if(ok)cuts.push(j)}
   let A=sets.reduce((a,r)=>a*r.length,1);if(pre[P]!==A)throw Error("CRT count");
   let maxGap=0,mn=0,mx=0;
   for(let j=0;j<P;j++){let v=P*pre[j]-A*j;mn=Math.min(mn,v);mx=Math.max(mx,v)}
   for(let i=0;i<cuts.length;i++)maxGap=Math.max(maxGap,(cuts[(i+1)%cuts.length]+(i===cuts.length-1?P:0))-cuts[i]);
   if((mx-mn)/A>E+1e-7||maxGap>Math.floor(E)+1)throw Error("discrepancy/gap");
   const cnt=j=>Math.floor(j/P)*A+pre[mod(j,P)];
   for(let i=0;i<2000;i++){let a=rand(P*2),l=rand(P*3);if(Math.abs((cnt(a+l)-cnt(a))*P/A-l)>E+1e-7)throw Error("interval");s.intervalChecks++}
   // Direct CRT factorization of selected Fourier frequencies.
   for(let k=1;k<=Math.min(P-1,40);k++){
    let mag=1;
    for(let i=0;i<ps.length;i++){let p=ps[i],b=P/p%p,inv=1;while(b*inv%p!==1)inv++;let re=0,im=0;for(let r of sets[i]){let ang=2*Math.PI*mod(k*inv*r,p)/p;re+=Math.cos(ang);im+=Math.sin(ang)}mag*=Math.hypot(re,im)/sets[i].length}
    let upper=Lambda;large.forEach((p,i)=>{if(k%p===0)upper/=ks[i]});
    if(mag>upper+1e-8)throw Error("CRT coeff");
    if(P<=15015){let re=0,im=0;for(let j of cuts){let ang=2*Math.PI*k*j/P;re+=Math.cos(ang);im+=Math.sin(ang)}if(Math.abs(Math.hypot(re,im)/A-mag)>1e-8)throw Error("CRT direct")}
    s.crtFrequencyChecks++;
   }
   // Rounded tail grid using the exact observed maximum gap as well as
   // the proved upper bound, to exercise nontrivial scales.
   if(kind==="d"){
    function round(z){let q=Math.ceil((z-3)/2),r=mod(q,P),base=q-r,l=0,h=cuts.length;while(l<h){let m=(l+h)>>1;if(cuts[m]<r)l=m+1;else h=m}return 2*(base+(l===cuts.length?P+cuts[0]:cuts[l]))+3}
    for(let J of [B,2*maxGap+4]){
     let ys=[];for(let z=3*J;z<=3*J*1024;z*=2){let y=round(z);if(y<z||y>=z+J||ys.length&&2*y<3*ys.at(-1))throw Error("round");ys.push(y);s.roundChecks++}
     for(let i=0;i<1000;i++){let p=2*J+rand(1000*J),y=ys.find(y=>5*y>p&&y<=2*p);if(y===undefined)throw Error("tail");s.tailChecks++}
    }
   }
   s.periods.push({S,kind,P,A,maxGap,normalizedDiscrepancy:(mx-mn)/A,provedIndexBound:E});
  }
 }
 for(let S of [100,200,500,1000,2000]){
  let ps=primes.filter(p=>p<=S),large=ps.filter(p=>p>=11),logP=ps.reduce((a,p)=>a+Math.log(p),0),logLambda=large.reduce((a,p)=>a-Math.log(((p-3)/2)*Math.sin(Math.PI/p)),0),logD=large.reduce((a,p)=>a+Math.log1p((((p-3)/2)*Math.sin(Math.PI/p)-1)/p),0),logRatio=Math.min(0,logLambda+logD+Math.log1p(logP));
  s.large.push({S,primeCount:ps.length,logP,logRatio,improvementDecimalExponent:-logRatio/Math.log(10)});
 }
 return s
}
console.log(JSON.stringify(audit(),null,2));
