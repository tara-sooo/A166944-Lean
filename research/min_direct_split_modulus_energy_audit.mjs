// Split-modulus Fourier energy bound for CRT barrier moving averages.
function audit(){
 const ps=[];for(let p=3;p<=2000;p+=2)if(!ps.some(q=>q*q<=p&&p%q===0))ps.push(p);
 const mod=(x,p)=>(x%p+p)%p;
 const local=(j,p,kind)=>kind==="H"?j<=(p-3)/2:p===3||[0,1].every(I=>{let r=mod(2*j-6*I,2*p);return r<2||r>p-3});
 const out={periods:[],finiteBounds:0,partialEnergyChecks:0,parsevalChecks:0,momentPositions:0,precursorBudgetChecks:0,formula:[]};
 for(let R of [7,11,13,17,19]){
  let pr=ps.filter(p=>p<=R),P=pr.reduce((a,p)=>a*p,1);
  for(let kind of ["H","d"]){
   let sets=pr.map(p=>Array.from({length:p},(_,j)=>j).filter(j=>local(j,p,kind)));
   let A=sets.reduce((a,s)=>a*s.length,1),pre=new Uint32Array(P+1);
   for(let j=0;j<P;j++)pre[j+1]=pre[j]+(pr.every((p,i)=>sets[i].includes(j%p))?1:0);
   if(pre[P]!==A)throw Error("CRT");
   let coeff=pr.map((p,i)=>{
    let inv=1;while((P/p%p)*inv%p!==1)inv++;
    return Array.from({length:p},(_,k)=>{
     let re=0,im=0;for(let a of sets[i]){let angle=2*Math.PI*mod(k*inv*a,p)/p;re+=Math.cos(angle);im+=Math.sin(angle)}
     return (re*re+im*im)/sets[i].length**2;
    })
   });
   let energy=new Float64Array(P);
   for(let k=0;k<P;k++){let v=1;for(let i=0;i<pr.length;i++)v*=coeff[i][k%pr[i]];energy[k]=v}
   let all=energy.reduce((a,b)=>a+b,0);
   if(Math.abs(all-P/A)>1e-7*P/A)throw Error("parseval");out.parsevalChecks++;
   let lengths=[Math.ceil(P**(2/3)),Math.ceil(P**.75),Math.ceil(P**.9)];
   let vars=[];
   const cnt=j=>Math.floor(j/P)*A+pre[mod(j,P)];
   for(let l of lengths){
    let sum=0,z=0;for(let j=0;j<P;j++){let c=cnt(j+l)-cnt(j);sum+=(P*c/(A*l)-1)**2;if(c===0)z++}
    let vv=sum/P,sp=0;
    for(let k=1;k<P;k++){let m=Math.min(k,P-k),v=Math.sin(Math.PI*l*m/P)/(l*Math.sin(Math.PI*m/P));sp+=energy[k]*v*v}
    if(Math.abs(vv-sp)>1e-7*Math.max(1,vv)||z/P>vv+1e-8)throw Error("moving parseval");out.momentPositions+=P;out.parsevalChecks++;
    vars.push({l,var:vv,zero:z/P});
    for(let i=1;i<pr.length;i++){
     let Q=pr.slice(0,i).reduce((a,p)=>a*p,1);
     if(Q>P/2)continue;
     let inside=sets.slice(0,i).reduce((a,s,j)=>a*pr[j]/s.length,1),kappa=Math.max(...pr.slice(i).map(p=>p<11?1:1/(((p-3)/2)*Math.sin(Math.PI/p))));
     let n=pr.length-i-Math.floor(Math.log(Q)/Math.log(pr[i])+1e-12),low=inside*kappa**(2*Math.max(0,n)),actual=0;
     for(let k=1;k<=Q;k++)actual+=energy[k];
     if(actual>low+1e-8)throw Error("partial energy");
     out.partialEnergyChecks++;
     let bd=2*low+(P/(2*l*(Q+1)))**2*P/A;
     if(vv>bd+1e-8)throw Error("split variance");
     out.finiteBounds++;
    }
   }
   out.periods.push({R,kind,P,A,vars});
  }
 }
 for(let R of [100,200,500,1000,2000]){
  let pr=ps.filter(p=>p<=R),r=pr.length,logP=pr.reduce((a,p)=>a+Math.log(p),0);
  for(let delta of [.25,1/3,.35]){
   let target=delta*logP+r,logQ=0,i=0;
   while(logQ<target&&i<pr.length)logQ+=Math.log(pr[i++]);
   if(i===pr.length)continue;
   let outside=pr.slice(i),kappa=Math.max(...outside.map(p=>p<11?1:1/(((p-3)/2)*Math.sin(Math.PI/p))));
   let n=Math.max(0,r-i-Math.floor(logQ/Math.log(pr[i]))),logInside=pr.slice(0,i).reduce((a,p)=>a+Math.log(p/(p<=7?3:(p-3)/2)),0);
   // Common density lower bound uses smaller of H and deficit local counts.
   logInside=pr.slice(0,i).reduce((a,p)=>a+Math.log(p/Math.min((p-1)/2,p<=7?3:(p-3)/2)),0);
   let logAll=pr.reduce((a,p)=>a+Math.log(p/Math.min((p-1)/2,p<=7?3:(p-3)/2)),0);
   let a=Math.log(2)+logInside+2*n*Math.log(kappa),b=2*(delta*logP-logQ)-Math.log(4)+logAll;
   let m=Math.max(a,b),bound=m+Math.log(Math.exp(a-m)+Math.exp(b-m));
   out.formula.push({R,delta,log10bound:bound/Math.log(10),insidePrimeCount:i,activeOutside:n});
  }
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
