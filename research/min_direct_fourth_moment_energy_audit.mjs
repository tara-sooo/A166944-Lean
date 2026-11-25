// Weighted fourth-moment subset energy bound for both CRT barrier families.
function audit(){
 const ps=[];for(let p=3;p<=199;p+=2)if(!ps.some(q=>q*q<=p&&p%q===0))ps.push(p);
 const mod=(a,b)=>(a%b+b)%b,z=3/5;
 function choose(n,k){if(k<0||k>n)return 0;let v=1;for(let i=1;i<=Math.min(k,n-k);i++)v=v*(n-i+1)/i;return v}
 function subs(n,q){let a=[];function go(i,s){if(s.length===q){a.push(s);return}for(let j=i;j<=n-q+s.length;j++)go(j+1,[...s,j])}go(0,[]);return a}
 const local=(j,p,kind)=>kind==="H"?j<=(p-3)/2:p===3||[0,1].every(I=>{let r=mod(2*j-6*I,2*p);return r<2||r>p-3});
 const out={localFourth:0,partialFourth:0,frequencyChecks:0,energyChecks:0,varianceChecks:0,momentPositions:0,periods:[]};
 for(let p of ps.filter(p=>p>=11))for(let kind of ["H","d"]){
  let A=Array.from({length:p},(_,j)=>j).filter(j=>local(j,p,kind)),s=0;
  for(let k=0;k<p;k++){let re=0,im=0;for(let j of A){let a=2*Math.PI*k*j/p;re+=Math.cos(a);im+=Math.sin(a)}s+=((re*re+im*im)/A.length**2)**2}
  let a=A.length,expected=p*(2*a*a+1)/(3*a**3);
  if(Math.abs(s-expected)>1e-10)throw Error("local fourth");out.localFourth++;
 }
 for(let R of [13,17,19]){
  let pr=ps.filter(p=>p<=R),P=pr.reduce((a,p)=>a*p,1),L=pr.filter(p=>p>=11),n=L.length,K=Math.max(...L.map(p=>1/(((p-3)/2)*Math.sin(Math.PI/p))));
  for(let kind of ["H","d"]){
   let sets=pr.map(p=>Array.from({length:p},(_,j)=>j).filter(j=>local(j,p,kind))),A=sets.reduce((a,s)=>a*s.length,1),pre=new Uint32Array(P+1);
   for(let i=0;i<P;i++)pre[i+1]=pre[i]+(pr.every((p,j)=>sets[j].includes(i%p))?1:0);
   if(pre[P]!==A)throw Error("CRT");
   let coeff=pr.map((p,i)=>{let inv=1;while((P/p%p)*inv%p!==1)inv++;return Array.from({length:p},(_,k)=>{let re=0,im=0;for(let j of sets[i]){let a=2*Math.PI*mod(k*inv*j,p)/p;re+=Math.cos(a);im+=Math.sin(a)}return (re*re+im*im)/sets[i].length**2})});
   let localM=L.map(p=>{let a=sets[pr.indexOf(p)].length;return z-1+p*(2*a*a+1)/(3*a**3)});
   const energy=k=>pr.reduce((v,p,i)=>v*coeff[i][k%p],1);
   const term=(p,k)=>k%p===0?z:coeff[pr.indexOf(p)][k%p]**2;
   const count=j=>Math.floor(j/P)*A+pre[mod(j,P)];
   for(let q=1;q<=Math.floor(n/2);q++){
    let U=subs(n,q),M=L.slice(0,q).reduce((a,p)=>a*p,1);
    let B=U.reduce((a,u)=>a+u.reduce((b,i)=>b*localM[i],1),0)/U.length;
    let factors=[];for(let t=0;t<=q;t++){
     let j=Math.max(Math.floor(5*t/8),Math.ceil(q-(n-t)/2),q-(n-t),0);
     if(j>Math.min(q,t))throw Error("feasible");
     let u=n-t-2*(q-j);if(u<0)throw Error("exponent");
     factors.push(choose(t,j)*choose(n-t,q-j)/choose(n,q)*z**j*K**(-2*u));
    }
    let F=Math.min(...factors),mass=0,mean=0;
    for(let u of U){let Q=u.reduce((a,i)=>a*L[i],1),v=0;for(let k=1;k<=Q;k++)v+=u.reduce((a,i)=>a*term(L[i],k),1);let expected=u.reduce((a,i)=>a*localM[i],1);if(Math.abs(v-expected)>1e-9)throw Error("partial fourth");out.partialFourth++}
    for(let k=1;k<=M;k++){
     let t=L.filter(p=>k%p===0).length,e=energy(k),avg=U.reduce((a,u)=>a+u.reduce((b,i)=>b*term(L[i],k),1),0)/U.length;
     if(t>q||avg+1e-10<e*factors[t])throw Error("weighted subset");mass+=e;mean+=avg;out.frequencyChecks++;
    }
    if(mean>B+1e-8||mass>B/F+1e-8)throw Error("energy");out.energyChecks++;
    let l=Math.ceil(P**(17/32)),v=0;
    for(let j=0;j<P;j++)v+=(P*(count(j+l)-count(j))/(A*l)-1)**2;
    v/=P;let bound=2*B/F+(P/(2*l*(M+1)))**2*P/A;
    if(v>bound+1e-8)throw Error("variance");out.varianceChecks++;out.momentPositions+=P;out.periods.push({R,kind,q,M,l,v,bound});
   }
  }
 }
 // Exact rational lower enclosures of both endpoint entropy margins.
 const D=10n**40n,ceil=(x,y)=>(x+y-1n)/y;
 function logBounds(a,b){
  a=BigInt(a);b=BigInt(b);if(a<b){let [l,u]=logBounds(b,a);return [-u,-l]}
  let zl=D*(a-b)/(a+b),zu=zl+1n,lo=0n,hi=0n,pl=zl,ph=zu;
  for(let i=0;i<300;i++){lo+=2n*pl/BigInt(2*i+1);hi+=ceil(2n*ph,BigInt(2*i+1));pl=pl*zl*zl/(D*D);ph=ceil(ph*zu*zu,D*D)}
  hi+=ceil(2n*ph*D*D,601n*(D*D-zu*zu));return [lo,hi]
 }
 function lower(terms){let l=0n;for(let [c,a,b] of terms){let [x,y]=logBounds(a,b);l+=BigInt(c)*(c>=0?x:y)}return l}
 // Scale all coefficients by 256; pi > 3.14159.
 let e0=lower([[32,314159,200000],[-120,14,15]]);
 let e1=lower([[92,314159,200000],[75,3,5],[-75,5,8],[-45,3,8],[-45,45,136],[-91,91,136],[120,15,32],[136,17,32],[-120,14,15]]);
 if(e0*1000n<=256n*D*88n||e1*1000n<=256n*D)throw Error("margin");
 out.marginLower={zero:Number(e0)/Number(256n*D),delta:Number(e1)/Number(256n*D)};
 return out
}
console.log(JSON.stringify(audit(),null,2));
