// Hypergeometric averaging of split CRT Fourier energies.
function audit(){
 const primes=[];for(let p=3;p<=2000;p+=2)if(!primes.some(q=>q*q<=p&&p%q===0))primes.push(p);
 const mod=(x,p)=>(x%p+p)%p,choose=(n,k)=>{if(k<0||k>n)return 0;k=Math.min(k,n-k);let v=1;for(let i=1;i<=k;i++)v=v*(n-i+1)/i;return v};
 const local=(j,p,kind)=>kind==="H"?j<=(p-3)/2:p===3||[0,1].every(I=>{let r=mod(2*j-6*I,2*p);return r<2||r>p-3});
 const out={subsetChecks:0,coefficientChecks:0,partialParsevalChecks:0,energyChecks:0,varianceChecks:0,momentPositions:0,monotoneChecks:0,periods:[],asymptoticMargin:null};
 const subsets=(n,q)=>{let a=[];function go(i,s){if(s.length===q){a.push(s);return}for(let j=i;j<=n-(q-s.length);j++)go(j+1,[...s,j])}go(0,[]);return a};
 for(let R of [13,17,19]){
  let ps=primes.filter(p=>p<=R),P=ps.reduce((a,p)=>a*p,1),large=ps.filter(p=>p>=11),n=large.length,kappa=Math.max(...large.map(p=>1/(((p-3)/2)*Math.sin(Math.PI/p))));
  for(let kind of ["H","d"]){
   const sets=ps.map(p=>Array.from({length:p},(_,j)=>j).filter(j=>local(j,p,kind))),A=sets.reduce((a,s)=>a*s.length,1),pre=new Uint32Array(P+1);
   for(let j=0;j<P;j++)pre[j+1]=pre[j]+(ps.every((p,i)=>sets[i].includes(j%p))?1:0);
   if(pre[P]!==A)throw Error("CRT count");
   let coeff=ps.map((p,i)=>{let inv=1;while((P/p%p)*inv%p!==1)inv++;let ar=Array.from({length:p},(_,k)=>{let re=0,im=0;for(let a of sets[i]){let angle=2*Math.PI*mod(k*inv*a,p)/p;re+=Math.cos(angle);im+=Math.sin(angle)}return (re*re+im*im)/sets[i].length**2});if(Math.abs(ar.reduce((a,b)=>a+b,0)-p/sets[i].length)>1e-9)throw Error("local Parseval");return ar});
   const energy=k=>ps.reduce((v,p,i)=>v*coeff[i][k%p],1);
   for(let q=1;q<n;q++){
    let subs=subsets(n,q),all=subs.map(s=>({s,indices:s.map(i=>ps.indexOf(large[i])),Q:s.reduce((a,i)=>a*large[i],1)}));
    let M=Math.min(...all.map(s=>s.Q)),kmax=Math.min(M,Math.floor(P/2)),B=all.map(o=>o.indices.reduce((v,i)=>v*ps[i]/sets[i].length,1)).reduce((a,b)=>a+b,0)/all.length;
    let F=t=>{let sum=0;for(let j=Math.max(0,q-(n-t));j<=Math.min(q,t);j++)sum+=choose(t,j)*choose(n-t,q-j)/choose(n,q)*kappa**(-2*(n-t-q+j));return sum};
    for(let t=0;t<n;t++){if(F(t)+1e-9<F(t+1))throw Error("monotonicity");out.monotoneChecks++}
    for(let o of all){let e=0;for(let k=1;k<=o.Q;k++)e+=o.indices.reduce((v,i)=>v*coeff[i][k%ps[i]],1);let target=o.indices.reduce((v,i)=>v*ps[i]/sets[i].length,1);if(Math.abs(e-target)>1e-8*target)throw Error("partial Parseval");out.partialParsevalChecks++}
    let mass=0,mean=0;
    for(let k=1;k<=kmax;k++){
     let t=large.filter(p=>k%p===0).length;
     if(t>q)throw Error("divisors");
     let a=energy(k),b=0;
     for(let o of all){let x=o.indices.reduce((v,i)=>v*coeff[i][k%ps[i]],1),u=large.filter((p,j)=>!o.s.includes(j)&&k%p!==0).length;if(a>x*kappa**(2*u)+1e-10)throw Error("pointwise");b+=x;out.subsetChecks++}
     b/=all.length;if(a*F(t)>b+1e-9||a*F(q)>b+1e-9)throw Error("hypergeometric");out.coefficientChecks++;mass+=a;mean+=b;
    }
    if(mean>B+1e-8||mass>B/F(q)+1e-8)throw Error("energy");out.energyChecks++;
    const count=j=>Math.floor(j/P)*A+pre[mod(j,P)];
    let vars=[];
    for(let l of [Math.ceil(P**.56),Math.ceil(P**.75)]){
     let sum=0;for(let j=0;j<P;j++){let c=count(j+l)-count(j);sum+=(P*c/(A*l)-1)**2}
     let vv=sum/P,bound=2*B/F(q)+(P/(2*l*(kmax+1)))**2*P/A;
     if(vv>bound+1e-8)throw Error("variance");out.varianceChecks++;out.momentPositions+=P;vars.push({l,vv,bound})
    }
    out.periods.push({R,kind,n,q,M:kmax,energy:mass,bound:B/F(q),vars});
   }
  }
 }
 // Rigorous rational enclosure for the entropy margin at delta=11/25,j=1/4.
 // log x=2 sum_{k=0}^{m-1} z^(2k+1)/(2k+1)+remainder, z=(x-1)/(x+1).
 // Use fixed-point BigInt interval arithmetic with scale 10^40.
 const D=10n**40n;
 function logBounds(a,b){
  a=BigInt(a);b=BigInt(b);if(a<b){let [l,u]=logBounds(b,a);return [-u,-l]}
  let zlo=D*(a-b)/(a+b),zhi=zlo+1n,lo=0n,hi=0n,pl=zlo,ph=zhi;
  const ceil=(x,y)=>(x+y-1n)/y;
  for(let i=0;i<300;i++){
   lo+=2n*pl/BigInt(2*i+1);hi+=ceil(2n*ph,BigInt(2*i+1));
   pl=pl*zlo*zlo/(D*D);ph=ceil(ph*zhi*zhi,D*D);
  }
  hi+=ceil(2n*ph*D*D,601n*(D*D-zhi*zhi));return [lo,hi];
 }
 // M=2c0*(1-2d+j)+d H(j/d)+(1-d)H((d-j)/(1-d))-H(d)-d log2.
 // For d=.44,j=.25, use 100-scaled exact rational coefficients.
 // Entropy expression: -j log(j/d)-(d-j)log((d-j)/d)
 // -(d-j)log((d-j)/(1-d))-(1-2d+j)log((1-2d+j)/(1-d))
 // +d log d+(1-d)log(1-d).
 let terms=[[74,314159,200000],[-25,25,44],[-19,19,44],[-19,19,56],[-37,37,56],[44,44,100],[56,56,100],[-44,2,1]];
 let low=0n,high=0n;for(let [c,a,b] of terms){let [l,u]=logBounds(a,b);let C=BigInt(c);low+=C*(C>=0n?l:u);high+=C*(C>=0n?u:l)}
 // pi > 3.14159; the positive coefficient of log(pi/2) means lower bound suffices.
 if(low<=D*28n/100n)throw Error("entropy margin below .0028");
 out.asymptoticMargin={certifiedLower:Number(low)/Number(100n*D),lowerPi:3.14159,actualDouble:2*Math.log(Math.PI/2)*.37+.44*(-25/44*Math.log(25/44)-19/44*Math.log(19/44))+.56*(-19/56*Math.log(19/56)-37/56*Math.log(37/56))+.44*Math.log(.44)+.56*Math.log(.56)-.44*Math.log(2)};
 return out
}
console.log(JSON.stringify(audit(),null,2));
