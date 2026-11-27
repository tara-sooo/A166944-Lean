// Exact rational sieve-coefficient enclosure and actual finite orbit checks.
// Run with node. Positive integrals alone do not verify the distribution theorems.
function audit(){
 const K=100000n,F=10n**18n,a=14400n,b=28450n,c=29600n;
 const ceil=(n,d)=>(n+d-1n)/d;
 function logBounds(n,d){
  if(n<d||d<=0n)throw Error("log domain");
  let u=n-d,v=n+d,p=u,q=v,lo=0n,hi=0n,N=32;
  for(let j=0;j<N;j++){let den=q*BigInt(2*j+1);lo+=2n*F*p/den;hi+=ceil(2n*F*p,den);p*=u*u;q*=v*v}
  hi+=ceil(2n*F*p*v*v,q*BigInt(2*N+1)*(v*v-u*u));
  return [lo,hi]
 }
 const Dn=39993n,Dd=70000n;
 const lb=logBounds(Dn*K-Dd*a,Dd*a);
 const Blo=2n*Dd*lb[0]/Dn,Bhi=ceil(2n*Dd*lb[1],Dn);
 let Uhi=0n,Ulo=0n,bins=0,minGap=999999n;
 for(let l=a;l<b;l++){
  let v=l+1n,d=(v<=25000n?K+l:2n*K-3n*v)-20n,g=d-2n*v;
  if(d<=4n*v||g<=2n*l||g>=6n*l)throw Error("level or linear sieve domain");
  if(d-4n*v<minGap)minGap=d-4n*v;
  Uhi+=ceil(4n*K*F,l*g);Ulo+=4n*K*F/(v*g);bins++;
 }
 function switched(lo,hi,kind){
  let up=0n,down=0n;
  for(let l=lo;l<hi;l++){
   let v=l+1n;
   let w=kind==="two"?F:kind==="three"?logBounds(K-2n*l,l)[1]:F+logBounds(K-2n*l,l)[1];
   up+=ceil(25n*w*K,7n*l*(K-l));
   if(3n*v<=K){
    let wd=kind==="two"?F:kind==="three"?logBounds(K-2n*v,v)[0]:F+logBounds(K-2n*v,v)[0];
    down+=25n*wd*K/(7n*v*(K-v));
   }
  }
  return [down,up]
 }
 const sw=switched(b,c,"all"),tr=switched(b,33334n,"three"),p2=[];
 for(let t of [28900n,29000n,29100n,29200n,29300n]){
  const two=switched(b,t,"two"),v=Blo-Uhi-tr[1]-two[1];
  p2.push({cutoff:Number(t)/Number(K),lower:String(v),approx:Number(v)/Number(F)})
 }
 if(Blo-Uhi-sw[1]<=F/100n||BigInt(p2[1].lower)<=15n*F/1000n)throw Error("positive margin");
 // Finite check of actual endpoint inequality, not proof of analytic distribution.
 const max=100002,spf=new Int32Array(max+1);
 for(let p=2;p<=max;p++)if(!spf[p]){spf[p]=p;if(p*p<=max)for(let q=p*p;q<=max;q+=p)if(!spf[q])spf[q]=p}
 function fac(x){let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function mod(a,p){return (a%p+p)%p}
 function next(x,n){let w=Infinity,p=0;
  for(let s of [-1,1])for(let q of fac(x+s)){let t=mod((s===1?0:q+2)-n,2*q)||2*q;if(t<w||(t===w&&q<p)){w=t;p=q}}
  return {w,p}
 }
 let roots=0,events=0,targets=0,nonTwinTargets=0,squareTargets=0,squareNonTwin=0,slowSlackChecks=0,firstEventP2Checks=0;
 for(let A=600;A<=max-2;A+=6){
  roots++;
  const first=next(A,3-A/2),q=spf[A+1],r=(A+1)/q;
  if(spf[A-1]===A-1&&q!==A+1&&spf[r]===r&&q>=11&&r>=11){
   const waitQ=((r%4)*q-7)/2,waitR=((q%4)*r-7)/2;
   if(first.w!==Math.min(waitQ,waitR)||first.p!==(waitQ<=waitR?q:r))throw Error("prime-semiprime calendar");
   firstEventP2Checks++;
  }
  const horizon=[Math.floor(A**.295),Math.floor(A**.4),Math.ceil(8*Math.sqrt(A+1))];
  let x=A,n=3-A/2,t=0,G=0,slack=0;
  for(let j=0;j<horizon.length;j++){
   const T=horizon[j];
   while(true){const e=next(x,n);if(t+e.w>T)break;x-=e.p-1;n+=e.w;t+=e.w;G+=e.p-1;slack+=Math.max(e.p-281,0);events++;
    if(x<=2)throw Error("range");
   }
   if(24*t>51*G+790-3*slack)throw Error("potential inequality");
   slowSlackChecks++;
   const I=T-t,qm=Math.min(spf[x-1],spf[x+1]),twin=spf[x-1]===x-1&&spf[x+1]===x+1;
   if(I>=2*qm)throw Error("idle bound");
   if(5*G<=2*T){
    targets++;if(j===2)squareTargets++;
    if(!twin){nonTwinTargets++;if(j===2)squareNonTwin++;}
    if(240*qm<=18*T-3950)throw Error("necessary roughness");
   }
  }
 }
 return {scale:String(F),base:[String(Blo),String(Bhi)],middle:[String(Ulo),String(Uhi)],switchAll:[String(sw[0]),String(sw[1])],tripleUpper:String(tr[1]),positiveLower:String(Blo-Uhi-sw[1]),bins,minLevelMargin:Number(minGap)/(2*Number(K)),p2,finite:{roots,events,targets,nonTwinTargets,squareTargets,squareNonTwin,slowSlackChecks,firstEventP2Checks}}
}
console.log(JSON.stringify(audit(),null,2));
