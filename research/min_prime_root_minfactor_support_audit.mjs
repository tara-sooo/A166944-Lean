// Reproduce: node research/min_prime_root_minfactor_support_audit.mjs
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),lo=2*X-2,hi=7*X,lim=hi+5,Q=Math.ceil(B/u),Qnew=Math.ceil(B/u**1.25),T=Math.floor(X/u**.75),ok=(b,m)=>{if(!b)throw Error(m);},mod=(a,m)=>((a%m)+m)%m,gcd=(a,b)=>{while(b){const c=a%b;a=b;b=c;}return a;};
 const spf=new Int32Array(lim+1),pr=[];for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n<=B&&n%2)pr.push(n);if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)if(!spf[j])spf[j]=n;}
 const fs=n=>{let a=[];while(n>1){const p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const rmap=new Uint16Array(hi+1),counts=new Map(),bands=new Map();let S=0,nonzero=0,highS=0,highCount=0,quotientChecks=0,twoSided=0,relS=0,relCount=0,maxEligible=0;
 for(let C=lo;C<=hi;C+=2){const a=fs(C-1),b=fs(C+1),p=Math.min(...a,...b);if(!Number.isFinite(p))continue;rmap[C]=p;S+=p;nonzero++;counts.set(p,(counts.get(p)||0)+1);const sig=(C-1)%p===0?-1:1;ok((C+sig)%p===0&&(C-sig)%p!==0,"unique side");const q=(C+sig)/p,n=(q-1)/2;ok(Number.isInteger(n)&&q%2===1,"integer quotient");for(const s of pr){if(s>=p)break;ok(q%s!==0&&(p*q-2*sig)%s!==0,"least-factor two forms");}quotientChecks++;
   if(a.length&&b.length)twoSided++;
   if(p>=Qnew/Math.sqrt(Math.log(Math.max(3,Qnew)))){highS+=p;highCount++;}
   if([...a,...b].some(v=>v>=Qnew&&p>v/Math.sqrt(Math.log(v)))){relS+=p;relCount++;}
   maxEligible=Math.max(maxEligible,a.length+b.length);const j=Math.floor(Math.log2(p));if(!bands.has(j))bands.set(j,{n:0,S:0});let v=bands.get(j);v.n++;v.S+=p;
 }
 let capChecks=0,totalCaps=0,strict=0;
 // Independent enumerate possible odd quotients for each minimal factor, both signs.
 for(const p of pr){
   let c=0;for(const sig of [-1,1]){let a=Math.ceil((lo+sig)/p);if(a%2===0)a++;for(;p*a-sig<=hi;a+=2){const C=p*a-sig;if(C<lo)continue;const rr=rmap[C];const pass=pr.every(s=>s>=p||a%s!==0&&(p*a-2*sig)%s!==0);ok(pass===(rr===p),"quotient sieve exact minimal factor");if(pass)c++;capChecks++;}}
   ok(c===(counts.get(p)||0),"exact factor bucket");
   // partial periodic sieve, small primes <=min(7,p-1), two residues each
   const qs=pr.filter(s=>s<p&&s<=7),P=qs.reduce((a,s)=>a*s,1),rho=qs.reduce((a,s)=>a*(s-2),1);let upper=0;for(const sig of [-1,1]){let a=Math.ceil((lo+sig)/p);if(a%2===0)a++;let H=Math.max(0,Math.floor(((hi+sig)/p-a)/2)+1);let per=0;for(let n=0;n<P;n++)if(qs.every(s=>(2*n+1)%s!==0&&(p*(2*n+1)-2*sig)%s!==0))per++;ok(per===rho,"period capacity");upper+=Math.min(H,rho*(Math.floor(H/P)+1));}
   ok(c<=upper,"factor bucket capacity");if(c<upper)strict++;totalCaps+=p*upper;
 }
 let N=0;for(let M=X+1;M<2*X;M+=2)if(spf[M]===M)N++;
 const run=(T,Q,mode)=>{
   const W=new Map();let R=0,G=0,events=0,literal=0,cross=0,twins=0,other=0,hiR=0,mediumR=0,cheapR=0,firstR=0,hiZ=0,medZ=0,rootHits=0;
   const k=mode==="analytic"?Math.max(1,Math.floor(u**.125)):1;
   for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){
     let t=M+2,C=2*M-2,cut=Math.floor((7*M-1)/4),hits=new Map(),med=new Map(),cost=0;
     while(C-(2*M-2)<T){
       let tt=Infinity,p=Infinity;
       for(const sig of [-1,1])for(const q of fs(C+sig)){let tick=t+1+mod((sig===-1?0:q+2)-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;}}
       if(X<=1024){let lt=Infinity,lp=Infinity;for(let s=t+1;s<=cut;s++){const f=fs(gcd(s%2?s-2:s,C+(s%2?1:-1)));if(f.length){lt=s;lp=f[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal clock");literal++;}
       if(tt>cut)break;
       const r=rmap[C];ok(r>0&&r<=p&&tt-t<=2*r,"clock");R+=r;cost+=r;events++;let n=(hits.get(p)||0)+1;hits.set(p,n);
       if(n<=k){firstR+=r;}else if(p>=5&&r<=p/Math.sqrt(Math.log(p))){cheapR+=r;}else if(p>=Q){hiR+=r;W.set(C,(W.get(C)||0)+1);rootHits++;}else{mediumR+=r;med.set(p,(med.get(p)||0)+1);}
       t=tt;C+=p-1;ok(C<=2*t,"invariant");
     }
     const gain=C-(2*M-2);G+=gain;ok(gain<T+B&&2*cost<=3*gain,"gain budget");
     if(gain>=T){cross++;ok(4*cost>=T-6,"cross lower");}else if(spf[C-1]===C-1&&spf[C+1]===C+1)twins++;else{other++;ok(cut-M-2<=3*T+2*B,"noncross");}
     for(const n of med.values())medZ+=n*n;
   }
   let E=0,supp=0,maxMass=0,thinR=0,thinE=0,thinN=0;const massCap=mode==="analytic"?B*u**1.5:4;
   for(const [C,n] of W){const r=rmap[C];E+=r*n*n;supp+=r;maxMass=Math.max(maxMass,n);if(n<=massCap){thinR+=r*n;thinE+=r*n*n;thinN++;}}
   ok(R===firstR+cheapR+hiR+mediumR&&N===cross+twins+other,"clock partition");ok(BigInt(hiR)**2n<=BigInt(supp)*BigInt(E)&&supp<=S,"Cauchy support");ok(thinR<=massCap*supp&&thinE<=massCap*thinR,"thin mass");
   return {mode,T,Q,k,R,G,events,literal,cross,twins,other,firstR,cheapR,mediumR,hiR,medZ,rootHits,E,supp,maxMass,massCap,thinR,thinE,thinN,finalE:E-thinE};
 };
 return {X,B,N,S,nonzero,highS,highCount,relS,relCount,quotientChecks,capChecks,strict,totalCaps,maxEligible,twoSided,scaled:S*u**3/(X*B),oldScaled:S*u**2/(X*B),bands:[...bands],runs:[run(T,Qnew,"analytic"),run(B,Math.max(5,Qnew),"short"),run(4*B,Math.max(5,Q),"four")]};
}
const xs=process.argv.slice(2).map(Number);for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X)));
