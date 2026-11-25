// Reproduce: node research/min_prime_root_quotient_blocks_audit.mjs
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),ell=Math.max(1,Math.log(Math.log(B))),analytic=mode==="analytic",b=analytic?Math.max(2,Math.floor(Math.log(B)**.25)):mode==="wide"?3:6,Y=analytic?Math.max(5,Math.ceil(ell)):mode==="wide"?7:17;
 const lim=7*X+5,spf=new Int32Array(lim+1),pr=[];
 for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n<=B&&n%2)pr.push(n);if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)if(!spf[j])spf[j]=n;}
 const fs=n=>{const a=[];while(n>1){const p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const mod=(a,m)=>((a%m)+m)%m,gcd=(a,b)=>{while(b){const c=a%b;a=b;b=c;}return a;},ok=(b,msg)=>{if(!b)throw Error(msg);};
 const rc=new Int32Array(lim+1);function least(C){if(rc[C])return rc[C]-1;let p=0;for(const n of [C-1,C+1])for(const q of fs(n))if(!p||q<p)p=q;rc[C]=p+1;return p;}
 const parms=p=>{const z=analytic?Math.max(2,Math.floor(Math.min(Math.sqrt(p),b**(1/16)))):mode==="wide"?3:5;return {z,eta:analytic?Math.min(1,1/Math.sqrt(Math.log(z))):.5,K:analytic?Math.max(1,Math.log(z)**1.5):3};};
 const W=new Map(), Wlate=new Map();let N=0,R=0,G=0,events=0,literal=0,nontwin=0,blocks=0,compact=0,lowCost=0,compactLow=0,compactHigh=0,otherLow=0,highBlocks=0,prefix=0,cheap=0,retained=0,small=0,allBig=0,Z=0,roughChecks=0,roughCount=0,roughCapacity=0,actualSpan=0,periodChecks=0,removedHits=0,retainedHits=0,maxMultiplicity=0,highRetained=0;
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){
   N++;let C=2*M-2,t=M+2,cut=Math.floor((7*M-1)/4),a=[],by=new Map();
   while(true){
     let tt=Infinity,p=Infinity,sg=0;
     for(const sigma of [-1,1])for(const q of fs(C+sigma)){const tick=t+1+mod((sigma===-1?0:q+2)-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;sg=sigma;}}
     if(X<=1024){let lt=Infinity,lp=Infinity;for(let u=t+1;u<=cut;u++){let f=fs(gcd(u%2?u-2:u,C+(u%2?1:-1)));if(f.length){lt=u;lp=f[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal gcd");literal++;}
     if(tt>cut)break;
     const r=least(C),v=(C+sg)/p;ok(Number.isInteger(v)&&v%2===1&&r>0&&r<=p&&tt-t<=2*r,"clock quotient");
     const e={C,p,sg,r,n:(v-1)/2};a.push(e);if(!by.has(p))by.set(p,[]);const list=by.get(p);if(list.length&&p>=5)ok(e.n>list[list.length-1].n,"strict quotient");list.push(e);R+=r;events++;t=tt;C+=p-1;ok(C<=2*t,"horizon");
   }
   const gain=C-(2*M-2);G+=gain;if(spf[C-1]!==C-1||spf[C+1]!==C+1)nontwin++;
   for(const [p,list] of by){
     if(p<Y){small+=list.reduce((s,e)=>s+e.r,0);continue;}
     const {z,eta,K}=parms(p);ok(p>z,"sieve p cutoff");const qs=pr.filter(q=>q<=z),P=qs.reduce((s,q)=>s*q,1),rhoNum=qs.reduce((s,q)=>s*(q-2),1);
     const permitted=(n,sigma)=>qs.every(q=>mod(2*n+1,q)!==0&&mod(p*(2*n+1)-2*sigma,q)!==0);
     if(P<=5000)for(const sig of [-1,1])ok(Array.from({length:P},(_,i)=>i).filter(n=>permitted(n,sig)).length===rhoNum,"period product");
     const pre=list.length%b;prefix+=list.slice(0,pre).reduce((s,e)=>s+e.r,0);removedHits+=pre;let spans=0,res=0,pblocks=0;
     for(let u=pre;u<list.length;u+=b){
       const ar=list.slice(u,u+b),H=ar[b-1].n-ar[0].n+1,span=ar[b-1].C-ar[0].C,rcost=ar.reduce((s,e)=>s+e.r,0);
       ok(H>=b&&span===2*p*(H-1)-ar[b-1].sg+ar[0].sg,"quotient span identity");spans+=span;blocks++;actualSpan+=H;
       let expensive=0,cap=0;for(const e of ar){const test=permitted(e.n,e.sg);ok(test===(e.r>z),"actual two-form roughness");roughChecks++;if(test)expensive++;}
       roughCount+=expensive;for(let n=ar[0].n;n<=ar[b-1].n;n++)if(permitted(n,-1)||permitted(n,1))cap++;
       ok(expensive<=cap&&cap<=Math.min(H,2*rhoNum*(Math.floor(H/P)+1)),"exact periodic union upper");periodChecks++;roughCapacity+=cap;
       ok(rcost<=z*b+(p-z)*expensive,"clock roughness charge");
       const dense=H<=K*b,cheapBlock=rcost<=eta*p*b;
       if(dense){compact++;if(cheapBlock)compactLow++;else compactHigh++;}
       if(cheapBlock){lowCost+=rcost;if(!dense)otherLow++;removedHits+=b;continue;}
       highBlocks++;pblocks++;allBig+=rcost;let pRes=0;
       for(const e of ar)if(e.r<=z){cheap+=e.r;removedHits++;}else{retained+=e.r;retainedHits++;pRes++;if(p>=Math.ceil(B/Math.log(B))){highRetained+=e.r;W.set(e.C,(W.get(e.C)||0)+1);if(e.C-(2*M-2)>B)Wlate.set(e.C,(Wlate.get(e.C)||0)+1);}}
       res+=pRes;ok(expensive>=Math.max(0,Math.ceil((rcost-z*b)/(p-z))),"expensive lower");
     }
     ok(spans<=gain,"disjoint block spans");ok(res<=pblocks*b,"residual multiplicity");maxMultiplicity=Math.max(maxMultiplicity,res);Z+=res*res;
   }
 }
 ok(R===small+prefix+lowCost+cheap+retained,"partition");ok(allBig===cheap+retained,"costly block partition");
 const energy=m=>[...m].reduce((s,[C,n])=>s+BigInt(least(C))*BigInt(n)**2n,0n).toString();
 return {mode,X,B,N,b,Y,R,G,events,literal,nontwin,blocks,compact,compactLow,compactHigh,otherLow,highBlocks,prefix,lowCost,cheap,retained,small,Z,roughChecks,roughCount,roughCapacity,actualSpan,periodChecks,removedHits,retainedHits,maxMultiplicity,highRetained,E:energy(W),Elate:energy(Wlate)};
}
const xs=process.argv.slice(2).map(Number),windows=xs.length?xs:[256,1024,4096,16384,65536,262144];for(const mode of ['analytic','wide','fixed'])for(const X of windows)console.log(JSON.stringify(audit(X,mode)));

function selbergOracle(){
 const gcd=(a,b)=>{while(b){const c=a%b;a=b;b=c;}return a;};
 const ok=(b,msg)=>{if(!b)throw Error(msg);};
 const prime=n=>n>=2&&Array.from({length:Math.max(0,Math.floor(Math.sqrt(n))-1)},(_,i)=>i+2).every(d=>n%d!==0);
 let systems=0,intervals=0,majorants=0,weightChecks=0,maxError=0;
 for(const z of [3,5,7,11,17,31,61,101]){
   const qs=[];for(let q=3;q<=z;q+=2)if(prime(q))qs.push(q);
   const ds=[];function gen(i,d,mu,g,h){if(i===qs.length){ds.push({d,mu,g,h});return;}gen(i+1,d,mu,g,h);const q=qs[i];if(d*q<=z)gen(i+1,d*q,-mu,g*2/q,h*(q-2)/2);}gen(0,1,1,1,1);
   const GG=ds.reduce((s,e)=>s+1/e.h,0);
   for(const a of ds){a.lambda=ds.filter(e=>e.d%a.d===0).reduce((s,e)=>s+a.mu/(GG*e.h*a.g),0);ok(Math.abs(a.lambda)<=a.d+1e-10,"Selberg weight bound");weightChecks++;}
   ok(Math.abs(ds.find(e=>e.d===1).lambda-1)<1e-10,"lambda one");
   const gg=d=>qs.filter(q=>d%q===0).reduce((s,q)=>s*2/q,1);
   let main=0,err=0;for(const a of ds)for(const c of ds){const lcm=a.d*c.d/gcd(a.d,c.d);main+=a.lambda*c.lambda*gg(lcm);err+=Math.abs(a.lambda*c.lambda)*qs.filter(q=>lcm%q===0).reduce((s,q)=>2*s,1);}
   const delta=Math.abs(main-1/GG);maxError=Math.max(maxError,delta);ok(delta<1e-9,"Selberg diagonal identity");
   const pp=[z+1,z+2,z+3].find(prime)||Array.from({length:100},(_,i)=>z+i+1).find(prime);
   for(const p of [pp,1009])for(const s of [-1,1]){
     systems++;
     const allowed=n=>qs.every(q=>(2*n+1)%q!==0&&(p*(2*n+1)-2*s)%q!==0);
     for(const start of [1,37,137])for(const H of [101,257]){
       let count=0,major=0;for(let n=start;n<start+H;n++){const a=2*n+1,c=p*a-2*s;let lambda=0;for(const e of ds)if(qs.every(q=>e.d%q!==0||a%q===0||c%q===0))lambda+=e.lambda;major+=lambda*lambda;if(allowed(n)){count++;ok(Math.abs(lambda-1)<1e-10,"survivor majorant");majorants++;}}
       ok(count<=major+1e-8&&major<=H/GG+err+1e-7,"Selberg interval bound");intervals++;
     }
   }
 }
 return {systems,intervals,majorants,weightChecks,maxError};
}
console.log(JSON.stringify({selberg:selbergOracle()}));
