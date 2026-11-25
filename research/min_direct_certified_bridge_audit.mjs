// Four-residue upper-sieve and actual certified-bridge diagnostics.
function audit(N=200000,steps=180){
 const mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a},P=[];
 for(let p=3;p<=251;p+=2)if(P.every(q=>q*q>p||p%q))P.push(p);
 let s={sieveCases:0,weights:0,quadraticTerms:0,integerChecks:0,degeneracyChecks:0,events:0,paths:0,certified:0,bridges:0,sameLabel:0,differentLabel:0,runChecks:0,capacityChecks:0,bridgeResidueChecks:0,progressionChecks:0,maxRun:0,maxPatternMultiplicity:0,example:null};
 // General four-root diagonalization, including colliding roots.
 for(let z of [37,61,101,173,251])for(let p of [257,263,269])for(let g of [4,6,36,38,74,76,112,222])for(let e of [1,-1]){
   const ps=P.filter(l=>l>31&&l<=z),bad=new Map(),rho=new Map();
   for(let l of ps){let arr=[];for(let q=0;q<l;q++)if([e-1,e+1,e+g-1,e+g+1].some(v=>mod(p*q+v,l)===0))arr.push(q);
    if((arr.length!==4)!==(g%l===0||(g-2)%l===0||(g+2)%l===0))throw Error("collision");
    rho.set(l,arr.length);bad.set(l,arr);s.degeneracyChecks++}
   let ds=[{d:1,mu:1,rs:1,den:1,fs:[]}];for(let l of ps)for(let x of ds.slice())if(x.d*l<=z)ds.push({d:x.d*l,mu:-x.mu,rs:x.rs*rho.get(l),den:x.den*(l-rho.get(l)),fs:[...x.fs,l]});
   let M=ps.reduce((a,l)=>a*BigInt(l-rho.get(l)),1n),R=ps.reduce((a,l)=>a*BigInt(rho.get(l)),1n),prod=ps.reduce((a,l)=>a*BigInt(l),1n);
   for(let x of ds)x.h=M/BigInt(x.den)*BigInt(x.rs);
   let G=ds.reduce((a,x)=>a+x.h,0n),scale=G*R;
   for(let x of ds){let T=ds.filter(y=>y.d%x.d===0).reduce((a,y)=>a+y.h,0n);x.w=BigInt(x.mu*x.d)*(R/BigInt(x.rs))*T;if((x.w<0n?-x.w:x.w)>BigInt(x.d)*scale)throw Error("weight");s.weights++}
   let Q=0n,E=0n;for(let x of ds)for(let y of ds){let l=x.d*y.d/gcd(x.d,y.d),r=1;for(let f of ps)if(l%f===0)r*=rho.get(f);Q+=x.w*y.w*BigInt(r)*(prod/BigInt(l));E+=(x.w<0n?-x.w:x.w)*(y.w<0n?-y.w:y.w)*BigInt(r);s.quadraticTerms++}
   if(ds[0].w!==scale||Q*G!==scale*scale*prod*M||E>BigInt(z)**6n*scale*scale)throw Error("quadratic");
   let count=0n,W=0n;
   for(let q=1;q<=500;q++){let hit=new Set(ps.filter(l=>bad.get(l).includes(q%l)));if(!hit.size)count++;let a=0n;for(let x of ds)if(x.fs.every(f=>hit.has(f)))a+=x.w;W+=a*a;s.integerChecks++}
   if(count*scale**2n>W||W*G>500n*M*scale**2n+E*G)throw Error("majorant");
   let M0=ps.reduce((a,l)=>a*BigInt(l-4),1n),G0=ds.reduce((a,x)=>a+M0/x.fs.reduce((v,l)=>v*BigInt(l-4),1n)*4n**BigInt(x.fs.length),0n);
   let jn=1n,jd=1n;for(let l of ps)if(rho.get(l)<4){jn*=BigInt(l);jd*=BigInt(l-4)}
   if(G0*M*jd>G*M0*jn)throw Error("singular");
   s.sieveCases++;
 }
 const cap=4*N+20000,spf=new Int32Array(cap+1);for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)spf[j]=i}
 function next(t,H){let best=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}}return best}
 for(let M=5;M<=N;M+=2){let t=M+2,H=2*M-2,ev=[];for(let i=0;i<steps&&H+Math.sqrt(H+1)+1<cap;i++){let r=next(t,H);if(!r)break;ev.push({...r,H,t});H+=r.p-1;t+=r.w;s.events++}
   if(!ev.length)continue;s.paths++;
   const Y=H,B=1+Math.floor(Math.cbrt(512*(Y+1))),cert=ev.filter(x=>x.p>B&&4*x.w>=x.p-1).map(x=>({...x,q:(x.H-x.e)/x.p}));
   s.certified+=cert.length;let patterns=new Map(),runs=[],start=0;
   for(let i=0;i<cert.length;i++){
    let a=cert[i];if(spf[a.q]!==a.q)throw Error("cofactor");
    if(i&&a.p!==cert[i-1].p){runs.push([start,i-1]);start=i}
    if(i+1===cert.length)runs.push([start,i]);
    if(i+1>=cert.length)continue;
    let b=cert[i+1],g=b.H-a.H,extra=g-(a.p-1);
    if(g<=2||extra<0||extra%2)throw Error("bridge");
    s.bridges++;
    if(a.p===b.p){s.sameLabel++;if(extra<a.p-1)throw Error("same label gap")}
    else {s.differentLabel++;let key=[a.p,b.p,extra,a.e,b.e].join(":"),old=patterns.get(key)||[];
      if(mod(a.p*a.q+a.e+g-b.e,b.p)!==0)throw Error("CRT");
      if(old.length&&(a.q-old.at(-1))%b.p!==0)throw Error("progression");old.push(a.q);patterns.set(key,old);s.progressionChecks++;
      if(!s.example||a.p+b.p>s.example.a.p+s.example.b.p)s.example={M,Y,a,b,g,extra};
    }
    for(let l of P)if(l>31&&l**3<=Y+1){if([a.H-1,a.H+1,b.H-1,b.H+1].some(v=>v%l===0))throw Error("rough bridge");s.bridgeResidueChecks++}
   }
   let span=0,gain=0;
   for(let [i,j] of runs){let a=cert[i],b=cert[j],m=j-i+1;span+=b.H-a.H;gain+=m*(a.p-1);s.maxRun=Math.max(s.maxRun,m);if(b.q-a.q<2*(m-1)||b.H-a.H!==a.p*(b.q-a.q)+b.e-a.e)throw Error("run");s.runChecks++}
   if(span>Y-(2*M-2)||gain!==cert.reduce((a,b)=>a+b.p-1,0))throw Error("run partition");
   for(let [key,qs] of patterns){let [p,r]=key.split(":").map(Number);if(qs.length>1+Math.floor((Y+1)/(p*r)))throw Error("capacity");s.capacityChecks++;s.maxPatternMultiplicity=Math.max(s.maxPatternMultiplicity,qs.length)}
 }
 return s;
}
console.log(JSON.stringify(audit(Number(process.argv[2]||200000),Number(process.argv[3]||180)),null,2));
