// Reproduce: node research/min_prime_root_gain_prefix_audit.mjs
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),ell=Math.max(1,Math.log(Math.log(B))),T=mode==="gain"?Math.floor(X/Math.pow(Math.log(B),.25)):mode==="short"?B:4*B,D=Math.max(1,Math.floor(T/(mode==="gain"?Math.max(4,ell):8))),Q=Math.ceil(B/Math.log(B)),Y=mode==="gain"?Math.max(5,Math.ceil(ell)):7;
 const lim=7*X+5,spf=new Int32Array(lim+1),pr=[];
 for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n<=B&&n%2)pr.push(n);if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)if(!spf[j])spf[j]=n;}
 const mod=(a,m)=>((a%m)+m)%m,gcd=(a,b)=>{while(b){const c=a%b;a=b;b=c;}return a;},ok=(b,msg)=>{if(!b)throw Error(msg);};
 const fs=n=>{const a=[];while(n>1){const p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const rc=new Int32Array(lim+1);function least(C){if(rc[C])return rc[C]-1;let p=0;for(const n of [C-1,C+1])for(const q of fs(n))if(!p||q<p)p=q;rc[C]=p+1;return p;}
 const W=new Map(),Wt=new Map(),Wnew=new Map(),Wr=new Map(),roots=new Map();let N=0,R=0,G=0,events=0,literal=0,cross=0,twins=0,uncrossNonTwin=0,crossCost=0,minCrossCost=Infinity,trimClock=0,ratioClock=0,rankClock=0,smallClock=0,mediumClock=0,highClock=0,mediumZ=0,highHits=0,expHits=0,periodChecks=0,roughChecks=0,rankChecks=0,maxLocalMass=0,maxRootSpan=0,maxRetainedPerLabel=0,rankBands=0,rankLabelCount=0;
 const add=(m,C)=>m.set(C,(m.get(C)||0)+1);
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){
   N++;let C=2*M-2,t=M+2,cut=Math.floor((7*M-1)/4),a=[],by=new Map(),cost=0;
   while(C-(2*M-2)<T){
     let tt=Infinity,p=Infinity,sg=0;
     for(const sigma of [-1,1])for(const q of fs(C+sigma)){const tick=t+1+mod((sigma===-1?0:q+2)-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;sg=sigma;}}
     if(X<=1024){let lt=Infinity,lp=Infinity;for(let u=t+1;u<=cut;u++){const f=fs(gcd(u%2?u-2:u,C+(u%2?1:-1)));if(f.length){lt=u;lp=f[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal gcd");literal++;}
     if(tt>cut)break;
     const r=least(C),v=(C+sg)/p;ok(r>0&&r<=p&&tt-t<=2*r&&Number.isInteger(v)&&v%2===1,"clock quotient");const e={C,p,r,sg,n:(v-1)/2,g:C-(2*M-2)};
     if(!by.has(p))by.set(p,[]);const list=by.get(p);if(list.length&&p>=5)ok(e.n>list[list.length-1].n,"quotient increasing");list.push(e);a.push(e);R+=r;cost+=r;events++;
     t=tt;C+=p-1;ok(C<=2*t,"horizon invariant");
   }
   const gain=C-(2*M-2);G+=gain;ok(gain<T+B&&2*cost<=3*gain,"gain cap");
   if(gain>=T){cross++;crossCost+=cost;minCrossCost=Math.min(minCrossCost,cost);ok(4*cost>=T-6&&2*(t-M-2)>=gain-6,"cross certificate");}
   else if(spf[C-1]===C-1&&spf[C+1]===C+1)twins++;
   else{uncrossNonTwin++;ok(cut-M-2<=2*cost+2*B&&cut-M-2<=3*T+2*B,"noncross no-twin cutoff");}
   let trimmed=0;const candidates=new Map(),bands=new Map();
   for(const [p,list] of by){
     if(p>=Y){
       const f=mode==="gain"?Math.sqrt(Math.log(p)):2,threshold=p/f,z=Math.min(7,p-1,Math.floor(threshold)),qs=pr.filter(q=>q<=z),P=qs.reduce((s,q)=>s*q,1),rho=qs.reduce((s,q)=>s*(q-2),1);
       const allowed=(n,sg)=>qs.every(q=>mod(2*n+1,q)!==0&&mod(p*(2*n+1)-2*sg,q)!==0);
       if(P<=105)for(const sg of [-1,1]){let cnt=0;for(let n=0;n<P;n++)if(allowed(n,sg))cnt++;ok(cnt===rho,"period");}
       const H=list[list.length-1].n-list[0].n+1;let nExp=0;
       for(const e of list){const v=allowed(e.n,e.sg);ok(v===(e.r>z),"rough iff");if(e.r>threshold){nExp++;ok(v,"relative expensive implies rough");}roughChecks++;}
       let cap=0;for(let n=list[0].n;n<=list[list.length-1].n;n++)if(allowed(n,-1)||allowed(n,1))cap++;
       ok(nExp<=cap&&cap<=Math.min(H,2*rho*(Math.floor(H/P)+1)),"quotient capacity");periodChecks++;expHits+=nExp;
     }
     for(const e of list){
       if(e.p>=Q)add(W,e.C);
       if(e.g<D||gain-(e.g+e.p-1)<D){trimClock+=e.r;trimmed+=e.r;continue;}
       if(e.p>=Q)add(Wt,e.C);
       if(p<Y){smallClock+=e.r;continue;}
       const f=mode==="gain"?Math.sqrt(Math.log(p)):2;
       if(e.r<=p/f){ratioClock+=e.r;continue;}
       if(!candidates.has(p))candidates.set(p,[]);candidates.get(p).push(e);
       if(e.p>=Q)add(Wnew,e.C);
     }
   }
   ok(trimmed<=3*(D+B),"two-sided linear trim");
   for(const [p,list] of candidates){
     const band=Math.floor(Math.log2(Math.log(p)));if(!bands.has(band))bands.set(band,[]);
     bands.get(band).push({p,list,weight:p*list.length});
   }
   for(const [band,items] of bands){
     const Ulog=2**band,cap=mode==="gain"?Math.max(1,Math.floor(Ulog**1.5)):1;
     items.sort((a,b)=>b.weight-a.weight||a.p-b.p);rankBands++;let c=0;
     for(let i=0;i<items.length;i++){const {p,list,weight}=items[i];if(i<cap){rankLabelCount++;rankClock+=list.reduce((s,e)=>s+e.r,0);c+=weight;continue;}
       ok(items.length>cap&&weight*cap<=items.slice(0,cap).reduce((s,x)=>s+x.weight,0),"rank charge");rankChecks++;
       maxRetainedPerLabel=Math.max(maxRetainedPerLabel,list.length);if(p<Q)mediumZ+=list.length**2;
       for(const e of list){if(p<Q)mediumClock+=e.r;else{highClock+=e.r;highHits++;add(Wr,e.C);let r=roots.get(e.C);if(!r){r={min:M,max:M,n:0};roots.set(e.C,r);}r.min=Math.min(r.min,M);r.max=Math.max(r.max,M);r.n++;}}
     }
     ok(c<=1.5*gain,"rank selected budget");
   }
 }
 ok(N===cross+twins+uncrossNonTwin&&R===trimClock+ratioClock+rankClock+smallClock+mediumClock+highClock,"partition");
 for(const [C,r] of roots){ok(2*(r.max-r.min)<T&&r.n===Wr.get(C),"local source support");maxLocalMass=Math.max(maxLocalMass,r.n);maxRootSpan=Math.max(maxRootSpan,r.max-r.min);}
 const energy=m=>[...m].reduce((s,[C,n])=>s+BigInt(least(C))*BigInt(n)**2n,0n).toString();
 return {mode,X,B,T,D,Q,Y,N,R,G,events,literal,cross,twins,uncrossNonTwin,crossCost,minCrossCost:Number.isFinite(minCrossCost)?minCrossCost:null,trimClock,ratioClock,rankClock,smallClock,mediumClock,highClock,mediumZ,highHits,expHits,periodChecks,roughChecks,rankChecks,maxLocalMass,maxRootSpan,maxRetainedPerLabel,rankBands,rankLabelCount,E:energy(W),Etrim:energy(Wt),Eratio:energy(Wnew),Erank:energy(Wr)};
}
const xs=process.argv.slice(2).map(Number),windows=xs.length?xs:[256,1024,4096,16384,65536,262144];for(const mode of ['gain','short','four'])for(const X of windows)console.log(JSON.stringify(audit(X,mode)));
