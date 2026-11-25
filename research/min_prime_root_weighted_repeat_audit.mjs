// Reproduce: node research/min_prime_root_weighted_repeat_audit.mjs
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),T=mode==="analytic"?Math.floor(X/u**.25):mode==="short"?B:4*B,Q=mode==="wide"?7:Math.max(5,Math.ceil(B/(mode==="analytic"?u:8))),m0=mode==="analytic"?Math.max(1,Math.floor(B*u**1.5)):mode==="short"?4:8,lim=7*X+5,spf=new Int32Array(lim+1),ok=(x,s)=>{if(!x)throw Error(s);},mod=(a,b)=>((a%b)+b)%b,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c;}return a;};
 for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)spf[j]=spf[j]||n;}
 const fs=n=>{let a=[];while(n>1){let p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const vertices=new Map(),roots=new Map();let N=0,R=0,G=0,events=0,high=0,literal=0,hiR=0;
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){N++;let C=2*M-2,t=M+2,cut=Math.floor((7*M-1)/4),a=[],cost=0;
  while(true){let e={M,C,t,p:0,r:0,w:0,prev:a.length?a[a.length-1]:null};a.push(e);let id=C+":"+t;if(!vertices.has(id))vertices.set(id,[]);vertices.get(id).push(e);
   if(C-(2*M-2)>=T)break;
   let tt=Infinity,p=Infinity;for(const s of [-1,1])for(const q of fs(C+s)){let tick=t+1+mod((s===-1?0:q+2)-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;}}
   if(X<=1024){let lt=Infinity,lp=Infinity;for(let s=t+1;s<=cut;s++){let f=fs(gcd(s%2?s-2:s,C+(s%2?1:-1)));if(f.length){lt=s;lp=f[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal");literal++;}
   if(tt>cut)break;
   let r=Math.min(...fs(C-1),...fs(C+1));ok(r<=p&&tt-t<=2*r,"clock");e.p=p;e.r=r;cost+=r;events++;if(p>=Q&&r>p/(mode==="analytic"?Math.sqrt(Math.log(p)):2)){e.w=r;hiR+=r;high++;}
   t=tt;C+=p-1;ok(C<=2*t,"horizon");
  }
  let gain=C-(2*M-2);R+=cost;G+=gain;ok(gain<T+B&&2*cost<=3*gain,"gain");
  let tail=0;for(let i=a.length-1;i>=0;i--){tail+=a[i].w;a[i].tail=tail;a[i].next=a[i+1]||null;}roots.set(M,a);
 }
 const H=T+B,y=3,L=6,analytic=mode==="analytic",Qm=analytic?Q:Math.max(7,Math.ceil(B/(mode==="wide"?4:8))),k=analytic?Math.max(1,Math.floor(u**.25)):mode==="wide"?2:1,scale=analytic?u**1.5:0.125;
 const pr=[];for(let p=3;p<Qm&&p<=B;p+=2)if(spf[p]===p)pr.push(p);
 const wt=r=>r+1.5*L,A=r=>Math.ceil(wt(r)**2*scale),blk=(r,C)=>Math.floor(C/A(r)),cap=r=>analytic?Math.max(1,Math.floor(Math.log(r)**6)):mode==="wide"?4:2;
 let initialLow=0,highLow=0,mediumClock=0,mediumLow=0,lowBlocks=0,lowMax=0,mediumTags=0,lowTotal=0,quotientChecks=0;
 const input=[];for(const [M,ar] of roots){
   const es=[];let anchor=null,lowGain=0,lowCost=0;
   function endLow(){if(!lowGain)return;ok(lowGain<L,"LOW block barrier");lowBlocks++;lowMax=Math.max(lowMax,lowGain);if(!anchor)initialLow+=lowCost;else if(anchor.p>=Qm)highLow+=lowCost;else{anchor.low=lowCost;mediumLow+=lowCost;}lowGain=0;lowCost=0;}
   for(const e of ar){if(!e.p)break;if(e.p<=y){lowGain+=e.p-1;lowCost+=e.r;lowTotal+=e.r;continue;}endLow();anchor={M,C:e.C,p:e.p,r:e.r,low:0};if(e.p<Qm){es.push(anchor);mediumClock+=e.r;mediumTags++;const sig=(e.C-1)%e.r===0?-1:1;ok((e.C+sig)%e.r===0&&(e.C+sig)/e.r%2===1,"least quotient");const q=(e.C+sig)/e.r;for(const s of fs(e.C-1).concat(fs(e.C+1)))ok(s>=e.r,"least factor");ok(q*e.r-2*sig===e.C-sig,"quotient second form");quotientChecks++;}}
   endLow();input.push(es);
 }
 ok(lowTotal===initialLow+highLow+mediumLow,"LOW assignment");
 const ell=1+Math.log(u),P=r=>2**Math.floor(Math.log2(r)),lambda=r=>Math.sqrt(P(r)/Qm)*Math.log(Qm)/Math.log(2*P(r));
 const D=r=>Math.max(1,Math.floor(analytic?r*u**1.5*Math.log(2+Math.min(r,u))**2/ell**1.5:r*(mode==="wide"?6:3)));
 const c=r=>Math.max(1,Math.floor(cap(r)/lambda(r)));
 const arith=new Map(),byPair=new Map(),bands=new Map(),maxCap=new Map(),pc=new Map(),get=r=>{let b=P(r);if(!bands.has(b))bands.set(b,{P:b,lambda:lambda(r),n:0,gain:0,first:0,rem:0,actualCoeff:0,coeff:0,trim:0,short:0,long:0,capped:0,heavy:0,nearCapacity:0,keys:0});return bands.get(b);};
 for(const r of pr)get(r).coeff+=N*wt(r)**2*(Math.ceil(H/A(r))+2);
 for(let C=2*X-2;C<=7*X;C+=2){const f=fs(C-1).concat(fs(C+1));if(!f.length)continue;const r=Math.min(...f);if(r>=Qm)continue;if(!arith.has(r))arith.set(r,[]);arith.get(r).push(C);}
 const ub=(a,x)=>{let l=0,h=a.length;while(l<h){let m=(l+h)>>1;if(a[m]<=x)l=m+1;else h=m;}return l;};
 let exact=0,nearChecks=0,wordChecks=0,nearKeys=0,longKeys=0,cappedKeys=0,heavyKeys=0,maxNear=0,maxV=0,nontrivialShort=0;
 for(const es of input){const cells=new Map(),idx=new Map();if(es.length){const a=roots.get(es[0].M);for(let i=0;i<a.length;i++)idx.set(a[i].C,i);}
   for(const e of es){const b=get(e.r),key=e.r+":"+blk(e.r,e.C);if(!cells.has(key))cells.set(key,[]);cells.get(key).push(e);b.n++;b.gain+=e.p-1;const aa=arith.get(e.r);const ky=e.r+":"+e.C;if(!pc.has(ky))pc.set(ky,ub(aa,e.C+D(e.r))-ub(aa,e.C));const n=pc.get(ky);b.nearCapacity+=2*n;maxNear=Math.max(maxNear,n);nearChecks++;}
   for(const g of cells.values()){const r=g[0].r,b=get(r),n=g.length;b.actualCoeff+=wt(r)**2;b.trim+=Math.max(0,n-k)**2;
     for(let i=0;i<n;i++){const e=g[i];ok(e.r+e.low<=wt(r),"weight");if(i<k)b.first+=e.r+e.low;else b.rem+=e.r+e.low;
       let nr=0;for(let j=i+1;j<n;j++){const h=g[j].C-e.C,near=h<=D(r);ok(h<A(r)&&h>0,"cell gap");exact+=2;if(near){nr++;b.short+=2;const a=roots.get(e.M),s=idx.get(e.C),t=idx.get(g[j].C);let gain=0;for(let v=s;v<t;v++){gain+=a[v].p-1;ok(a[v].p-1<=h,"donor bound");}ok(gain===h,"actual word gain");wordChecks++;if(t-s>1)nontrivialShort++;}else b.long+=2;
         const key=r+":"+e.C+":"+g[j].C;byPair.set(key,(byPair.get(key)||0)+1);
       }ok(nr<=pc.get(r+":"+e.C),"short repeat capacity");
     }
   }
 }
 for(const [key,v] of byPair){const [r,C,E]=key.split(":").map(Number),b=get(r);b.keys++;maxV=Math.max(maxV,v);if(E-C<=D(r)){nearKeys++;continue;}longKeys++;if(v<=c(r)){b.capped+=2*v;cappedKeys++;}else{b.heavy+=2*v;heavyKeys++;}}
 let short=0,long=0,capped=0,heavy=0,weightedCap=0,weightedHeavy=0,weightedLong=0,coeffW=0,shortBound=0,shortArithmeticBound=0,totalRem=0,totalFirst=0,trim=0,gain=0;
 for(const b of bands.values()){ok(b.long===b.capped+b.heavy&&b.trim<=b.short+b.long&&b.short<=b.nearCapacity&&b.n*(b.P-1)<=b.gain&&b.actualCoeff<=b.coeff,"band ledger");
   ok(BigInt(b.rem)**2n<=BigInt(b.actualCoeff)*BigInt(b.trim),"band Cauchy");
   short+=b.short;long+=b.long;capped+=b.capped;heavy+=b.heavy;weightedCap+=b.lambda*b.capped;weightedHeavy+=b.lambda*b.heavy;weightedLong+=b.lambda*b.long;coeffW+=b.coeff/b.lambda;shortBound+=Math.sqrt(b.coeff*b.short);shortArithmeticBound+=Math.sqrt(b.coeff*b.nearCapacity);totalRem+=b.rem;totalFirst+=b.first;trim+=b.trim;gain+=b.gain;
 }
 ok(exact===short+long&&long===capped+heavy&&totalFirst+totalRem===mediumClock+mediumLow&&gain<=G,"partition");
 ok(Math.abs(weightedLong-weightedCap-weightedHeavy)<1e-5*Math.max(1,weightedLong),"weighted partition");
 ok(totalRem<=shortBound+Math.sqrt(coeffW*weightedLong)+1e-6&&totalRem<=shortArithmeticBound+Math.sqrt(coeffW*weightedCap)+Math.sqrt(coeffW*weightedHeavy)+1e-6,"split Cauchy");
 return {mode,X,B,T,Qm,N,R,G,events,literal,mediumTags,mediumClock,mediumLow,k,scale,exact,short,long,capped,heavy,trim,totalRem,totalFirst,weightedLong,weightedCap,weightedHeavy,coeffW,shortBound,shortArithmeticBound,nearChecks,wordChecks,nontrivialShort,nearKeys,longKeys,cappedKeys,heavyKeys,maxNear,maxV,bands:[...bands.values()]};
}

const xs=process.argv.slice(2).map(Number);for(const mode of ['short','wide','analytic'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
