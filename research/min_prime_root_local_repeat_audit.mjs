// Reproduce: node research/min_prime_root_local_repeat_audit.mjs
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
 const C1=2*X-2,C2=7*X,arithmetic=new Map(),rmap=new Uint16Array(C2+1);
 for(let C=C1;C<=C2;C+=2){const f=fs(C-1).concat(fs(C+1));if(!f.length)continue;const r=Math.min(...f);rmap[C]=r;if(r>=Qm)continue;const key=r+":"+blk(r,C);arithmetic.set(key,(arithmetic.get(key)||0)+1);}
 let arithmeticPairs=0;for(const n of arithmetic.values())arithmeticPairs+=n*(n-1)/2;
 function ledger(useR){
   let total=0,first=0,firstBound=0,res=0,off=0,trimZ=0,globalOff=0,groups=0,actualCoeff=0,budget=0,capped=0,heavy=0,keys=0,heavyKeys=0,maximum=0,residueChecks=0,sameSide=0,oppositeSide=0;
   const byPair=new Map(),hist=new Map();
   for(const es of input){
     const cells=new Map(),glob=new Map();for(const e of es){const r=useR?e.r:e.p,ky=r+":"+blk(r,e.C);if(!cells.has(ky))cells.set(ky,[]);cells.get(ky).push(e);glob.set(r,(glob.get(r)||0)+1);}
     for(const n of glob.values())globalOff+=n*(n-1);
     for(const [ky,g] of cells){const r=Number(ky.split(":")[0]),n=g.length,w=wt(r);groups++;actualCoeff+=w*w;firstBound+=w*Math.min(k,n);off+=n*(n-1);trimZ+=Math.max(0,n-k)**2;ok(n<=k||n-k<=n-1,"rank trim");
       for(let i=0;i<n;i++){const e=g[i];ok(e.r+e.low<=w,"attached weight");total+=e.r+e.low;if(i<k)first+=e.r+e.low;else res+=e.r+e.low;}
       for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){const C=g[i].C,D=g[j].C,h=D-C;ok(h>0&&h<A(r)&&blk(r,C)===blk(r,D),"local pair");if(useR){const sig=(C-1)%r===0?-1:1,tau=(D-1)%r===0?-1:1;ok((h+tau-sig)%r===0&&rmap[C]===r&&rmap[D]===r,"repeat quotient congruence");if(sig===tau)sameSide++;else oppositeSide++;if(r>3)ok(h%6===0,"rough spacing");}
         const key=r+":"+C+":"+D;byPair.set(key,(byPair.get(key)||0)+1);
       }
     }
   }
   const formula=pr.reduce((s,r)=>s+wt(r)**2*(Math.ceil(H/A(r))+2),0)*N;const firstEnvelope=pr.reduce((s,r)=>s+wt(r)*(Math.ceil(H/A(r))+2),0)*N*k;
   ok(total===mediumClock+mediumLow&&total===first+res&&first<=firstBound&&firstBound<=firstEnvelope&&actualCoeff<=formula&&trimZ<=off&&off<=globalOff,"clock moment ledger");
   ok(BigInt(res)**2n<=BigInt(actualCoeff)*BigInt(trimZ)&&BigInt(res)**2n<=BigInt(formula)*BigInt(off),"Cauchy");
   let sum=0;for(const [key,n] of byPair){const [r,C,D]=key.split(":").map(Number),h=D-C;keys++;sum+=n;maximum=Math.max(maximum,n);if(n<=cap(r))capped+=2*n;else{heavy+=2*n;heavyKeys++;}
     const j=Math.floor(Math.log2(r));if(!hist.has(j))hist.set(j,{r:2**j,keys:0,off:0,capped:0,heavy:0});const v=hist.get(j);v.keys++;v.off+=2*n;if(n<=cap(r))v.capped+=2*n;else v.heavy+=2*n;
     if(useR&&r>3){for(const q of [5,7,11,13,17,19,23,29,31])if(q<r&&h%q&&(h-2)%q&&(h+2)%q){let count=0;const sig=(C-1)%r===0?-1:1;for(let z=0;z<q;z++){const d=r*(2*z+1)-sig;if([d-1,d+1,d+h-1,d+h+1].some(n=>mod(n,q)===0))count++;}ok(count===4,"four distinct quotient residues");residueChecks++;}}
   }
   ok(2*sum===off&&off===capped+heavy,"overlap moment identity");if(useR)ok(keys<=arithmeticPairs,"arithmetic support");
   return {kind:useR?"r":"p",total,first,firstBound,res,off,trimZ,globalOff,groups,actualCoeff,formula,firstEnvelope,capped,heavy,keys,heavyKeys,maximum,residueChecks,sameSide,oppositeSide,hist:[...hist.values()]};
 }
 return {mode,X,B,T,Qm,N,R,G,events,literal,y,L,k,scale,mediumClock,mediumLow,mediumTags,lowTotal,initialLow,highLow,lowBlocks,lowMax,quotientChecks,arithmeticPairs,arithmeticCells:arithmetic.size,r:ledger(true),p:ledger(false)};
}

const xs=process.argv.slice(2).map(Number);for(const mode of ['short','wide','analytic'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
