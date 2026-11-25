// Reproduce: node research/min_prime_root_quota_transfer_audit.mjs
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
 const H=T+B,y=3,L=6,analytic=mode==="analytic",Qm=analytic?Q:Math.max(7,Math.ceil(B/(mode==="wide"?4:8))),k=analytic?Math.max(1,Math.floor(u**.25)):mode==="wide"?2:mode==="phase"?3:1,scale=analytic?u**1.5:mode==="phase"?0.5:0.125;
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
 const cellWidths=analytic?[Math.ceil(H),Math.ceil(H/Math.max(1,u**.125)),Math.ceil(H/Math.max(1,u**.25))]:[Math.ceil(H),Math.ceil(H/2),Math.ceil(H/4)];
 const bcap=r=>{const p=P(r),lp=Math.log(2*p),ep=1+Math.log(lp);return Math.max(1,Math.floor(analytic?(B/p)**2/u**1.5*Math.sqrt(p/Qm)*(p>=u*u?lp**6/ep**4:lp**2/(1+L/p)**2):c(r)*2*Math.sqrt(Qm/p)));};
 const subcap=(r,d)=>Math.max(1,Math.floor(bcap(r)/(Math.ceil(H/(2*d))+2)));
 const ell0=1+Math.log(u),quota=r=>analytic?Math.max(1,Math.ceil(u**1.5/ell0**1.25+u**1.5*Math.log(2*P(r))*(1+L/P(r))*(P(r)/Qm)**.25/ell0)):k;
 const d=cellWidths.at(-1),sourceCell=M=>Math.floor((M-X)/d),mcell=r=>subcap(r,d);
 const pairMap=new Map(),byRoot=new Map();let first=0,short=0,long=0,medium=0,edges=0,shortEdges=0,fullPairs=0,selectedPairs=0,maxK=0;
 for(const es of input){if(!es.length)continue;const M=es[0].M,ar=roots.get(M),idx=new Map(ar.map((e,i)=>[e.C,i])),cells=new Map();byRoot.set(M,new Map(es.map(e=>[e.C,e])));
   for(const e of es){const ky=e.r+":"+blk(e.r,e.C);if(!cells.has(ky))cells.set(ky,[]);cells.get(ky).push(e);medium+=e.r+e.low;}
   for(const g of cells.values()){const r=g[0].r,kk=quota(r);maxK=Math.max(maxK,kk);fullPairs+=g.length*(g.length-1)/2;
     for(let i=0;i<g.length;i++){const e=g[i],cost=e.r+e.low;if(i<kk){first+=cost;continue;}let paid=0;
       for(let j=i-kk;j<i;j++){const C=g[j].C,E=e.C,amount=cost/kk;paid+=amount;edges++;if(E-C<=D(r)){short+=amount;shortEdges++;continue;}long+=amount;selectedPairs++;
         const ky=r+":"+C+":"+E;if(!pairMap.has(ky))pairMap.set(ky,[]);pairMap.get(ky).push({M,t:ar[idx.get(C)].t,s:ar[idx.get(E)].t,amount});
       }ok(Math.abs(paid-cost)<1e-7,"exact quota allocation");
     }
   }
 }
 const near=(x,y)=>Math.abs(x-y)<=1e-6*Math.max(1,Math.abs(x),Math.abs(y));
 ok(near(medium,first+short+long)&&medium===mediumClock+mediumLow&&selectedPairs+shortEdges===edges&&edges<=fullPairs,"quota partition");
 let band=0,cellCost=0,res=0,early=0,newSync=0,async=0,phaseChecks=0,cellChecks=0,finalKeys=0,partnerEdges=0;
 const endpoint=new Map(),syncPair=new Map();
 for(const [key,ar] of pairMap){const [r,C,E]=key.split(":").map(Number),v=ar.length;
   if(v<=bcap(r)){for(const a of ar)band+=a.amount;continue;}
   let keep=new Set(ar.map(a=>a.M));
   for(const width of cellWidths){const cells=new Map();for(const a of ar){const i=Math.floor((a.M-X)/width);if(!cells.has(i))cells.set(i,[]);cells.get(i).push(a);}
     ok(cells.size<=Math.ceil(H/(2*width))+2,"cell locality");for(const g of cells.values()){cellChecks++;if(g.length<=subcap(r,width))for(const a of g)keep.delete(a.M);}
   }
   for(const a of ar)if(!keep.has(a.M))cellCost+=a.amount;
   if(!keep.size)continue;finalKeys++;
   const cells=new Map();for(const a of ar){let i=sourceCell(a.M);if(!cells.has(i))cells.set(i,[]);cells.get(i).push(a);}
   for(const g of cells.values()){const n=g.length;for(const a of g){if(!keep.has(a.M))continue;ok(n>mcell(r),"dense quota cell");res+=a.amount;let paid=0;
     for(const b of g){if(b.M===a.M)continue;const w=a.amount/(n-1);paid+=w;partnerEdges++;const same=a.s===b.s;ok(a.t!==b.t||same,"phase coarsening");if(a.t===b.t)early+=w;else if(same)newSync+=w;else async+=w;
       const id=r+":"+E+":"+a.M+":"+b.M,old=endpoint.get(id)||{w:0,n:0,same,r,E,M:a.M,Mp:b.M};old.w+=w;old.n++;ok(old.same===same,"endpoint phase");endpoint.set(id,old);
     }ok(near(paid,a.amount),"normalized focal quota");phaseChecks++;
   }}
 }
 let endpointBound=0,syncBound=0,asyncBound=0,maxMult=0,rankSmall=0,rankLarge=0,cellSmall=0,cellExtra=0,cellLarge=0,cellSmallCount=0,smallPairCount=0,tailBound=0,maxTail=0,tailChecks=0;
 const massCap=mode==="analytic"?Math.max(1,Math.floor(u**6/ell0**4)):mode==="short"?4:8;
 const potf=(n,m)=>n<=m?n*n:2*m*n-m*m;
 const tails=new Map();for(const [M,ar] of roots){let t=0,aa=new Float64Array(ar.length);const em=byRoot.get(M);for(let i=ar.length-1;i>=0;i--){let e=em?.get(ar[i].C);if(e)t+=wt(e.r)/mcell(e.r);aa[i]=t;}tails.set(M,aa);maxTail=Math.max(maxTail,t);}
 for(const v of endpoint.values()){const lim=wt(v.r)/mcell(v.r);ok(v.n<=quota(v.r)&&v.w<=lim+1e-7,"quota endpoint transfer");endpointBound+=lim;maxMult=Math.max(maxMult,v.n);
   if(v.same){syncBound+=lim;const a=Math.min(v.M,v.Mp),b=Math.max(v.M,v.Mp),ky=a+":"+b;syncPair.set(ky,(syncPair.get(ky)||0)+v.w);}else asyncBound+=lim;
 }
 for(const [ky,w] of syncPair){const [M,Mp]=ky.split(":").map(Number),a=roots.get(M),b=roots.get(Mp);let i=0,j=0;while(i<a.length&&j<b.length){if(a[i].C<b[j].C)i++;else if(a[i].C>b[j].C)j++;else if(a[i].t===b[j].t)break;else{i++;j++;}}
   ok(i<a.length&&j<b.length,"first physical meeting");let n=vertices.get(a[i].C+":"+a[i].t).length;const bound=2*Math.min(tails.get(M)[i],tails.get(Mp)[j]);ok(w<=bound+1e-6,"synchronous tail bound");tailBound+=bound;tailChecks++;if(n<=massCap){rankSmall+=w;smallPairCount++;}else rankLarge+=w;
   ok(sourceCell(M)===sourceCell(Mp),"same fixed source cell");
   const local=vertices.get(a[i].C+":"+a[i].t).filter(e=>sourceCell(e.M)===sourceCell(M)).length;
   if(local<=massCap){cellSmall+=w;cellSmallCount++;if(n>massCap)cellExtra+=w;}else cellLarge+=w;
 }
 let pot=0,loss=0,start=0,smallFirst=0;for(const es of vertices.values()){let n=es.length,ends=0;const g=new Map();for(const e of es){let ky=e.prev?e.prev.C+":"+e.prev.t:"root:"+e.M;g.set(ky,(g.get(ky)||0)+1);if(!e.next)ends++;if(!e.prev)start++;}
   const ss=[...g.values()],dd=potf(n,massCap)-ss.reduce((a,b)=>a+potf(b,massCap),0);pot+=dd;loss+=potf(n,massCap)-potf(n-ends,massCap);if(n<=massCap)smallFirst+=(n*n-ss.reduce((a,b)=>a+b*b,0))/2;
 }
 ok(pot===loss-start&&pot<=2*massCap*N&&smallFirst<=massCap*N&&smallPairCount<=smallFirst,"small merger potential");
 let cellPot=0,cellLoss=0,cellStart=0,cellSmallFirst=0;
 for(const es of vertices.values()){const cc=new Map();for(const e of es){const c=sourceCell(e.M);if(!cc.has(c))cc.set(c,[]);cc.get(c).push(e);}
   for(const ar of cc.values()){const n=ar.length,g=new Map();let ends=0;for(const e of ar){const ky=e.prev?e.prev.C+":"+e.prev.t:"root:"+e.M;g.set(ky,(g.get(ky)||0)+1);if(!e.next)ends++;if(!e.prev)cellStart++;}
     const ss=[...g.values()];cellPot+=potf(n,massCap)-ss.reduce((s,v)=>s+potf(v,massCap),0);cellLoss+=potf(n,massCap)-potf(n-ends,massCap);
     if(n<=massCap)cellSmallFirst+=(n*n-ss.reduce((s,v)=>s+v*v,0))/2;
   }
 }
 ok(cellPot===cellLoss-cellStart&&cellPot<=2*massCap*N&&cellSmallCount<=cellSmallFirst&&cellSmallFirst<=massCap*N,"restricted cell potential");
 ok(near(cellSmall,rankSmall+cellExtra)&&near(cellSmall+cellLarge,early+newSync)&&cellSmall<=2*massCap*N*maxTail+1e-6,"restricted tail transfer");
 ok(near(long,band+cellCost+res)&&near(res,early+newSync+async)&&near(early+newSync,rankSmall+rankLarge)&&res<=endpointBound+1e-6&&rankSmall<=2*massCap*N*maxTail+1e-6,"global transfer partition");
 return {mode,X,B,T,Qm,N,events,literal,medium,first,short,long,edges,shortEdges,fullPairs,selectedPairs,maxK,band,cellCost,res,early,newSync,async,phaseChecks,cellChecks,finalKeys,partnerEdges,maxMult,endpointBound,syncBound,asyncBound,rankSmall,rankLarge,smallPairCount,smallFirst,pot,loss,start,massCap,maxTail,tailChecks,tailBound,cellSmall,cellExtra,cellLarge,cellSmallCount,cellPot,cellLoss,cellStart,cellSmallFirst};
}

const xs=process.argv.slice(2).map(Number);for(const mode of ['short','wide','analytic','phase'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
