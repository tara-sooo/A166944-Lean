// Reproduce: node research/min_prime_root_exit_reallocation_audit.mjs
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
 const H=T+B,y=3,L=6,analytic=mode==="analytic",Qm=analytic?Q:Math.max(7,Math.ceil(B/(mode==="wide"?4:8))),k=analytic?Math.max(1,Math.floor(u**.25)):mode==="wide"?2:(mode==="phase"||mode==="stress")?3:1,scale=analytic?u**1.5:(mode==="phase"||mode==="stress")?0.5:0.125;
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
 const bcap=r=>{const p=P(r),lp=Math.log(2*p),ep=1+Math.log(lp);return Math.max(1,Math.floor(analytic?(B/p)**2/u**1.5*Math.sqrt(p/Qm)*(p>=u*u?lp**6/ep**4:lp**2/(1+L/p)**2):mode==="stress"?2:c(r)*2*Math.sqrt(Qm/p)));};
 const subcap=(r,d)=>Math.max(1,Math.floor(bcap(r)/(Math.ceil(H/(2*d))+2)));
 const ell0=1+Math.log(u),quota=r=>analytic?Math.max(1,Math.ceil(u**1.5/ell0**1.25+u**1.5*Math.log(2*P(r))*(1+L/P(r))*(P(r)/Qm)**.25/ell0)):k;
 const d=cellWidths.at(-1),sourceCell=M=>Math.floor((M-X)/d),mcell=r=>subcap(r,d);
 const pairMap=new Map(),byRoot=new Map();let first=0,short=0,long=0,medium=0,edges=0,shortEdges=0,fullPairs=0,selectedPairs=0,maxK=0;
 for(const es of input){if(!es.length)continue;const M=es[0].M,ar=roots.get(M),idx=new Map(ar.map((e,i)=>[e.C,i])),cells=new Map();byRoot.set(M,new Map(es.map(e=>[e.C,e])));
   for(const e of es){const ky=e.r+":"+blk(e.r,e.C);if(!cells.has(ky))cells.set(ky,[]);cells.get(ky).push(e);medium+=e.r+e.low;}
   for(const g of cells.values()){const r=g[0].r,kk=quota(r);maxK=Math.max(maxK,kk);fullPairs+=g.length*(g.length-1)/2;
     for(let i=0;i<g.length;i++){const e=g[i],cost=e.r+e.low;if(i<kk){first+=cost;continue;}let paid=0;
       for(let j=i-kk;j<i;j++){const C=g[j].C,E=e.C,amount=cost/kk;paid+=amount;edges++;if(E-C<=D(r)){short+=amount;shortEdges++;continue;}long+=amount;selectedPairs++;
         const ky=r+":"+C+":"+E;if(!pairMap.has(ky))pairMap.set(ky,[]);pairMap.get(ky).push({M,t:ar[idx.get(C)].t,s:ar[idx.get(E)].t,out:ar[idx.get(E)+1].t,J:ar[idx.get(E)+1].C,p:e.p,amount});
       }ok(Math.abs(paid-cost)<1e-7,"exact quota allocation");
     }
   }
 }
 const near=(x,y)=>Math.abs(x-y)<=1e-6*Math.max(1,Math.abs(x),Math.abs(y));
 ok(near(medium,first+short+long)&&medium===mediumClock+mediumLow&&selectedPairs+shortEdges===edges&&edges<=fullPairs,"quota partition");
 let band=0,cellCost=0,res=0,tiny=0,close=0,far=0,heavy=0,already=0,immediate=0,heavyFocal=0,smallFocal=0,tinyFocal=0,groups=0,cellChecks=0,degreeChecks=0,partnerChecks=0,maxDegree=0,maxRatio=0,maxMult=0,keys=0,maxKappa=0;
 const kappa=r=>analytic?Math.ceil(u**.125*u/Math.log(2*P(r))):mode==="stress"?2:mode==="short"?3:4;
 const eta=r=>analytic?u**(1/32):mode==="stress"?4:2;
 const gap=r=>analytic?Math.floor(P(r)*u**(1/16)):mode==="short"||mode==="stress"?1:Math.max(1,Math.floor(P(r)/2));
 const outKey=a=>a.out+":"+a.J;
 const endpoints=new Map(),pairCharges=new Map();
 for(const [key,ar] of pairMap){const [r,C,E]=key.split(":").map(Number),v=ar.length;
   if(v<=bcap(r)){for(const a of ar)band+=a.amount;continue;}
   const keep=new Set(ar.map(a=>a.M));for(const width of cellWidths){const cc=new Map();for(const a of ar){let j=Math.floor((a.M-X)/width);if(!cc.has(j))cc.set(j,[]);cc.get(j).push(a);}ok(cc.size<=Math.ceil(H/(2*width))+2,"source locality");for(const g of cc.values()){cellChecks++;if(g.length<=subcap(r,width))for(const a of g)keep.delete(a.M);}}
   for(const a of ar)if(!keep.has(a.M))cellCost+=a.amount;if(!keep.size)continue;keys++;
   const cc=new Map();for(const a of ar){let j=sourceCell(a.M);if(!cc.has(j))cc.set(j,[]);cc.get(j).push(a);}
   for(const g of cc.values()){
     if(!g.some(a=>keep.has(a.M)))continue;
     const n=g.length,K=kappa(r),U=eta(r),D0=gap(r),m=mcell(r);maxKappa=Math.max(K,maxKappa);ok(n>m,"dense cell");
     const gg=new Map();for(const a of g){let ky=outKey(a);if(!gg.has(ky))gg.set(ky,[]);gg.get(ky).push(a);ok(a.out>a.s&&a.out-a.s<=2*r&&a.J===E+a.p-1,"actual exit");}
     const gs=[...gg.values()];groups+=gs.length;
     const large=ar=>ar.length>=Math.max(2,n/K),pool=gs.filter(ar=>!large(ar)).flat(),s=pool.length;
     const degBound=fs(E-1).concat(fs(E+1)).filter(p=>p>=r&&p<Qm).reduce((z,p)=>z+Math.floor(D0/p)+1,0);
     const byTick=new Map();for(const a of g){if(byTick.has(a.out))ok(byTick.get(a.out)===a.J,"unique selected label");else byTick.set(a.out,a.J);}
     for(const ar of gs){const q=ar[0],d=gs.filter(br=>Math.abs(br[0].out-q.out)<=D0).length;ok(d<=degBound,"exit degree");degreeChecks++;maxDegree=Math.max(maxDegree,d);}
     for(const a of g){if(!keep.has(a.M))continue;res+=a.amount;const ag=gg.get(outKey(a)),big=large(ag);
       if(!big&&(s<2||s<n/U)){tiny+=a.amount;tinyFocal++;continue;}
       const partners=big?ag:pool;ok(partners.length>=2&&partners.includes(a),"partner pool");let paid=0,nearWeight=0;
       if(big){heavyFocal++;heavy+=a.amount;}else smallFocal++;
       for(const b of partners){if(a.M===b.M)continue;const w=a.amount/(partners.length-1);paid+=w;partnerChecks++;
         let cls;if(big){ok(a.out===b.out&&a.J===b.J,"shared successor");if(a.s===b.s){already+=w;cls="already";}else{immediate+=w;cls="immediate";}}
         else if(Math.abs(a.out-b.out)<=D0){close+=w;nearWeight+=w;cls="close";}
         else{far+=w;cls="far";ok(a.s!==b.s&&Math.abs(a.s-b.s)>D0-2*r,"far input lag");}
         if(cls==="close")continue;
         const id=r+":"+E+":"+a.M+":"+b.M,v=endpoints.get(id)||{w:0,n:0,cls,r,E,M:a.M,Mp:b.M};ok(v.cls===cls,"fixed endpoint class");v.w+=w;v.n++;endpoints.set(id,v);
       }
       ok(near(paid,a.amount),"allocation");
       if(!big){const nb=pool.filter(b=>b.M!==a.M&&Math.abs(a.out-b.out)<=D0).length;ok(near(nearWeight,a.amount*nb/(s-1))&&nb<=degBound*Math.max(1,n/K),"near pool capacity");maxRatio=Math.max(maxRatio,nb/(s-1));}
     }
   }
 }
 // For an endpoint pair, the class is fixed among kept edges: identical exit
 // cannot be far; identical exit is either already or immediate by input time.
 let endpointBound=0,tailChecks=0,immediateChecks=0,smallAlready=0,smallImmediate=0,largeAlready=0,largeImmediate=0,alreadyPairs=0,immediatePairs=0,maxTail=0,firstSmall=0,firstLarge=0;
 const weight=r=>wt(r)*Math.max(2*kappa(r),2*eta(r))/mcell(r);
 const tails=new Map();for(const [M,ar] of roots){let t=0,aa=new Float64Array(ar.length);const em=byRoot.get(M);for(let i=ar.length-1;i>=0;i--){let e=em?.get(ar[i].C);if(e)t+=weight(e.r);aa[i]=t;}tails.set(M,aa);maxTail=Math.max(maxTail,t);}
 for(const v of endpoints.values()){const bound=weight(v.r);ok(v.n<=quota(v.r)&&v.w<=bound+1e-6,"endpoint quota bound");endpointBound+=bound;maxMult=Math.max(maxMult,v.n);if(v.cls==="far")continue;
   let M=Math.min(v.M,v.Mp),Mp=Math.max(v.M,v.Mp),id=M+":"+Mp,q=pairCharges.get(id)||{M,Mp,a:0,i:0,pre:null};if(v.cls==="already")q.a+=v.w;else{q.i+=v.w;if(q.pre!==null)ok(q.pre===v.E,"unique immediate merger horizon");q.pre=v.E;}pairCharges.set(id,q);
 }
 const ma=mode==="analytic"?Math.max(1,Math.floor(u**6/ell0**4)):mode==="short"?4:8,mb=analytic?Math.max(ma,Math.floor(H/Qm*ma)):ma*3;
 for(const q of pairCharges.values()){
   const a=roots.get(q.M),b=roots.get(q.Mp);let i=0,j=0;while(i<a.length&&j<b.length){if(a[i].C<b[j].C)i++;else if(a[i].C>b[j].C)j++;else if(a[i].t===b[j].t)break;else{i++;j++;}}
   ok(i<a.length&&j<b.length,"first physical meeting");const es=vertices.get(a[i].C+":"+a[i].t),local=es.filter(e=>sourceCell(e.M)===sourceCell(q.M)).length;
   if(q.a){tailChecks++;ok(q.a<=2*Math.min(tails.get(q.M)[i],tails.get(q.Mp)[j])+1e-6,"already tail bound");if(local<=ma){smallAlready+=q.a;alreadyPairs++;}else largeAlready+=q.a;}
   if(q.i){immediateChecks++;ok(i>0&&j>0&&a[i-1].C===q.pre&&b[j-1].C===q.pre&&a[i-1].t!==b[j-1].t,"immediate first meeting");ok(q.i<=2*weight(a[i-1].r)+1e-6,"one immediate weight");if(local<=mb){smallImmediate+=q.i;immediatePairs++;}else largeImmediate+=q.i;}
 }
 const potential=m=>{const f=n=>n<=m?n*n:2*m*n-m*m;let D=0,loss=0,start=0,count=0;for(const es of vertices.values()){const cc=new Map();for(const e of es){let c=sourceCell(e.M);if(!cc.has(c))cc.set(c,[]);cc.get(c).push(e);}for(const g of cc.values()){let n=g.length,ends=0,pr=new Map();for(const e of g){let k=e.prev?e.prev.C+":"+e.prev.t:"root:"+e.M;pr.set(k,(pr.get(k)||0)+1);if(!e.next)ends++;if(!e.prev)start++;}const ss=[...pr.values()];D+=f(n)-ss.reduce((s,x)=>s+f(x),0);loss+=f(n)-f(n-ends);if(n<=m)count+=(n*n-ss.reduce((s,x)=>s+x*x,0))/2;}}ok(D===loss-start&&D<=2*m*N&&count<=m*N,"restricted potential");return {m,D,loss,start,count};};
 // Independently exercise immediate synchronizations on all original medium events,
 // even if the preceding quota and arithmetic caps leave none in the selected ledger.
 const exits=new Map();for(const [M,ar] of roots){for(const e of ar){if(e.p<=y||e.p>=Qm)continue;const id=e.C+":"+e.next.t+":"+e.next.C;if(!exits.has(id))exits.set(id,[]);exits.get(id).push(e);}}
 const immediateOracle=new Set();let oracleChecks=0,oracleLocal=0;
 for(const g of exits.values())for(let i=0;i<g.length;i++)for(let j=i+1;j<g.length;j++){const a=g[i],b=g[j];if(a.t===b.t)continue;const id=Math.min(a.M,b.M)+":"+Math.max(a.M,b.M);ok(!immediateOracle.has(id),"unique immediate merger on full medium list");immediateOracle.add(id);oracleChecks++;
   ok(a.next.t===b.next.t&&a.next.C===b.next.C&&a.next.prev===a&&b.next.prev===b,"common actual successor");if(sourceCell(a.M)===sourceCell(b.M))oracleLocal++;}
 for(const [id,q] of pairCharges)if(q.i)ok(immediateOracle.has(id),"selected immediate oracle");
 const pa=potential(ma),pb=potential(mb);ok(alreadyPairs<=pa.count&&immediatePairs<=pb.count,"first pair caps");
 ok(near(long,band+cellCost+res)&&near(res,tiny+close+far+heavy)&&near(heavy,already+immediate)&&near(already,smallAlready+largeAlready)&&near(immediate,smallImmediate+largeImmediate),"allocation partition");
 return {mode,X,B,T,Qm,N,literal,medium,first,short,long,edges,fullPairs,band,cellCost,res,tiny,close,far,heavy,already,immediate,smallAlready,smallImmediate,largeAlready,largeImmediate,final:far+largeAlready+largeImmediate,heavyFocal,smallFocal,tinyFocal,groups,keys,cellChecks,degreeChecks,partnerChecks,maxDegree,maxRatio,maxMult,maxKappa,endpointBound,tailChecks,immediateChecks,alreadyPairs,immediatePairs,oracleChecks,oracleLocal,pa,pb};
}

const xs=process.argv.slice(2).map(Number);for(const mode of ['short','wide','analytic','phase','stress'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
