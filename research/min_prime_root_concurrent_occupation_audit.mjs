// Reproduce: node research/min_prime_root_concurrent_occupation_audit.mjs
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),T=mode==="analytic"?Math.floor(X/u**.25):mode==="short"?B:4*B,Q=mode==="wide"?7:Math.max(5,Math.ceil(B/(mode==="analytic"?u:8))),m0=mode==="analytic"?Math.max(1,Math.floor(B*u**1.5)):mode==="short"?4:8,lim=7*X+5,spf=new Int32Array(lim+1),ok=(x,s)=>{if(!x)throw Error(s);},mod=(a,b)=>((a%b)+b)%b,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c;}return a;};
 for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)spf[j]=spf[j]||n;}
 const fs=n=>{let a=[];while(n>1){let p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const vertices=new Map(),roots=new Map();let N=0,R=0,G=0,events=0,high=0,literal=0,hiR=0,totalTime=0,deltaFinal=0,crossingRoots=0;
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){N++;let C=2*M-2,t=M+2,cut=Math.floor((7*M-1)/4),a=[],cost=0;
  while(true){let e={M,C,t,p:0,r:0,w:0,prev:a.length?a[a.length-1]:null};a.push(e);let id=C+":"+t;if(!vertices.has(id))vertices.set(id,[]);vertices.get(id).push(e);
   if(C-(2*M-2)>=T)break;
   let tt=Infinity,p=Infinity;for(const s of [-1,1])for(const q of fs(C+s)){let tick=t+1+mod((s===-1?0:q+2)-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;}}
   if(X<=1024){let lt=Infinity,lp=Infinity;for(let s=t+1;s<=cut;s++){let f=fs(gcd(s%2?s-2:s,C+(s%2?1:-1)));if(f.length){lt=s;lp=f[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal");literal++;}
   if(tt>cut)break;
   let r=Math.min(...fs(C-1),...fs(C+1));ok(r<=p&&tt-t<=2*r,"clock");e.p=p;e.r=r;cost+=r;events++;if(p>=Q&&r>p/(mode==="analytic"?Math.sqrt(Math.log(p)):2)){e.w=r;hiR+=r;high++;}
   t=tt;C+=p-1;ok(C<=2*t,"horizon");
  }
  let gain=C-(2*M-2),elapsed=t-(M+2),delta=2*t-C;ok(2*elapsed===gain+delta-6&&delta>=0,"clock difference identity");totalTime+=elapsed;deltaFinal+=delta;if(gain>=T)crossingRoots++;R+=cost;G+=gain;ok(gain<T+B&&2*cost<=3*gain,"gain");
  let tail=0;for(let i=a.length-1;i>=0;i--){tail+=a[i].w;a[i].tail=tail;a[i].next=a[i+1]||null;}roots.set(M,a);
 }
 const H=T+B,y=3,L=6,analytic=mode==="analytic",Qm=analytic?Q:Math.max(7,Math.ceil(B/(mode==="wide"?4:8))),k=analytic?Math.max(1,Math.floor(u**.25)):mode==="wide"?2:(mode==="phase"||(mode==="stress"||(mode==="broad"||mode==="concurrent")))?3:1,scale=analytic?u**1.5:(mode==="phase"||(mode==="stress"||(mode==="broad"||mode==="concurrent")))?0.5:0.125;
 const pr=[];for(let p=3;p<Qm&&p<=B;p+=2)if(spf[p]===p)pr.push(p);
 const wt=r=>r+1.5*L,A=r=>Math.ceil(wt(r)**2*scale),blk=(r,C)=>Math.floor(C/A(r)),cap=r=>analytic?Math.max(1,Math.floor(Math.log(r)**6)):mode==="wide"?4:2;
 let initialLow=0,highLow=0,mediumClock=0,mediumLow=0,lowBlocks=0,lowMax=0,mediumTags=0,lowTotal=0,quotientChecks=0;
 let initialActual=0,highActual=0,mediumActual=0,lowActual=0;const input=[];for(const [M,ar] of roots){
   const es=[];let anchor=null,lowGain=0,lowCost=0,lowTime=0;
   function endLow(){if(!lowGain)return;ok(lowGain<L,"LOW block barrier");lowBlocks++;lowMax=Math.max(lowMax,lowGain);if(!anchor){initialLow+=lowCost;initialActual+=lowTime;}else if(anchor.p>=Qm){highLow+=lowCost;highActual+=lowTime;}else{anchor.low=lowCost;mediumLow+=lowCost;anchor.actual+=lowTime;mediumActual+=lowTime;anchor.endC+=lowGain;anchor.endT+=lowTime;}lowGain=0;lowCost=0;lowTime=0;}
   for(const e of ar){if(!e.p)break;if(e.p<=y){lowGain+=e.p-1;lowCost+=e.r;lowTotal+=e.r;lowTime+=e.next.t-e.t;lowActual+=e.next.t-e.t;continue;}endLow();anchor={M,C:e.C,p:e.p,r:e.r,low:0,actual:e.next.t-e.t,endC:e.next.C,endT:e.next.t};if(e.p>=Qm)highActual+=anchor.actual;if(e.p<Qm){es.push(anchor);mediumActual+=anchor.actual;mediumClock+=e.r;mediumTags++;const sig=(e.C-1)%e.r===0?-1:1;ok((e.C+sig)%e.r===0&&(e.C+sig)/e.r%2===1,"least quotient");const q=(e.C+sig)/e.r;for(const s of fs(e.C-1).concat(fs(e.C+1)))ok(s>=e.r,"least factor");ok(q*e.r-2*sig===e.C-sig,"quotient second form");quotientChecks++;}}
   endLow();input.push(es);
 }
 ok(lowTotal===initialLow+highLow+mediumLow,"LOW assignment");ok(totalTime===initialActual+highActual+mediumActual&&2*totalTime===G+deltaFinal-6*N&&totalTime<=2*R,"actual root ledger");
 const ell=1+Math.log(u),P=r=>2**Math.floor(Math.log2(r)),lambda=r=>Math.sqrt(P(r)/Qm)*Math.log(Qm)/Math.log(2*P(r));
 const D=r=>Math.max(1,Math.floor(analytic?r*u**1.5*Math.log(2+Math.min(r,u))**2/ell**1.5:r*(mode==="wide"?6:3)));
 const c=r=>Math.max(1,Math.floor(cap(r)/lambda(r)));
 const cellWidths=analytic?[Math.ceil(H),Math.ceil(H/Math.max(1,u**.125)),Math.ceil(H/Math.max(1,u**.25))]:[Math.ceil(H),Math.ceil(H/2),Math.ceil(H/4)];
 const bcap=r=>{const p=P(r),lp=Math.log(2*p),ep=1+Math.log(lp);return Math.max(1,Math.floor(analytic?(B/p)**2/u**1.5*Math.sqrt(p/Qm)*(p>=u*u?lp**6/ep**4:lp**2/(1+L/p)**2):(mode==="stress"||(mode==="broad"||mode==="concurrent"))?2:c(r)*2*Math.sqrt(Qm/p)));};
 const subcap=(r,d)=>Math.max(1,Math.floor(bcap(r)/(Math.ceil(H/(2*d))+2)));
 const ell0=1+Math.log(u),quota=r=>analytic?Math.max(1,Math.ceil(u**1.5/ell0**1.25+u**1.5*Math.log(2*P(r))*(1+L/P(r))*(P(r)/Qm)**.25/ell0)):k;
 const d=cellWidths.at(-1),sourceCell=M=>Math.floor((M-X)/d),mcell=r=>subcap(r,d);
 const pairMap=new Map(),byRoot=new Map(),timeIntervals=new Map();const rho=analytic?u**(-1/64):mode==="concurrent"?.25:mode==="broad"?2.5:1;let actualFirst=0,actualShort=0,actualLong=0,fastEdgeCost=0,fastEdges=0,upperDisjointChecks=0;let first=0,short=0,long=0,medium=0,edges=0,shortEdges=0,fullPairs=0,selectedPairs=0,maxK=0;
 for(const es of input){if(!es.length)continue;const M=es[0].M,ar=roots.get(M),idx=new Map(ar.map((e,i)=>[e.C,i])),cells=new Map();byRoot.set(M,new Map(es.map(e=>[e.C,e])));
   for(const e of es){const ky=e.r+":"+blk(e.r,e.C);if(!cells.has(ky))cells.set(ky,[]);cells.get(ky).push(e);medium+=e.r+e.low;}
   for(const g of cells.values()){const r=g[0].r,kk=quota(r);maxK=Math.max(maxK,kk);fullPairs+=g.length*(g.length-1)/2;
     for(let i=0;i<g.length;i++){const e=g[i],cost=e.r+e.low;ok(e.actual<=2*cost&&e.actual===e.endT-ar[idx.get(e.C)].t,"actual attached cost");if(i<kk){first+=cost;actualFirst+=e.actual;continue;}let paid=0;
       for(let j=i-kk;j<i;j++){const C=g[j].C,E=e.C,amount=cost/kk;paid+=amount;edges++;if(E-C<=D(r)){short+=amount;actualShort+=e.actual/kk;shortEdges++;continue;}long+=amount;actualLong+=e.actual/kk;selectedPairs++;const fast=e.endT-ar[idx.get(C)].t<=rho*(E-C);if(fast){fastEdgeCost+=e.actual/kk;fastEdges++;if(!timeIntervals.has(M))timeIntervals.set(M,[]);timeIntervals.get(M).push({C,E:e.endC,t:ar[idx.get(C)].t,s:e.endT,hit:E,cost:e.actual});}
         const ky=r+":"+C+":"+E;if(!pairMap.has(ky))pairMap.set(ky,[]);pairMap.get(ky).push({M,t:ar[idx.get(C)].t,s:ar[idx.get(E)].t,earlyOut:ar[idx.get(C)+1].t,earlyJ:ar[idx.get(C)+1].C,earlyP:ar[idx.get(C)].p,out:ar[idx.get(E)+1].t,J:ar[idx.get(E)+1].C,p:e.p,Ftime:e.endT,amount,actual:e.actual/kk,fast});
       }ok(Math.abs(paid-cost)<1e-7,"exact quota allocation");
     }
   }
 }
 const near=(x,y)=>Math.abs(x-y)<=1e-6*Math.max(1,Math.abs(x),Math.abs(y));
 ok(near(medium,first+short+long)&&medium===mediumClock+mediumLow&&selectedPairs+shortEdges===edges&&edges<=fullPairs,"quota partition");
 ok(near(mediumActual,actualFirst+actualShort+actualLong),"actual quota");
 // Greedy minimal-cover scan. At most two selected intervals cover any open gain point.
 let unionGain=0,coverGain=0,coverTime=0,endpointTime=0,coverN=0,coverRoots=0,depthChecks=0,unionChecks=0;
 for(const [M,iv] of timeIntervals){
   const a=iv.slice().sort((x,y)=>x.C-y.C||y.E-x.E),selected=[],ends=new Map();let i=0,reach=-1,ul=0,lo=-1,hi=-1;
   for(const x of a){if(x.C>=hi){ul+=Math.max(0,hi-lo);lo=x.C;hi=x.E;}else hi=Math.max(hi,x.E);ends.set(x.hit,x.cost);ok(x.s-x.t<=rho*(x.E-x.C),"extended interval fast");}ul+=Math.max(0,hi-lo);
   while(i<a.length){if(a[i].C>reach)reach=a[i].C;let best=null;
     while(i<a.length&&a[i].C<=reach){if(!best||a[i].E>best.E)best=a[i];i++;}
     if(best&&best.E>reach){selected.push(best);reach=best.E;}
   }
   let sl=0,st=0,cl=-1,cr=-1,cu=0;
   for(let j=0;j<selected.length;j++){const x=selected[j];if(j>=2){ok(selected[j-2].E<=x.C,"cover depth <=2");depthChecks++;}sl+=x.E-x.C;st+=x.s-x.t;
     if(x.C>=cr){cu+=Math.max(0,cr-cl);cl=x.C;cr=x.E;}else cr=Math.max(cr,x.E);}
   cu+=Math.max(0,cr-cl);
   // Independently check every input interval covered by selected union.
   let j=0;const components=[];for(const x of selected){const z=components.at(-1);if(z&&x.C<=z[1])z[1]=Math.max(z[1],x.E);else components.push([x.C,x.E]);}
   for(const x of a){while(j<components.length&&components[j][1]<x.E)j++;ok(j<components.length&&components[j][0]<=x.C&&components[j][1]>=x.E,"input interval covered");unionChecks++;}
   const ec=[...ends.values()].reduce((s,x)=>s+x,0),rootGain=roots.get(M).at(-1).C-roots.get(M)[0].C;
   ok(cu===ul&&sl<=2*ul&&ul<=rootGain&&st<=rho*sl+1e-6&&ec<=st,"actual endpoint cover");
   unionGain+=ul;coverGain+=sl;coverTime+=st;endpointTime+=ec;coverN+=selected.length;coverRoots++;
 }
 ok(fastEdgeCost<=endpointTime+1e-6&&coverTime<=2*rho*G+1e-6,"global fast clock bound");
 const ac={band:0,cell:0,phase:0,tiny:0,close:0,earlyClose:0,already:0,immediate:0,farNear:0,farFast:0,farDisjointSlow:0,farOverlapSlow:0,fastAlready:0,fastImmediate:0,smallAlready:0,smallImmediate:0,largeAlready:0,largeImmediate:0,farDisjoint:0,farOverlap:0};
 let actualRes=0,fastResidualCost=0,slowOverlapChecks=0;const occupationEdges=[];
 let band=0,cellCost=0,res=0,tiny=0,close=0,far=0,heavy=0,already=0,immediate=0,heavyFocal=0,smallFocal=0,tinyFocal=0,groups=0,cellChecks=0,degreeChecks=0,partnerChecks=0,maxDegree=0,maxRatio=0,maxMult=0,keys=0,maxKappa=0;
 const kappa=r=>analytic?Math.ceil(u**.125*u/Math.log(2*P(r))):(mode==="stress"||(mode==="broad"||mode==="concurrent"))?2:mode==="short"?3:4;
 const eta=r=>analytic?u**(1/32):(mode==="stress"||(mode==="broad"||mode==="concurrent"))?4:2;
 const gap=r=>analytic?Math.floor(P(r)*u**(1/16)):mode==="short"||(mode==="stress"||(mode==="broad"||mode==="concurrent"))?1:Math.max(1,Math.floor(P(r)/2));
 const outKey=a=>a.out+":"+a.J,earlyKey=a=>a.earlyOut+":"+a.earlyJ;
 const gapBand=h=>2**Math.floor(Math.log2(h)),Ab=r=>Math.ceil((2*P(r)+1.5*L)**2*scale);
 const phaseWidth=(r,S)=>analytic?Math.max(1,Math.ceil(S*u**(-1/16)*(Qm/P(r))**.75)):(mode==="broad"||mode==="concurrent")?4*H:Math.max(2,Math.ceil(S*(mode==="stress"?1:2)));
 const gapCap=(r,S)=>Math.max(1,Math.floor(bcap(r)*Ab(r)/(Math.max(1,u)*S)));
 const phaseCount=(r,S)=>{const W=phaseWidth(r,S);return (Math.ceil(4*H/W)+4)*(Math.ceil(6*S/W)+3);};
 const phaseCap=(r,S)=>Math.max(1,Math.floor(gapCap(r,S)/((Math.ceil(H/(2*d))+2)*phaseCount(r,S))));
 // A uniform band cap for endpoint domination, computed over all possible dyadic gaps.
 const minCaps=new Map();function minCap(r){if(!minCaps.has(r)){let m=Infinity;for(let S=1;S<=Ab(r);S*=2)if(2*S>D(r))m=Math.min(m,phaseCap(r,S));minCaps.set(r,Number.isFinite(m)?m:1);}return minCaps.get(r);}
 const originCut=r=>analytic?Math.max(1,Math.floor(u**4.5/ell0**4*(Qm/P(r))**.125)):16;
 let nearOriginFar=0,nearOriginChecks=0,farOriginFar=0,nearOriginEndpointBound=0,nearOriginEndpointCost=0;
 let gapChecks=0,earlierTransfers=0,earlierMaxMult=0,maxLagRatio=0,fastDisjoint=0,fastChecks=0,driftChecks=0,capChecks=0;
 const earlierEndpoint=new Map();
 let phaseThin=0,phaseGroups=0,phaseChecks2=0,earlyClose=0,farDisjoint=0,farOverlap=0,farFlip=0,earlyDegreeChecks=0,maxPhaseCount=0,maxElapsed=0,maxDrift=0,earlyRefinement=0;
 const endpoints=new Map(),pairCharges=new Map();
 for(const [key,ar] of pairMap){const [r,C,E]=key.split(":").map(Number),v=ar.length,S=gapBand(E-C);ok(S<=E-C&&E-C<2*S&&S<Ab(r),"gap band");gapChecks++;
   if(v<=bcap(r)){for(const a of ar){band+=a.amount;ac.band+=a.actual;}continue;}
   const keep=new Set(ar.map(a=>a.M));for(const width of cellWidths){const cc=new Map();for(const a of ar){let j=Math.floor((a.M-X)/width);if(!cc.has(j))cc.set(j,[]);cc.get(j).push(a);}ok(cc.size<=Math.ceil(H/(2*width))+2,"source locality");for(const g of cc.values()){cellChecks++;if(g.length<=subcap(r,width))for(const a of g)keep.delete(a.M);}}
   for(const a of ar)if(!keep.has(a.M)){cellCost+=a.amount;ac.cell+=a.actual;}if(!keep.size)continue;keys++;
   const cc=new Map(),phaseBySource=new Map(),W=phaseWidth(r,S);
   for(const a of ar){let j=sourceCell(a.M),ky=j+":"+Math.floor(a.t/W)+":"+Math.floor(a.s/W);if(!cc.has(ky))cc.set(ky,[]);cc.get(ky).push(a);if(!phaseBySource.has(j))phaseBySource.set(j,new Set());phaseBySource.get(j).add(ky);
     ok(a.s-a.t>=1&&a.s-a.t<=3*(E-C),"segment duration");maxElapsed=Math.max(maxElapsed,a.s-a.t);}
   // At finite diagnostic widths h may exceed W: use the general envelope.
   const phaseLimit=phaseCount(r,S);
   for(const set of phaseBySource.values()){ok(set.size<=phaseLimit,"phase cell count");maxPhaseCount=Math.max(maxPhaseCount,set.size);phaseChecks2++;}
   for(const g of cc.values()){
     if(!g.some(a=>keep.has(a.M)))continue;
     const n=g.length,K=kappa(r),U=eta(r),D0=gap(r),m=phaseCap(r,S);ok(m>=minCap(r),"uniform phase cap");capChecks++;maxKappa=Math.max(K,maxKappa);phaseGroups++;
     if(n<=m){for(const a of g)if(keep.has(a.M)){phaseThin+=a.amount;ac.phase+=a.actual;}continue;}
     const gg=new Map();for(const a of g){let ky=outKey(a);if(!gg.has(ky))gg.set(ky,[]);gg.get(ky).push(a);ok(a.out>a.s&&a.out-a.s<=2*r&&a.J===E+a.p-1,"actual exit");}
     const gs=[...gg.values()];groups+=gs.length;
     const ee=new Map();for(const a of g){const k=earlyKey(a);if(ee.has(k))ok(ee.get(k).out===a.out&&ee.get(k).J===a.J,"early successor refines late");else ee.set(k,a);earlyRefinement++;ok(a.earlyOut>a.t&&a.earlyOut-a.t<=2*r&&a.earlyJ===C+a.earlyP-1,"early exit");}
     const earlyDegree=fs(C-1).concat(fs(C+1)).filter(p=>p>=r&&p<Qm).reduce((z,p)=>z+Math.floor(D0/p)+1,0);
     for(const a of ee.values()){const deg=[...ee.values()].filter(b=>Math.abs(a.earlyOut-b.earlyOut)<=D0).length;ok(deg<=earlyDegree,"early degree");earlyDegreeChecks++;}
     const large=ar=>ar.length>=Math.max(2,n/K),pool=gs.filter(ar=>!large(ar)).flat(),s=pool.length;
     const degBound=fs(E-1).concat(fs(E+1)).filter(p=>p>=r&&p<Qm).reduce((z,p)=>z+Math.floor(D0/p)+1,0);
     const byTick=new Map();for(const a of g){if(byTick.has(a.out))ok(byTick.get(a.out)===a.J,"unique selected label");else byTick.set(a.out,a.J);}
     for(const ar of gs){const q=ar[0],d=gs.filter(br=>Math.abs(br[0].out-q.out)<=D0).length;ok(d<=degBound,"exit degree");degreeChecks++;maxDegree=Math.max(maxDegree,d);}
     for(const a of g){if(!keep.has(a.M))continue;res+=a.amount;actualRes+=a.actual;const ag=gg.get(outKey(a)),big=large(ag);
       if(!big&&(s<2||s<n/U)){tiny+=a.amount;ac.tiny+=a.actual;tinyFocal++;continue;}
       const partners=big?ag:pool;ok(partners.length>=2&&partners.includes(a),"partner pool");let paid=0,nearWeight=0,earlyWeight=0;
       if(big){heavyFocal++;heavy+=a.amount;}else smallFocal++;
       for(const b of partners){if(a.M===b.M)continue;const w=a.amount/(partners.length-1),aw=a.actual/(partners.length-1);ok(aw<=2*w+1e-7,"focal domination");paid+=w;partnerChecks++;
         let cls;if(big){ok(a.out===b.out&&a.J===b.J,"shared successor");if(a.s===b.s){already+=w;cls="already";}else{immediate+=w;cls="immediate";}}
         else if(Math.abs(a.out-b.out)<=D0){close+=w;nearWeight+=w;cls="close";}
         else if(Math.abs(a.earlyOut-b.earlyOut)<=D0){earlyClose+=w;earlyWeight+=w;cls="earlyClose";}
         else{far+=w;cls="far";ok(a.s!==b.s&&Math.abs(a.s-b.s)>D0-2*r&&a.t!==b.t&&Math.abs(a.t-b.t)>D0-2*r,"both far input lags");ok(Math.abs(a.s-b.s)<W&&Math.abs(a.t-b.t)<W,"phase width");const da=b.t-a.t,db=b.s-a.s;ok(Math.abs(db-da)<=3*(E-C),"lag drift");maxDrift=Math.max(maxDrift,Math.abs(db-da));if(Math.abs(a.M-b.M)<=originCut(r)){nearOriginFar+=w;nearOriginChecks++;}else farOriginFar+=w;if(Math.max(a.t,b.t)>=Math.min(a.s,b.s)){farDisjoint+=w;ok(a.s-a.t<W&&b.s-b.t<W,"disjoint both fast");fastDisjoint+=w;fastChecks++;}else farOverlap+=w;maxLagRatio=Math.max(maxLagRatio,Math.abs(da)/(E-C),Math.abs(db)/(E-C));ok(Math.abs(db-da)<2*W,"localized drift");driftChecks++;if(da*db<0)farFlip+=w;}
         if(cls==="close"||cls==="earlyClose"){ac[cls]+=aw;continue;}if(cls==="far"){const disjoint=Math.max(a.t,b.t)>=Math.min(a.s,b.s);ac[disjoint?"farDisjoint":"farOverlap"]+=aw;if(analytic&&P(r)>=Qm/u**(1/24)&&disjoint){upperDisjointChecks++;ok(a.fast,"upper disjoint fast (finite test only if bound holds)");}if(Math.abs(a.M-b.M)<=originCut(r))ac.farNear+=aw;else if(a.fast){ac.farFast+=aw;fastResidualCost+=aw;}else{ac[disjoint?"farDisjointSlow":"farOverlapSlow"]+=aw;if(!disjoint){slowOverlapChecks++;occupationEdges.push({M:a.M,Mp:b.M,C,E,r,t:a.t,s:a.s,t2:b.t,s2:b.s,Ftime:a.Ftime,w:aw});}}}else{ac[cls]+=aw;if(a.fast){ac[cls==="already"?"fastAlready":"fastImmediate"]+=aw;fastResidualCost+=aw;}}
         const id=r+":"+E+":"+a.M+":"+b.M,v=endpoints.get(id)||{w:0,aw:0,n:0,cls,r,E,M:a.M,Mp:b.M};ok(v.cls===cls,"fixed endpoint class");v.w+=w;v.aw+=a.fast?0:aw;v.n++;endpoints.set(id,v);const id0=r+":"+C+":"+a.M+":"+b.M,v0=earlierEndpoint.get(id0)||{w:0,n:0,r};v0.w+=w;v0.n++;earlierEndpoint.set(id0,v0);
       }
       ok(near(paid,a.amount),"allocation");
       if(!big){const nb=pool.filter(b=>b.M!==a.M&&Math.abs(a.out-b.out)<=D0).length;ok(near(nearWeight,a.amount*nb/(s-1))&&nb<=degBound*Math.max(1,n/K),"near pool capacity");maxRatio=Math.max(maxRatio,nb/(s-1));const eb=pool.filter(b=>b.M!==a.M&&Math.abs(a.earlyOut-b.earlyOut)<=D0).length,ebOnly=pool.filter(b=>b.M!==a.M&&Math.abs(a.earlyOut-b.earlyOut)<=D0&&Math.abs(a.out-b.out)>D0).length;ok(eb<=earlyDegree*Math.max(1,n/K)&&near(earlyWeight,a.amount*ebOnly/(s-1)),"early pool capacity");}
     }
   }
 }
 // For an endpoint pair, the class is fixed among kept edges: identical exit
 // cannot be far; identical exit is either already or immediate by input time.
 let endpointBound=0,tailChecks=0,immediateChecks=0,smallAlready=0,smallImmediate=0,largeAlready=0,largeImmediate=0,alreadyPairs=0,immediatePairs=0,maxTail=0,firstSmall=0,firstLarge=0;
 const weight=r=>wt(r)*Math.max(2*kappa(r),2*eta(r))/minCap(r);
 for(const e of earlierEndpoint.values()){ok(e.n<=quota(e.r)&&e.w<=weight(e.r)+1e-6,"earlier quota endpoint transfer");earlierMaxMult=Math.max(earlierMaxMult,e.n);earlierTransfers++;}
 const tails=new Map();for(const [M,ar] of roots){let t=0,aa=new Float64Array(ar.length);const em=byRoot.get(M);for(let i=ar.length-1;i>=0;i--){let e=em?.get(ar[i].C);if(e)t+=weight(e.r);aa[i]=t;}tails.set(M,aa);maxTail=Math.max(maxTail,t);}
 for(const v of endpoints.values()){const bound=weight(v.r);ok(v.n<=quota(v.r)&&v.w<=bound+1e-6,"endpoint quota bound");endpointBound+=bound;maxMult=Math.max(maxMult,v.n);if(v.cls==="far"){if(Math.abs(v.M-v.Mp)<=originCut(v.r)){nearOriginEndpointBound+=bound;nearOriginEndpointCost+=v.w;}continue;}
   let M=Math.min(v.M,v.Mp),Mp=Math.max(v.M,v.Mp),id=M+":"+Mp,q=pairCharges.get(id)||{M,Mp,a:0,i:0,aa:0,ai:0,pre:null};if(v.cls==="already"){q.a+=v.w;q.aa+=v.aw;}else{q.i+=v.w;q.ai+=v.aw;if(q.pre!==null)ok(q.pre===v.E,"unique immediate merger horizon");q.pre=v.E;}pairCharges.set(id,q);
 }
 const ma=mode==="analytic"?Math.max(1,Math.floor(u**6/ell0**4)):mode==="short"?4:8,mb=analytic?Math.max(ma,Math.floor(H/Qm*ma)):ma*3;
 for(const q of pairCharges.values()){
   const a=roots.get(q.M),b=roots.get(q.Mp);let i=0,j=0;while(i<a.length&&j<b.length){if(a[i].C<b[j].C)i++;else if(a[i].C>b[j].C)j++;else if(a[i].t===b[j].t)break;else{i++;j++;}}
   ok(i<a.length&&j<b.length,"first physical meeting");const es=vertices.get(a[i].C+":"+a[i].t),local=es.filter(e=>sourceCell(e.M)===sourceCell(q.M)).length;
   if(q.a){tailChecks++;ok(q.a<=2*Math.min(tails.get(q.M)[i],tails.get(q.Mp)[j])+1e-6,"already tail bound");if(local<=ma){smallAlready+=q.a;ac.smallAlready+=q.aa;alreadyPairs++;}else{largeAlready+=q.a;ac.largeAlready+=q.aa;}}
   if(q.i){immediateChecks++;ok(i>0&&j>0&&a[i-1].C===q.pre&&b[j-1].C===q.pre&&a[i-1].t!==b[j-1].t,"immediate first meeting");ok(q.i<=2*weight(a[i-1].r)+1e-6,"one immediate weight");if(local<=mb){smallImmediate+=q.i;ac.smallImmediate+=q.ai;immediatePairs++;}else{largeImmediate+=q.i;ac.largeImmediate+=q.ai;}}
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
 ok(near(nearOriginFar,nearOriginEndpointCost)&&nearOriginEndpointCost<=nearOriginEndpointBound+1e-6&&near(far,nearOriginFar+farOriginFar),"near origin transfer");
 ok(near(long,band+cellCost+phaseThin+res)&&near(res,tiny+close+earlyClose+far+heavy)&&near(far,farDisjoint+farOverlap)&&near(heavy,already+immediate)&&near(already,smallAlready+largeAlready)&&near(immediate,smallImmediate+largeImmediate),"allocation partition");
 ok(near(actualLong,ac.band+ac.cell+ac.phase+actualRes)&&near(actualRes,ac.tiny+ac.close+ac.earlyClose+ac.already+ac.immediate+ac.farDisjoint+ac.farOverlap)&&near(ac.already,ac.fastAlready+ac.smallAlready+ac.largeAlready)&&near(ac.immediate,ac.fastImmediate+ac.smallImmediate+ac.largeImmediate)&&near(ac.farDisjoint+ac.farOverlap,ac.farNear+ac.farFast+ac.farDisjointSlow+ac.farOverlapSlow)&&fastResidualCost<=fastEdgeCost+1e-6,"actual residual ledger");
 // Common-time occupation tests. All masses are ORIGINAL active tags in one fixed source cell.
 const mg=u**4.75/ell0**4,thin=Math.max(1,Math.floor(analytic?mg/u**.5:4)),crowd=Math.max(1,Math.floor(analytic?mg/u**.25:8)),
  closeH=Math.max(1,Math.floor(analytic?u**.25:6)),nearTick=Math.max(1,Math.floor(analytic?u**.125:2)),
  largeP=Math.max(5,Math.ceil(analytic?B**.125:5)),wideH=Math.ceil(largeP*(analytic?u**.125:6)),
  sameJ=Math.max(1,Math.floor(analytic?u**.25:2)),etaOcc=analytic?u**(-1/16):.25,
  Amax=Math.ceil((Qm+1.5*L)**2*scale);
 const byCell=new Map();for(const [M,ar] of roots){const c=sourceCell(M);if(!byCell.has(c))byCell.set(c,[]);byCell.get(c).push(ar);}
 const queries=new Map();
 for(const x of occupationEdges){ok(sourceCell(x.M)===sourceCell(x.Mp),"occupation source cell");const c=sourceCell(x.M);x.good=0;x.kinds=[0,0,0,0];x.overlap=Math.max(0,Math.min(x.s,x.s2)-Math.max(x.t,x.t2));x.length=x.Ftime-x.t;ok(x.length>=x.s-x.t&&x.overlap>0,"actual occupation interval");if(!queries.has(c))queries.set(c,new Map());const q=queries.get(c);
   for(let t=Math.max(x.t,x.t2);t<Math.min(x.s,x.s2);t++){if(!q.has(t))q.set(t,[]);q.get(t).push(x);}
 }
 let occupationChecks=0,degreeChecksOcc=0,distinctWaitingChecks=0,clockChecks=0,queryTicks=0,maxActive=0,maxGroup=0,maxDegreeOcc=0,goodTicks=0,crossingChecks=0,positiveCrossings=0;
 const sampledGood=new Map();
 // Group by waiting horizon at a common integer time; all active tags at one horizon have the same next event.
 for(const [c,q] of queries){
   const ars=byCell.get(c),ptr=new Int32Array(ars.length);
   for(const t of [...q.keys()].sort((a,b)=>a-b)){
     queryTicks++;const hs=new Map(),tag=new Map();
     for(let i=0;i<ars.length;i++){const ar=ars[i];while(ptr[i]+1<ar.length&&ar[ptr[i]+1].t<=t)ptr[i]++;const e=ar[ptr[i]];if(!e.next||t<e.t||t>=e.next.t)continue;
       let g=hs.get(e.C);if(!g){g={C:e.C,p:e.p,s:e.next.t,n:0};hs.set(e.C,g);}else ok(g.p===e.p&&g.s===e.next.t,"same waiting horizon deterministic exit");
       g.n++;tag.set(e.M,g);ok(e.next.t>t&&e.next.t-t<=2*e.r,"active wait");clockChecks++;
     }
     maxActive=Math.max(maxActive,tag.size);const gs=[...hs.values()];for(const g of gs){maxGroup=Math.max(maxGroup,g.n);g.crowd=gs.reduce((z,h)=>z+(Math.abs(g.C-h.C)<=Amax?h.n:0),-1);}
     const factorMax=Math.ceil(Math.log(7*X+5)/Math.log(largeP));
     let oriented=0,symmetric=0;
     // Exact bounded-outdegree directed tests. The union relation is symmetrized later.
     function kind(g,h){const gap=Math.abs(g.C-h.C);if(!gap)return -1;
       if(g.crowd<=crowd&&gap<=Amax)return 0;
       if(h.n<=thin&&gap<=closeH)return 1;
       if(h.n<=thin&&g.p>=largeP&&h.p>=largeP&&gap<=wideH&&Math.abs(g.s-h.s)<=nearTick)return 2;
       if(h.n<=thin&&g.p===h.p&&gap<=sameJ*g.p)return 3;
       return -1;
     }
     for(const g of gs){let n=0,d2=0,d3=0;for(const h of gs){if(g===h)continue;const dC=h.C-g.C;
       if(h.p===g.p){const sig=x=>x.s%2?1:-1;ok(mod(dC+sig(h)-sig(g),g.p)===0,"same outgoing prime congruence");if(g.s===h.s)ok(mod(dC,2*g.p)===0,"same tick and same prime");}
       if(h.n<=thin&&g.p>=largeP&&h.p>=largeP&&Math.abs(dC)<=wideH&&Math.abs(g.s-h.s)<=nearTick)d2++;
       if(h.n<=thin&&h.p===g.p&&Math.abs(dC)<=sameJ*g.p)d3++;
       if(kind(g,h)>=0)n+=h.n;if(kind(g,h)>=0||kind(h,g)>=0)symmetric+=g.n*h.n;
     }
     const bd2=(2*nearTick+1)*factorMax*(Math.floor(wideH/largeP)+1);
     ok(d2<=bd2&&d3<=2*(sameJ+1),"arithmetic occupation degree");
     const bound=crowd+thin*(2*closeH+bd2+2*(sameJ+1));ok(n<=bound,"directed occupation tag degree");maxDegreeOcc=Math.max(maxDegreeOcc,n);oriented+=g.n*n;degreeChecksOcc++;
     }
     ok(symmetric<=2*oriented,"symmetric total tag degree");
     for(const x of q.get(t)){const g=tag.get(x.M),h=tag.get(x.Mp);ok(g&&h&&g.C!==h.C&&g.C>=x.C&&g.C<x.E&&h.C>=x.C&&h.C<x.E,"async active distinct horizons");distinctWaitingChecks++;
       const f=kind(g,h),b=kind(h,g),j=f>=0?f:b;occupationChecks++;
       if(j>=0){x.good++;x.kinds[j]++;goodTicks++;const ky=x.M+":"+x.Mp;if(!sampledGood.has(ky))sampledGood.set(ky,new Set());sampledGood.get(ky).add(t);}
       const a0=roots.get(x.M),b0=roots.get(x.Mp);
       // Clock order crossing is necessarily a jump, not an equal waiting state. Test only interior consecutive ticks.
       if(t+1<Math.min(x.s,x.s2)){const g2=g.s===t+1?g.C+g.p-1:g.C,h2=h.s===t+1?h.C+h.p-1:h.C;ok(g2!==h2,"no interior waiting merger");crossingChecks++;if((g.C-h.C)*(g2-h2)<0){positiveCrossings++;ok(Math.max(g.s===t+1?g.p-1:0,h.s===t+1?h.p-1:0)>Math.abs(g.C-h.C),"crossing requires overtaking jump");}}
     }
   }
 }
 let occPaid=0,occKept=0,occEdgesPaid=0,occEdgesKept=0,occKinds=[0,0,0,0],occCoverChecks=0,occUnion=0,occSelectedLength=0,occEndpointTime=0,occGoodUnion=0;
 const accepted=new Map();
 for(const x of occupationEdges){
   if(x.good+1e-9>=etaOcc*x.length){occPaid+=x.w;occEdgesPaid++;for(let k=0;k<4;k++)occKinds[k]+=x.kinds[k];const ky=x.M+":"+x.Mp;if(!accepted.has(ky))accepted.set(ky,[]);accepted.get(ky).push(x);}
   else{occKept+=x.w;occEdgesKept++;}
 }
 // For a fixed directed source pair use the SAME-union depth-two cover in time.
 for(const [ky,ar] of accepted){
   const iv=ar.slice().sort((a,b)=>a.t-b.t||b.Ftime-a.Ftime),chosen=[],ends=new Map();let i=0,reach=-1,lo=-1,hi=-1,ul=0;
   for(const x of iv){if(x.t>=hi){ul+=Math.max(0,hi-lo);lo=x.t;hi=x.Ftime;}else hi=Math.max(hi,x.Ftime);const k=x.r+":"+x.E,old=ends.get(k)||{w:0,n:0,b:x.Ftime-x.s};old.w+=x.w;old.n++;ends.set(k,old);}
   ul+=Math.max(0,hi-lo);
   while(i<iv.length){if(iv[i].t>reach)reach=iv[i].t;let best=null;while(i<iv.length&&iv[i].t<=reach){if(!best||iv[i].Ftime>best.Ftime)best=iv[i];i++;}if(best&&best.Ftime>reach){chosen.push(best);reach=best.Ftime;}}
   let sl=0,sg=0,eu=0,ec=0;for(let j=0;j<chosen.length;j++){const x=chosen[j];if(j>=2)ok(chosen[j-2].Ftime<=x.t,"occupation cover depth");sl+=x.length;sg+=x.good;}
   const ticks=new Set();for(const x of iv)for(let t=x.t;t<x.Ftime;t++)ticks.add(t);
   const covered=new Set();for(const x of chosen)for(let t=x.t;t<x.Ftime;t++)covered.add(t);
   ok(ticks.size===ul&&covered.size===ul&&[...ticks].every(t=>covered.has(t)),"occupation union cover");
   const good=sampledGood.get(ky);let gu=0;for(const t of ticks)if(good.has(t))gu++;
   for(const [k,e] of ends){const r=Number(k.split(":")[0]);ok(e.n<=quota(r)&&e.w<=2*weight(r)+1e-6,"occupation endpoint domination");eu+=e.b;ec+=e.w;}
   ok(eu<=ul&&ul<=sl&&sl<=2*ul&&etaOcc*sl<=sg+1e-6&&sg<=2*gu&&ul<=2*gu/etaOcc+1e-6,"occupation time-cover bound");occCoverChecks++;occUnion+=ul;occSelectedLength+=sl;occEndpointTime+=eu;occGoodUnion+=gu;
 }
 ok(near(occPaid+occKept,ac.farOverlapSlow),"occupation residual partition");
 return {mode,X,B,T,Qm,N,literal,occupationEdges:occupationEdges.length,occPaid,occKept,occEdgesPaid,occEdgesKept,occKinds,occCoverChecks,occUnion,occSelectedLength,occEndpointTime,occGoodUnion,occupationChecks,degreeChecksOcc,distinctWaitingChecks,clockChecks,queryTicks,maxActive,maxGroup,maxDegreeOcc,goodTicks,crossingChecks,positiveCrossings,thin,crowd,closeH,nearTick,largeP,wideH,sameJ,etaOcc,actualFinalAfterOccupation:ac.largeAlready+ac.largeImmediate+ac.farDisjointSlow+occKept,totalTime,deltaFinal,crossingRoots,G,R,initialActual,highActual,mediumActual,actualFirst,actualShort,actualLong,fastEdgeCost,fastEdges,rho,unionGain,coverGain,coverTime,endpointTime,coverN,coverRoots,depthChecks,unionChecks,upperDisjointChecks,actualRes,fastResidualCost,slowOverlapChecks,ac,actualFinal:ac.largeAlready+ac.largeImmediate+ac.farDisjointSlow+ac.farOverlapSlow,nearOriginFar,nearOriginChecks,farOriginFar,nearOriginEndpointBound,nearOriginEndpointCost,finalAfterOrigin:farOriginFar+largeAlready+largeImmediate,gapChecks,earlierTransfers,earlierMaxMult,maxLagRatio,fastDisjoint,fastChecks,driftChecks,capChecks,medium,first,short,long,edges,fullPairs,band,cellCost,phaseThin,phaseGroups,phaseChecks2,earlyClose,farDisjoint,farOverlap,farFlip,earlyDegreeChecks,maxPhaseCount,maxElapsed,maxDrift,earlyRefinement,res,tiny,close,far,heavy,already,immediate,smallAlready,smallImmediate,largeAlready,largeImmediate,final:far+largeAlready+largeImmediate,heavyFocal,smallFocal,tinyFocal,groups,keys,cellChecks,degreeChecks,partnerChecks,maxDegree,maxRatio,maxMult,maxKappa,endpointBound,tailChecks,immediateChecks,alreadyPairs,immediatePairs,oracleChecks,oracleLocal,pa,pb};
}

const xs=process.argv.slice(2).map(Number);for(const mode of ['short','wide','analytic','phase','stress','broad','concurrent'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
