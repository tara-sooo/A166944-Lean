// Derived from joint_residence audit at 8d268d30c48d. Reproduce: node research/min_prime_root_boundary_hall_audit.mjs
function audit(X,mode,crtStress=false,gainStress=false,windowStress=false,reverseStress=false,ancestryStress=false,birthStress=false,anchorStress=false,multiStress=false,precutStress=false,gridStress=false,starStress=false,prefixStress=false,resetStress=false,thresholdStress=false,coverStress=false,excursionStress=false,residenceStress=false,entropyStress=false,jointResidenceStress=false,boundaryHallStress=false){
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
 let actualRes=0,fastResidualCost=0,slowOverlapChecks=0;const occupationEdges=[],farSlowEdges=[];
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
         if(cls==="close"||cls==="earlyClose"){ac[cls]+=aw;continue;}if(cls==="far"){const disjoint=Math.max(a.t,b.t)>=Math.min(a.s,b.s);ac[disjoint?"farDisjoint":"farOverlap"]+=aw;if(analytic&&P(r)>=Qm/u**(1/24)&&disjoint){upperDisjointChecks++;ok(a.fast,"upper disjoint fast (finite test only if bound holds)");}if(Math.abs(a.M-b.M)<=originCut(r))ac.farNear+=aw;else if(a.fast){ac.farFast+=aw;fastResidualCost+=aw;}else{ac[disjoint?"farDisjointSlow":"farOverlapSlow"]+=aw;const edge={M:a.M,Mp:b.M,C,E,r,t:a.t,s:a.s,t2:b.t,s2:b.s,Ftime:a.Ftime,w:aw,disjoint};farSlowEdges.push(edge);if(!disjoint){slowOverlapChecks++;occupationEdges.push(edge); }}}else{ac[cls]+=aw;if(a.fast){ac[cls==="already"?"fastAlready":"fastImmediate"]+=aw;fastResidualCost+=aw;}}
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
   ok(i<a.length&&j<b.length,"first physical meeting");const es=vertices.get(a[i].C+":"+a[i].t),local=es.filter(e=>sourceCell(e.M)===sourceCell(q.M)).length;q.physicalLocal=local;q.physicalTime=a[i].t;q.physicalHorizon=a[i].C;
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
 const big2=crtStress?5:Math.max(5,Math.ceil(B/(analytic?u:8))),d2tick=crtStress?8:Math.max(1,Math.floor(analytic?u**.125:4)),rank2=Math.max(1,Math.floor(analytic?mg/u**2:2));
 const div2=Math.ceil(Math.log(7*X+5)/Math.log(big2)),crt2=1+Math.floor(Amax/(big2*big2));
 // Two parities each; at most crt2 even horizons per residue pair.
 const keyBound2=4*crt2*((2*d2tick+1)**2*div2**2+2*(2*d2tick+1)*div2+1);
 const degree2=2*rank2*keyBound2;
 let crtChecks=0,crtOriented=0,crtSymmetric=0,crtQueryHits=0,crtNewTicks=0,crtPaid=0,crtEdges=0,crtRankDeep=0;
 for(const x of occupationEdges){ok(sourceCell(x.M)===sourceCell(x.Mp),"occupation source cell");const c=sourceCell(x.M);x.good=0;x.goodOld=0;x.kinds=[0,0,0,0,0];x.overlap=Math.max(0,Math.min(x.s,x.s2)-Math.max(x.t,x.t2));x.length=x.Ftime-x.t;ok(x.length>=x.s-x.t&&x.overlap>0,"actual occupation interval");if(!queries.has(c))queries.set(c,new Map());const q=queries.get(c);
   for(let t=Math.max(x.t,x.t2);t<Math.min(x.s,x.s2);t++){if(!q.has(t))q.set(t,[]);q.get(t).push(x);}
 }
 // Independent positive-control samples: actual paths with two adjacent large labels, even if no quota edge queried them.
 let extraSamples=0;for(const [c,ars] of byCell){if(extraSamples>=64)break;if(!queries.has(c))queries.set(c,new Map());const qm=queries.get(c);for(const ar of ars){if(extraSamples>=64)break;for(const e of ar){if(extraSamples>=64)break;if(e.next&&e.prev?.p>=big2&&e.p>=big2&&!qm.has(e.t)){qm.set(e.t,[]);extraSamples++;}}}}
 let occupationChecks=0,degreeChecksOcc=0,distinctWaitingChecks=0,clockChecks=0,queryTicks=0,maxActive=0,maxGroup=0,maxDegreeOcc=0,goodTicks=0,crossingChecks=0,positiveCrossings=0;
 const sampledGood=new Map();let totalOrientedMassTime=0,totalSymmetricMassTime=0,sampledRootTime=0,degreeTimeEnvelope=0,maxEndpointCoefficient=0,acceptedEndpointCost=0;
 // Group by waiting horizon at a common integer time; all active tags at one horizon have the same next event.
 for(const [c,q] of queries){
   const ars=byCell.get(c),ptr=new Int32Array(ars.length);
   for(const t of [...q.keys()].sort((a,b)=>a-b)){
     queryTicks++;const hs=new Map(),tag=new Map(),meta=new Map(),fine=new Map(),agg=new Map();
     for(let i=0;i<ars.length;i++){const ar=ars[i];while(ptr[i]+1<ar.length&&ar[ptr[i]+1].t<=t)ptr[i]++;const e=ar[ptr[i]];if(!e.next||t<e.t||t>=e.next.t)continue;
       let g=hs.get(e.C);if(!g){g={C:e.C,p:e.p,s:e.next.t,n:0};hs.set(e.C,g);}else ok(g.p===e.p&&g.s===e.next.t,"same waiting horizon deterministic exit");
       g.n++;tag.set(e.M,g);const q0=e.prev?.p||0,a={M:e.M,C:e.C,p:e.p,q:q0,t0:e.t,s:e.next.t};meta.set(e.M,a);if(q0>=big2&&e.p>=big2){ok(q0!==e.p&&mod(e.C+2*(e.t%2),q0)===0&&mod(e.t,2*q0)===(e.t%2?q0+2:0)&&mod(e.C+(e.next.t%2?1:-1),e.p)===0&&mod(e.next.t,2*e.p)===(e.next.t%2?e.p+2:0),"two-clock congruences");crtChecks++;for(const [map,key] of [[fine,e.C+":"+q0+":"+e.t],[agg,e.C+":"+q0]]){if(!map.has(key))map.set(key,[]);map.get(key).push(a);}}ok(e.next.t>t&&e.next.t-t<=2*e.r,"active wait");clockChecks++;
     }
     maxActive=Math.max(maxActive,tag.size);const gs=[...hs.values()];for(const g of gs){maxGroup=Math.max(maxGroup,g.n);g.crowd=gs.reduce((z,h)=>z+(Math.abs(g.C-h.C)<=Amax?h.n:0),-1);}
     const factorMax=Math.ceil(Math.log(7*X+5)/Math.log(largeP));
     let oriented=0,symmetric=0;
     for(const [map,field] of [[fine,"fineRank"],[agg,"aggRank"]])for(const ar of map.values()){ar.sort((a,b)=>a.M-b.M);for(let i=0;i<ar.length;i++)ar[i][field]=Math.min(i+1,ar.length-i);}
     function crtKind(a,b){if(a.C===b.C||Math.abs(a.C-b.C)>Amax||b.q<big2||b.p<big2)return false;
       const ent=Math.abs(a.t0-b.t0)<=d2tick,ex=Math.abs(a.s-b.s)<=d2tick,sp=a.p===b.p,sq=a.q===b.q;
       return ((ent&&ex||sp&&ent)&&b.fineRank<=rank2)||((sq&&ex||sq&&sp)&&b.aggRank<=rank2);
     }
     let o2=0,s2=0;for(const a of meta.values()){let deg=0;for(const b of meta.values()){const f=crtKind(a,b),rev=crtKind(b,a);if(f)deg++;if(f||rev)s2++;}ok(deg<=degree2,"two-clock arithmetic degree");o2+=deg;}
     ok(s2<=2*o2,"two-clock symmetry");crtOriented+=o2;crtSymmetric+=s2;
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
     ok(symmetric<=2*oriented,"symmetric total tag degree");totalOrientedMassTime+=oriented+o2;totalSymmetricMassTime+=symmetric+s2;sampledRootTime+=tag.size;degreeTimeEnvelope+=2*tag.size*(degree2+crowd+thin*(2*closeH+(2*nearTick+1)*factorMax*(Math.floor(wideH/largeP)+1)+2*(sameJ+1)));
     for(const x of q.get(t)){const g=tag.get(x.M),h=tag.get(x.Mp);ok(g&&h&&g.C!==h.C&&g.C>=x.C&&g.C<x.E&&h.C>=x.C&&h.C<x.E,"async active distinct horizons");distinctWaitingChecks++;
       const f=kind(g,h),b=kind(h,g);let j=f>=0?f:b;occupationChecks++;if(j>=0)x.goodOld++;const a2=meta.get(x.M),b2=meta.get(x.Mp),g2=crtKind(a2,b2)||crtKind(b2,a2);if(g2){crtQueryHits++;if(j<0){j=4;crtNewTicks++;}}
       if(j>=0){x.good++;x.kinds[j]++;goodTicks++;const ky=x.M+":"+x.Mp;if(!sampledGood.has(ky))sampledGood.set(ky,new Set());sampledGood.get(ky).add(t);}
       // Clock order crossing is necessarily a jump, not an equal waiting state. Test only interior consecutive ticks.
       if(t+1<Math.min(x.s,x.s2)){const g2=g.s===t+1?g.C+g.p-1:g.C,h2=h.s===t+1?h.C+h.p-1:h.C;ok(g2!==h2,"no interior waiting merger");crossingChecks++;if((g.C-h.C)*(g2-h2)<0){positiveCrossings++;ok(Math.max(g.s===t+1?g.p-1:0,h.s===t+1?h.p-1:0)>Math.abs(g.C-h.C),"crossing requires overtaking jump");}}
     }
   }
 }
 let occPaid=0,occKept=0,occEdgesPaid=0,occEdgesKept=0,occKinds=[0,0,0,0,0],occCoverChecks=0,occUnion=0,occSelectedLength=0,occEndpointTime=0,occGoodUnion=0;
 const accepted=new Map();
 for(const x of occupationEdges){
   if(x.good+1e-9>=etaOcc*x.length){x.occCovered=true;occPaid+=x.w;occEdgesPaid++;if(x.goodOld+1e-9<etaOcc*x.length){crtPaid+=x.w;crtEdges++;}for(let k=0;k<5;k++)occKinds[k]+=x.kinds[k];const ky=x.M+":"+x.Mp;if(!accepted.has(ky))accepted.set(ky,[]);accepted.get(ky).push(x);}
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
   for(const [k,e] of ends){const r=Number(k.split(":")[0]),coef=weight(r)/wt(r);ok(e.n<=quota(r)&&e.w<=coef*e.b+1e-6,"occupation actual-relative endpoint domination");maxEndpointCoefficient=Math.max(maxEndpointCoefficient,coef);eu+=e.b;ec+=e.w;}
   ok(eu<=ul&&ul<=sl&&sl<=2*ul&&etaOcc*sl<=sg+1e-6&&sg<=2*gu&&ul<=2*gu/etaOcc+1e-6,"occupation time-cover bound");occCoverChecks++;occUnion+=ul;occSelectedLength+=sl;occEndpointTime+=eu;occGoodUnion+=gu;acceptedEndpointCost+=ec;
 }
 let allSampledGood=0;for(const ts of sampledGood.values())allSampledGood+=ts.size;
 ok(allSampledGood<=totalSymmetricMassTime&&totalSymmetricMassTime<=2*totalOrientedMassTime&&totalSymmetricMassTime<=degreeTimeEnvelope&&sampledRootTime<=totalTime,"global sampled occupation budget");
 ok(occGoodUnion<=allSampledGood&&near(occPaid,acceptedEndpointCost)&&occPaid<=maxEndpointCoefficient*occEndpointTime+1e-6&&occPaid<=2*maxEndpointCoefficient*occGoodUnion/etaOcc+1e-6,"global time-transfer charge");
 ok(near(occPaid+occKept,ac.farOverlapSlow),"occupation residual partition");
 // Gain-axis relation: original gain intervals, no simultaneous-clock requirement.
 const gainY=Math.max(5,Math.ceil(B/(analytic?u:8))),gainD=Math.max(1,Math.floor(analytic?u**.25:4)),gainEta=analytic?u**(-1/16):.25;
 const gainDiv=Math.ceil(Math.log(7*X+5)/Math.log(gainY)),gainCrt=1+Math.floor(B/(2*gainY));
 function gainCaps(bp){const f=(Qm/bp)**(1/16),c0=Math.max(1,Math.floor((analytic?mg/u**.25:gainStress?8:2)*f)),c1=Math.max(1,Math.floor((analytic?mg/u**.5:gainStress?8:2)*f)),c2=Math.max(1,Math.floor((analytic?mg/u**1.5:gainStress?8:2)*f));
   return {c0,c1,c2,degree:10*c0+2*c1*(4*gainD+2+(2*gainD+1)*gainDiv)+2*c2*(2+(2*gainD+1)*gainDiv)*gainCrt};
 }
 const gainQueries=new Map(),gainGood=new Map(),gainAccepted=new Map();
 let gainControlSamples=0,gainArithmeticChecks=0,gainArithmeticMax=[0,0,0,0],gainArithmeticPositive=[0,0,0,0],gainPaid=0,gainDisjointPaid=0,gainNeverPaid=0,gainEdges=0,gainChecks=0,gainQueryCount=0,gainDegreeChecks=0,gainDegreeMax=0,gainSampledPairMeasure=0,gainEnvelope=0,gainGoodMeasure=0,gainNeverEdges=0,gainCoveredKinds=Array(8).fill(0);
 const gainID=(M,Mp,bp)=>M+":"+Mp+":"+bp;
 for(const z of farSlowEdges)if(!z.occCovered){
   const c=sourceCell(z.M),bp=P(z.r);z.gainGood=0;z.gainKinds=Array(8).fill(0);z.gainF=byRoot.get(z.M).get(z.E).endC;
   ok(z.gainF>z.E&&z.Ftime>z.t&&sourceCell(z.Mp)===c,"gain extended interval");
   if(!gainQueries.has(c))gainQueries.set(c,new Map());const qs=gainQueries.get(c);
   for(let x=z.C;x<z.E;x+=2){if(!qs.has(x))qs.set(x,[]);qs.get(x).push(z);}
 }
 // Independent actual gain controls, including analytic mode with an empty residual.
 for(const [c,ars] of byCell){if(gainControlSamples>=32)break;if(!gainQueries.has(c))gainQueries.set(c,new Map());const qs=gainQueries.get(c);
   for(const ar of ars){if(gainControlSamples>=32)break;for(const e of ar){if(gainControlSamples>=32)break;
     if(e.next&&e.prev&&(e.p>=gainY||e.prev.p>=gainY)&&!qs.has(e.C)){qs.set(e.C,[]);gainControlSamples++;}}}}
 // Each root occupies one original gain interval at x. Waiting measure per two gain units.
 function gainWt(e){return 2*(e.next.t-e.t)/(e.p-1);}
 function gNear(list,a,b,cap){if(!list)return false;return b>a?ub(list,b)-ub(list,a)<=cap:ub(list,a-1)-ub(list,b-1)<=cap;}
 for(const [c,qs] of gainQueries){
   const ev=byCell.get(c).flat().filter(e=>e.next).sort((a,b)=>a.C-b.C||a.M-b.M),live=new Map();let ei=0;
   for(const x of [...qs.keys()].sort((a,b)=>a-b)){
     for(const [M,e] of live)if(e.next.C<=x)live.delete(M);
     while(ei<ev.length&&ev[ei].C<=x){const e=ev[ei++];if(e.next.C>x){ok(!live.has(e.M),"one active gain interval");live.set(e.M,e);}}
     const ar=[...live.values()].sort((a,b)=>a.M-b.M),all=ar.map(e=>e.M),maps=Array.from({length:6},()=>new Map());
     const keys=e=>[e.C,e.next.C,e.C+":"+e.p,e.C+":"+e.p+":"+e.next.t,e.C+":"+(e.prev?.p||0),e.C+":"+(e.prev?.p||0)+":"+e.t];
     for(const e of ar){ok(e.C<=x&&x+2<=e.next.C&&e.next.C-e.C===e.p-1,"gain occupation exact interval");const kk=keys(e);for(let i=0;i<6;i++){const m=maps[i],k=kk[i];if(!m.has(k))m.set(k,[]);m.get(k).push(e.M);}}
     function gKind(a,b,cap){if(a.M===b.M)return -1;const {c0,c1,c2}=cap,k=keys(b),ap=a.prev?.p||0,bp=b.prev?.p||0,near=(i,m)=>gNear(maps[i].get(k[i]),a.M,b.M,m);
       if(gNear(all,a.M,b.M,c0))return 0;
       if(a.C===b.C&&near(0,c0))return 1;
       if(a.next.C===b.next.C&&near(1,c0))return 2;
       if(a.p===b.p&&near(2,c0))return 3;
       if((Math.abs(a.C-b.C)<=gainD&&near(0,c1))||(Math.abs(a.next.C-b.next.C)<=gainD&&near(1,c1)))return 4;
       if(b.p>=gainY&&Math.abs(a.next.t-b.next.t)<=gainD&&near(3,c1))return 5;
       if(bp>=gainY&&ap===bp&&near(4,c2))return 6;
       if(bp>=gainY&&Math.abs(a.t-b.t)<=gainD&&near(5,c2))return 7;
       return -1;
     }
     // Check the individual arithmetic capacities before imposing source rank or priority.
     const checkFocal=new Map();for(const z of qs.get(x)){checkFocal.set(z.M,live.get(z.M));checkFocal.set(z.Mp,live.get(z.Mp));}
     if(!checkFocal.size)for(const a of ar)if(a.p>=gainY||(a.prev?.p||0)>=gainY)checkFocal.set(a.M,a);
     for(const a of checkFocal.values()){
       const g=[new Set(),new Set(),new Set(),new Set()],aq=a.prev?.p||0;
       for(const b of ar){const q=b.prev?.p||0;
         if(b.p===a.p){ok(mod(b.C+(b.next.t%2?1:-1),b.p)===0,"same gain label arithmetic");g[0].add(b.C);}
         if(b.p>=gainY&&Math.abs(a.next.t-b.next.t)<=gainD){ok(mod(b.next.t-(b.next.t%2?2:0),b.p)===0&&mod(b.C+(b.next.t%2?1:-1),b.p)===0,"gain exit arithmetic");g[1].add(b.C+":"+b.p+":"+b.next.t);}
         if(q>=gainY&&aq===q){ok(mod(b.C+2*(b.t%2),q)===0,"same gain incoming arithmetic");g[2].add(b.C+":"+q);}
         if(q>=gainY&&Math.abs(a.t-b.t)<=gainD){ok(mod(b.t-2*(b.t%2),q)===0&&mod(b.C+2*(b.t%2),q)===0,"gain entry arithmetic");g[3].add(b.C+":"+q+":"+b.t);}
       }
       const bd=[2,(2*gainD+1)*gainDiv,2*gainCrt,(2*gainD+1)*gainDiv*gainCrt];
       for(let k=0;k<4;k++){ok(g[k].size<=bd[k],"individual gain arithmetic capacity");gainArithmeticMax[k]=Math.max(gainArithmeticMax[k],g[k].size);if(g[k].size>1)gainArithmeticPositive[k]++;}gainArithmeticChecks++;
     }
     const seenFocal=new Set(),seenPairs=new Set();
     for(const z of qs.get(x)){
       const a=live.get(z.M),b=live.get(z.Mp),bp=P(z.r),cap=gainCaps(bp),id=gainID(z.M,z.Mp,bp);
       ok(a&&b&&a.C>=z.C&&b.C>=z.C&&a.next.C<=z.E&&b.next.C<=z.E,"both gain paths traverse common segment");gainChecks++;
       const fok=z.M+":"+bp;if(!seenFocal.has(fok)){seenFocal.add(fok);let deg=0;for(const p of ar)if(gKind(a,p,cap)>=0)deg++;
         ok(deg<=cap.degree,"gain arithmetic degree");gainDegreeChecks++;gainDegreeMax=Math.max(gainDegreeMax,deg);gainEnvelope+=gainWt(a)*cap.degree;}
       const k=gKind(a,b,cap);gainQueryCount++;if(k>=0){const w=gainWt(a);z.gainGood+=w;z.gainKinds[k]+=w;
         if(!seenPairs.has(id)){seenPairs.add(id);gainSampledPairMeasure+=w;if(!gainGood.has(id))gainGood.set(id,new Map());gainGood.get(id).set(x,w);}
       }
     }
   }
 }
 ok(gainSampledPairMeasure<=gainEnvelope+1e-6,"gain sampled degree-time bound");
 for(const z of farSlowEdges)if(!z.occCovered&&z.gainGood+1e-9>=gainEta*(z.Ftime-z.t)){
   z.gainCovered=true;gainPaid+=z.w;gainEdges++;if(z.disjoint)gainDisjointPaid+=z.w;
   if(!firstWait(z.M,z.Mp)){gainNeverPaid+=z.w;gainNeverEdges++;}
   for(let k=0;k<8;k++)gainCoveredKinds[k]+=z.gainKinds[k];
   const id=gainID(z.M,z.Mp,P(z.r));if(!gainAccepted.has(id))gainAccepted.set(id,[]);gainAccepted.get(id).push(z);
 }
 function muAt(M,x){const ar=roots.get(M);let l=0,r=ar.length;while(l<r){const mid=(l+r)>>1;if(ar[mid].C<=x)l=mid+1;else r=mid;}const e=ar[l-1];ok(e&&e.next&&e.C<=x&&x+2<=e.next.C,"gain measure oracle");return gainWt(e);}
 let gainCoverChecks=0,gainMuUnion=0,gainMuSelected=0,gainMuEndpoint=0,gainMaxCoefficient=0;
 for(const [id,zs] of gainAccepted){
   const iv=zs.slice().sort((a,b)=>a.C-b.C||b.gainF-a.gainF),chosen=[],ends=new Map(),ux=new Set(),cx=new Set();let i=0,reach=-1;
   for(const z of iv){for(let x=z.C;x<z.gainF;x+=2)ux.add(x);const k=z.r+":"+z.E,o=ends.get(k)||{w:0,n:0,b:z.Ftime-z.s};o.w+=z.w;o.n++;ends.set(k,o);}
   while(i<iv.length){if(iv[i].C>reach)reach=iv[i].C;let best=null;while(i<iv.length&&iv[i].C<=reach){if(!best||iv[i].gainF>best.gainF)best=iv[i];i++;}if(best&&best.gainF>reach){chosen.push(best);reach=best.gainF;}}
   let sel=0,good=0,uni=0,gu=0,em=0,ec=0,mc=0;const M=iv[0].M,gm=gainGood.get(id);
   for(let j=0;j<chosen.length;j++){const z=chosen[j];if(j>=2)ok(chosen[j-2].gainF<=z.C,"gain cover depth");sel+=z.Ftime-z.t;good+=z.gainGood;let mm=0;for(let x=z.C;x<z.gainF;x+=2){cx.add(x);mm+=muAt(M,x);}ok(near(mm,z.Ftime-z.t),"gain measure agrees actual time");}
   ok(cx.size===ux.size&&[...ux].every(x=>cx.has(x)),"gain exact cover union");
   for(const x of ux){uni+=muAt(M,x);if(gm.has(x))gu+=gm.get(x);}
   for(const [k,o] of ends){const r=Number(k.split(":")[0]),coef=weight(r)/wt(r);ok(o.n<=quota(r)&&o.w<=coef*o.b+1e-6,"gain endpoint coefficient");mc=Math.max(mc,coef);em+=o.b;ec+=o.w;}
   ok(em<=uni+1e-6&&uni<=sel+1e-6&&sel<=2*uni+1e-6&&gainEta*sel<=good+1e-6&&good<=2*gu+1e-6&&ec<=mc*em+1e-6,"weighted gain-cover transfer");
   gainCoverChecks++;gainMuUnion+=uni;gainMuSelected+=sel;gainMuEndpoint+=em;gainGoodMeasure+=gu;gainMaxCoefficient=Math.max(gainMaxCoefficient,mc);
 }
 ok(gainGoodMeasure<=gainSampledPairMeasure+1e-6&&gainPaid<=gainMaxCoefficient*gainMuEndpoint+1e-6&&gainPaid<=2*gainMaxCoefficient*gainGoodMeasure/gainEta+1e-6,"global gain occupation transfer");
 // The clock-state forest includes one terminal snapshot, which expires immediately.
 const wfBase=Math.max(1,Math.floor(analytic?mg/u**.25:2)),H0=Math.ceil(4*H)+2;
 const massAt=x=>Math.max(1,Math.floor(wfBase*Math.sqrt(H0/(x+1))));
 const caps=[...new Set([wfBase,2*wfBase,4*wfBase,massAt(0)])].sort((a,b)=>a-b);
 const wp=caps.map(m=>({m,D:0,loss:0,first:0}));
 const ff=(n,m)=>n<=m?n*n:2*m*n-m*m;
 const ledger=new Map(),queriesWF=new Map(),pairsWF=new Map(),massHist=new Map();
 const pairId=(a,b)=>Math.min(a,b)+":"+Math.max(a,b);
 function addCharge(M,Mp,r,E,cost,type){
   if(cost<=0)return;const e=byRoot.get(M).get(E),id=M+":"+Mp+":"+r+":"+E,x=ledger.get(id)||{M,Mp,r,E,t:e.endT-e.actual,F:e.endT,b:e.actual,cost:0,type};
   ok(x.type===type&&e.actual>0,"waiting charge block");x.cost+=cost;ledger.set(id,x);
 }
 for(const v of endpoints.values())if(v.cls!=="far"&&v.aw>0){
   const q=pairCharges.get(pairId(v.M,v.Mp));
   if(q.physicalLocal>(v.cls==="already"?ma:mb))addCharge(v.M,v.Mp,v.r,v.E,v.aw,v.cls);
 }
 for(const x of farSlowEdges)if(!x.occCovered&&!x.gainCovered)addCharge(x.M,x.Mp,x.r,x.E,x.w,"far");
 function firstWait(M,Mp){
   const a=roots.get(M),b=roots.get(Mp);let i=0,j=0;
   while(i<a.length&&j<b.length){const x=a[i],y=b[j],l=Math.max(x.t,y.t),xe=x.next?.t??x.t+1,ye=y.next?.t??y.t+1,r=Math.min(xe,ye);
     if(l<r&&x.C===y.C)return {t:l,C:x.C,terminal:(x.next===null||y.next===null),bothArrive:x.t===l&&y.t===l};
     if(xe<=ye)i++;if(ye<=xe)j++;
   }return null;
 }
 for(const x of ledger.values()){const id=pairId(x.M,x.Mp);if(!pairsWF.has(id)){
   const M=Math.min(x.M,x.Mp),Mp=Math.max(x.M,x.Mp),v=firstWait(M,Mp);const q={M,Mp,v,mass:0,rank:0,stationary:false};pairsWF.set(id,q);
   if(v){const k=sourceCell(M)+":"+v.t+":"+v.C;if(!queriesWF.has(k))queriesWF.set(k,[]);queriesWF.get(k).push(q);}
 }}
 // Independent small-window rank oracle, including pairs with no retained charge.
 const oracleRankMap=new Map();let oracleOnlyCount=0,oracleRankChecks=0;
 if(X<=1024)for(const ars of byCell.values()){const ids=ars.map(a=>a[0].M).sort((a,b)=>a-b);for(let i=0;i<ids.length;i++){
   const M=ids[i],list=[];for(let j=i+1;j<ids.length;j++){const Mp=ids[j],v=firstWait(M,Mp);if(v)list.push({Mp,v});}
   list.sort((a,b)=>a.v.t-b.v.t||a.Mp-b.Mp);
   for(let k=0;k<list.length;k++){const {Mp,v}=list[k],id=pairId(M,Mp);let q=pairsWF.get(id);
     if(!q){q={M,Mp,v,mass:0,rank:0,stationary:false};const ky=sourceCell(M)+":"+v.t+":"+v.C;if(!queriesWF.has(ky))queriesWF.set(ky,[]);queriesWF.get(ky).push(q);oracleOnlyCount++;}
     oracleRankMap.set(id,{q,expected:k+1});
   }
 }}
 let waitingEvents=0,waitingVertices=0,waitingRootInjections=0,waitingExpirations=0,waitingFirstPairs=0,stationaryFirstPairs=0,jumpJumpFirstPairs=0,rootFirstPairs=0,rankSum=0,rankChecks=0,queryCountWF=0,terminalQuery=0,stationaryQuery=0;
 const seen=new Map(),localHist=new Map();
 const ent=n=>n?n*Math.log(n):0,gapBase=Math.max(1,Math.floor(analytic?wfBase/u:2)),gapHist=new Map();let entD=0,entLoss=0,minorityTotal=0,gapNewCost=0,gapNewUnits=0,gapDeepUnits=0;
 // Count cross-branch pairs by distance in the ORDERED MERGED group.
 const gapCaps=[1,2,4,8,16],gapCounts=gapCaps.map(()=>0);let entryChecks=0,cohortDegreeChecks=0,localScoreChecks=0,localFormationPairs=0,rootStationaryPairs=0,cohortImprovedPairs=0,maxCohorts=0,maxEligibleCohorts=0,regularCohorts=0,nearCohorts=0,sameCohorts=0,maxLocalScore=0,localPotentialChecks=0;const Z=analytic?Math.max(1,Math.floor(u**.125)):2;const endRank=(i,n)=>Math.min(i+1,n-i);
 function ub(a,x){let l=0,r=a.length;while(l<r){let m=(l+r)>>1;if(a[m]<=x)l=m+1;else r=m;}return l;}
 // Process only original event ticks, keeping waiting groups between them.
 for(const [c,ars] of byCell){
   const events=ars.flat().sort((a,b)=>a.t-b.t||a.C-b.C||a.M-b.M),active=new Map(),entryMeta=new Map();
   for(let i=0;i<events.length;){const t=events[i].t,arr=new Map(),rem=new Map();let j=i;
     for(;j<events.length&&events[j].t===t;j++){const e=events[j];waitingEvents++;if(e.prev){if(!rem.has(e.prev.C))rem.set(e.prev.C,[]);rem.get(e.prev.C).push(e.M);}else waitingRootInjections++;
       if(!arr.has(e.C))arr.set(e.C,[]);arr.get(e.C).push(e);}
     for(const [C,ms] of rem){const old=active.get(C);ok(old&&old.length===ms.length,"whole waiting group moves");ms.sort((a,b)=>a-b);ok(ms.every((m,i)=>m===old[i]),"waiting predecessor exact tags");active.delete(C);}
     for(const [C,es] of arr){
       const branches=new Map(),stationary=active.get(C)||[],term=new Set();if(stationary.length)branches.set("stay",stationary);
       for(const e of es){const k=e.prev?"jump:"+e.prev.C:"root:"+e.M;if(!branches.has(k))branches.set(k,[]);branches.get(k).push(e.M);if(!e.next)term.add(e.M);}
       const parent=new Map(),all=[];let jumpMass=0,jumpSquares=0,rootMass=0;
       for(const [k,ms] of branches){ms.sort((a,b)=>a-b);for(const M of ms){ok(!parent.has(M),"unique waiting parent");parent.set(M,{k,ms});all.push(M);}if(k.startsWith("jump")){jumpMass+=ms.length;jumpSquares+=ms.length**2;}if(k.startsWith("root"))rootMass+=ms.length;}
       all.sort((a,b)=>a-b);const n=all.length,counts=[...branches.values()].map(x=>x.length),pairs=(n*n-counts.reduce((s,x)=>s+x*x,0))/2;
       const minMass=n-Math.max(...counts),dEnt=ent(n)-counts.reduce((z,a)=>z+ent(a),0);
       ok(dEnt+1e-7>=Math.log(2)*minMass,"entropy minor branch");entD+=dEnt;entLoss+=ent(n)-ent(n-term.size);minorityTotal+=minMass;
       for(let k=0;k<gapCaps.length;k++){const m=gapCaps[k];let local=0;for(let a=0;a<n;a++)for(let b=a+1;b<Math.min(n,a+m+1);b++)if(parent.get(all[a]).k!==parent.get(all[b]).k)local++;
         ok(local<=2*m*minMass,"ordered merger rank gap");gapCounts[k]+=local;}
       const sp=stationary.length*jumpMass,jp=(jumpMass**2-jumpSquares)/2,rp=rootMass*(n-rootMass)+rootMass*(rootMass-1)/2;
       ok(pairs===sp+jp+rp,"waiting first branch partition");waitingFirstPairs+=pairs;stationaryFirstPairs+=sp;jumpJumpFirstPairs+=jp;rootFirstPairs+=rp;massHist.set(n,(massHist.get(n)||0)+pairs);waitingVertices++;
       // Refine the stationary predecessor by its ORIGINAL entry tick and incoming label.
       const localScores=new Map(),rawScores=new Map(),stationMeta=new Map(),cohorts=new Map(),localCounts=wp.map(()=>0);
       if(stationary.length){
         rootStationaryPairs+=stationary.length*rootMass;
         const rr=Math.min(...fs(C-1),...fs(C+1));ok(Number.isFinite(rr),"stationary eligible minimum");
         stationary.sort((a,b)=>a-b);
         for(let i=0;i<stationary.length;i++){
           const M=stationary[i],e=entryMeta.get(M),q=e.prev?.p||0;
           ok(e.C===C&&e.t<t&&e.next&&e.next.t>t&&t-e.t<2*rr,"stationary entry window");
           if(q){ok(mod(C+2*(e.t%2),q)===0&&mod(e.t,2*q)===(e.t%2?q+2:0),"entry horizon and tick");entryChecks++;}
           else ok(C===2*M-2&&e.t===M+2,"stationary root entry");
           const key=e.t+":"+q,g=cohorts.get(key)||{q,t:e.t,ms:[]};g.ms.push(M);cohorts.set(key,g);
           stationMeta.set(M,{rank:endRank(i,stationary.length),g});
         }
         maxCohorts=Math.max(maxCohorts,cohorts.size);
         for(const g of cohorts.values())for(let i=0;i<g.ms.length;i++)stationMeta.get(g.ms[i]).cr=endRank(i,g.ms.length);
         const omega=new Set(fs(C).concat(fs(C+2))).size;
         for(const [k,ms] of branches){if(k==="stay")continue;const q=k.startsWith("jump")?C-Number(k.slice(5))+1:0;
           if(q)ok(q>=3&&mod(C+2*(t%2),q)===0&&mod(t,2*q)===(t%2?q+2:0),"arriving branch congruence");
           const eligible=new Set();
           for(const g of cohorts.values()){const d=t-g.t,reg=g.q>0&&g.q*Z>=rr,near0=d<=2*Z,same=q>0&&g.q===q&&d<=2*Z*q;if(reg)regularCohorts++;if(near0)nearCohorts++;if(same)sameCohorts++;if(reg||near0||same)eligible.add(g);}
           const K=eligible.size;ok(K<=(3*Z+2)*omega+Z+1,"arithmetic stationary cohort bound");cohortDegreeChecks++;maxEligibleCohorts=Math.max(maxEligibleCohorts,K);
           for(let i=0;i<ms.length;i++)for(const S of stationary){const z=stationMeta.get(S),aRank=endRank(i,ms.length),sRank=eligible.has(z.g)?Math.min(z.rank,K*z.cr):z.rank,score=Math.max(aRank,sRank);
             ok(score>=1,"local stationary rank");const id=pairId(ms[i],S);ok(!localScores.has(id),"first local pair unique");localScores.set(id,score);const raw=Math.max(aRank,z.rank);rawScores.set(id,raw);if(score<raw)cohortImprovedPairs++;localHist.set(score,(localHist.get(score)||0)+1);localFormationPairs++;maxLocalScore=Math.max(maxLocalScore,score);
             for(let k0=0;k0<wp.length;k0++)if(score<=wp[k0].m)localCounts[k0]++;
           }
         }
         for(let k0=0;k0<wp.length;k0++){const m=wp[k0].m,D=ff(n,m)-counts.reduce((s,x)=>s+ff(x,m),0);ok(localCounts[k0]<=8*D,"stationary capped admission potential");localPotentialChecks++;}
       }
       for(const v of wp){const D=ff(n,v.m)-counts.reduce((s,x)=>s+ff(x,v.m),0);ok(D>=0,"waiting convex increment");v.D+=D;v.loss+=ff(n,v.m)-ff(n-term.size,v.m);if(n<=v.m)v.first+=pairs;}
       for(const q of queriesWF.get(c+":"+t+":"+C)||[]){const p=parent.get(q.M),p2=parent.get(q.Mp);ok(p&&p2&&p.k!==p2.k,"queried first waiting merger branches");q.mass=n;q.orderGap=ub(all,q.Mp)-ub(all,q.M);ok(q.orderGap>0,"positive merger rank gap");q.stationary=p.k==="stay"||p2.k==="stay";q.localScore=localScores.get(pairId(q.M,q.Mp))??Infinity;q.rawLocalScore=rawScores.get(pairId(q.M,q.Mp))??Infinity;ok(q.stationary===Number.isFinite(q.localScore),"stationary local-score coverage");if(q.stationary)localScoreChecks++;q.rank=(seen.get(q.M)||0)+ub(all,q.Mp)-ub(all,q.M)-ub(p.ms,q.Mp)+ub(p.ms,q.M);ok(q.rank>=1,"waiting first rank");rankChecks++;queryCountWF++;if(q.v.terminal)terminalQuery++;if(q.stationary)stationaryQuery++;}
       for(let z=0;z<n;z++){const M=all[z],p=parent.get(M),inc=n-z-1-(p.ms.length-ub(p.ms,M));ok(inc>=0,"new larger partner count");seen.set(M,(seen.get(M)||0)+inc);rankSum+=inc;}
       waitingExpirations+=term.size;for(const e of es)entryMeta.set(e.M,e);for(const M of term)entryMeta.delete(M);const remain=all.filter(M=>!term.has(M));if(remain.length)active.set(C,remain);else active.delete(C);
     }i=j;
   }ok(active.size===0&&entryMeta.size===0,"waiting forest expires");
 }
 ok(waitingRootInjections===N&&waitingExpirations===N&&waitingFirstPairs===rankSum&&waitingFirstPairs===stationaryFirstPairs+jumpJumpFirstPairs+rootFirstPairs,"waiting forest root and rank ledger");
 ok(near(entD,entLoss)&&entD<=N*(Math.log(N)+1)+1e-6&&Math.log(2)*minorityTotal<=entD+1e-6,"expiry entropy budget");
 for(let k=0;k<gapCaps.length;k++)ok(gapCounts[k]<=2*gapCaps[k]*minorityTotal,"global rank gap budget");
 for(const v of wp)ok(v.D===v.loss-N&&v.D<=2*v.m*N&&v.first<=v.m*N,"waiting forest potential");
 let oraclePairs=0,oracleTerminal=0,oracleEarly=0,oracleNoPhysical=0,oracleStationary=0;
 if(X<=1024){let c0=0;const hist=new Map();
   for(const ars of byCell.values()){const ids=ars.map(a=>a[0].M).sort((a,b)=>a-b);for(let i=0;i<ids.length;i++){const M=ids[i],a=roots.get(M),res=[];
     for(let j=i+1;j<ids.length;j++){const Mp=ids[j],v=firstWait(M,Mp);if(!v)continue;c0++;res.push({Mp,v});if(v.terminal)oracleTerminal++;if(!v.bothArrive)oracleStationary++;
       const b=roots.get(Mp);let k=0,l=0,phys=null;while(k<a.length&&l<b.length){if(a[k].t<b[l].t)k++;else if(a[k].t>b[l].t)l++;else{if(a[k].C===b[l].C){phys=a[k].t;break;}k++;l++;}}
       if(phys===null)oracleNoPhysical++;else{ok(v.t<=phys,"waiting meeting no later than physical");if(v.t<phys)oracleEarly++;}
     }
     res.sort((a,b)=>a.v.t-b.v.t||a.Mp-b.Mp);for(let k=0;k<res.length;k++){const q=pairsWF.get(pairId(M,res[k].Mp));if(q)ok(q.rank===k+1,"independent chronological rank");}
   }}oraclePairs=c0;ok(oraclePairs===waitingFirstPairs,"independent all first waiting pairs");}
 let paidMass=0,paidRank=0,paidBand=0,paidLocal=0,paidRawLocal=0,paidCohortOnly=0,localOnlyLarge=0,bandUnits=0,localUnits=0,localFar=0,bandFar=0,localPairSet=new Set(),bandPairSet=new Set(),keptWF=0,neverCost=0,farFuture=0,farPaid=0,syncPaid=0,immediatePaid=0,paidUnits=0,massUnits=0,rankUnits=0,maxCoefWF=0,ledgerCost=0,ledgerBlocks=0,meetingPairs=0,neverPairs=0,farFuturePairs=new Set(),paidPairs=new Set(),maxMeetingMass=0,maxRankWF=0,farMeetingChecks=0,largeMassPaid=0;
 const pairBlocks=new Map();for(const q of pairsWF.values()){if(q.v){meetingPairs++;ok(q.mass>0&&q.rank>0,"queried waiting merger found");maxMeetingMass=Math.max(maxMeetingMass,q.mass);maxRankWF=Math.max(maxRankWF,q.rank);}else neverPairs++;}
 ok(meetingPairs+oracleOnlyCount===queryCountWF,"all requested waiting meetings found");for(const {q,expected} of oracleRankMap.values()){ok(q.rank===expected,"all small-window independent chronological ranks");oracleRankChecks++;}
 for(const x of ledger.values()){ledgerCost+=x.cost;ledgerBlocks++;const q=pairsWF.get(pairId(x.M,x.Mp)),coef=weight(x.r)/wt(x.r);ok(x.cost<=coef*x.b+1e-6&&x.F-x.t===x.b,"actual density cap");maxCoefWF=Math.max(maxCoefWF,coef);
   const ky=x.M+":"+x.Mp;if(!pairBlocks.has(ky))pairBlocks.set(ky,[]);pairBlocks.get(ky).push(x);
   if(!q.v){ok(x.type==="far","synchronous pair has waiting merger");neverCost+=x.cost;keptWF+=x.cost;x.rem=x.cost;continue;}
   if(x.type==="far"){ok(q.v.C>x.E,"far meeting after shared horizon");const ar=roots.get(x.M),br=roots.get(x.Mp),ea=ar.find(e=>e.C===x.E),eb=br.find(e=>e.C===x.E);ok(ea.next.t<=q.v.t&&eb.next.t<=q.v.t,"far E completed before waiting merger");farFuture+=x.cost;farFuturePairs.add(pairId(x.M,x.Mp));farMeetingChecks++;}
   let nm=0,nr=0,nb=0,nl=0,nc=0,ng=0;const bp=P(x.r),fac=(Qm/bp)**(1/16);for(let t=x.t;t<x.F;t++){const xdist=Math.abs(t-q.v.t);ok(xdist<H0,"within focal lifetime");const m=massAt(xdist),mp=Math.max(m,Math.floor(wfBase*fac*Math.sqrt(H0/(xdist+1))));if(q.mass<=m)nm++;else if(q.rank<=m)nr++;else if(q.mass<=mp||q.rank<=mp)nb++;else if(q.localScore<=mp){nl++;if(q.rawLocalScore>mp)nc++;}else if(q.orderGap<=Math.max(1,Math.floor(gapBase*fac*Math.sqrt(H0/(xdist+1))))){ng++;gapNewUnits++;gapNewCost+=x.cost/x.b;if(q.rawLocalScore>mp)gapDeepUnits++;}}
   x.rem=x.cost*(x.b-nm-nr-nb-nl-ng)/x.b;const wm=x.cost*nm/x.b,wr=x.cost*nr/x.b,wb=x.cost*nb/x.b,wl=x.cost*nl/x.b;paidMass+=wm;paidRank+=wr;paidBand+=wb;paidLocal+=wl;paidCohortOnly+=x.cost*nc/x.b;paidRawLocal+=x.cost*(nl-nc)/x.b;massUnits+=nm;rankUnits+=nr;bandUnits+=nb;localUnits+=nl;paidUnits+=nm+nr+nb+nl;keptWF+=x.cost-wm-wr-wb-wl;if(nb)bandPairSet.add(ky);if(nl){localPairSet.add(ky);localOnlyLarge+=wl;}if(x.type==="far"){localFar+=wl;bandFar+=wb;}
   if(q.mass>wfBase)largeMassPaid+=wm+wr+wb+wl;if(nm+nr+nb+nl)paidPairs.add(ky);
   if(x.type==="far")farPaid+=wm+wr+wb+wl;else if(x.type==="already")syncPaid+=wm+wr+wb+wl;else immediatePaid+=wm+wr+wb+wl;
 }
 for(const ar of pairBlocks.values()){ar.sort((a,b)=>a.t-b.t);for(let i=1;i<ar.length;i++)ok(ar[i-1].F<=ar[i].t,"disjoint later actual blocks per pair");}
 let layerSum=0,layerMass=0,layerRank=0;
 // Exact finite upper counts for all possible time distances from first meeting.
 for(let x=0;x<H0;x++)layerSum+=massAt(x);
 for(const [n,c] of massHist){let l=0,r=H0;while(l<r){const m=(l+r)>>1;if(massAt(m)>=n)l=m+1;else r=m;}layerMass+=4*l*c;}
 for(const c of seen.values()){let sum=0;for(let r=1;r<=c;r++){let l=0,h=H0;while(l<h){const x=(l+h)>>1;if(massAt(x)>=r)l=x+1;else h=x;}sum+=l;if(l===0)break;}layerRank+=4*sum;}
 ok(massUnits<=layerMass&&rankUnits<=layerRank&&layerMass<=4*N*layerSum&&layerRank<=4*N*layerSum,"integrated waiting formation budgets");
 let cdf=0;for(const [m,n] of [...localHist].sort((a,b)=>a[0]-b[0])){cdf+=n;ok(cdf<=16*m*N,"global local-rank pair count");}
 ok(cdf===localFormationPairs&&localFormationPairs===stationaryFirstPairs+rootStationaryPairs&&near(paidLocal,paidRawLocal+paidCohortOnly),"local first pair ledger");
 let bandLayerEnvelope=0,localLayerEnvelope=0;for(let bp=2;bp<Qm;bp*=2){const f=(Qm/bp)**(1/16);let sum=0;for(let x=0;x<H0;x++)sum+=Math.max(1,Math.floor(wfBase*f*Math.sqrt(H0/(x+1))));bandLayerEnvelope+=8*N*sum;localLayerEnvelope+=64*N*sum;}
 ok(bandUnits<=bandLayerEnvelope&&localUnits<=localLayerEnvelope,"band adaptive integrated layers");
 ok(near(ledgerCost,ac.largeAlready+ac.largeImmediate+ac.farDisjointSlow+occKept-gainPaid)&&near(ledgerCost,paidMass+paidRank+paidBand+paidLocal+keptWF)&&near(paidMass+paidRank+paidBand+paidLocal,farPaid+syncPaid+immediatePaid)&&paidMass+paidRank+paidBand+paidLocal<=maxCoefWF*paidUnits+1e-6,"waiting actual charge partition");
 // Independently test the same entropy/ordered-rank inequality on high physical tail layers.
 const physicalLayers=[];for(const layer of [1,Math.max(1,Math.floor(B/4)),B]){
   let D=0,loss=0,minority=0,pairs=0,nRoots=0;
   for(const es of vertices.values()){
     const a=es.filter(e=>e.tail>=layer).sort((a,b)=>a.M-b.M);if(!a.length)continue;
     const groups=new Map(),keys=[];let ends=0;
     for(const e of a){const k=e.prev?e.prev.C+":"+e.prev.t:"root:"+e.M;keys.push(k);groups.set(k,(groups.get(k)||0)+1);if(!e.prev)nRoots++;if(!e.next||e.next.tail<layer)ends++;}
     const counts=[...groups.values()],n=a.length,l=n-Math.max(...counts),d=ent(n)-counts.reduce((z,k)=>z+ent(k),0);
     D+=d;loss+=ent(n)-ent(n-ends);minority+=l;let local=0;for(let i=0;i<n;i++)for(let j=i+1;j<Math.min(n,i+5);j++)if(keys[i]!==keys[j])local++;
     ok(local<=8*l&&d+1e-7>=Math.log(2)*l,"physical rank gap layer");pairs+=local;
   }
   ok(near(D,loss)&&D<=nRoots*(Math.log(N)+1)+1e-6&&pairs<=8*minority,"physical layer entropy telescope");physicalLayers.push({layer,nRoots,minority,pairs,D,loss});
 }
 ok(gapNewCost<=keptWF+1e-6&&crtPaid<=occPaid+1e-6,"new exclusion partition");
 // Window-local projected contact graph. Components are persistent WITHIN one window only.
 // Both sweeps treat a whole shared horizon as ONE simultaneous hyperedge.
 const wStats={windows:0,roots:0,merges:0,pairs:0,rankPairs:0,gapPairs:0,minority:0,entropy:0,queries:0,viaChain:0,maxMass:0};
 function sweepWindow(groups,queries,cap,gcap,reverse,stats){
   const ids=new Set();for(const g of groups)for(const M of g.ms)ids.add(M);
   const root=new Map(),parts=new Map();for(const M of ids){root.set(M,M);parts.set(M,[M]);}
   let cross=0,rankN=0,gapN=0,minor=0,entSum=0,mergeN=0,chain=0,maxMass=0;
   const todo=new Map(queries),ordered=groups.slice().sort((a,b)=>reverse?b.C-a.C:a.C-b.C);
   for(const g of ordered){
     const labs=[...new Set(g.ms.map(M=>root.get(M)))];if(labs.length<=1)continue;
     const all=labs.flatMap(k=>parts.get(k)).sort((a,b)=>a-b),n=all.length,sizes=labs.map(k=>parts.get(k).length),l=n-Math.max(...sizes),de=ent(n)-sizes.reduce((z,v)=>z+ent(v),0);
     ok(de+1e-7>=Math.log(2)*l,"window entropy increment");entSum+=de;minor+=l;mergeN++;maxMass=Math.max(maxMass,n);
     cross+=(n*n-sizes.reduce((z,a)=>z+a*a,0))/2;
     const pos=new Map(all.map((M,i)=>[M,i])),which=new Set(g.ms),rs=new Set(labs);
     let smallGap=0;
     for(let i=0;i<n;i++){
       const M=all[i],ar=parts.get(root.get(M)),old=ar.length-ub(ar,M),newN=n-i-1-old;
       ok(newN>=0,"new local larger connections");
       rankN+=Math.min(newN,Math.max(0,cap-old));
       for(let j=i+1;j<Math.min(n,i+gcap+1);j++)if(root.get(M)!==root.get(all[j]))smallGap++;
     }
     ok(smallGap<=2*gcap*l,"window interleaving gap");gapN+=smallGap;
     for(const [id,q] of todo){
       const a=root.get(q.M),b=root.get(q.Mp);if(a===b||!rs.has(a)||!rs.has(b))continue;
       const ar=parts.get(a),old=ar.length-ub(ar,q.M),newRank=ub(all,q.Mp)-ub(all,q.M)-ub(ar,q.Mp)+ub(ar,q.M),rank=old+newRank,gap=pos.get(q.Mp)-pos.get(q.M);
       ok(rank>=1&&gap>=1&&rank<=n-1,"first connection rank");
       const direct=which.has(q.M)&&which.has(q.Mp);if(!direct)chain++;
       q.scores.push({C:g.C,rank,gap,mass:n,direct,covered:rank<=cap||gap<=gcap,rankCovered:rank<=cap});todo.delete(id);
     }
     const k=labs[0];for(const M of all)root.set(M,k);for(const j of labs)parts.delete(j);parts.set(k,all);
   }
   ok(todo.size===0,"all queried common-horizon pairs connect");
   const fin=[...parts.values()].map(a=>a.length),finEnt=fin.reduce((z,a)=>z+ent(a),0),finCross=fin.reduce((z,a)=>z+a*(a-1)/2,0);
   ok(cross===finCross&&near(entSum,finEnt)&&entSum<=ids.size*Math.log(Math.max(1,ids.size))+1e-6&&rankN<=cap*ids.size&&gapN<=2*gcap*minor&&Math.log(2)*minor<=entSum+1e-6,"window exact forest budgets");
   if(X<=1024){ // independent graph connectivity oracle on query pairs, no union-find
     for(const q of queries.values()){const adj=new Map([...ids].map(m=>[m,new Set()]));let at=null;
       for(const g of ordered){for(const M of g.ms){adj.get(M).add(g.ms[0]);adj.get(g.ms[0]).add(M);}const seen=new Set([q.M]),stack=[q.M];while(stack.length){for(const b of adj.get(stack.pop()))if(!seen.has(b)){seen.add(b);stack.push(b);}}
         if(seen.has(q.Mp)){at=g.C;break;}}
       ok(at===q.scores.at(-1).C,"independent transitive first connection");
     }
   }
   stats.windows++;stats.roots+=ids.size;stats.merges+=mergeN;stats.pairs+=cross;stats.rankPairs+=rankN;stats.gapPairs+=gapN;stats.minority+=minor;stats.entropy+=entSum;stats.queries+=queries.size;stats.viaChain+=chain;stats.maxMass=Math.max(stats.maxMass,maxMass);
 }
 const winWidths=[2,8,-2,-8],mWin=(bp)=>Math.max(1,Math.floor((analytic?mg/u**.25:windowStress?4:2)*(Qm/bp)**(1/16))),gWin=bp=>Math.max(1,Math.floor(mWin(bp)/(analytic?u:2))),winWidth=(bp,k)=>Math.ceil(Math.abs(k)*(bp+L)),medWindows=new Map(),medStats={...wStats},medQueries=new Map(),medByScale={};
 function winKey(M,r,E,k){const bp=P(r),w=winWidth(bp,k);return k+":"+bp+":"+sourceCell(M)+":"+Math.floor(E/w)+(k<0?":"+r:"");}
 for(const x of ledger.values())if(x.rem>1e-9){x.win=[];for(const k of winWidths){const key=winKey(x.M,x.r,x.E,k),id=pairId(x.M,x.Mp);if(!medWindows.has(key))medWindows.set(key,{groups:new Map(),qs:new Map()});const z=medWindows.get(key),q=z.qs.get(id)||{M:Math.min(x.M,x.Mp),Mp:Math.max(x.M,x.Mp),scores:[]};z.qs.set(id,q);x.win.push(q);}}
 // Populate selected windows from FULL frozen original medium events, not the residual pair graph.
 for(const es of input)for(const e of es)for(const k of winWidths){const key=winKey(e.M,e.r,e.C,k),z=medWindows.get(key);if(z){if(!z.groups.has(e.C))z.groups.set(e.C,[]);z.groups.get(e.C).push(e.M);}}
 for(const [key,z] of medWindows){const [k,bp]=key.split(":").map(Number),g=[...z.groups].map(([C,ms])=>({C,ms})),cap=k<0&&analytic?Math.max(1,Math.floor(mWin(bp)*bp/(bp+L))):mWin(bp),gc=k<0&&analytic?Math.max(1,Math.floor(cap/u)):gWin(bp);sweepWindow(g,z.qs,cap,gc,false,medStats);sweepWindow(g,z.qs,cap,gc,true,medStats);}
 let windowPaid=0,windowNeverPaid=0,windowBlocks=0,windowRankPaid=0,windowGapPaid=0,windowChainPaid=0,windowReverseOnly=0,windowSecondScaleOnly=0,windowExactOnly=0,endpointPaid=0,endpointNeverPaid=0,endpointChecks=0,endpointMaxDegree=0,windowResidual=0,windowNeverResidual=0;
 const endQueries=new Map();
 for(const x of ledger.values())if(x.rem>1e-9){
   const scores=x.win.flatMap(q=>q.scores);ok(scores.length===8,"four-window two-sweep scores");
   if(scores.some(q=>q.covered)){windowPaid+=x.rem;windowBlocks++;if(!pairsWF.get(pairId(x.M,x.Mp)).v)windowNeverPaid+=x.rem;if(scores.some(q=>q.rankCovered))windowRankPaid+=x.rem;else windowGapPaid+=x.rem;if(scores.some(q=>q.covered&&!q.direct))windowChainPaid+=x.rem;if(!scores.some((q,i)=>i%2===0&&q.covered))windowReverseOnly+=x.rem;if(!scores[0].covered&&!scores[1].covered&&scores.slice(2,4).some(q=>q.covered))windowSecondScaleOnly+=x.rem;if(!scores.slice(0,4).some(q=>q.covered))windowExactOnly+=x.rem;x.winPaid=true;continue;}
   const key=sourceCell(x.M)+":"+x.E;if(!endQueries.has(key))endQueries.set(key,{es:[],xs:[]});endQueries.get(key).xs.push(x);
 }
 for(const es of input)for(const e of es){const z=endQueries.get(sourceCell(e.M)+":"+e.C);if(z)z.es.push(e);}
 for(const z of endQueries.values()){
   const ar=z.es.sort((a,b)=>a.M-b.M),src=ar.map(e=>e.M),ep=new Map(ar.map(e=>[e.M,e])),time=ar.slice().sort((a,b)=>a.t-b.t||a.M-b.M),exit=ar.slice().sort((a,b)=>a.endT-b.endT||a.M-b.M);
   // actual exit of medium event (not attached LOW) retrieved from original path
   const raw=new Map(ar.map(e=>[e.M,roots.get(e.M).find(v=>v.C===e.C)]));exit.sort((a,b)=>raw.get(a.M).next.t-raw.get(b.M).next.t||a.M-b.M);
   const tr=new Map(time.map((e,i)=>[e.M,i])),xr=new Map(exit.map((e,i)=>[e.M,i])),qc=new Map(),pc=new Map();
   for(const e of ar){const a=raw.get(e.M),q=a.prev?.p||0;if(!qc.has(q))qc.set(q,[]);qc.get(q).push(e.M);if(!pc.has(e.p))pc.set(e.p,[]);pc.get(e.p).push(e.M);}
   const r=ar[0].r,cap=mWin(P(r)),c2=Math.max(1,Math.floor(cap/(analytic?u:2))),C=ar[0].C;
   ok(qc.size<=new Set(fs(C).concat(fs(C+2))).size+1&&pc.size<=new Set(fs(C-1).concat(fs(C+1))).size,"endpoint label cohort count");
   function good(M,Mp){if(M===Mp)return false;return gNear(src,M,Mp,cap)||Math.abs(tr.get(M)-tr.get(Mp))<=cap||Math.abs(xr.get(M)-xr.get(Mp))<=cap||gNear(qc.get(raw.get(Mp).prev?.p||0),M,Mp,c2)||gNear(pc.get(ep.get(Mp).p),M,Mp,c2);}
   for(const M of new Set(z.xs.map(x=>x.M))){const n=ar.filter(e=>good(M,e.M)).length;ok(n<=6*cap+2*c2*(qc.size+pc.size),"direct endpoint degree");endpointChecks++;endpointMaxDegree=Math.max(endpointMaxDegree,n);}
   for(const x of z.xs){ok(ep.has(x.M)&&ep.has(x.Mp),"endpoint original pair");const never=!pairsWF.get(pairId(x.M,x.Mp)).v;if(good(x.M,x.Mp)){endpointPaid+=x.rem;if(never)endpointNeverPaid+=x.rem;}else{windowResidual+=x.rem;if(never)windowNeverResidual+=x.rem;x.revCandidate=true;}}
 }
 ok(near([...ledger.values()].reduce((z,x)=>z+x.rem,0),keptWF-gapNewCost)&&near(windowPaid+endpointPaid+windowResidual,keptWF-gapNewCost)&&near(windowNeverPaid+endpointNeverPaid+windowNeverResidual,neverCost),"new projected-window residual partition");
 // Independently bound actual charge over each focal/pair/window at its own band.
 for(const k of winWidths){const sums=new Map();for(const x of ledger.values())if(x.rem>1e-9){const key=winKey(x.M,x.r,x.E,k)+":"+x.M+":"+x.Mp,z=sums.get(key)||{cost:0,b:0,max:0,maxBlock:0,lo:Infinity,hi:-Infinity};z.cost+=x.rem;z.b+=x.b;z.max=Math.max(z.max,weight(x.r)/wt(x.r));z.maxBlock=Math.max(z.maxBlock,x.b);z.lo=Math.min(z.lo,x.E);z.hi=Math.max(z.hi,x.E);sums.set(key,z);}
   for(const z of sums.values())ok(z.cost<=z.max*z.b+1e-6&&z.b<=3*(z.hi-z.lo)+z.maxBlock,"local window actual block capacity");
 }
 // Arithmetic reverse frontiers, frozen original histories. No recursion through accounting-deleted paths.
 const revY=analytic?Math.max(5,Math.ceil(B/u)):Math.max(5,Math.ceil(B/(reverseStress?16:8))),physY=analytic?Math.max(5,Math.ceil(B/2)):revY;
 const revK=analytic?Math.max(1,Math.floor(Math.log(u)/(16*Math.log(32)))):reverseStress?3:2;
 const revJ=analytic?2*Math.max(1,Math.floor(Math.log(u)/(16*Math.log(2)))):reverseStress?16:8;
 const physK=analytic?Math.max(1,Math.floor(Math.log(u)/(32*Math.log(256)))):revK,physJ=revJ;
 const rawByRoot=new Map();for(const [M,ar] of roots)rawByRoot.set(M,new Map(ar.map(e=>[e.C,e])));
 const incoming=C=>[...new Set(fs(C).concat(fs(C+2)))];
 const binom=(n,k)=>{let v=1;for(let i=1;i<=k;i++)v=v*(n-k+i)/i;return Math.round(v);};
 const revD=Y=>2*Math.ceil(Math.log(7*X+5)/Math.log(Y)),bound=(Y,K,J)=>{let b=0;for(let k=0;k<=K;k++)b+=3*revD(Y)**k*binom(J/2+k+1,k+1);return b;};
 const revBound=bound(revY,revK,revJ),physBound=bound(physY,physK,physJ);
 const frontierCache=new Map(),revControl=new Map();let revChecks=0,revRootLeaves=0,revRootMax=0,revLabelChecks=0,revSmallChecks=0,revPhysChecks=0,revMaxCohorts=[0,0,0],revMaxDegree=[0,0,0],revDegreeChecks=0,revFullRootCount=0,revAnchorMassMax=0;
 function signature(e,Y,K,J){
   let v=e,g=0,small=0,k=0,status="",word=[],anchor=null,last=null;
   while(true){
     if(!v.prev){status="R";break;}
     const a=v.prev,q=a.p;
     if(q<Y){if(small+q-1>J){status="S";break;}small+=q-1;g+=q-1;v=a;continue;}
     if(k===K){status="K";break;}
     const D=v.C;ok(incoming(D).includes(q)&&mod(v.t,2*q)===(v.t%2?q+2:0),"frontier incoming congruence");
     word.push(g,q);g=0;k++;if(anchor)ok(anchor.t-v.t<=2*B+3*J&&anchor.t>v.t,"reverse consecutive large posttime window");else ok(e.t-v.t<=3*J,"reverse latest large posttime window");anchor=v;last=q;v=a;
   }
   word.push(g);let D=e.C,ns=0;for(let i=0;i<k;i++){const z=word[2*i],q=word[2*i+1];ok(z>=0&&z%2===0&&incoming(D-z).includes(q),"reverse projected word arithmetic");D-=z+q-1;ns+=z;revLabelChecks++;}
   D-=word[2*k];ns+=word[2*k];ok(D===v.C&&ns===small&&small<=J&&k<=K,"reverse frontier exact boundary");revSmallChecks++;
   if(status==="R"){ok(v.M===e.M&&v.C===2*e.M-2&&v.t===e.M+2&&spf[e.M]===e.M,"unique prime root leaf");revRootLeaves++;}
   if(status==="S")ok(v.prev&&v.prev.p<Y&&small+v.prev.p-1>J,"small gain overflow");
   if(status==="K")ok(k===K&&v.prev&&v.prev.p>=Y,"depth cut");
   return {key:status+":"+word.join(","),status,D,k,anchor,last,word,small};
 }
 function desc(e){
   let a=frontierCache.get(e);if(a)return a;
   let v=e,qs=[];for(let i=0;i<2;i++){if(!v.prev){qs.push(0);break;}qs.push(v.prev.p);v=v.prev;}
   let D=e.C;for(const q of qs){if(!q)break;ok(incoming(D).includes(q),"two-step exact reverse labels");D-=q-1;}ok(D===v.C,"two-step reverse horizon");
   const z=signature(e,revY,revK,revJ),f=signature(e,physY,physK,physJ);
   let phys=null;if(f.anchor){const a=f.anchor;phys=Math.floor(e.t/B)+":"+f.key+":"+a.C+":"+a.t;const ar=vertices.get(a.C+":"+a.t);ok(ar&&ar.some(t=>t.M===e.M),"actual physical frontier anchor membership");revAnchorMassMax=Math.max(revAnchorMassMax,ar.length);revPhysChecks++;}
   a={e,key2:qs.join(","),z,f,phys};frontierCache.set(e,a);revChecks++;return a;
 }
 function reversePartition(es){
   const maps=[new Map(),new Map(),new Map()],byM=new Map(),rootKeys=new Map(),byBin=new Map(),byWord=new Map(),C=es[0].C;
   for(const e of es){const a=desc(e);byM.set(e.M,a);
     for(const [i,key] of [[0,a.key2],[1,a.z.key],[2,a.phys]]){if(key===null)continue;const mp=maps[i];if(!mp.has(key))mp.set(key,[]);mp.get(key).push(e.M);}
     if(a.z.status==="R"){ok(!rootKeys.has(a.z.key),"root code injectivity at endpoint");rootKeys.set(a.z.key,e.M);}
     if(a.phys){const bin=Math.floor(e.t/B);if(!byBin.has(bin))byBin.set(bin,new Set());byBin.get(bin).add(a.phys);const key=bin+":"+a.f.key;if(!byWord.has(key))byWord.set(key,{k:a.f.k,set:new Set()});byWord.get(key).set.add(a.phys);}
   }
   for(const mp of maps)for(const ar of mp.values())ar.sort((a,b)=>a-b);
   let d2=1;for(const q of incoming(C))d2+=1+incoming(C-q+1).length;
   ok(maps[0].size<=d2&&maps[1].size<=revBound&&rootKeys.size<=revBound,"arithmetic frontier cohort capacities");
   // Per time bin, each projected word has a bounded number of actual anchor clocks.
   const clockMult=1+Math.ceil((2*B+3*physJ)/(2*physY));
   for(const set of byBin.values())ok(set.size<=physBound*clockMult**physK,"physical anchor cohort capacity");for(const {k,set} of byWord.values())ok(set.size<=clockMult**k,"per-word physical anchor clock capacity");
   revRootMax=Math.max(revRootMax,rootKeys.size);revFullRootCount+=rootKeys.size;
   revMaxCohorts[0]=Math.max(revMaxCohorts[0],maps[0].size);revMaxCohorts[1]=Math.max(revMaxCohorts[1],maps[1].size);for(const v of byBin.values())revMaxCohorts[2]=Math.max(revMaxCohorts[2],v.size);
   return {maps,byM,byBin,d2};
 }
 function reverseKinds(part,M,Mp,m){
   const a=part.byM.get(M),b=part.byM.get(Mp);if(M===Mp)return -1;
   const {maps,byBin}=part,c0=Math.max(1,Math.floor(m/maps[0].size)),c1=Math.max(1,Math.floor(m/maps[1].size));
   if(gNear(maps[0].get(b.key2),M,Mp,c0))return 0;
   if(gNear(maps[1].get(b.z.key),M,Mp,c1))return 1;
   if(b.phys){const bin=Math.floor(a.e.t/B),bp=Math.floor(b.e.t/B);if(Math.abs(bin-bp)<=1){let n=0;for(let j=bin-1;j<=bin+1;j++)n+=byBin.get(j)?.size||0;const c2=Math.max(1,Math.floor(m/Math.max(1,n)));
       if(gNear(maps[2].get(b.phys),M,Mp,c2))return 2;
   }}
   return -1;
 }
 function checkReverseDegree(part,M,m){
   const n=[0,0,0],a=part.byM.get(M),bin=Math.floor(a.e.t/B);let count=0;for(let j=bin-1;j<=bin+1;j++)count+=part.byBin.get(j)?.size||0;
   for(const Mp of part.byM.keys()){const k=reverseKinds(part,M,Mp,m);if(k>=0)n[k]++;}
   const cap=[part.maps[0].size,part.maps[1].size,count];for(let i=0;i<3;i++){ok(n[i]<=2*Math.max(m,cap[i]),"reverse frontier directed degree");revMaxDegree[i]=Math.max(revMaxDegree[i],n[i]);}revDegreeChecks++;
 }
 // Medium: same fixed source cells and same original endpoint lists as previous direct masks.
 let reversePaid=0,reverseNeverPaid=0,reverseResidual=0,reverseNeverResidual=0,reversePaidKinds=[0,0,0],reverseBlocks=0,reverseMedGroups=0;
 for(const z of endQueries.values()){
   const xs=z.xs.filter(x=>x.revCandidate);if(!xs.length)continue;const es=z.es.map(e=>rawByRoot.get(e.M).get(e.C)),part=reversePartition(es),r=es[0].r,m=analytic?mWin(P(r)):reverseStress?8:2;
   reverseMedGroups++;for(const M of new Set(xs.map(x=>x.M)))checkReverseDegree(part,M,m);
   for(const x of xs){const k=reverseKinds(part,x.M,x.Mp,m),never=!pairsWF.get(pairId(x.M,x.Mp)).v;if(k>=0){reversePaid+=x.rem;reversePaidKinds[k]+=x.rem;reverseBlocks++;if(never)reverseNeverPaid+=x.rem;}else{reverseResidual+=x.rem;if(never)reverseNeverResidual+=x.rem;x.historyCandidate=true;}}
 }
 ok(near(reversePaid+reverseResidual,windowResidual)&&near(reverseNeverPaid+reverseNeverResidual,windowNeverResidual),"reverse medium residual partition");
 // Direct projected high-rank energy, including unequal physical times; natural high list only.
 const hh=new Map();for(const ar of roots.values())for(const e of ar)if(e.w){if(!hh.has(e.C))hh.set(e.C,[]);hh.get(e.C).push(e);}
 const highWindows=new Map(),highFactorWindows=new Map(),highStats={...wStats},highW=2*B,highCap=Math.max(1,Math.floor(analytic?B*u**1.5:windowStress?8:4)),highGapCap=Math.max(1,Math.floor(analytic?highCap/u:2));let highWindowExtra=0,highWindowAsync=0,highWindowRank=0,highWindowGap=0,highWindowChain=0,highWindowReverseOnly=0,highFactorExtra=0,highFactorAsync=0;const highFactorStats={...wStats};let highRankTotal=0,highRankPaid=0,highRankAsync=0,highRankSync=0,highRankCohortExtra=0,highRankCellExtra=0,highRankMax=0,highRankChecks=0,highRankR=0,highRankGroups=0;
 const hcap=Math.max(1,Math.floor(analytic?B*u**1.5:4)),hqcap=Math.max(1,Math.floor(analytic?B*Math.sqrt(u):2)),hd=Math.max(2,Math.floor(analytic?B:B/8)),hdcap=Math.max(1,Math.floor(analytic?hd/B*u**1.75:2));
 for(const es of hh.values()){
   es.sort((a,b)=>a.M-b.M);const times=es.slice().sort((a,b)=>a.t-b.t||a.M-b.M),tr=new Map(times.map((e,i)=>[e.M,i])),sr=new Map(es.map((e,i)=>[e.M,i])),qs=new Map(),cells=new Map(),r=es[0].r;
   for(const e of es){ok(e.r===r,"common high r");const q=e.prev?.p||0,c=Math.floor((e.M-X)/hd);if(!qs.has(q))qs.set(q,[]);qs.get(q).push(e.M);if(!cells.has(c))cells.set(c,[]);cells.get(c).push(e.M);}
   const omega=new Set(fs(es[0].C).concat(fs(es[0].C+2))).size;ok(qs.size<=omega+1,"high incoming cohort count");ok(cells.size<=Math.ceil(H/(2*hd))+2,"high cell count");
   highRankR+=r*es.length;highRankTotal+=r*es.length**2;highRankGroups++;const wi=Math.floor(es[0].C/highW),hw=highWindows.get(wi)||{groups:[],qs:new Map()};hw.groups.push({C:es[0].C,ms:es.map(e=>e.M)});highWindows.set(wi,hw);const hfkey=r+":"+Math.floor(es[0].C/(2*r)),hf=highFactorWindows.get(hfkey)||{groups:[],qs:new Map(),r};hf.groups.push({C:es[0].C,ms:es.map(e=>e.M)});highFactorWindows.set(hfkey,hf);
   for(const a of es){let deg=0;for(const b of es){if(a===b)continue;let k=-1;
       if(Math.abs(sr.get(a.M)-sr.get(b.M))<=hcap||Math.abs(tr.get(a.M)-tr.get(b.M))<=hcap)k=0;
       else if(gNear(qs.get(b.prev?.p||0),a.M,b.M,hqcap))k=1;
       else if(gNear(cells.get(Math.floor((b.M-X)/hd)),a.M,b.M,hdcap))k=2;
       if(k<0){const id=pairId(a.M,b.M),q=hw.qs.get(id)||{M:Math.min(a.M,b.M),Mp:Math.max(a.M,b.M),scores:[],energy:0,async:0};q.energy+=r;if(a.t!==b.t)q.async+=r;hw.qs.set(id,q);const fq=hf.qs.get(id)||{M:q.M,Mp:q.Mp,scores:[],energy:0,async:0,parts:new Map()};fq.energy+=r;if(a.t!==b.t)fq.async+=r;const part=fq.parts.get(q)||{energy:0,async:0};part.energy+=r;if(a.t!==b.t)part.async+=r;fq.parts.set(q,part);hf.qs.set(id,fq);continue;}deg++;highRankPaid+=r;if(a.t!==b.t)highRankAsync+=r;else highRankSync+=r;if(k===1)highRankCohortExtra+=r;if(k===2)highRankCellExtra+=r;
     }ok(deg<=4*hcap+2*hqcap*qs.size+2*hdcap*cells.size,"high projected rank degree");highRankMax=Math.max(highRankMax,deg);highRankChecks++;}
 }
 ok(highRankPaid===highRankAsync+highRankSync&&highRankPaid<=highRankTotal-highRankR,"high projected direct energy partition");for(const hw of highWindows.values()){sweepWindow(hw.groups,hw.qs,highCap,highGapCap,false,highStats);sweepWindow(hw.groups,hw.qs,highCap,highGapCap,true,highStats);for(const q of hw.qs.values()){ok(q.energy<=3*(highW+B),"high pair window gain bound");if(!q.scores.some(v=>v.covered))continue;highWindowExtra+=q.energy;highWindowAsync+=q.async;if(q.scores.some(v=>v.rankCovered))highWindowRank+=q.energy;else highWindowGap+=q.energy;if(q.scores.some(v=>v.covered&&!v.direct))highWindowChain+=q.energy;if(!q.scores[0].covered)highWindowReverseOnly+=q.energy;}}ok(highRankPaid+highWindowExtra<=highRankTotal-highRankR&&highWindowExtra===highWindowRank+highWindowGap,"high window added energy partition");
 // Exact-factor window memberships can be charged to original weighted incidences, not all possible factors/windows.
 let weightedMembership=0;
 for(const hf of highFactorWindows.values()){
   const ids=new Set(hf.groups.flatMap(g=>g.ms));weightedMembership+=hf.r*ids.size;
   sweepWindow(hf.groups,hf.qs,highCap,highGapCap,false,highFactorStats);sweepWindow(hf.groups,hf.qs,highCap,highGapCap,true,highFactorStats);
   for(const q of hf.qs.values()){ok(q.energy<=2*(1.5*2*hf.r+hf.r),"exact high-factor window pair bound");if(!q.scores.some(v=>v.covered))continue;
     for(const [orig,piece] of q.parts)if(!orig.scores.some(v=>v.covered)){highFactorExtra+=piece.energy;highFactorAsync+=piece.async;}
   }
 }
 ok(weightedMembership<=highRankR&&highRankPaid+highWindowExtra+highFactorExtra<=highRankTotal-highRankR,"factor-weighted memberships and energy partition");
 // Persistent larger-source ancestry, independent of arbitrary accounting holes.
 const historyD=Math.max(2,Math.floor(analytic?H/u**2:B/(ancestryStress?2:8))),historyEps=analytic?u**(-.25):ancestryStress?.25:.125,historyZeta=analytic?u**(-.125):.5,historyCoef=2*(-Math.expm1(-historyEps))/historyZeta;
 let histGlobalLog=0,histCellLog=0,histMarkedGain=0,histMarkedEvents=0,histGlobalMarks=0,histCellOnlyMarks=0,histMaxCells=0,histRootChecks=0,histCutChecks=0,histGrowthChecks=0,histMarkedActual=0,histMarkedMedium=0,histMarkedHighR=0,histMediumPaid=0,histNeverPaid=0;
 for(const es of vertices.values()){
   const ar=es.slice().sort((a,b)=>a.M-b.M),counts=new Map();
   for(let i=ar.length-1;i>=0;i--){const e=ar[i];e.histN=ar.length-i;e.histCells=new Map(counts);const c=sourceCell(e.M);counts.set(c,(counts.get(c)||0)+1);}
 }
 for(const ar of roots.values()){
   let j=0,gl=0,cl=0,gain=0,actual=0,old=ar[0],seen=new Set();
   ok(old.histN===1&&old.histCells.size===0,"prime root has no other physical ancestors");
   for(let i=0;i<ar.length;i++){
     const e=ar[i];ok(e.histN>=old.histN,"persistent global larger companions");
     gl+=Math.log(e.histN/old.histN);
     for(const [c,n] of old.histCells)ok((e.histCells.get(c)||0)>=n,"persistent cell larger companions");
     for(const [c,n] of e.histCells){cl+=Math.log((1+n)/(1+(old.histCells.get(c)||0)));seen.add(c);}
     histGrowthChecks++;old=e;
     while(j+1<=i&&ar[j+1].C<=e.C-historyD)j++;
     const a=ar[j];e.histCut=a;
     ok(j===0&&e.C-ar[0].C<historyD||e.C-a.C>=historyD&&e.C-a.C<historyD+B,"history cut overshoot");
     const g=Math.log(e.histN/a.histN);let h=0;
     for(const [c,n] of e.histCells)h=Math.max(h,Math.log((1+n)/(1+(a.histCells.get(c)||0))));
     e.histBad=g>historyEps+1e-12||h>historyEps+1e-12;
     histCutChecks++;
     if(e.next&&e.histBad){histMarkedEvents++;if(g>historyEps+1e-12)histGlobalMarks++;else histCellOnlyMarks++;gain+=e.p-1;actual+=e.next.t-e.t;if(e.w)histMarkedHighR+=e.r;const me=byRoot.get(e.M)?.get(e.C);if(me)histMarkedMedium+=me.actual;}
   }
   const last=ar.at(-1),cellEnd=[...last.histCells.values()].reduce((s,n)=>s+Math.log(1+n),0);
   ok(near(gl,Math.log(last.histN))&&near(cl,cellEnd),"exact logarithmic telescope");
   ok(seen.size<=Math.ceil(H/(2*d))+2&&gl+cl<=(1+seen.size)*Math.log(N+1)+1e-6,"source-localized growth budget");
   ok(gain<=(historyD+2*B)/historyEps*(gl+cl)+1e-6&&actual<=3*gain,"marked gain Fubini budget");
   histGlobalLog+=gl;histCellLog+=cl;histMarkedGain+=gain;histMarkedActual+=actual;histMaxCells=Math.max(histMaxCells,seen.size);histRootChecks++;
 }
 ok(histMarkedMedium<=3*(historyD+2*B+L)/historyEps*(histGlobalLog+histCellLog)+1e-6,"attached LOW history budget");
 for(const x of ledger.values())if(x.historyCandidate&&rawByRoot.get(x.M).get(x.E).histBad){histMediumPaid+=x.rem;if(!pairsWF.get(pairId(x.M,x.Mp)).v)histNeverPaid+=x.rem;}
 ok(histMediumPaid<=histMarkedMedium+1e-6&&histMediumPaid<=reverseResidual+1e-6&&histNeverPaid<=reverseNeverResidual+1e-6,"marked focal medium budget");
 // Whole physical group density gate on the current input natural high tags.
 // No quadratic smallness is assumed for the removed tags.
 let histDensityR=0,histDensityGroups=0,histKeepR=0,histKeepE=0,histKeepSyncE=0,histRecentSyncE=0,histOldSyncE=0,histDensityChecks=0,histExactPairChecks=0,histMaxRecentRatio=0,histMarkedHighTags=0,histKeepHighTags=0;
 function oldCompanion(a,b){return rawByRoot.get(b.M).get(a.histCut.C)?.t===a.histCut.t;}
 for(const es of hh.values()){
   const groups=new Map();for(const e of es){if(!groups.has(e.t))groups.set(e.t,[]);groups.get(e.t).push(e);if(e.histBad)histMarkedHighTags++;}
   let nh=0;for(const ar of groups.values()){
     ar.sort((a,b)=>a.M-b.M);const n=ar.length,kept=ar.filter(e=>!e.histBad),r=ar[0].r;
     for(const e of ar)e.histKeep=false;
     if(kept.length<historyZeta*n){histDensityR+=r*kept.length;if(kept.length)histDensityGroups++;continue;}
     for(const e of kept)e.histKeep=true;
     nh+=kept.length;histKeepHighTags+=kept.length;histKeepR+=r*kept.length;histKeepSyncE+=r*kept.length**2;
     let recent=0;
     for(const a of kept){
       let ng=0,nold=0;for(const b of ar)if(a.M<b.M){ng++;if(oldCompanion(a,b)){nold++;ok(a.histCut.C<=a.C-historyD,"old shared physical cut");}else if(b.histKeep)recent+=2;}
       ok(ng+1===a.histN&&nold+1===a.histCut.histN,"exact persistent larger companions at cut");
       ok(ng-nold<=(-Math.expm1(-historyEps))*a.histN+1e-8,"recent companion fraction");
       histExactPairChecks++;
     }
     ok(recent<=historyCoef*kept.length**2+1e-7,"relative recent physical count");
     histRecentSyncE+=r*recent;histOldSyncE+=r*(kept.length*(kept.length-1)-recent);
     histMaxRecentRatio=Math.max(histMaxRecentRatio,recent/kept.length**2);histDensityChecks++;
   }
   histKeepE+=es[0].r*nh**2;
 }
 ok(histDensityR<=historyZeta*highRankR+1e-6&&histKeepR+histDensityR+histMarkedHighR===highRankR,"linear density partition");
 ok(histKeepSyncE===histKeepR+histRecentSyncE+histOldSyncE&&histRecentSyncE<=historyCoef*histKeepE+1e-6,"relative high energy absorption");
 // Source-distance-adaptive two-sided trimming on full NATURAL shared high weights.
 const sharedAge=new Map(),ageBands=new Map();
 function ageCap(h){let j=Math.max(0,Math.floor(Math.log2(H/h))),dj=H/2**j;while(h>dj){j--;dj*=2;}while(h<=dj/2){j++;dj/=2;}
   const K=Math.max(1,Math.floor((analytic?B*u**1.5:B/(ancestryStress?4:16)/Math.log(2+H))*H*Math.log(2+dj)/(dj*(j+1)**2)));
   return {j,dj,K};}
 for(const es of hh.values())for(let i=0;i<es.length;i++)for(let j=i+1;j<es.length;j++){
   const a=es[i],b=es[j],id=pairId(a.M,b.M),h=Math.abs(a.M-b.M);ok(h<H/2,"natural shared pair localization");
   let z=sharedAge.get(id);if(!z){const {j,dj,K}=ageCap(h);z={j,dj,K,total:0,before:0,paid:0};sharedAge.set(id,z);const v=ageBands.get(j)||{pairs:0,K,dj,paid:0};v.pairs++;ageBands.set(j,v);}z.total+=a.r;
 }
 const birthPairs=new Map();function birthPair(M,Mp){const id=pairId(M,Mp);let q=birthPairs.get(id);if(!q){q={M:Math.min(M,Mp),Mp:Math.max(M,Mp),med:0,medLo:0,medHi:0,never:0,high:0,sync:0,async:0};birthPairs.set(id,q);}return q;}
 for(const x of ledger.values())if(x.historyCandidate&&!rawByRoot.get(x.M).get(x.E).histBad){const q=birthPair(x.M,x.Mp);q.med+=x.rem;if(x.M===q.M)q.medLo+=x.rem;else q.medHi+=x.rem;if(!pairsWF.get(pairId(x.M,x.Mp)).v)q.never+=x.rem;}
 let ageFullPaid=0,ageFullAsync=0,ageFullFront=0,ageFullBack=0,agePairBudget=0,agePairChecks=0,ageFullBoth=0,ageExtra=0,ageExtraAsync=0,ageExtraFront=0,ageExtraBack=0,histEnergyRemoved=0,histRecentExtra=0,histFinalResidual=0,histFinalAsync=0,histFinalSync=0,histAgeResidual=0;
 // High: preserve previous direct rank + both projected window masks before new reverse masks.
 let highReverseExtra=0,highReverseAsync=0,highReverseKinds=[0,0,0],highReverseGroups=0,highReverseResidual=0,highReverseChecked=0,highReverseEligible=0;
 for(const es of [...hh.values()].sort((a,b)=>a[0].C-b[0].C)){
   const C=es[0].C,r=es[0].r,hw=highWindows.get(Math.floor(C/highW)),hf=highFactorWindows.get(r+":"+Math.floor(C/(2*r))),part=reversePartition(es),m=analytic?highCap:reverseStress?8:4;
   highReverseGroups++;
   const times=es.slice().sort((a,b)=>a.t-b.t||a.M-b.M),tr=new Map(times.map((e,i)=>[e.M,i])),sr=new Map(es.map((e,i)=>[e.M,i])),qs=new Map(),cells=new Map();
   for(const e of es){const q=e.prev?.p||0,c=Math.floor((e.M-X)/hd);if(!qs.has(q))qs.set(q,[]);qs.get(q).push(e.M);if(!cells.has(c))cells.set(c,[]);cells.get(c).push(e.M);}
   for(const a of es){let tested=false;for(const b of es){if(a===b)continue;
       const az=sharedAge.get(pairId(a.M,b.M)),front=az.before<az.K,back=az.total-az.before-r<az.K,young=front||back;
       if(young){ageFullPaid+=r;if(a.t!==b.t)ageFullAsync+=r;if(front)ageFullFront+=r;if(back)ageFullBack+=r;if(front&&back)ageFullBoth+=r;if(a.M<b.M)az.paid+=r;}
       if(Math.abs(sr.get(a.M)-sr.get(b.M))<=hcap||Math.abs(tr.get(a.M)-tr.get(b.M))<=hcap||gNear(qs.get(b.prev?.p||0),a.M,b.M,hqcap)||gNear(cells.get(Math.floor((b.M-X)/hd)),a.M,b.M,hdcap))continue;
       const id=pairId(a.M,b.M),q=hw.qs.get(id),f=hf.qs.get(id);ok(q&&f,"high original direct residual pair");if(q.scores.some(v=>v.covered)||f.scores.some(v=>v.covered))continue;
       tested=true;highReverseEligible+=r;const k=reverseKinds(part,a.M,b.M,m);if(k>=0){highReverseExtra+=r;highReverseKinds[k]+=r;if(a.t!==b.t)highReverseAsync+=r;}else{highReverseResidual+=r;if(young){ageExtra+=r;if(a.t!==b.t)ageExtraAsync+=r;if(front)ageExtraFront+=r;else ageExtraBack+=r;}else{histAgeResidual+=r;if(!a.histKeep||!b.histKeep)histEnergyRemoved+=r;else{const sm=a.M<b.M?a:b,bg=a.M<b.M?b:a;if(a.t===b.t&&!oldCompanion(sm,bg))histRecentExtra+=r;else{histFinalResidual+=r;const q=birthPair(a.M,b.M);q.high+=r;if(a.t===b.t){histFinalSync+=r;q.sync+=r;if(!q.resHits)q.resHits=new Map();q.resHits.set(C,(q.resHits.get(C)||0)+r);}else{histFinalAsync+=r;q.async+=r;}}}}}
     }if(tested){checkReverseDegree(part,a.M,m);highReverseChecked++;}}
   for(let i=0;i<es.length;i++)for(let j=i+1;j<es.length;j++)sharedAge.get(pairId(es[i].M,es[j].M)).before+=r;
 }
 ok(highReverseEligible===highRankTotal-highRankR-highRankPaid-highWindowExtra-highFactorExtra&&highReverseExtra+highReverseResidual===highReverseEligible,"high reverse exact priority partition");
 for(const az of sharedAge.values()){ok(az.before===az.total&&az.paid<=2*(az.K+B)&&az.total<=1.5*H,"two-sided shared natural clock budget");agePairBudget+=4*(az.K+B);ageBands.get(az.j).paid+=2*az.paid;agePairChecks++;}
 ok(ageFullPaid<=agePairBudget&&ageFullPaid===ageFullFront+ageFullBack-ageFullBoth&&ageFullPaid===[...ageBands.values()].reduce((s,z)=>s+z.paid,0),"pair age partition");
 ok(highReverseResidual===ageExtra+histEnergyRemoved+histRecentExtra+histFinalResidual&&histAgeResidual===histEnergyRemoved+histRecentExtra+histFinalResidual&&histFinalResidual===histFinalAsync+histFinalSync&&histRecentExtra<=histRecentSyncE,"new isolated high residual partition");
 // A fixed birth-key classifier, independent of accounting holes and of the sign of a charge.
 const birthY=Math.max(5,Math.ceil(analytic?B**.125:birthStress?B**.1:B**.125)),birthDmax=6+5*H;
 const birthBaseMed=analytic?N*H/(X*u**.25):birthStress?8:2,birthBaseHigh=analytic?H*H*B*u**.75/X:(birthStress?8:2)*H;
 const birthTypes=new Map(),birthPhysical=new Map(),birthProjected=new Map(),birthKindCount={},birthLagStats={min:Infinity,max:0,sameIncoming:0,rough:0},birthSupportSamples=[];
 let birthPairChecks=0,birthPhysicalPairs=0,birthProjectedPairs=0,birthNoPhysical=0,birthPriorHigh=0,birthAfterHigh=0,birthMaxKeyPairs=0,birthMaxFullTail=0,birthTickChecks=0,birthNoProjected=0,birthRootContacts=0,birthMixed=0,birthSame=0,birthRelaxChecks=0,birthSupportTotal=0,birthRoughSupportChecks=0;
 function dBand(d0){let j=0,D=birthDmax;while(d0<=D/2){D/=2;j++;}ok(d0>D/2&&d0<=D,"birth deficit band");return {j,D};}
 const labelFee=(p,q=0)=>q?(Math.min(p,q)>=birthY?1:ell**2):p>=birthY?1:ell;
 function phase(e){const d0=2*e.t-e.C,q=e.prev?.p||0,s=e.t%2;ok(d0>=0&&d0<=birthDmax,"birth deficit strip");
   if(q){ok(mod(e.C+2*s,q)===0&&mod(e.t,2*q)===(s?q+2:0)&&mod(d0-6*s,2*q)===0,"birth incoming phase");}else ok(d0===6&&e.C===2*e.M-2,"birth canonical root phase");
   return {q,s,d0};
 }
 function makeKey(kind,key,factor,info){ok(factor>0&&Number.isFinite(factor),"positive birth quota");return {kind,key,factor,info};}
 function projKey(a,b){
   const p=a.prev?.p||0,q=b.prev?.p||0,C=a.C;ok(C===b.C,"projected birth horizon");
   if(!p||!q){const M=!p?a.M:b.M;ok(C===2*M-2,"projected root contact");return makeKey("projected-root","PR:"+M,X/N,{M});}
   ok(p!==q&&incoming(C).includes(p)&&incoming(C).includes(q),"distinct projected first-contact labels");
   const lo=Math.min(p,q),hi=Math.max(p,q);return makeKey("projected-mixed","PM:"+C+":"+lo+":"+hi,1/labelFee(lo,hi),{C,p:lo,q:hi});
 }
 function physKey(a,b){
   const u0=a.prev,v0=b.prev;ok(a.C===b.C&&a.t===b.t,"common physical birth");
   ok(u0&&v0,"no noninitial visit to prime source state");
   ok(u0.C!==v0.C||u0.t!==v0.t,"distinct physical birth children");
   if(!u0.prev||!v0.prev){const M=!u0.prev&&!v0.prev?Math.min(a.M,b.M):!u0.prev?a.M:b.M;birthRootContacts++;return makeKey("physical-root-child","R:"+M,X/N,{M});}
   const ap=phase(a),bp=phase(b),p=ap.q,q=bp.q;
   if(p!==q){
     birthMixed++;const lo=Math.min(p,q),hi=Math.max(p,q),d0=ap.d0,s=ap.s,C=a.C;
     ok(mod(C+2*s,p*q)===0&&mod(d0-6*s,2*p*q)===0,"mixed first-birth CRT");
     if(d0<=6){ok(d0===6*s,"mixed reset line");return makeKey("mixed-reset","MR:"+C+":"+a.t+":"+lo+":"+hi,1/labelFee(lo,hi),{C,t:a.t,p:lo,q:hi,d0,s});}
     const {j,D}=dBand(d0);ok(2*p*q<=d0,"nonreset mixed prime product");
     return makeKey("mixed-nonreset","MN:"+C+":"+a.t+":"+lo+":"+hi,lo*hi/(D*(j+1)**2*labelFee(lo,hi)),{C,t:a.t,p:lo,q:hi,d0,s,j,D});
   }
   birthSame++;const early=u0.t<v0.t?u0:v0,late=early===u0?v0:u0,lag=late.t-early.t,C=late.C,r=late.r,l=phase(late),e=phase(early);
   ok(C===early.C&&early.next.t===late.next.t&&early.p===late.p&&lag>0&&lag<a.t-early.t&&lag<2*r,"true first waiting birth");
   if(e.q===l.q){ok(l.q>0&&lag%(2*l.q)===0&&r>l.q,"same incoming label true birth");birthLagStats.sameIncoming++;}
   birthLagStats.min=Math.min(birthLagStats.min,lag);birthLagStats.max=Math.max(birthLagStats.max,lag);
   const rough=lag>=birthY;if(rough){ok(r>birthY/2,"rough birth horizon");birthLagStats.rough++;}
   const {q:ql,s,d0}=l,amp=rough?u*u:1,cls=rough?"rough":"plain";
   ok(ql>0,"nonroot later arrival");
   if(d0<=6){return makeKey("same-low-"+cls,"SL:"+C+":"+late.t+":"+ql+":"+cls,amp/labelFee(ql),{C,t:late.t,q:ql,d0,s,rough,lag,r});}
   const {j,D}=dBand(d0);ok(2*ql<=d0,"true birth positive phase");
   return makeKey("same-nonreset-"+cls,"SN:"+C+":"+late.t+":"+ql+":"+cls,amp*ql/(D*(j+1)**2*labelFee(ql)),{C,t:late.t,q:ql,d0,s,j,D,rough,lag,r});
 }
 // Freeze a separate LOW partition, independent of the inherited medium LOW rule.
 // Finite y=5 (L=30), stress y=7 (L=210); analytic diagnostics y=3.
 const ay=analytic?3:anchorStress?7:5,aL=ay===3?6:ay===5?30:210;
 let anchorGainBudget=0,anchorRootBudget=0,anchorBlocks=0,anchorVertices=0,anchorMaxGain=0,anchorMaxWait=0,anchorBarrierChecks=0;
 const anchorMembership=new Map();
 for(const [M,ar] of roots){
   let a=ar[0],q=0;for(const e of ar){
     if(e.prev&&e.prev.p>ay){a=e;q=e.prev.p;}
     e.anchor=a;e.anchorQ=q;
     const g=e.C-a.C,w=e.t-a.t;ok(g>=0&&g<aL&&w>=0&&w<=3*g,"compressed LOW gain/clock barrier");
     if(e.prev&&e.prev.p<=ay){
       const c=e.prev.C,nextBoundary=Math.ceil(c/aL)*aL;
       ok(c%aL!==0&&e.C<=nextBoundary,"LOW cannot cross primorial boundary");anchorBarrierChecks++;
     }
     if(e===a){
       const key="AT:"+M+":"+a.C;const weight=q?q-1:B;
       ok(!anchorMembership.has(key),"unique original anchor block");
       anchorMembership.set(key,{weight,q,M,C:a.C});anchorBlocks++;
       if(q)anchorGainBudget+=weight;else anchorRootBudget+=weight;
     }
     anchorVertices++;anchorMaxGain=Math.max(anchorMaxGain,g);anchorMaxWait=Math.max(anchorMaxWait,w);
   }
 }
 ok(anchorGainBudget<=G&&anchorRootBudget===N*B&&anchorGainBudget+anchorRootBudget<=N*(H+B),"actual anchor membership budget");
 const anchorFactorScale=X/(N*H);
 // Spread each original gain weight over the next k whole LOW blocks,
 // independently of all queries, with a constant-budget mixture of scales.
 const multiDepths=[1,4,16],prefixDepths=[2,4,8,16,Infinity],multiLambda=analytic?B*u**1.5:B/(multiStress?2:8);
 let multiMass=0,multiExpected=0,multiRootChecks=0,multiDegreeChecks=0,multiDegreeMax=0,multiDegreeBudget=0,multiRankPairs=0,multiRankExtra=0,multiRankAsync=0,multiRankBefore=0,multiRankOnlyOld=0,multiRankOnlyComplex=0,multiRankOnlySource=0;
 for(const ar of roots.values()){
   const starts=[];for(let i=0;i<ar.length;i++){const e=ar[i];e.multiIndex=i;e.multiMass=0;if(e.anchor===e)starts.push(i);}
   starts.push(ar.length);let total=0,expected=0,logK=Math.log(aL),retained=0;
   for(let j=ar.length-1;j>=0;j--){const e=ar[j];if(e.w&&e.histKeep)retained+=e.r;e.multiRetTail=retained;}
   for(let j=0;j<starts.length-1;j++){
     const i=starts[j],e=ar[i],q=e.anchorQ,weight=q?q-1:B;
     expected+=weight;
     if(q){const d0=incoming(e.C).filter(p=>p>ay).length;ok(d0>=1,"Kraft actual incoming label");logK+=Math.log(aL*d0);}
     for(let z=i;z<starts[j+1];z++){ar[z].multiBlock=j;ar[z].multiLogK=logK;ar[z].multiStarts=starts;}
     for(const k of multiDepths){const end=starts[Math.min(j+k,starts.length-1)],a=weight/(end-i)/multiDepths.length;
       for(let z=i;z<end;z++)ar[z].multiMass+=a;}
   }
   total=ar.reduce((z,e)=>z+e.multiMass,0);ok(near(total,expected),"multi-anchor exact source budget");
   multiMass+=total;multiExpected+=expected;multiRootChecks++;
 }
 ok(near(multiMass,multiExpected)&&near(multiExpected,anchorGainBudget+anchorRootBudget),"multi-anchor global gain budget");
 // Full projected tag lists at queried birth horizons (not residual cohorts).
 const multiGroups=new Map();
 function multiCap(e){return e.multiRetTail>0?Math.floor(multiLambda*e.multiMass/(2*e.multiRetTail)):0;}
 function multiGood(a,b){const g=multiGroups.get(a.C),cap=multiCap(a);if(cap<=0||a.M===b.M)return 0;
   let kind=0;if(Math.abs(g.sr.get(a.M)-g.sr.get(b.M))<=cap)kind|=1;
   if(g.kr.get(b.M)<cap)kind|=2;return kind;
 }
 function multiPrefixOverlap(a,b,depth,countAll=false){
   const aa=roots.get(a.M),bb=roots.get(b.M),i0=depth===Infinity?0:a.multiStarts[Math.max(0,a.multiBlock-depth+1)],j0=depth===Infinity?0:b.multiStarts[Math.max(0,b.multiBlock-depth+1)];
   let i=i0,j=j0,count=0;while(i<a.multiIndex&&j<b.multiIndex){const x=aa[i].C,y=bb[j].C;if(x===y){if(!countAll)return x;count++;i++;j++;}else if(x<y)i++;else j++;}return countAll?count:null;
 }
 let anchorPairChecks=0,anchorRootPairs=0,anchorSamePairs=0,anchorMixedPairs=0,anchorCompressedPairs=0,anchorLongSameChecks=0,anchorSmallContactPairs=0,anchorSmallPromoted=0,anchorLocalChecks=0,anchorLocalReject=0,anchorLocalPairs=0,anchorMaxLocalMasks=0;
 const anchorKeySet=new Map(),anchorGroups=new Map();
 function tagKey(e){
   const a=e.anchor,q=e.anchorQ,id="AT:"+e.M+":"+a.C,v=anchorMembership.get(id);
   ok(v&&v.q===q,"actual tag anchor membership");
   return makeKey("anchor-tag",id,anchorFactorScale*v.weight,{M:e.M,C:a.C,q});
 }
 function anchorCode(e){return e.anchor.C+":"+e.anchorQ;}
 function compressedKey(a,b){
   const D=a.anchor.C,E=b.anchor.C,p=a.anchorQ,q=b.anchorQ;
   ok(a.C===b.C&&Math.abs(D-E)<aL,"compressed contact offset");
   ok(D!==E||p!==q,"distinct compressed first contact keys");
   const candidates=[tagKey(a),tagKey(b)];
   if(!p||!q){
     const M=!p&&!q?Math.min(a.M,b.M):!p?a.M:b.M;
     candidates.push(makeKey("compressed-root","AR:"+M,X/N,{M}));anchorRootPairs++;
   }else if(p===q){
     ok(D!==E,"same compressed label distinct horizons");
     const d=Math.abs(D-E);ok([0,2,p-2].includes(mod(d,p)),"same compressed offset congruence");
     if(p>aL+2){ok(d===2&&Math.abs(a.t-b.t)>=p-2-3*aL,"long same label asynchronous lag");anchorLongSameChecks++;}
     candidates.push(makeKey("compressed-same","AS:"+Math.min(D,E)+":"+Math.max(D,E)+":"+p,1/((1+aL/p)*labelFee(p)),{D:Math.min(D,E),E:Math.max(D,E),p,q}));anchorSamePairs++;
   }else{
     const k=[{D,p},{D:E,p:q}].sort((x,y)=>x.D-y.D||x.p-y.p);
     candidates.push(makeKey("compressed-mixed","AC:"+k[0].D+":"+k[0].p+":"+k[1].D+":"+k[1].p,1/(aL*labelFee(p,q)),{D:k[0].D,E:k[1].D,p:k[0].p,q:k[1].p}));anchorMixedPairs++;
   }
   // Anchor cohorts retain exact LOW vertex masks and source tags.
   // Build only queried anchor keys, then populate them from FULL original blocks below.
   const aa=anchorCode(a),bb=anchorCode(b);
   for(const [id,e] of [[aa,a],[bb,b]])if(!anchorGroups.has(id))anchorGroups.set(id,{D:e.anchor.C,q:e.anchorQ,roots:new Map()});
   for(const key of candidates){const old=anchorKeySet.get(key.key);if(old)ok(old.factor===key.factor,"fixed compressed capacity");else anchorKeySet.set(key.key,key);}
   anchorPairChecks++;if(a.prev&&a.prev.p<=ay||b.prev&&b.prev.p<=ay){anchorSmallContactPairs++;if(p>ay&&q>ay)anchorSmallPromoted++;}
   if(a.anchor!==a||b.anchor!==b)anchorCompressedPairs++;
   return candidates;
 }
 function classifyBirth(z){
   const a=roots.get(z.M),b=roots.get(z.Mp);let i=0,j=0,pr=null,ph=null;
   while(i<a.length&&j<b.length){
     if(a[i].C<b[j].C)i++;else if(a[i].C>b[j].C)j++;else{if(!pr)pr=[a[i],b[j]];if(a[i].t===b[j].t){ph=[a[i],b[j]];break;}i++;j++;}
   }
   ok(pr,"charged pair has a projected contact");if(!pr){birthNoProjected++;return;}
   z.pr=projKey(...pr);z.ac=compressedKey(...pr);z.acRefs=pr;birthProjectedPairs++;birthPairChecks++;
   if(ph){z.ph=physKey(...ph);birthPhysicalPairs++;const [v,w]=ph;
     ok(v.M<w.M&&v.tail<=w.tail&&z.sync<=2*v.tail,"ordered natural birth tail");
     birthMaxFullTail=Math.max(birthMaxFullTail,2*v.tail);birthAfterHigh+=z.sync;birthPriorHigh+=z.async;
     if(X<=1024||birthTickChecks<64){const A=a.map(e=>[e.t,e.next?e.next.t:e.t+1,e.C]),B0=b.map(e=>[e.t,e.next?e.next.t:e.t+1,e.C]);let k=0,l=0,first=null;while(k<A.length&&l<B0.length){const t=Math.max(A[k][0],B0[l][0]);if(A[k][2]===B0[l][2]&&t<Math.min(A[k][1],B0[l][1])){first=[t,A[k][2]];break;}if(A[k][1]<B0[l][1])k++;else l++;}
       const same=v.prev.p===w.prev.p,exp=same?[Math.max(v.prev.t,w.prev.t),v.prev.C]:[v.t,v.C];ok(first&&first[0]===exp[0]&&first[1]===exp[1],"independent first waiting birth interval oracle");birthTickChecks++;}
   }else{ok(z.sync===0,"no synchronous residual without physical birth");birthNoPhysical++;}
   ok(z.high<=3*H&&z.med>=z.never-1e-8,"whole pair bounds");
 }
 function addBirthGroup(map,key,z,med,high){
   if(!key)return;let g=map.get(key.key);if(!g){g={...key,pairs:[],med:0,high:0,never:0,sync:0,async:0};map.set(key.key,g);}
   ok(g.factor===key.factor&&g.kind===key.kind,"frozen key quota");g.pairs.push(z);g.med+=med;g.high+=high;g.never+=z.never;g.sync+=z.sync;g.async+=z.async;
 }
 for(const z of birthPairs.values()){classifyBirth(z);z.orig={med:z.med,never:z.never,high:z.high,sync:z.sync,async:z.async};addBirthGroup(birthPhysical,z.ph,z,z.med,z.high);}
 const birthSummary={};
 function payBirth(map,stage){
   const out={med:0,never:0,high:0,sync:0,async:0,medBefore:0,highBefore:0,medCap:0,highCap:0,medFull:0,highFull:0,keys:map.size,medKeys:0,highKeys:0,positiveMed:0,positiveHigh:0,medResidualKeys:0,highResidualKeys:0};
   for(const g of map.values()){
     const mc=birthBaseMed*g.factor,hc=birthBaseHigh*g.factor,mp=Math.min(g.med,mc),hp=Math.min(g.high,hc),mf=g.med?mp/g.med:0,hf=g.high?hp/g.high:0;
     ok(mp<=mc+1e-8&&hp<=hc+1e-8,"key budget");
     out.medBefore+=g.med;out.highBefore+=g.high;out.medCap+=mc;out.highCap+=hc;if(g.med>0){out.medKeys++;if(g.med<=mc)out.medFull++;if(mp>0)out.positiveMed++;if(g.med>mc)out.medResidualKeys++;}if(g.high>0){out.highKeys++;if(g.high<=hc)out.highFull++;if(hp>0)out.positiveHigh++;if(g.high>hc)out.highResidualKeys++;}
     birthMaxKeyPairs=Math.max(birthMaxKeyPairs,g.pairs.length);
     const by=birthSummary[stage+":"+g.kind]||{keys:0,pairs:0,med:0,high:0,never:0,sync:0,async:0,medCap:0,highCap:0};by.keys++;by.pairs+=g.pairs.length;by.med+=mp;by.high+=hp;by.never+=g.never*mf;by.sync+=g.sync*hf;by.async+=g.async*hf;by.medCap+=mc;by.highCap+=hc;birthSummary[stage+":"+g.kind]=by;
     out.med+=mp;out.never+=g.never*mf;out.high+=hp;out.sync+=g.sync*hf;out.async+=g.async*hf;
     for(const z of g.pairs){z.med*=1-mf;z.never*=1-mf;z.high*=1-hf;z.sync*=1-hf;z.async*=1-hf;}
   }
   ok(near(out.high,out.sync+out.async)&&out.med<=out.medCap+1e-6&&out.high<=out.highCap+1e-6,"key payment partition");
   return out;
 }
 const physicalPay=payBirth(birthPhysical,"physical");
 for(const z of birthPairs.values())if(z.med>1e-12||z.high>1e-12)addBirthGroup(birthProjected,z.pr,z,z.med,z.high);
 const projectedPay=payBirth(birthProjected,"projected");
 let birthMedResidual=0,birthNeverResidual=0,birthHighResidual=0,birthSyncResidual=0,birthAsyncResidual=0;
 for(const z of birthPairs.values()){birthMedResidual+=z.med;birthNeverResidual+=z.never;birthHighResidual+=z.high;birthSyncResidual+=z.sync;birthAsyncResidual+=z.async;}
 ok(near(birthMedResidual+physicalPay.med+projectedPay.med,reverseResidual-histMediumPaid)&&near(birthNeverResidual+physicalPay.never+projectedPay.never,reverseNeverResidual-histNeverPaid)&&near(birthHighResidual+physicalPay.high+projectedPay.high,histFinalResidual)&&near(birthSyncResidual+physicalPay.sync+projectedPay.sync,histFinalSync)&&near(birthAsyncResidual+physicalPay.async+projectedPay.async,histFinalAsync),"birth residual partitions");
 // Optimize both arithmetic quota families jointly. The graph nodes are
 // actual intersections of fixed birth keys, not individual event incidences.
 function jointBirthFlow(metric,extended=false,trimmed=false,custom=false){
   const high=metric==="high",base=high?birthBaseHigh:birthBaseMed,ks=new Map(),edges=new Map();
   let total=0,otherTotal=0;
   for(const z of birthPairs.values()){
     const w=custom?(high?z.pcHigh:z.pcMed):z.orig[metric];if(w<=0||trimmed&&z.multiPaid)continue;const keys=[z.pr,...(z.ph?[z.ph]:[]),...(extended?z.ac:[]),...(custom&&z.pcKey?[z.pcKey]:[])];
     for(const k of keys){const old=ks.get(k.key);if(old)ok(old.factor===k.factor,"joint fixed key");else ks.set(k.key,k);}
     const id=keys.map(k=>k.key).join("|"),e=edges.get(id)||{keys:keys.map(k=>k.key),w:0,other:0,pairs:0,tags:[]};e.tags.push(z);
     const other=custom?(high?z.pcAsync:z.pcNever):z.orig[high?"async":"never"];e.w+=w;e.other+=other;e.pairs++;edges.set(id,e);total+=w;otherTotal+=other;
   }
   let nv=2;for(const k of ks.values())k.node=nv++;for(const e of edges.values())e.node=nv++;
   const adj=Array.from({length:nv},()=>[]),src=0,sink=1,EPS=1e-9;
   function add(a,b,c){const f={to:b,rev:adj[b].length,cap:c,initial:c},r={to:a,rev:adj[a].length,cap:0,initial:0};adj[a].push(f);adj[b].push(r);return f;}
   for(const k of ks.values())add(k.node,sink,base*k.factor);
   for(const e of edges.values()){e.arc=add(src,e.node,e.w);e.arcs=[];for(const id of e.keys)e.arcs.push(add(e.node,ks.get(id).node,total+1));}
   const level=new Int32Array(nv),it=new Int32Array(nv);
   function bfs(){level.fill(-1);const q=[src];level[src]=0;for(let i=0;i<q.length;i++){const v=q[i];for(const e of adj[v])if(e.cap>EPS&&level[e.to]<0){level[e.to]=level[v]+1;q.push(e.to);}}return level[sink]>=0;}
   function dfs(v,f){if(v===sink)return f;for(;it[v]<adj[v].length;it[v]++){const e=adj[v][it[v]];if(e.cap<=EPS||level[e.to]!==level[v]+1)continue;const d=dfs(e.to,Math.min(f,e.cap));if(d>EPS){e.cap-=d;adj[e.to][e.rev].cap+=d;return d;}}return 0;}
   let flow=0,rounds=0;while(bfs()){it.fill(0);let d;while((d=dfs(src,total+1))>EPS)flow+=d;rounds++;}
   // Failed final BFS leaves exactly the source side of a minimum cut.
   const cutKeys=[...ks.values()].filter(k=>level[k.node]>=0),cutSet=new Set(cutKeys.map(k=>k.key));
   let cutWeight=0,cutCap=0,paidOther=0,paidDirect=0,internalPairs=0,physPaid=0,projPaid=0,compressedPaid=0,tagPaid=0;
   for(const k of cutKeys)cutCap+=base*k.factor;
   const usage=new Map();
   for(const e of edges.values()){
     const f=e.w-e.arc.cap;if(custom)for(const z of e.tags)z[high?"gridUnpaidHigh":"gridUnpaidMed"]=Math.max(0,Math.min(1,e.arc.cap/e.w));if(extended&&high&&!trimmed&&!custom)for(const z of e.tags)z.multiUnpaid=e.arc.cap/e.w;ok(f>=-EPS&&f<=e.w+EPS,"joint intersection flow");paidDirect+=f;paidOther+=e.other*f/e.w;
     const used=e.arcs.map(a=>a.initial-a.cap);ok(near(used.reduce((s,x)=>s+x,0),f),"joint node conservation");
     for(let i=0;i<used.length;i++){const id=e.keys[i];usage.set(id,(usage.get(id)||0)+used[i]);if(ks.get(id).kind==="anchor-tag"||ks.get(id).kind==="precut-same")tagPaid+=used[i];else if(ks.get(id).kind.startsWith("compressed-"))compressedPaid+=used[i];else if(i===0)projPaid+=used[i];else physPaid+=used[i];}
     if(e.keys.every(k=>cutSet.has(k))){cutWeight+=e.w;internalPairs+=e.pairs;}
   }
   for(const [id,v] of usage)ok(v<=base*ks.get(id).factor+1e-6,"joint per-key budget");
   ok(near(flow,paidDirect)&&near(flow,physPaid+projPaid+compressedPaid+tagPaid)&&near(total-flow,cutWeight-cutCap),"joint max-flow/min-cut excess");
   const prev=high?physicalPay.high+projectedPay.high:physicalPay.med+projectedPay.med;
   if(!trimmed&&!custom)ok(flow+1e-6>=prev,"joint no worse than sequential");
   const groups=new Map();for(const e of edges.values())if(e.arc.cap>EPS){const id=e.keys[0],g=groups.get(id)||{key:id,w:0,pairs:0};g.w+=e.arc.cap;g.pairs+=e.pairs;groups.set(id,g);}
   const cutKinds={};for(const k of cutKeys)cutKinds[k.kind]=(cutKinds[k.kind]||0)+1;
   return {cutIds:extended?[...cutSet]:[],total,paid:flow,residual:total-flow,otherResidual:otherTotal-paidOther,physPaid,projPaid,compressedPaid,tagPaid,improvement:flow-prev,keys:ks.size,intersections:edges.size,rounds,cutWeight,cutCap,cutKeys:cutKeys.length,cutKinds,internalPairs,topResidualProjected:[...groups.values()].sort((a,b)=>b.w-a.w).slice(0,5)};
 }
 const jointMed=jointBirthFlow("med"),jointHigh=jointBirthFlow("high");
 const anchorJointMed=jointBirthFlow("med",true),anchorJointHigh=jointBirthFlow("high",true);
 ok(anchorJointMed.paid+1e-6>=jointMed.paid&&anchorJointHigh.paid+1e-6>=jointHigh.paid,"extended flow contains prior feasible solution");
 for(const z of birthPairs.values())if(z.orig.high>0||z.orig.med>0)multiGroups.set(z.acRefs[0].C,{es:[]});
 for(const ar of roots.values())for(const e of ar){const g=multiGroups.get(e.C);if(g)g.es.push(e);}
 for(const g of multiGroups.values()){
   const ar=g.es.sort((a,b)=>a.M-b.M);g.sr=new Map(ar.map((e,i)=>[e.M,i]));
   const kr=ar.slice().sort((a,b)=>a.multiLogK-b.multiLogK||a.M-b.M);g.kr=new Map(kr.map((e,i)=>[e.M,i]));
   // Check the exact Kraft inequality on original projected tags.
   ok(ar.reduce((z,e)=>z+Math.exp(-e.multiLogK),0)<=1+1e-8,"full projected prefix Kraft bound");
   for(const e of ar){const cap=multiCap(e),n=ar.filter(b=>multiGood(e,b)).length;
     ok(n<=3*cap&&2*e.multiRetTail*n<=3*multiLambda*e.multiMass+1e-6,"multi-anchor first-contact degree budget");
     multiDegreeChecks++;multiDegreeMax=Math.max(multiDegreeMax,n);multiDegreeBudget+=2*e.multiRetTail*n;
   }
 }
 ok(multiDegreeBudget<=3*multiLambda*multiMass+1e-6,"global weighted degree budget");
 for(const z of birthPairs.values())if(z.orig.high>0){
   const [a,b]=z.acRefs,k=multiGood(a,b)|multiGood(b,a),w=z.orig.high*z.multiUnpaid;
   ok(z.orig.high<=2*Math.min(a.multiRetTail,b.multiRetTail)+1e-6,"retained tail envelope at first contact");
   multiRankBefore+=w;
   if(k){z.multiPaid=true;multiRankPairs++;multiRankExtra+=w;multiRankAsync+=z.orig.async*z.multiUnpaid;if(k===1)multiRankOnlySource+=w;if(k===2)multiRankOnlyComplex+=w;
     // Independent same-scale k=1 allocation: if the old one-block budget
     // cannot cover either orientation, the extension really uses older blocks.
     function oldCap(e){const end=e.multiStarts[e.multiBlock+1],start=e.multiStarts[e.multiBlock];return e.multiRetTail?Math.floor(multiLambda*(e.anchorQ?e.anchorQ-1:B)/(2*e.multiRetTail*(end-start))):0;}
     function oldGood(a,b){const g=multiGroups.get(a.C),c=oldCap(a);return Math.abs(g.sr.get(a.M)-g.sr.get(b.M))<=c||g.kr.get(b.M)<c;}
     if(!oldGood(a,b)&&!oldGood(b,a))multiRankOnlyOld+=w;
   }
 }
 ok(near(multiRankBefore,anchorJointHigh.residual)&&multiRankExtra<=multiRankBefore+1e-6&&multiRankAsync<=anchorJointHigh.otherResidual+1e-6,"multi-anchor extra mask partition");
 const multiReoptHigh=jointBirthFlow("high",true,true);
 delete multiReoptHigh.cutIds;
 const multiFullPaid=[...birthPairs.values()].reduce((v,z)=>v+(z.multiPaid?z.orig.high:0),0);
 ok(near(multiFullPaid+multiReoptHigh.total,anchorJointHigh.total)&&multiReoptHigh.residual<=anchorJointHigh.residual-multiRankExtra+1e-6,"reoptimization after absolute rank mask");
 // Actual medium orientations: use original remaining gain, not partner or high tail.
 const pcMedLambda=analytic?mg/u**.25:precutStress?128:32;
 const medCap=e=>{const rem=roots.get(e.M).at(-1).C-e.C;return rem?Math.floor(pcMedLambda*e.multiMass/rem):0;};
 function medMultiGood(a,b){const g=multiGroups.get(a.C),m=medCap(a);return m>0&&(Math.abs(g.sr.get(a.M)-g.sr.get(b.M))<=m||g.kr.get(b.M)<m);}
 let pcMedDegree=0,pcMedDegreeBudget=0,pcMedMaxDegree=0,pcMedFullPaid=0,pcMedNeverPaid=0,pcMedDirections=0,pcMedRatioMax=0;
 for(const g of multiGroups.values())for(const e of g.es){const rem=roots.get(e.M).at(-1).C-e.C,m=medCap(e),n=g.es.filter(b=>b!==e&&medMultiGood(e,b)).length;ok(n<=3*m&&rem*n<=3*pcMedLambda*e.multiMass+1e-6,"directed medium rank budget");pcMedDegree++;pcMedMaxDegree=Math.max(pcMedMaxDegree,n);pcMedDegreeBudget+=rem*n;}
 ok(pcMedDegreeBudget<=3*pcMedLambda*multiMass+1e-6,"total medium rank budget");
 for(const z of birthPairs.values()){
   const [a,b]=z.acRefs;ok(a.M===z.M&&b.M===z.Mp&&near(z.medLo+z.medHi,z.orig.med),"directed original medium aggregation");
   const ma=medMultiGood(a,b),mb=medMultiGood(b,a),pay=(ma?z.medLo:0)+(mb?z.medHi:0);
   z.pcLo=ma?0:z.medLo;z.pcHi=mb?0:z.medHi;z.pcMed=z.pcLo+z.pcHi;z.pcNever=z.orig.never?z.pcMed:0;
   ok(!z.orig.never||near(z.orig.never,z.orig.med),"never is a whole pair property");
   pcMedFullPaid+=pay;pcMedNeverPaid+=z.orig.never?pay:0;pcMedDirections+=(ma&&z.medLo>0?1:0)+(mb&&z.medHi>0?1:0);
   for(const [e,w] of [[a,z.medLo],[b,z.medHi]])if(w>0){const g=roots.get(e.M).at(-1).C-e.C;ok(g>0,"positive medium tail");pcMedRatioMax=Math.max(pcMedRatioMax,w*mg/g);}
   z.pcHigh=z.multiPaid?0:z.orig.high;z.pcAsync=z.multiPaid?0:z.orig.async;
 }
 const pcMedAfterRanks=jointBirthFlow("med",true,false,true);delete pcMedAfterRanks.cutIds;
 ok(near(pcMedFullPaid+pcMedAfterRanks.total,anchorJointMed.total)&&pcMedAfterRanks.residual<=anchorJointMed.residual+1e-6,"directed medium reoptimization");
 // One aligned cut strictly before the first projected contact. At the cut
 // use the full original crossing-edge tag lists; no residual-only ranks.
 const pcD=Math.max(1,Math.floor(analytic?H/u**2:B/(precutStress?4:8))),pcHighCap=Math.floor(analytic?B*u**1.5*pcD/H:precutStress?12:4),pcMedCap=Math.floor(analytic?mg/u**.25*pcD/H:precutStress?16:4),pcY=Math.max(5,Math.floor(analytic?u**2:B**.125));
 const pcGroups=new Map();let pcShallow=0,pcEligible=0,pcSame=0,pcMixed=0,pcLanding=0,pcRootShallow=0,pcMembership=0,pcDegreeChecks=0,pcDegreeMax=[0,0],pcSlots=0,pcSlotBound=0,pcMaxSlots=0,pcFullHigh=0,pcFullMed=0,pcFullNever=0,pcFullAsync=0,pcPaidHighPairs=0,pcPaidMedDirections=0,pcSameKeys=new Map(),pcSameProducts=0,pcSameHigh=0,pcSameMed=0,pcSameKeyChecks=0,pcIndependent=0,pcOracleSlots=0,pcOracleChecks=0,pcThinHigh=0,pcThinMed=0,pcThinChecks=0,pcControlCuts=0,pcHighKinds=[0,0,0,0,0],pcMedKinds=[0,0,0,0,0];
 for(const z of birthPairs.values())if(z.pcHigh>0||z.pcMed>0){
   const C=z.acRefs[0].C,x=pcD*Math.floor((C-1)/pcD);if(x<2*z.Mp-2){pcShallow++;if(C===2*z.Mp-2)pcRootShallow++;continue;}
   z.pcX=x;if(!pcGroups.has(x))pcGroups.set(x,{es:[],map:new Map(),labels:new Map(),edges:new Map(),small:[],cells:new Map()});pcEligible++;
 }
 for(let i=1;i<=8;i++){const x=pcD*Math.floor((2*X+i*X/4)/pcD);if(!pcGroups.has(x)){pcGroups.set(x,{es:[],map:new Map()});pcControlCuts++;}}
 for(const ar of roots.values())for(const e of ar)if(e.next){
   for(let x=pcD*Math.ceil(e.C/pcD);x<e.next.C;x+=pcD){const g=pcGroups.get(x);if(!g)continue;ok(!g.map.has(e.M),"unique crossing edge");g.es.push(e);g.map.set(e.M,e);pcMembership++;}
 }
 ok(pcMembership<=N*(1+Math.ceil(H/pcD)),"grid membership budget");
 function pcGroup(es){const z={es:es.slice().sort((a,b)=>a.M-b.M),map:new Map(),labels:new Map(),edges:new Map(),small:[]};for(const e of z.es){z.map.set(e.M,e);const p=e.p,id=e.C+":"+p;if(!z.labels.has(p))z.labels.set(p,[]);z.labels.get(p).push(e.M);if(!z.edges.has(id))z.edges.set(id,[]);z.edges.get(id).push(e.M);if(p<=pcY)z.small.push(id);}z.small=[...new Set(z.small)];z.all=z.es.map(e=>e.M);return z;}
 const primesAll=[];for(let p=3;p<=B;p+=2)if(spf[p]===p)primesAll.push(p);
 for(const [x,g] of pcGroups){Object.assign(g,pcGroup(g.es));const cells=new Map();for(const e of g.es){const c=sourceCell(e.M);if(!cells.has(c))cells.set(c,[]);cells.get(c).push(e);}g.cells=new Map([...cells].map(([c,a])=>[c,pcGroup(a)]));
   // For each p, at most one even post-horizon on each CRT side.
   for(const [p,ms] of g.labels){const edges=[...new Set(ms.map(M=>g.map.get(M).C))].sort((a,b)=>a-b);ok(edges.length<=2,"at most two arithmetic crossing slots");if(edges.length===2)ok(edges[1]-edges[0]===2,"same-label opposite-side offset");}
   const oracle=new Set();for(const p of primesAll)for(const s of [0,-2]){const E=x+1+mod(s-x-1,2*p);if(E<=x+p-1)oracle.add((E-p+1)+":"+p);}
   for(const key of g.edges.keys()){ok(oracle.has(key),"independent arithmetic crossing slot");pcOracleChecks++;}
   pcOracleSlots+=oracle.size;
   pcSlots+=g.edges.size;pcSlotBound+=2*primesAll.length;pcMaxSlots=Math.max(pcMaxSlots,g.edges.size);
 }
 function pcKind(g,a,b,m){if(m<=0||a.M===b.M||a.C===b.C)return -1;const key=b.C+":"+b.p;
   if(gNear(g.all,a.M,b.M,m))return 0;
   if(a.p===b.p&&gNear(g.labels.get(b.p),a.M,b.M,m))return 1;
   const n=g.edges.size,c=n?Math.floor(m/n):0;if(c&&gNear(g.edges.get(key),a.M,b.M,c))return 2;
   const sc=g.small.length?Math.floor(m/g.small.length):0;if(b.p<=pcY&&sc&&gNear(g.edges.get(key),a.M,b.M,sc))return 3;
   // Nearby entry or exit horizon: O(J) distinct horizons, but possibly
   // many outgoing labels. Group the full original crossing slots by each endpoint.
   const J=2,ak=a.C+":"+a.p;g.nearCache??=new Map();if(!g.nearCache.has(ak))g.nearCache.set(ak,new Set([...g.edges.keys()].filter(id=>{const [C,p]=id.split(":").map(Number);return Math.abs(C-a.C)<=J||Math.abs(C+p-1-a.next.C)<=J;})));const nearEdges=g.nearCache.get(ak);
   const nc=nearEdges.size?Math.floor(m/nearEdges.size):0;
   if(nc&&nearEdges.has(key)&&gNear(g.edges.get(key),a.M,b.M,nc))return 4;
   return -1;
 }
 function pcCheck(g,m,which){for(const a of g.es){let n=0;for(const b of g.es)if(pcKind(g,a,b,m)>=0)n++;ok(n<=10*m,"crossing rank degree");pcDegreeChecks++;pcDegreeMax[which]=Math.max(pcDegreeMax[which],n);}}
 // Degree is verified via complete lists at queried cuts. Avoid quadratic
 // work on the largest lists by checking all focal tags used by actual pairs,
 // and an independent small sample of full-list focal tags.
 const pcFocals=new Map();
 for(const z of birthPairs.values())if(z.pcX!==undefined){
   const g=pcGroups.get(z.pcX),a=g.map.get(z.M),b=g.map.get(z.Mp),C=z.acRefs[0].C;
   ok(a&&b&&a.C<=z.pcX&&z.pcX<a.next.C&&b.C<=z.pcX&&z.pcX<b.next.C&&a.next.C<=C&&b.next.C<=C,"strict prior crossing edges");
   ok(a.C!==b.C&&(a.next.C!==b.next.C||a.next.C===C)&&a.C!==b.next.C&&a.next.C!==b.C,"first-contact prior crossing disjoint");
   if(a.p===b.p){ok(Math.abs(a.C-b.C)===2&&Math.abs(a.next.t-b.next.t)>=a.p-2,"same-label prior crossing clock lag");pcSame++;
     const p=a.p,id="PC:"+z.pcX+":"+p,factor=pcD*u/B;
     z.pcKey=makeKey("precut-same",id,factor,{x:z.pcX,p});
     const rec=pcSameKeys.get(id)||{x:z.pcX,p,n:0,med:0,high:0};rec.n++;pcSameKeys.set(id,rec);
   }else {pcMixed++;if(a.next.C===b.next.C)pcLanding++;}
   const ca=sourceCell(a.M),cb=sourceCell(b.M),mg0=ca===cb?g.cells.get(ca):null;
   const highA=pcKind(g,a,b,pcHighCap),highB=pcKind(g,b,a,pcHighCap);
   function thin(g,e,m,small){const count=small?g.small.length:g.edges.size;return count>0&&(!small||e.p<=pcY)&&g.edges.get(e.C+":"+e.p).length<=Math.floor(m/count);}
   for(const [f,h,k] of [[a,b,highA],[b,a,highB]]){if(thin(g,h,pcHighCap,false)){ok(k>=0,"all members of thin high crossing group admitted");pcThinHigh++;}pcThinChecks++;if(mg0&&thin(mg0,h,pcMedCap,true)){ok(pcKind(mg0,f,h,pcMedCap)>=0,"all members of thin small medium group admitted");pcThinMed++;}}
   if(z.pcHigh>0&&(highA>=0||highB>=0)){pcFullHigh+=z.pcHigh;pcFullAsync+=z.pcAsync;pcPaidHighPairs++;pcHighKinds[highA>=0?highA:highB]+=z.pcHigh;z.pcHigh=0;z.pcAsync=0;}
   if(z.pcMed>0){ok(mg0,"medium same original cell");const ma=pcKind(mg0,a,b,pcMedCap),mb=pcKind(mg0,b,a,pcMedCap),pa=ma>=0?z.pcLo:0,pb=mb>=0?z.pcHi:0;
     pcFullMed+=pa+pb;pcFullNever+=z.pcNever?pa+pb:0;pcPaidMedDirections+=(pa>0?1:0)+(pb>0?1:0);if(pa)pcMedKinds[ma]+=pa;if(pb)pcMedKinds[mb]+=pb;z.pcLo-=pa;z.pcHi-=pb;z.pcMed=z.pcLo+z.pcHi;z.pcNever=z.pcNever?z.pcMed:0;
   }
   if(z.pcKey){const rec=pcSameKeys.get(z.pcKey.key);rec.med+=z.pcMed;rec.high+=z.pcHigh;}
   for(const e of [a,b]){const id=z.pcX+":"+e.M;if(!pcFocals.has(id))pcFocals.set(id,{g,e});}
   if(pcIndependent<128){const find=M=>roots.get(M).find(e=>e.next&&e.C<=z.pcX&&z.pcX<e.next.C);ok(find(z.M)===a&&find(z.Mp)===b,"independent crossing oracle");pcIndependent++;}
 }
 // Avoid repeated per-focal recomputation of the nearby cohort partition.
 // The earlier function is identical; enumerate only queried focal tags.
 for(const {g,e} of pcFocals.values()){
   for(const [v,m,i] of [[g,pcHighCap,0],[g.cells.get(sourceCell(e.M)),pcMedCap,1]]){
     let n=0;for(const b of v.es)if(pcKind(v,e,b,m)>=0)n++;ok(n<=10*m,"queried full crossing degree");pcDegreeChecks++;pcDegreeMax[i]=Math.max(pcDegreeMax[i],n);
   }
 }
 for(const rec of pcSameKeys.values()){const g=pcGroups.get(rec.x),ms=g.labels.get(rec.p),parts=new Map();for(const M of ms){const e=g.map.get(M);parts.set(e.C,(parts.get(e.C)||0)+1);}const a=[...parts.values()];ok(a.length===2&&rec.n<=a[0]*a[1],"same-label crossing product envelope");pcSameProducts+=a[0]*a[1];pcSameHigh+=rec.high;pcSameMed+=rec.med;pcSameKeyChecks++;}
 const pcFinalHigh=jointBirthFlow("high",true,false,true),pcFinalMed=jointBirthFlow("med",true,false,true);delete pcFinalHigh.cutIds;delete pcFinalMed.cutIds;
 ok(near(multiFullPaid+pcFullHigh+pcFinalHigh.total,anchorJointHigh.total)&&near(pcMedFullPaid+pcFullMed+pcFinalMed.total,anchorJointMed.total),"precontact exact input partition");
 ok(pcFinalHigh.residual<=multiReoptHigh.residual+1e-6&&pcFinalMed.residual<=pcMedAfterRanks.residual+1e-6,"precontact reoptimization monotone");
 // Additional grids: assign the first feasible finer cut, rather than charge
 // a pair repeatedly. Keep the old coarse-mask result intact.
 const gridDs=[...new Set([pcD,Math.max(1,Math.floor(pcD/4)),Math.max(1,Math.floor(pcD/16)),1])],gridPairs=[...birthPairs.values()].filter(z=>z.pcMed>1e-12||z.pcHigh>1e-12),gridInfo=[],gridData=new Map(),gridAssigned=new Map();
 let gridShallow=0,gridRootContacts=0,gridAssignedPairs=0,gridSame=0,gridLanding=0,gridHighPaid=0,gridMedPaid=0,gridNeverPaid=0,gridAsyncPaid=0,gridMembership=0,gridOracle=0,gridDegreeChecks=0;
 for(const z of gridPairs){
   const C=z.acRefs[0].C;let found=false;
   for(let j=0;j<gridDs.length;j++){const d0=gridDs[j],x=d0*Math.floor((C-1)/d0);if(x<2*z.Mp-2)continue;
     const id=j+":"+x;z.gridId=id;z.gridJ=j;found=true;gridAssignedPairs++;
     if(!gridData.has(id))gridData.set(id,{x,j,es:[],pairs:[]});gridData.get(id).pairs.push(z);break;
   }
   if(!found){gridShallow++;if(C===2*z.Mp-2)gridRootContacts++;ok(C===2*z.Mp-2,"unit grid excludes only root contacts");}
 }
 for(let j=0;j<gridDs.length;j++){
   const d0=gridDs[j],fee=1/(j+1)**2,hm=analytic?Math.floor(B*u**1.5*d0/H*fee):gridStress?8:3,mm=analytic?Math.floor(mg/u**.25*d0/H*fee):gridStress?6:2;
   const info={d:d0,hm,mm,members:0,cuts:0,pairs:0,high:0,med:0};gridInfo.push(info);
   const queries=new Map([...gridData.values()].filter(g=>g.j===j).map(g=>[g.x,g]));
   if(queries.size)for(const ar of roots.values())for(const e of ar)if(e.next)for(let x=d0*Math.ceil(e.C/d0);x<e.next.C;x+=d0){const g=queries.get(x);if(g){g.es.push(e);info.members++;}}
   ok(info.members<=N*(1+Math.ceil(H/d0)),"multigrid full membership budget");
   gridMembership+=info.members;info.cuts=queries.size;
   for(const g of queries.values()){
     Object.assign(g,pcGroup(g.es));ok(g.map.size===g.es.length,"multigrid unique membership");
     const cells=new Map();for(const e of g.es){const c=sourceCell(e.M);if(!cells.has(c))cells.set(c,[]);cells.get(c).push(e);}g.cells=new Map([...cells].map(([c,a])=>[c,pcGroup(a)]));
     for(const [p,ms] of g.labels){const ss=[...new Set(ms.map(M=>g.map.get(M).C))].sort((a,b)=>a-b);ok(ss.length<=2&&(ss.length<2||ss[1]-ss[0]===2),"multigrid arithmetic slots");gridOracle++;}
     for(const z of g.pairs){
       const a=g.map.get(z.M),b=g.map.get(z.Mp),C=z.acRefs[0].C;ok(a&&b&&a.C<=g.x&&b.C<=g.x&&a.next.C>g.x&&b.next.C>g.x&&a.next.C<=C&&b.next.C<=C&&a.C!==b.C,"multigrid actual prior crossings");
       if(a.p===b.p){ok(Math.abs(a.C-b.C)===2&&Math.abs(a.next.t-b.next.t)>=a.p-2,"multigrid same-label phase");gridSame++;}
       if(a.next.C===b.next.C){ok(a.next.C===C,"multigrid landing");gridLanding++;}
       info.pairs++;z.gridA=a;z.gridB=b;
       if(z.pcHigh>0&&(pcKind(g,a,b,hm)>=0||pcKind(g,b,a,hm)>=0)){info.high+=z.pcHigh;gridHighPaid+=z.pcHigh;gridAsyncPaid+=z.pcAsync;z.pcHigh=z.pcAsync=0;}
       if(z.pcMed>0){const cg=g.cells.get(sourceCell(a.M));ok(cg.map.has(b.M),"multigrid medium cell");const pa=pcKind(cg,a,b,mm)>=0?z.pcLo:0,pb=pcKind(cg,b,a,mm)>=0?z.pcHi:0;info.med+=pa+pb;gridMedPaid+=pa+pb;gridNeverPaid+=z.pcNever?pa+pb:0;z.pcLo-=pa;z.pcHi-=pb;z.pcMed=z.pcLo+z.pcHi;z.pcNever=z.pcNever?z.pcMed:0;}
     }
     // Full-list checks at a deterministic sample of focal tags.
     for(const e of g.es.slice(0,8))for(const [v,m] of [[g,hm],[g.cells.get(sourceCell(e.M)),mm]]){ok(v.es.filter(b=>pcKind(v,e,b,m)>=0).length<=10*m,"multigrid rank degree");gridDegreeChecks++;}
   }
 }
 ok(gridAssignedPairs+gridShallow===gridPairs.length,"multigrid assignment partition");
 const gridAfterHigh=jointBirthFlow("high",true,false,true),gridAfterMed=jointBirthFlow("med",true,false,true);delete gridAfterHigh.cutIds;delete gridAfterMed.cutIds;
 ok(gridAfterHigh.residual<=pcFinalHigh.residual+1e-6&&gridAfterMed.residual<=pcFinalMed.residual+1e-6,"multigrid reopt monotonic");
 // Actual residual support cores. Freeze the unpaid fractions of the feasible
 // multigrid flow; remove only these amounts from the original pair weights.
 // Use global root constraints plus
 // per-cut and per-opposite-edge-cohort constraints. A pair is in at most
 // six endpoint constraints, and every constraint is removed at most once.
 function gridCore(metric){
   const hi=metric==="high",key=hi?"pcHigh":"pcMed",other=hi?"pcAsync":"pcNever",edgeList=[],nodes=new Map(),unit=hi?3*H:H/mg;
   const globalCap=analytic?(hi?B*u**1.5:mg/u**.25)*unit:hi?H/(gridStress?4:16):gridStress?.5:.1;
   let paid=0,paidOther=0,deleted=0,coreBudget=0,full=0,fullOther=0,initialByKind={},paidByKind={},peelsByKind={},pairGroups=new Map();
   function node(id,cap,kind){let n=nodes.get(id);if(!n){n={id,cap,kind,degree:0,edges:[],dead:false};nodes.set(id,n);coreBudget+=cap;initialByKind[kind]=(initialByKind[kind]||0)+cap;}else ok(near(n.cap,cap),"fixed core capacity");return n;}
   for(const z of gridPairs){const frac=z[hi?"gridUnpaidHigh":"gridUnpaidMed"]||0,w=z[key]*frac;if(w<=1e-12)continue;const e={z,w,frac,other:z[other]*frac,nodes:[],dead:false},g=z.gridId!==undefined?gridData.get(z.gridId):null;
     full+=w;fullOther+=e.other;
     for(const M of [z.M,z.Mp])e.nodes.push(node("R:"+M,globalCap,"root"));
     if(!g)e.nodes.push(node("Y:"+z.Mp,globalCap,"root-contact"));
     if(g){
       const d0=gridDs[g.j],fee=1/(g.j+1)**2,scale=analytic?unit*(hi?B*u**1.5:mg/u**.25)*d0/H*fee:hi?H/(gridStress?4:32):gridStress?.5:.08;
       const v=hi?g:g.cells.get(sourceCell(z.M));ok(v.map.has(z.Mp),"core medium cell");
       const [a,b]=[z.gridA,z.gridB],aa=a.C+":"+a.p,bb=b.C+":"+b.p,cid=hi?"all":sourceCell(z.M),base=z.gridId+":"+cid;
       for(const [f,partner] of [[a,bb],[b,aa]]){
         e.nodes.push(node("G:"+base+":"+f.M,scale,"cut"));
         e.nodes.push(node("E:"+base+":"+f.M+":"+partner,scale/Math.max(1,v.edges.size),"opposite"));
       }
       const id=base+"|"+[aa,bb].sort().join("|");let rec=pairGroups.get(id);if(!rec){rec={id,g,a:aa<bb?aa:bb,b:aa<bb?bb:aa,es:[],cap:scale/Math.max(1,v.edges.size)};pairGroups.set(id,rec);}rec.es.push(e);
     }
     for(const n of e.nodes){n.degree+=w;n.edges.push(e);}edgeList.push(e);
   }
   const q=[];for(const n of nodes.values())if(n.degree<=n.cap+1e-10)q.push(n);
   let nodePops=0;for(let i=0;i<q.length;i++){const n=q[i];if(n.dead||n.degree>n.cap+1e-10)continue;n.dead=true;nodePops++;peelsByKind[n.kind]=(peelsByKind[n.kind]||0)+1;let charge=0;
     for(const e of n.edges)if(!e.dead){e.dead=true;charge+=e.w;paid+=e.w;paidOther+=e.other;deleted++;for(const v of e.nodes){v.degree-=e.w;if(!v.dead&&v.degree<=v.cap+1e-10)q.push(v);}}
     ok(charge<=n.cap+1e-7,"core peel within local capacity");paidByKind[n.kind]=(paidByKind[n.kind]||0)+charge;
   }
   let remaining=0,otherRemaining=0,edges=0,activeNodes=0,minDegree=Infinity;
   for(const e of edgeList)if(e.dead){e.z[key]*=1-e.frac;e.z[other]*=1-e.frac;if(!hi){e.z.pcLo*=1-e.frac;e.z.pcHi*=1-e.frac;}}else{remaining+=e.w;otherRemaining+=e.other;edges++;for(const n of e.nodes)ok(!n.dead&&n.degree>n.cap-1e-8,"surviving core degree");}
   for(const n of nodes.values())if(!n.dead&&n.degree>1e-9){activeNodes++;minDegree=Math.min(minDegree,n.degree/n.cap);}
   let rectangles=0,rectRaw=0,rectAllowed=0,rectWeight=0,rectEnvelope=0,rectWitness=0,rectMinLeft=Infinity,rectMinRight=Infinity,rectMoment1=0,rectMoment2=0,rectDegreeChecks=0,rectMaxDensity=0;
   for(const rec of pairGroups.values()){
     const live=rec.es.filter(e=>!e.dead);if(!live.length)continue;rectangles++;
     const A=new Map(),B0=new Map(),actual=new Set();
     for(const e of live){const z=e.z,a=z.gridA,b=z.gridB;const [v,w]=a.C+":"+a.p===rec.a?[a,b]:[b,a];A.set(v.M,v);B0.set(w.M,w);actual.add(pairId(v.M,w.M));rectWeight+=e.w;}
     rectMinLeft=Math.min(rectMinLeft,A.size);rectMinRight=Math.min(rectMinRight,B0.size);
     let allowed=0,raw=A.size*B0.size,envelope=0;
     for(const a of A.values())for(const b of B0.values()){
       // All original horizons up to the crossing prevertex inclusive.
       // These are strictly earlier than every eligible pair's first contact.
       const ar=roots.get(a.M),br=roots.get(b.M);let i=0,j=0,Z=0;
       while(i<=a.multiIndex&&j<=b.multiIndex){if(ar[i].C===br[j].C){Z++;i++;j++;}else if(ar[i].C<br[j].C)i++;else j++;}
       rectMoment1+=Z;rectMoment2+=Z*Z;
       if(Z){rectWitness++;ok(!actual.has(pairId(a.M,b.M)),"actual core edge has disjoint prior prefixes");continue;}
       allowed++;envelope+=hi?2*Math.min(a.multiRetTail,b.multiRetTail):((ar.at(-1).C-a.C)+(br.at(-1).C-b.C))/mg;
     }
     rectRaw+=raw;rectAllowed+=allowed;rectEnvelope+=envelope;rectMaxDensity=Math.max(rectMaxDensity,live.length/Math.max(1,allowed));
     ok(live.length<=allowed,"core rectangle actual support");
     for(const e of live){const z=e.z;const a=z.gridA,b=z.gridB;const an=e.nodes.find(n=>n.kind==="opposite"&&n.id.includes(":"+a.M+":")),bn=e.nodes.find(n=>n.kind==="opposite"&&n.id.includes(":"+b.M+":"));ok(an&&bn&&an.degree>an.cap-1e-8&&bn.degree>bn.cap-1e-8,"both opposite core degrees");rectDegreeChecks++;}
   }
   ok(near(full,paid+remaining)&&near(fullOther,paidOther+otherRemaining)&&paid<=coreBudget+1e-6,"core weight conservation");
   // Independent simultaneous-round peeling, recomputing weighted degrees
   // from scratch. The greatest admissible support is order independent.
   const liveSet=new Set(edgeList);let rounds=0,oracleChecks=0;
   while(true){const sums=new Map();for(const e of liveSet)for(const n of e.nodes)sums.set(n,(sums.get(n)||0)+e.w);
     const bad=new Set([...sums].filter(([n,w])=>w<=n.cap+1e-10).map(([n])=>n));if(!bad.size)break;
     let count=0;for(const e of liveSet)if(e.nodes.some(n=>bad.has(n))){liveSet.delete(e);count++;}ok(count>0,"batch core progress");rounds++;
   }
   for(const e of edgeList){ok(liveSet.has(e)===!e.dead,"order-independent core oracle");oracleChecks++;}
   const upperBudget=2*N*globalCap+gridInfo.reduce((z,v,j)=>{const scale=analytic?unit*(hi?B*u**1.5:mg/u**.25)*v.d/H/(j+1)**2:hi?H/(gridStress?4:32):gridStress?.5:.08;return z+2*scale*v.members;},0);
   ok(coreBudget<=upperBudget+1e-6,"full original core capacity budget");
   ok(!hi||rectWeight<=rectEnvelope+1e-6,"retained-tail rectangle upper bound");
   ok(rectMoment2===0||rectMoment1*rectMoment1/rectMoment2<=rectWitness+1e-6,"rectangle witness moment");
   return {full,fullOther,paid,paidOther,remaining,otherRemaining,deleted,edges,rounds,oracleChecks,upperBudget,nodes:nodes.size,nodePops,activeNodes,coreBudget,minDegree:Number.isFinite(minDegree)?minDegree:0,initialByKind,paidByKind,peelsByKind,rectangles,rectRaw,rectAllowed,rectWeight,rectEnvelope,rectWitness,rectMoment1,rectMoment2,rectMinLeft:Number.isFinite(rectMinLeft)?rectMinLeft:0,rectMinRight:Number.isFinite(rectMinRight)?rectMinRight:0,rectDegreeChecks,rectMaxDensity};
 }
 const gridHighCore=gridCore("high"),gridMedCore=gridCore("med");
 const gridFinalHigh=jointBirthFlow("high",true,false,true),gridFinalMed=jointBirthFlow("med",true,false,true);delete gridFinalHigh.cutIds;delete gridFinalMed.cutIds;
 ok(near(gridHighCore.full,gridAfterHigh.residual)&&near(gridMedCore.full,gridAfterMed.residual)&&near(gridFinalHigh.total+gridHighCore.paid,gridAfterHigh.total)&&near(gridFinalMed.total+gridMedCore.paid,gridAfterMed.total)&&gridFinalHigh.residual<=gridHighCore.remaining+1e-6&&gridFinalMed.residual<=gridMedCore.remaining+1e-6,"unpaid core then reoptimization conservation");
 // Root-attached cut: the older root crosses x=2*M'-3 even if the
 // younger root has not yet made a single selection.
 const starY=Math.max(5,Math.ceil(analytic?B*Math.exp(-Math.sqrt(u)):B/(starStress?4:8))),starS=Math.max(1,Math.floor(analytic?u**.25:starStress?8:4)),starRare=new Set(),starAgeHist={},starQuery=new Map();
 let starRareProxy=0,starRareActual=0,starRareCount=0,starRareWitnesses=0,starRareOracle=0,starSupport0=0,starSupportShort=0,starSlotChecks=0,starPrefixChecks=0,starQueryPairs=0,starRootPairs=0,starNearPairs=0,starNearLargePairs=0,starNearLargeHigh=0,starNearLargeMed=0,starMaxAge=0,starMaxLanding=0,starEarlierConflicts=0;
 const starKeys=new Map(),starRootKeys=new Map(),starBandCounts=new Map();
 const ageBand=a=>a<=1?0:Math.ceil(Math.log2(a));
 function starFee(p){return p>=starY?1/Math.sqrt(u):p>=B**.125?1:ell;}
 // All original prime roots; independent factor scan of the shallow interval.
 for(const [M,ar] of roots){
   let large=false,seen=new Set();
   for(let i=0;i<=starS;i++)for(const q of [...new Set(fs(M+i-1).concat(fs(M+i)))]){
     // Landing D=2M-2+2i must be reachable across x=2M-3.
     if(2*i>q-2)continue;const id=i+":"+q;seen.add(id);
     if(q>=starY){large=true;starRareWitnesses++;}
   }
   starSupportShort+=seen.size;starSupport0+=[...seen].filter(k=>k.startsWith("0:")).length;
   if(large){starRare.add(M);starRareCount++;starRareProxy+=ar.reduce((v,e)=>v+e.r,0);starRareActual+=ar.at(-1).t-ar[0].t;}
   if(starRareOracle<64){
     const x=2*M-3,oracle=new Set();for(const q of primesAll)for(const sigma of [0,-2]){const D=x+1+mod(sigma-x-1,2*q);if(D<=x+q-1&&D<=x+1+2*starS)oracle.add((D-x-1)/2+":"+q);}
     ok(oracle.size===seen.size&&[...oracle].every(k=>seen.has(k)),"independent prime-root shallow support");starRareOracle++;
   }
 }
 // Independent prime progression enumeration for ALL shallow support keys.
 let starAPSupport=0,starAPSupport0=0,starAPLarge=0,starAPRootContacts=0,starAPLargeRootContacts=0,starAPRootContactMax=0;const apRare=new Set(),actualRootContacts=new Map();
 for(const q of primesAll)for(let i=0;i<=starS&&2*i<=q-2;i++)for(const res of [mod(1-i,q),mod(-i,q)]){
   for(let M=X+mod(res-X,q);M<2*X;M+=q)if(roots.has(M)){
     starAPSupport++;if(i===0)starAPSupport0++;if(q>=starY){starAPLarge++;apRare.add(M);}
   }
 }
 ok(starAPSupport===starSupportShort&&starAPSupport0===starSupport0&&starAPLarge===starRareWitnesses&&apRare.size===starRare.size&&[...apRare].every(M=>starRare.has(M)),"complete independent prime progression support enumeration");
 // All actual first projected contacts at a larger prime's initial horizon.
 // These include pairs absent from the residual and give nonempty controls.
 for(const [M,ar] of roots)for(const v of ar)if(v.prev){
   const Mp=(v.C+2)/2;if(Mp<=M||!roots.has(Mp))continue;
   const e=v.prev,q=e.p,x=2*Mp-3;
   ok(e.C<=x&&x<v.C&&q<=B&&q<Mp&&(Mp-1)%q===0&&v.t%2===0,"actual root contact crossing and parity");
   ok(!roots.get(Mp).some(w=>w.C<v.C),"younger root has no preceding projected vertex");
   starAPRootContacts++;if(q>=starY){starAPLargeRootContacts++;ok(starRare.has(Mp),"root contact exceptional support");}
   actualRootContacts.set(Mp,(actualRootContacts.get(Mp)||0)+1);starAPRootContactMax=Math.max(starAPRootContactMax,actualRootContacts.get(Mp));
 }
 // Current input uses only unpaid fractions of the final multigrid flow.
 for(const z of birthPairs.values()){
   const h=z.pcHigh*(z.gridUnpaidHigh||0),m=z.pcMed*(z.gridUnpaidMed||0);if(h<=1e-9&&m<=1e-12)continue;
   const [a,b]=z.acRefs,C=a.C,x=2*z.Mp-3,A=roots.get(z.M),B0=roots.get(z.Mp);
   let lo=0,hi=A.length;while(lo<hi){const k=(lo+hi)>>1;if(A[k].C<=x)lo=k+1;else hi=k;}const e=A[lo-1];
   ok(e&&e.next&&e.C<=x&&e.next.C>x&&e.next.C<=C&&b.C===C,"older crossing immediately before younger root");
   const age=(C-x-1)/2,i=(e.next.C-x-1)/2,p=e.p,j=ageBand(age),S=2**j;
   ok(Number.isInteger(age)&&age>=0&&i>=0&&i<=age&&2*i<=p-2,"root-star age and landing offset");
   ok((z.Mp+i-1)%p===0||(z.Mp+i)%p===0,"root-star prime progression");
   ok(i!==0||((z.Mp-1)%p===0&&e.next.t%2===0),"root landing uses even arrival only");
   // Earlier root prefix of younger source up to first contact must avoid
   // the older crossing landing, unless that landing IS the first contact.
   if(e.next.C<C){ok(!rawByRoot.get(z.Mp).has(e.next.C),"no earlier contact at landing");starPrefixChecks++;}
   if(age<=starS&&p>=starY){ok(starRare.has(z.Mp),"large shallow landing implies exceptional prime root");starNearLargePairs++;starNearLargeHigh+=h;starNearLargeMed+=m;}
   if(age===0)starRootPairs++;if(age<=starS)starNearPairs++;
   starMaxAge=Math.max(starMaxAge,age);starMaxLanding=Math.max(starMaxLanding,i);starQueryPairs++;
   z.star={e,age,i,p,j,S,h,m,x};const rk=z.Mp+":"+j,key=rk+":"+i+":"+p;
   if(!starKeys.has(key))starKeys.set(key,{M:z.Mp,j,S,i,p,es:[]});starKeys.get(key).es.push(z);
   if(!starRootKeys.has(rk))starRootKeys.set(rk,{M:z.Mp,j,S,es:[]});starRootKeys.get(rk).es.push(z);
   if(!starQuery.has(z.Mp))starQuery.set(z.Mp,{x,es:[],keys:new Map()});
   const rec=starAgeHist[j]||{pairs:0,high:0,med:0,root:0};rec.pairs++;rec.high+=h;rec.med+=m;if(age===0)rec.root++;starAgeHist[j]=rec;
 }
 // Populate full older crossing lists at each queried younger-root cut.
 // Iterate younger prime starts in each actual older edge's interval.
 const youngs=[...starQuery.keys()].sort((a,b)=>a-b);
 let starMembership=0,starMaxGroup=0,starActualGroups=0,starRankChecks=0,starHighRank=0,starMedRank=0,starNeverRank=0,starAsyncRank=0,starRankDirections=0;
 function starLower(a,x){let l=0,r=a.length;while(l<r){const m=(l+r)>>1;if(a[m]<x)l=m+1;else r=m;}return l;}
 for(const ar of roots.values())for(const e of ar)if(e.next){
   // x=2*M'-3 in [C,D), with M'>M.
   let k=starLower(youngs,Math.max(e.M+1,Math.ceil((e.C+3)/2)));
   while(k<youngs.length&&2*youngs[k]-3<e.next.C){const M=youngs[k++],g=starQuery.get(M);g.es.push(e);starMembership++;}
 }
 for(const [M,g] of starQuery){
   ok(new Set(g.es.map(e=>e.M)).size===g.es.length,"one crossing per older root");
   g.es.sort((a,b)=>b.M-a.M);
   for(const e of g.es){const i=(e.next.C-2*M+2)/2,id=i+":"+e.p;
     ok(i>=0&&2*i<=e.p-2&&((M+i-1)%e.p===0||(M+i)%e.p===0),"full reference root-slot arithmetic");if(!g.keys.has(id))g.keys.set(id,[]);g.keys.get(id).push(e);starSlotChecks++;}
   starActualGroups+=g.keys.size;starMaxGroup=Math.max(starMaxGroup,...[...g.keys.values()].map(a=>a.length));
 }
 // For each age band, allocate a summable rank budget at one younger root.
 // No membership factor for fine grids. Directed medium mask admits either
 // direction because whole unordered pair envelope is used in the budget.
 for(const [rk,rec] of starRootKeys){
   const g=starQuery.get(rec.M),slots=[...g.keys.entries()].filter(([k])=>Number(k.split(":")[0])<=rec.S),a=slots.length;
   const hcap=analytic?Math.floor(B*u**1.5/(rec.j+1)**2):starStress?16:4,mcap=analytic?Math.floor(mg/u**.25/(rec.j+1)**2):starStress?8:2;
   const ranks=new Map(g.es.map((e,i)=>[e.M,i]));
   const lr=new Map();for(const [k,es] of slots)for(let i=0;i<es.length;i++)lr.set(es[i].M,i);
   function admit(z,m){return ranks.get(z.M)<m||(a>0&&lr.get(z.M)<Math.floor(m/a));}
   for(const [m,kind] of [[hcap,"h"],[mcap,"m"]]){const n=g.es.filter(e=>ranks.get(e.M)<m||lr.has(e.M)&&lr.get(e.M)<Math.floor(m/Math.max(1,a))).length;ok(n<=2*m,"root-star rank degree");starRankChecks++;}
   for(const z of rec.es){const st=z.star;ok(g.keys.get(st.i+":"+st.p)?.includes(st.e),"actual older crossing in full reference slot");
     if(st.h>1e-9&&admit(z,hcap)){starHighRank+=st.h;starAsyncRank+=z.pcAsync*(z.gridUnpaidHigh||0);st.hp=true;}
     if(st.m>1e-12&&admit(z,mcap)){starMedRank+=st.m;starNeverRank+=z.pcNever*(z.gridUnpaidMed||0);st.mp=true;starRankDirections++;}
   }
 }
 // Arithmetic slot budgets, with a reciprocal-prime fee and age-band fee.
 // Use actual unpaid weights and simultaneous core constraints only.
 function starCore(hi){
   const key=hi?"pcHigh":"pcMed",other=hi?"pcAsync":"pcNever",frac=hi?"gridUnpaidHigh":"gridUnpaidMed",U=hi?3*H:H/mg,L0=hi?B*u**1.5:mg/u**.25;
   const base=analytic?U*L0:hi?H/(starStress?2:8):starStress?1:.15;
   let full=0,fullOther=0,rankPaid=0,rankOther=0,paid=0,paidOther=0,edges=[],nodes=new Map(),caps=0,groups=0,rounds=0,remaining=0,remainingOther=0,root0=0,live=0,liveKeys=0,maxDegree=0,byKind={},rankCount=0;
   function node(id,b,kind){let n=nodes.get(id);if(!n){n={id,b,kind,d:0,es:[],dead:false};nodes.set(id,n);caps+=b;}else ok(near(n.b,b),"frozen star capacity");return n;}
   for(const z of birthPairs.values())if(z.star){const st=z.star,w=hi?st.h:st.m,f=z[frac]||0;if(w<=(hi?1e-9:1e-12))continue;const o=z[other]*f;full+=w;fullOther+=o;
     if(hi?st.hp:st.mp){rankPaid+=w;rankOther+=o;rankCount++;z[key]*=1-f;z[other]*=1-f;if(!hi){z.pcLo*=1-f;z.pcHi*=1-f;}continue;}
     const t=1/(st.j+1)**2,scale=base*t,fee=starFee(st.p),slotCap=scale/(Math.min(st.S+1,st.p)*fee);
     const e={z,w,o,f,dead:false,ns:[node("R:"+z.Mp+":"+st.j,scale,"band"),node("K:"+z.Mp+":"+st.j+":"+st.i+":"+st.p,slotCap,"slot")]};
     for(const n of e.ns){n.d+=w;n.es.push(e);}edges.push(e);
   }
   const q=[...nodes.values()].filter(n=>n.d<=n.b+1e-10);
   for(let k=0;k<q.length;k++){const n=q[k];if(n.dead||n.d>n.b+1e-10)continue;n.dead=true;let w=0;
     for(const e of n.es)if(!e.dead){e.dead=true;w+=e.w;paid+=e.w;paidOther+=e.o;for(const a of e.ns){a.d-=e.w;if(!a.dead&&a.d<=a.b+1e-10)q.push(a);}}
     ok(w<=n.b+1e-7,"root-star peel cap");byKind[n.kind]=(byKind[n.kind]||0)+w;
   }
   const oracle=new Set(edges);
   while(true){const deg=new Map();for(const e of oracle)for(const n of e.ns)deg.set(n,(deg.get(n)||0)+e.w);const bad=new Set([...deg].filter(([n,d])=>d<=n.b+1e-10).map(([n])=>n));if(!bad.size)break;for(const e of oracle)if(e.ns.some(n=>bad.has(n)))oracle.delete(e);rounds++;}
   for(const e of edges){ok(oracle.has(e)===!e.dead,"independent star core oracle");if(e.dead){e.z[key]*=1-e.f;e.z[other]*=1-e.f;if(!hi){e.z.pcLo*=1-e.f;e.z.pcHi*=1-e.f;}}else{remaining+=e.w;remainingOther+=e.o;live++;if(e.z.star.age===0)root0+=e.w;for(const n of e.ns)ok(n.d>n.b-1e-8,"actual star degree");}}
   for(const n of nodes.values())if(!n.dead&&n.d>1e-10){if(n.kind==="slot")liveKeys++;maxDegree=Math.max(maxDegree,n.es.filter(e=>!e.dead).length);}
   ok(near(full,rankPaid+paid+remaining)&&near(fullOther,rankOther+paidOther+remainingOther)&&paid<=caps+1e-6,"root-star weight conservation");
   return {full,fullOther,rankPaid,rankOther,rankCount,paid,paidOther,remaining,remainingOther,root0,live,liveKeys,maxDegree,caps,rounds,byKind,edges:edges.length};
 }
 const starHighCore=starCore(true),starMedCore=starCore(false);
 const starFinalHigh=jointBirthFlow("high",true,false,true),starFinalMed=jointBirthFlow("med",true,false,true);delete starFinalHigh.cutIds;delete starFinalMed.cutIds;
 ok(near(starHighCore.full,gridFinalHigh.residual)&&near(starMedCore.full,gridFinalMed.residual)&&near(starFinalHigh.total+starHighCore.rankPaid+starHighCore.paid,gridFinalHigh.total)&&near(starFinalMed.total+starMedCore.rankPaid+starMedCore.paid,gridFinalMed.total),"root-star disjoint payment conservation");
 ok(starFinalHigh.residual<=starHighCore.remaining+1e-6&&starFinalMed.residual<=starMedCore.remaining+1e-6,"root-star feasible reoptimization");
 // Absorbing local projected DAG at a younger root. Each younger
 // visited offset is terminal; it cannot be traversed before the first hit.
 const absQueries=new Map(),absAgeLimit=analytic?Math.max(1,Math.floor(u**.25)):prefixStress?Math.floor(B/2):Math.floor(B/4);
 let absPairCount=0,absOutside=0,absHighBefore=0,absMedBefore=0,absHighPaid=0,absMedPaid=0,absAsyncPaid=0,absNeverPaid=0,absRankChecks=0,absOldMembership=0,absRelaxMembership=0,absExactMembership=0,absSlotRaw=0,absSlotAllowed=0,absDAGNodes=0,absDAGEdges=0,absOracleChecks=0,absReverseWords=0,absMaxReverseWords=0,absPhysical=0,absNoPhysical=0,absReset=0,absNonreset=0,absNonresetBig=0,absPhysicalShallow=0,absConeChecks=0,absLagChecks=0,absMaxLag=0,absLargeCrossHigh=0,absLargeCrossPairs=0;
 const absPairList=[],absBackDepth=Math.max(1,Math.floor(Math.log(u))),absBackCounts={root:0,reset:0,depth:0,steps:0,shallow:0,shallowRoot:0,shallowReset:0,shallowDepth:0,maxGain:0},absLargeP=analytic?Math.max(3,Math.ceil(B*u**(-1.25))):Math.max(3,Math.ceil(B/(prefixStress?4:2))),absLargeS=analytic?Math.floor(u**.25):prefixStress?32:16;
 for(const z of birthPairs.values()){
   const fH=z.gridUnpaidHigh||0,fM=z.gridUnpaidMed||0,h=z.pcHigh*fH,m=z.pcMed*fM;if(h<=1e-9&&m<=1e-12)continue;
   const st=z.star;ok(st,"unpaid pair has original star");
   absHighBefore+=h;absMedBefore+=m;absPairList.push(z);
   if(st.age<=absLargeS&&st.p>=absLargeP){absLargeCrossPairs++;absLargeCrossHigh+=h;z.absLarge=true;}
   const ar=roots.get(z.M),br=roots.get(z.Mp),v=st.e.next,d0=2*v.t-v.C,s0=v.t%2,p0=st.p;
   if(d0===6*s0)absReset++;else absNonreset++;
   if(p0>=5&&d0!==6*s0){ok(d0>=2*p0,"nonreset crossing deficit");absNonresetBig++;}
   let i=0,j=0,meet=null;
   while(i<ar.length&&j<br.length){const a=ar[i],b=br[j];if(a.C<b.C)i++;else if(a.C>b.C)j++;else{if(a.t===b.t){meet=[a,b];break;}i++;j++;}}
   if(meet){
     absPhysical++;const [a,b]=meet,g=(b.C-(2*z.Mp-2))/2,d1=2*b.t-b.C;
     ok(g>=st.age&&d1<=6+10*g&&d0<=d1+(b.C-v.C)&&d0<=6+12*g-2*st.i,"younger age deficit cone");absConeChecks++;
     if(g<=absAgeLimit)absPhysicalShallow++;
     if(p0>=5&&d0!==6*s0)ok(2*p0<=6+12*g-2*st.i,"large nonreset crossing delays physical birth");
     let cur=v,k=0,maxD=Math.max(6,d0),gain=0;
     while(cur.prev&&2*cur.t-cur.C!==6*(cur.t%2)&&k<absBackDepth){
       const d=2*cur.t-cur.C,q=cur.prev.p,D0=Math.max(6,d),dpre=2*cur.prev.t-cur.prev.C;
       ok(q-1<=D0/2&&Math.max(6,dpre)<=1.5*D0&&dpre-d<=q-3,"nonreset reverse step cone");
       gain+=q-1;cur=cur.prev;k++;absBackCounts.steps++;
     }
     const kind=!cur.prev?"root":2*cur.t-cur.C===6*(cur.t%2)?"reset":"depth";
     ok(gain<=maxD*(1.5**k-1)+1e-6&&Math.max(6,2*cur.t-cur.C)<=maxD*1.5**k+1e-6,"reverse gain/deficit cone");
     absBackCounts[kind]++;absBackCounts.maxGain=Math.max(absBackCounts.maxGain,gain);
     if(g<=absAgeLimit){absBackCounts.shallow++;absBackCounts["shallow"+kind[0].toUpperCase()+kind.slice(1)]++;
       if(kind==="root")ok(2*(z.Mp-z.M)<=gain,"short reverse root distance");
     }
     const [c,e]=z.acRefs,lag=Math.abs(c.t-e.t);
     ok(lag<=3*(a.C-c.C),"first projected lag needs shared gain");absLagChecks++;absMaxLag=Math.max(absMaxLag,lag);
   }else absNoPhysical++;
   if(st.age>absAgeLimit){absOutside++;continue;}
   absPairCount++;const M=z.Mp,j0=st.j,id=M+":"+j0;
   if(!absQueries.has(id))absQueries.set(id,{M,j:j0,S:Math.min(absAgeLimit,2**j0),pairs:[]});absQueries.get(id).pairs.push(z);
 }
 // Nonempty independent arithmetic controls even when the previous residual is zero.
 let absControlQueries=0,absControlRoots=0;
 for(const M of roots.keys()){if(absControlRoots>=8)break;absControlRoots++;
   const S=Math.min(absAgeLimit,16),id="control:"+M;
   // Controls need only the arithmetic DAG and BFS, not the actual star list.
   absQueries.set(id,{M,j:0,S,pairs:[],control:true});absControlQueries++;
 }
 // At each queried star band, compute all possible FIRST younger hits for
 // every landing offset, by a descending dynamic program on the relaxed DAG.
 for(const q of absQueries.values()){
   const M=q.M,S=q.S,ar=roots.get(M),seen=new Set(ar.map(e=>(e.C-(2*M-2))/2).filter(i=>i<=S)),hit=Array.from({length:S+1},()=>new Set()),out=Array.from({length:S+1},()=>[]),words=new Float64Array(S+1);
   for(let k=1;k<=S;k++)for(const p of new Set(fs(M+k-1).concat(fs(M+k)))){const i=k-(p-1)/2;if(i>=0){out[i].push(k);absDAGEdges++;}}
   absDAGNodes+=S+1;
   for(let i=S;i>=0;i--){if(seen.has(i)){hit[i].add(i);words[i]=1;}else for(const k of out[i]){for(const a of hit[k])hit[i].add(a);words[i]=Math.min(Number.MAX_SAFE_INTEGER,words[i]+words[k]);}absReverseWords+=words[i];absMaxReverseWords=Math.max(absMaxReverseWords,words[i]);}
   // Independent forward BFS for every landing offset, stopping at first hit.
   for(let i=0;i<=S;i++){const Q=[i],V=new Set([i]),R=new Set();for(let j=0;j<Q.length;j++){const k=Q[j];if(seen.has(k)){R.add(k);continue;}for(const l of out[k])if(!V.has(l)){V.add(l);Q.push(l);}}
     ok(R.size===hit[i].size&&[...R].every(a=>hit[i].has(a)),"absorbing first-hit DAG oracle");absOracleChecks++;
   }
   function band(a){return q.j===0?a<=1:a>2**(q.j-1)&&a<=2**q.j;}
   if(q.control)continue;
   const can=i=>i>=0&&i<=S&&[...hit[i]].some(band),g=starQuery.get(M);
   ok(g,"queried full star list exists");
   const elig=g.es.filter(e=>(e.next.C-2*M+2)/2<=S),relax=elig.filter(e=>can((e.next.C-2*M+2)/2));
   absOldMembership+=elig.length;absRelaxMembership+=relax.length;
   const slotRaw=new Set(elig.map(e=>(e.next.C-2*M+2)/2+":"+e.p)),slotAllowed=new Set(relax.map(e=>(e.next.C-2*M+2)/2+":"+e.p));absSlotRaw+=slotRaw.size;absSlotAllowed+=slotAllowed.size;
   const exact=[];
   for(const e of relax){const old=roots.get(e.M);let i=e.next.multiIndex,a=null;for(;i<old.length;i++){const k=(old[i].C-2*M+2)/2;if(k>S)break;if(seen.has(k)){a=k;break;}}
     if(a!==null){ok(hit[(e.next.C-2*M+2)/2].has(a),"actual path in absorbing DAG");if(band(a))exact.push(e);}
   }
   absExactMembership+=exact.length;
   const ranks=new Map(exact.map((e,i)=>[e.M,i])),groups=new Map();
   for(const e of exact){const id=(e.next.C-2*M+2)/2+":"+e.p;if(!groups.has(id))groups.set(id,[]);groups.get(id).push(e);}
   const local=new Map();for(const es of groups.values())for(let i=0;i<es.length;i++)local.set(es[i].M,i);
   const hcap=analytic?Math.floor(B*u**1.5/(q.j+1)**2):prefixStress?12:4,mcap=analytic?Math.floor(mg/u**.25/(q.j+1)**2):prefixStress?6:2;
   const good=(M,m)=>ranks.get(M)<m||local.get(M)<Math.floor(m/Math.max(1,groups.size));
   for(const m of [hcap,mcap]){ok(exact.filter(e=>good(e.M,m)).length<=2*m,"exact absorbing cohort rank");absRankChecks++;}
   for(const z of q.pairs){ok(ranks.has(z.M)&&hit[z.star.i].has(z.star.age),"actual first contact in exact cohort");
     z.absHP=good(z.M,hcap);z.absMP=good(z.M,mcap);
   }
 }
 // Whole high pair class with short younger age and large older crossing
 // paid directly by older gain: at most S+1 younger roots per such edge.
 let absLargeControls=0,absLargeUpper=0,absLargeGain=0;
 for(const ar of roots.values())for(const e of ar)if(e.p>=absLargeP){absLargeControls++;absLargeUpper+=Math.min(absLargeS+1,Math.floor((e.p-2)/2)+1);absLargeGain+=e.p-1;}
 ok(absLargeCrossPairs<=absLargeUpper&&absLargeGain<=G,"older large crossing gain-count bound");
 for(const z of absPairList){const f=z.gridUnpaidHigh||0,g=z.gridUnpaidMed||0;
   if(z.absHP||z.absLarge){absHighPaid+=z.pcHigh*f;absAsyncPaid+=z.pcAsync*f;z.pcHigh*=1-f;z.pcAsync*=1-f;}
   if(z.absMP){absMedPaid+=z.pcMed*g;absNeverPaid+=z.pcNever*g;z.pcMed*=1-g;z.pcNever*=1-g;z.pcLo*=1-g;z.pcHi*=1-g;}
 }
 const absFinalHigh=jointBirthFlow("high",true,false,true),absFinalMed=jointBirthFlow("med",true,false,true);delete absFinalHigh.cutIds;delete absFinalMed.cutIds;
 ok(near(absHighBefore,starFinalHigh.residual)&&near(absMedBefore,starFinalMed.residual)&&near(absFinalHigh.total+absHighPaid,starFinalHigh.total)&&near(absFinalMed.total+absMedPaid,starFinalMed.total)&&absFinalHigh.residual<=absHighBefore-absHighPaid+1e-6&&absFinalMed.residual<=absMedBefore-absMedPaid+1e-6,"absorbing prefix disjoint accounting");
 // Actual reset renewal graph: each physical reset has one next reset
 // (if any original tag reaches it), and the continuing tags are a suffix.
 const renewK=Math.max(1,Math.floor(analytic?Math.sqrt(u):resetStress?4:3)),renewEps=analytic?u**(-.125):resetStress?.125:.25,renewA=Math.max(1,Math.ceil(analytic?8*u**(2/3):B/(resetStress?2:4))),renewP=Math.max(1,Math.ceil(analytic?B/u**.5:B/(resetStress?4:2)));
 const renewGroups=new Map(),renewId=e=>e.C+":"+e.t,resetV=e=>2*e.t-e.C===6*(e.t%2);
 let renewVisits=0,renewTransitions=0,renewRoots=0,renewShortEntries=0,renewShortChecks=0,renewLongEntries=0,renewGrowth=0,renewMarkCount=0,renewSpanSum=0,renewSpanMarks=0,renewGain=0,renewLoss=0,renewLossPairs=0,renewBirthPairs=0,renewMaxMass=0,renewMaxIn=0,renewSuffixChecks=0,renewIndegreeChecks=0,renewNearRoots=0,renewWindowChecks=0;
 const choose2=n=>n*(n-1)/2;
 for(const ar of roots.values()){
   const rr=[];let latest=null,prev=null,gsum=0,ssum=0,marks=0,spanMarks=0;
   for(const e of ar){
     if(resetV(e)){
       const key=renewId(e);let g=renewGroups.get(key);if(!g){g={key,es:[],incoming:new Map(),out:null,outTags:[],roots:0};renewGroups.set(key,g);}
       g.es.push(e);renewVisits++;e.renewIndex=rr.length;rr.push(e);
       if(!prev){ok(e===ar[0]&&e.histN===1,"prime reset injection singleton");g.roots++;renewRoots++;}
       else{const a=renewGroups.get(renewId(prev));if(a.out===null)a.out=key;ok(a.out===key,"deterministic reset successor");a.outTags.push(e.M);if(!g.incoming.has(a.key))g.incoming.set(a.key,[]);g.incoming.get(a.key).push(e.M);renewTransitions++;renewGain+=e.C-prev.C;
         const q=e.prev.p,w=e.t-e.prev.t,gap=e.prev.C-prev.C,dpre=2*e.prev.t-e.prev.C;
         if(q>=5){const V=Math.max(1,Math.floor(q/8));if(w<=V){renewShortEntries++;ok(dpre===q-1+6*(e.t%2)-2*w&&5*gap>=q-2*V-7,"short reset entry excursion");renewShortChecks++;}else renewLongEntries++;}
       }
       const back=rr[Math.max(0,rr.length-1-renewK)];e.renewBack=back;e.renewSpan=e.C-back.C;e.renewLog=Math.log(e.histN/back.histN);e.renewMark=e.renewLog>renewEps+1e-12;e.renewLong=e.renewSpan>=renewP;
       ok(e.renewLog>=-1e-12,"reset larger ancestry monotonic");gsum+=e.renewLog;ssum+=e.renewSpan;if(e.renewMark)marks++;if(e.renewLong)spanMarks++;
       latest=e;prev=e;renewWindowChecks++;
     }
     ok(latest,"initial reset exists");e.renewLatest=latest;
   }
   ok(gsum<=renewK*Math.log(rr.at(-1).histN)+1e-7&&ssum<=renewK*(ar.at(-1).C-ar[0].C),"reset index window budgets");
   ok(marks*renewEps<=gsum+1e-7&&spanMarks*renewP<=ssum,"marked reset budgets");
   renewGrowth+=gsum;renewSpanSum+=ssum;renewMarkCount+=marks;renewSpanMarks+=spanMarks;
 }
 ok(renewRoots===N&&renewGain<=G&&renewSpanSum<=renewK*G&&renewGrowth<=renewK*N*Math.log(N)+1e-6,"global reset conservation");
 for(const g of renewGroups.values()){
   g.es.sort((a,b)=>a.M-b.M);g.outTags.sort((a,b)=>a-b);
   const n=g.es.length,m=g.outTags.length;renewMaxMass=Math.max(renewMaxMass,n);renewMaxIn=Math.max(renewMaxIn,g.incoming.size);
   ok(m<=n&&g.outTags.every((M,i)=>M===g.es[n-m+i].M),"continuing reset cohort is exact source suffix");renewSuffixChecks++;
   const seen=new Set();let q=0,pairs=0;
   for(const [id,ms] of g.incoming){const a=renewGroups.get(id);ok(a.out===g.key&&a.outTags.length===ms.length&&ms.every(M=>a.outTags.includes(M)),"renewal transport edge exact");q+=ms.length;pairs+=choose2(ms.length);for(const M of ms){ok(!seen.has(M),"disjoint reset incoming sources");seen.add(M);}}
   ok(q+g.roots===n&&g.es.every(e=>seen.has(e.M)||!e.prev),"exact reset mass recurrence");if(g.roots)ok(n===1&&g.incoming.size===0,"no arrival at original prime reset");renewIndegreeChecks++;
   renewLoss+=n-m;renewLossPairs+=choose2(n)-choose2(m);renewBirthPairs+=choose2(n)-pairs;
 }
 ok(renewLoss===N&&renewBirthPairs===renewLossPairs,"global renewal pair telescope");
 // Exact ordered natural synchronous energy AFTER a first shared reset.
 // Each common complete renewal arc is counted by the number of
 // continuing source pairs. Each last shared reset has a smaller exiting
 // source and its actual terminal suffix.
 let renewArcEnergy=0,renewExitEnergy=0,renewArcGainPairs=0,renewExitGainPairs=0,renewArcChecks=0,renewExitChecks=0,renewSameEnergy=0,renewDifferentEnergy=0,renewAllSync=0,renewHitChecks=0,renewPairOracle=0,renewPairOracleGain=0,renewPairOracleCount=0;
 for(const g of renewGroups.values()){
   const n=g.es.length,m=g.outTags.length;
   if(m){
     const e=g.es[n-1],ar=roots.get(e.M),next=renewGroups.get(g.out).es.find(v=>v.M===e.M);
     ok(next&&next.C>e.C,"actual common renewal arc");
     let R0=0;for(let i=e.multiIndex;i<next.multiIndex;i++)R0+=ar[i].w;
     renewArcEnergy+=2*choose2(m)*R0;renewArcGainPairs+=choose2(m)*(next.C-e.C);renewArcChecks++;
   }
   for(let i=0;i<n-m;i++){
     const e=g.es[i],ar=roots.get(e.M),last=ar.at(-1);let R0=0;for(let j=e.multiIndex;j<ar.length;j++)R0+=ar[j].w;
     ok(R0===e.tail,"actual exit tail");renewExitEnergy+=2*(n-i-1)*R0;renewExitGainPairs+=(n-i-1)*(last.C-e.C);renewExitChecks++;
   }
 }
 // Independent natural high vertex-by-vertex partition, not retained ledger.
 for(const es of vertices.values()){
   const a=es.filter(e=>e.w);if(a.length<2)continue;
   const r=a[0].w;ok(a.every(e=>e.w===r),"common natural high label");
   const groups=new Map();for(const e of a){const k=renewId(e.renewLatest);groups.set(k,(groups.get(k)||0)+1);}
   const same=[...groups.values()].reduce((s,n)=>s+2*choose2(n)*r,0),all=2*choose2(a.length)*r;
   renewSameEnergy+=same;renewDifferentEnergy+=all-same;renewAllSync+=all;renewHitChecks++;
 }
 ok(renewArcEnergy+renewExitEnergy===renewSameEnergy&&renewSameEnergy+renewDifferentEnergy===renewAllSync,"exact reset transport of natural sync high energy");
 ok(renewSameEnergy<=3*(renewArcGainPairs+renewExitGainPairs),"reset gain-pair upper bound");
 // Small independent enumeration of all pairs that share a reset.
 if(X<=16384){
   const pairs=new Map();
   for(const g of renewGroups.values())for(let i=0;i<g.es.length;i++)for(let j=i+1;j<g.es.length;j++){
     const a=g.es[i],b=g.es[j],id=pairId(a.M,b.M),z=pairs.get(id)||{first:a,last:a,M:a.M,Mp:b.M};if(a.C<z.first.C)z.first=a;if(a.C>z.last.C)z.last=a;pairs.set(id,z);
   }
   for(const z of pairs.values()){const ar=roots.get(z.M),end=ar.at(-1);renewPairOracleCount++;renewPairOracleGain+=end.C-z.first.C;for(let i=z.first.multiIndex;i<ar.length;i++)renewPairOracle+=2*ar[i].w;}
   ok(renewPairOracleCount===renewBirthPairs&&renewPairOracleGain===renewArcGainPairs+renewExitGainPairs&&renewPairOracle===renewSameEnergy,"independent reset pair and suffix telescope");
 }
 // For every queried unpaid pair, use latest older reset at/before the
 // original crossing landing. Count nearby younger starts, not all pairs
 // in the same cohort. Freeze the unmasked original larger-source mass.
 const renewThinH=analytic?Math.floor(B*u**1.5/(2*renewA+3)):resetStress?16:4,renewThinM=analytic?Math.floor(mg/u**.25/(2*renewA+3)):resetStress?8:2;
 let renewPairs=0,renewNear=0,renewFar=0,renewStable=0,renewOld=0,renewStableChecks=0,renewMinOldMass=Infinity,renewMaxBackSpan=0,renewInherited=0,renewNearControls=0,renewHBefore=0,renewMBefore=0,renewHPaid=0,renewMPaid=0,renewAPaid=0,renewNPaid=0,renewHClass=[0,0,0],renewMClass=[0,0,0],renewHCounts=[0,0,0],renewMCounts=[0,0,0],renewByAge={},renewUse=new Map(),renewPairList=[];
 for(const z of birthPairs.values()){
   const f=z.gridUnpaidHigh||0,b=z.gridUnpaidMed||0,h=z.pcHigh*f,m=z.pcMed*b;
   if(h<=1e-9&&m<=1e-12)continue;renewHBefore+=h;renewMBefore+=m;renewPairs++;ok(z.star,"renewal uses original older crossing");
   const r=z.star.e.next.renewLatest,back=r.renewBack,C0=2*z.Mp-2,off=Math.abs(r.C-C0)/2;
   ok(r.M===z.M&&r.C<=z.star.e.next.C&&back.C<=r.C,"older latest reset");
   if(off>renewA){renewFar++;continue;}renewNear++;renewPairList.push(z);z.renewR=r;z.renewBack=back;
   const id=z.M+":"+renewId(r);if(!renewUse.has(id))renewUse.set(id,new Set());renewUse.get(id).add(z.Mp);
   // At a fixed younger root there are at most 2*(2A+1) reset
   // physical keys. Within each key n_M is exactly reverse source rank.
   let hc=r.renewMark?0:r.histN<=renewThinH?1:r.renewLong?2:-1,mc=r.renewMark?0:r.histN<=renewThinM?1:-1;
   if(h>1e-9&&hc>=0){renewHPaid+=h;renewAPaid+=z.pcAsync*f;renewHClass[hc]+=h;renewHCounts[hc]++;z.pcHigh*=1-f;z.pcAsync*=1-f;}
   if(m>1e-12&&mc>=0){renewMPaid+=m;renewNPaid+=z.pcNever*b;renewMClass[mc]+=m;renewMCounts[mc]++;z.pcMed*=1-b;z.pcNever*=1-b;z.pcLo*=1-b;z.pcHi*=1-b;}
   if(!r.renewMark){renewStable++;ok(back.histN+1e-9>=Math.exp(-renewEps)*r.histN,"stable inherited reset mass");renewStableChecks++;
     const g0=renewGroups.get(renewId(back)),g1=renewGroups.get(renewId(r)),inherited=g0.es.filter(e=>e.M>z.M);
     ok(inherited.length+1===back.histN&&inherited.every(e=>rawByRoot.get(e.M).get(r.C)?.t===r.t),"actual inherited larger reset members");
     const older=inherited.filter(e=>e.M<z.Mp);ok(older.length>=back.histN-1-renewA-1,"inherited strictly older sources");renewInherited+=older.length;
     if(h>1e-9&&hc<0||m>1e-12&&mc<0){ok(r.renewIndex>=renewK,"stable heavy reset has full earlier reset window");renewOld++;renewMinOldMass=Math.min(renewMinOldMass,back.histN);renewMaxBackSpan=Math.max(renewMaxBackSpan,r.renewSpan);}
   }
   const age=z.star.age,j=age<=1?0:Math.ceil(Math.log2(age)),rec=renewByAge[j]||{pairs:0,high:0,med:0};rec.pairs++;rec.high+=h;rec.med+=m;renewByAge[j]=rec;
 }
 ok(renewNear+renewFar===renewPairs&&[...renewUse.values()].every(ms=>ms.size<=2*renewA+1),"near reset pair multiplicity");
 // Independent controls: compare physical reset group count and future
 // path membership for a deterministic sample of original nonempty cohorts.
 let renewOracleChecks=0;
 for(const g of renewGroups.values()){if(renewOracleChecks>=128)break;if(g.es.length<2)continue;
   const v=g.es[0],actual=vertices.get(renewId(v));ok(actual&&actual.length===g.es.length&&actual.every(e=>g.es.includes(e)),"independent physical reset fibre");
   const a=g.es[0],b=g.es.at(-1),aa=roots.get(a.M).slice(a.multiIndex),bb=roots.get(b.M).slice(b.multiIndex);for(let i=0;i<aa.length;i++)ok(bb[i]&&aa[i].C===bb[i].C&&aa[i].t===bb[i].t,"actual ordered reset suffix");renewOracleChecks++;
 }
 const renewFinalHigh=jointBirthFlow("high",true,false,true),renewFinalMed=jointBirthFlow("med",true,false,true);delete renewFinalHigh.cutIds;delete renewFinalMed.cutIds;
 ok(near(renewHBefore,absFinalHigh.residual)&&near(renewMBefore,absFinalMed.residual)&&near(renewFinalHigh.total+renewHPaid,absFinalHigh.total)&&near(renewFinalMed.total+renewMPaid,absFinalMed.total)&&renewFinalHigh.residual<=renewHBefore-renewHPaid+1e-6&&renewFinalMed.residual<=renewMBefore-renewMPaid+1e-6,"reset transport unpaid conservation");
 // Truncated mass potential, evaluated on full original reset transport.
 // Each threshold has a budget N, not N times the number of reset visits.
 const thM=analytic?Math.max(2,Math.floor(renewThinH/8)):thresholdStress?3:2,thA=analytic?Math.ceil(u**2):Math.ceil(B/(thresholdStress?2:4));
 const thScales=[...new Set([1,2,4,8,16,32,64,thM])].sort((a,b)=>a-b),thStats=[];
 let thBirthStates=0,thBranchStates=0,thSmallTags=0,thBirthTags=0,thPotential=0,thLoss=0,thMassBound=0,thMarkedTags=0,thChecks=0,thThresholdOracle=0,thActivationOracle=0,thCorridorPairs=0,thCorridorChecks=0;
 for(const m of thScales){
   const f=n=>Math.max(0,n-m);let create=0,loss=0,births=0,branch=0,birthTags=0,smallTags=0,maxMass=0,branchMass=0,heavyIn=0;const first=new Map(),exit=new Map();
   for(const ar of roots.values()){const rr=ar.filter(resetV);const v=rr.find(e=>e.histN>m);if(v){first.set(renewId(v),(first.get(renewId(v))||0)+1);const end=rr.at(-1);exit.set(renewId(end),(exit.get(renewId(end))||0)+1);}thActivationOracle++;}
   for(const g of renewGroups.values()){
     const n=g.es.length,cont=g.outTags.length,parents=[...g.incoming.values()],delta=f(n)-parents.reduce((v,a)=>v+f(a.length),0),lost=f(n)-f(cont),thick=parents.filter(a=>a.length>=m);
     ok(delta>=0&&lost>=0,"nonnegative truncated reset potential");
     ok(delta===(first.get(g.key)||0)&&lost===(exit.get(g.key)||0),"threshold potential equals actual first rank attainment and terminal exit");thThresholdOracle++;
     if(!g.roots)ok(delta===parents.reduce((v,a)=>v+Math.min(m,a.length),0)-Math.min(m,n),"truncated parent identity");
     create+=delta;loss+=lost;maxMass=Math.max(maxMass,n);
     if(n>=2*m){
       const small=parents.filter(a=>a.length<m),smallMass=small.reduce((v,a)=>v+a.length,0);
       if(!thick.length){births++;birthTags+=n;ok(delta>=n/2,"all-small heavy reset birth");}
       if(thick.length>=2){branch++;branchMass+=n;ok(delta>=m*(thick.length-1),"thick reset branching debit");}
       if(thick.length)ok(delta>=smallMass,"small incoming tag debit");
       smallTags+=smallMass;heavyIn+=Math.max(0,thick.length-1);
       if(m===thM){g.thHeavy=thick.length;g.thSmall=new Set(small.flat());g.thMarked=thick.length!==1;for(const e of g.es)ok(g.thSmall.has(e.M)===small.some(a=>a.includes(e.M)),"small incoming tag membership");}
     }
     thChecks++;
   }
   ok(create===loss&&loss<=N&&m*(births+heavyIn)<=N&&birthTags<=2*N&&smallTags<=2*N,"global threshold birth and small inflow bounds");
   thStats.push({m,create,loss,births,branch,birthTags,smallTags,branchMass,maxMass,heavyIn});
   if(m===thM){thBirthStates=births;thBranchStates=branch;thBirthTags=birthTags;thSmallTags=smallTags;thPotential=create;thLoss=loss;thMassBound=maxMass;thMarkedTags=branchMass+birthTags;}
 }
 // Freeze first attainment of the current dyadic rank at physical vertices
 // AND at reset vertices, using full original larger-source companions.
 let thPhysicalActivations=0,thResetActivations=0,thRankChecks=0,thMaxRank=0;
 const rankLev=n=>Math.floor(Math.log2(n));
 for(const ar of roots.values()){
   let a=null,b=null,ja=-1,jb=-1;
   for(const e of ar){
     const j=rankLev(e.histN);if(j>ja){a=e;thPhysicalActivations++;ja=j;}
     e.thRank=a;ok(a.C<=e.C&&a.histN>=2**j&&(!a.prev||a.prev.histN<2**j),"first physical dyadic rank activation");
     if(resetV(e)){if(j>jb){b=e;jb=j;thResetActivations++;}e.thResetRank=b;ok(b.C<=e.C&&b.histN>=2**j,"first reset dyadic activation");}
     thRankChecks++;thMaxRank=Math.max(thMaxRank,j);
   }
 }
 ok(thPhysicalActivations<=N*(1+Math.floor(Math.log2(N)))&&thResetActivations<=thPhysicalActivations,"dyadic activation counts");
 const thRH=analytic?Math.ceil(B*u**1.25):Math.ceil(B/(thresholdStress?2:8)),thRM=analytic?Math.ceil(u**3):Math.max(2,Math.ceil(B/(thresholdStress?8:32)));
 let thHBefore=0,thMBefore=0,thHPaid=0,thMPaid=0,thAPaid=0,thNPaid=0,thHClass=[0,0,0],thMClass=[0,0],thHCounts=[0,0,0],thMCounts=[0,0],thPairs=0,thSurvHigh=0,thSurvMed=0,thStalePhysical=0,thStaleReset=0,thStripVisits=0,thHeavyStrip=0,thUniqueStrip=0,thSmallStrip=0,thBranchStrip=0,thOracle=0;
 const thPairUse=new Map(),thActUseH=new Map(),thActUseM=new Map(),thPaidSet=new Set(),thRemain=[];
 function use(map,id,M){if(!map.has(id))map.set(id,new Set());map.get(id).add(M);}
 for(const z of birthPairs.values()){
   const f=z.gridUnpaidHigh||0,b=z.gridUnpaidMed||0,h=z.pcHigh*f,m=z.pcMed*b;if(h<=1e-9&&m<=1e-12)continue;
   thPairs++;thHBefore+=h;thMBefore+=m;
   const st=z.star,v=st.e.next,C0=2*z.Mp-2,a=v.thRank,r=v.renewLatest,ra=r.thResetRank;
   ok(a&&ra&&v.C>=C0&&v.C-C0===2*st.i&&a.C<=v.C&&ra.C<=r.C,"rank activation at original landing");
   // At a given old source/rank activation all paid younger starts lie in
   // a short interval. Both old landing and reset activation variants.
   const freshH=v.C-a.C<=thRH;
   const freshM=st.i<=thRM&&v.C-a.C<=thRM;
   const freshR=Math.abs(r.C-C0)<=2*renewA&&r.C-ra.C<=thRM;
   if(freshH&&h>1e-9){ok(C0>=a.C-B&&C0<=a.C+thRH,"high fresh activation interval");use(thActUseH,z.M+":"+a.C,z.Mp);}
   if(freshM&&m>1e-12){ok(C0>=a.C-2*thRM&&C0<=a.C+thRM,"medium fresh landing interval");use(thActUseM,"P:"+z.M+":"+a.C,z.Mp);}
   if(freshR&&m>1e-12){ok(C0>=ra.C-2*renewA&&C0<=ra.C+thRM+2*renewA,"medium fresh reset interval");use(thActUseM,"R:"+z.M+":"+ra.C,z.Mp);}
   let hit=null,smallHit=null,visits=0;
   const ar=roots.get(z.M);
   for(let j=v.multiIndex;j>=0&&ar[j].C>=C0-2*thA;j--){
     const e=ar[j];if(e.C>C0+2*thA||!resetV(e))continue;
     visits++;thStripVisits++;const g=renewGroups.get(renewId(e));if(g.es.length<2*thM)continue;
     thHeavyStrip++;
     if(g.thMarked){hit=e;thBranchStrip++;}else{thUniqueStrip++;if(g.thSmall.has(z.M)){smallHit=e;thSmallStrip++;}}
   }
   if(h>1e-9&&hit){use(thPairUse,renewId(hit),z.Mp);ok(Math.abs(hit.C-C0)<=2*thA,"branch strip distance");}
   let hc=freshH?0:hit?1:smallHit?2:-1,mc=freshM?0:freshR?1:-1;
   if(h>1e-9&&hc>=0){thHPaid+=h;thAPaid+=z.pcAsync*f;thHClass[hc]+=h;thHCounts[hc]++;z.pcHigh*=1-f;z.pcAsync*=1-f;}
   if(m>1e-12&&mc>=0){thMPaid+=m;thNPaid+=z.pcNever*b;thMClass[mc]+=m;thMCounts[mc]++;z.pcMed*=1-b;z.pcNever*=1-b;z.pcLo*=1-b;z.pcHi*=1-b;}
   if(h>1e-9&&hc<0){thSurvHigh++;ok(!hit&&!smallHit&&v.C-a.C>thRH,"surviving high stale physical rank and unique local thick parent");
     thStalePhysical+=2**rankLev(v.histN);
     // Every companion of the first rank activation persists to landing.
     const es=vertices.get(renewId(a)),larger=es.filter(e=>e.M>z.M);ok(larger.length+1===a.histN&&larger.every(e=>rawByRoot.get(e.M).get(v.C)?.t===v.t),"inherited physical activation companions");
     thOracle++;
     if(a.C<=C0-2*thA&&2**rankLev(v.histN)>=2*thM){thCorridorPairs++;for(let j=v.multiIndex;j>=0&&ar[j].C>=C0-2*thA;j--){const e=ar[j];if(e.C>C0+2*thA||!resetV(e))continue;const g=renewGroups.get(renewId(e));ok(e.histN>=2*thM&&g.thHeavy===1&&!g.thSmall.has(z.M),"unique inherited thick reset corridor");thCorridorChecks++;}}
   }
   if(m>1e-12&&mc<0){thSurvMed++;if(st.i<=thRM)ok(v.C-a.C>thRM,"surviving medium shallow landing stale");if(Math.abs(r.C-C0)<=2*renewA){ok(r.C-ra.C>thRM,"surviving medium near reset stale");thStaleReset+=2**rankLev(r.histN);}}
 }
 ok([...thPairUse.values()].every(ms=>ms.size<=2*thA+1)&&[...thActUseH.values()].every(ms=>ms.size<=Math.ceil((thRH+B)/2)+1)&&[...thActUseM.values()].every(ms=>ms.size<=2*thRM+2*renewA+2),"activation and branch younger root multiplicity");
 const thFinalHigh=jointBirthFlow("high",true,false,true),thFinalMed=jointBirthFlow("med",true,false,true);delete thFinalHigh.cutIds;delete thFinalMed.cutIds;
 ok(near(thHBefore,renewFinalHigh.residual)&&near(thMBefore,renewFinalMed.residual)&&near(thFinalHigh.total+thHPaid,renewFinalHigh.total)&&near(thFinalMed.total+thMPaid,renewFinalMed.total)&&thFinalHigh.residual<=thHBefore-thHPaid+1e-6&&thFinalMed.residual<=thMBefore-thMPaid+1e-6,"threshold unpaid accounting");
 // Physical DAG, all actual completed edges, not only resets.
 const cvM=analytic?Math.max(2,Math.floor(B*u**1.125)):coverStress?4:3,cvBM=analytic?thM:coverStress?3:2,cvS=analytic?Math.max(1,Math.floor(u**.25)):coverStress?16:8,cvD=6+12*cvS,cvA=analytic?Math.ceil(u**2):coverStress?Math.ceil(B/2):Math.ceil(B/4),cvQ=analytic?Math.max(3,Math.ceil(B/u)):Math.max(3,Math.ceil(B/(coverStress?8:4)));
 const cvSort=[...vertices.entries()].sort((a,b)=>a[1][0].C-b[1][0].C||a[1][0].t-b[1][0].t),cvPhys=new Map();
 for(const [id,es] of cvSort)cvPhys.set(id,{es:es.slice().sort((a,b)=>a.M-b.M),ins:new Map(),out:[],dest:null});
 for(const [id,g] of cvPhys)for(const e of g.es)if(e.next){const k=renewId(e.next);if(g.dest===null)g.dest=k;ok(g.dest===k,"unique physical successor");g.out.push(e.M);const dest=cvPhys.get(k);if(!dest.ins.has(id))dest.ins.set(id,[]);dest.ins.get(id).push(e.M);}
 let cvChecks=0,cvDelta=0,cvLoss=0,cvAllSmall=0,cvBranch=0,cvSmall=0,cvBirthTags=0,cvExcess=0,cvExit=0;
 const cvF=n=>Math.max(0,n-cvBM);
 for(const [id,g] of cvPhys){
   const n=g.es.length,k=g.out.length,parents=[...g.ins.values()];
   ok(g.out.every((M,i)=>M===g.es[n-k+i].M)&&g.es.filter(e=>!e.prev).length+parents.reduce((a,b)=>a+b.length,0)===n,"physical suffix recurrence");
   const de=cvF(n)-parents.reduce((a,b)=>a+cvF(b.length),0),lo=cvF(n)-cvF(k);
   ok(de===g.es.filter(e=>e.histN>cvBM&&(!e.prev||e.prev.histN<=cvBM)).length&&lo===g.es.slice(0,n-k).filter(e=>e.histN>cvBM).length,"physical threshold first-attainment");
   ok(de>=0&&lo>=0,"physical threshold nonnegative");cvDelta+=de;cvLoss+=lo;cvExit+=n-k;cvChecks++;
   if(n>=2*cvBM){const thick=parents.filter(a=>a.length>=cvBM),small=parents.filter(a=>a.length<cvBM);g.mark=thick.length!==1;g.small=new Set(small.flat());g.thick=thick.length;
     if(!thick.length){cvAllSmall++;cvBirthTags+=n;ok(de>=n/2,"physical all-small birth");}
     if(thick.length>=2){cvBranch++;cvExcess+=thick.length-1;}
     cvSmall+=g.small.size;
   }
 }
 ok(cvExit===N&&cvDelta===cvLoss&&cvDelta<=N&&cvBM*(cvAllSmall+cvExcess)<=N&&cvSmall<=2*N&&cvBirthTags<=2*N,"physical branching budget");
 // Greedy largest-source representatives; disjoint seed populations.
 const cvCovered=new Set(),cvSeedTags=new Set(),cvReps=new Set(),cvLargeKeys=new Set();
 let cvHeavy=0,cvSeeds=0,cvRepGain=0,cvRepLarge=0,cvHeavyHigh=0,cvHeavyLarge=0;
 for(const [id,es] of cvSort){if(es.length<cvM)continue;cvHeavy++;if(cvCovered.has(id))continue;
   const e=es.reduce((a,b)=>a.M>b.M?a:b);ok(!cvReps.has(e.M),"fresh representative");
   for(const v of es){ok(!cvSeedTags.has(v.M),"disjoint seed populations");cvSeedTags.add(v.M);}
   cvReps.add(e.M);cvSeeds++;const ar=roots.get(e.M);for(let i=e.multiIndex;i<ar.length;i++)cvCovered.add(renewId(ar[i]));
 }
 for(const [id,es] of cvSort)if(es.length>=cvM){ok(cvCovered.has(id),"heavy physical cover");const e=es.find(e=>e.next);if(e?.w)cvHeavyHigh++;if(e&&e.p>=cvQ){cvHeavyLarge++;cvLargeKeys.add(id);}}
 for(const M of cvReps){const ar=roots.get(M);cvRepGain+=ar.at(-1).C-ar[0].C;for(const e of ar)if(e.next&&e.p>=cvQ)cvRepLarge++;}
 ok(cvSeeds*cvM<=cvSeedTags.size&&cvSeedTags.size<=N&&cvRepGain<=cvSeeds*H&&cvHeavyLarge<=cvRepLarge+cvSeeds&&cvRepLarge*(cvQ-1)<=cvRepGain,"heavy representative gain budget");
 // Every heavy completed large edge is actually traversed by some selected representative.
 const cvOracleKeys=new Set();for(const M of cvReps)for(const e of roots.get(M))if(e.next&&e.p>=cvQ)cvOracleKeys.add(renewId(e));
 const cvRepTerminals=new Set([...cvReps].map(M=>renewId(roots.get(M).at(-1))));let cvExtraLarge=0;for(const k of cvLargeKeys)if(!cvOracleKeys.has(k)){ok(cvRepTerminals.has(k),"untraversed covered edge at representative terminal");cvExtraLarge++;}ok(cvExtraLarge<=cvSeeds,"terminal exception budget");
 const cvControl=[];
 for(const k of [2,8]){
   const seen=new Set(),seed=new Set(),rr=[],edgeKeys=new Set(),termKeys=new Set();
   for(const [id,es] of cvSort)if(es.length>=k&&!seen.has(id)){
     const e=es.at(-1); // Original simulator inserts roots in increasing order.
     ok(es.every(v=>v.M<=e.M),"largest representative control");
     for(const v of es){ok(!seed.has(v.M),"independent disjoint cover seeds");seed.add(v.M);}
     rr.push(e.M);const ar=roots.get(e.M);for(let i=e.multiIndex;i<ar.length;i++){const v=ar[i];seen.add(renewId(v));if(v.next)edgeKeys.add(renewId(v));else termKeys.add(renewId(v));}
   }
   let n=0,extras=0,large=0;
   for(const [id,es] of cvSort)if(es.length>=k){ok(seen.has(id),"independent heavy cover control");n++;const e=es.find(v=>v.next);if(e&&e.p>=cvQ){large++;if(!edgeKeys.has(id)){ok(termKeys.has(id),"independent terminal exception");extras++;}}}
   ok(rr.length*k<=seed.size&&seed.size<=N&&extras<=rr.length,"independent cover budget");
   cvControl.push({k,seeds:rr.length,seedMass:seed.size,heavy:n,large,extras});
 }
 const cvRareRoots=new Set(),cvPrimes=[...roots.keys()];let cvRareInc=0;
 function cvLB(a,x){let l=0,r=a.length;while(l<r){const k=(l+r)>>1;if(a[k]<x)l=k+1;else r=k;}return l;}
 for(const id of cvLargeKeys){const e=cvPhys.get(id).es[0],c=(e.C+2)/2;for(let k=cvLB(cvPrimes,c-cvS);k<cvPrimes.length&&cvPrimes[k]<=c+cvS;k++){cvRareRoots.add(cvPrimes[k]);cvRareInc++;}}
 ok(cvRareRoots.size<=cvRareInc&&cvRareInc<=(2*cvS+1)*cvHeavyLarge,"rare nearby heavy large support");
 // Enumerate all low-deficit arithmetic landing slots for younger roots.
 let cvSlots=0,cvSlotReset=0,cvSlotNonreset=0,cvSlotOracle=0,cvSlotMax=0;const cvSlotSets=new Map();
 for(const M of roots.keys()){
   const keys=new Set();for(let i=0;i<=cvS;i++){const D=2*M-2+2*i;for(const p of new Set(fs(M+i-1).concat(fs(M+i)))){if(p>B||2*i>p-2)continue;
     for(const side of [0,1]){if((D+2*side)%p)continue;for(let d=mod(6*side,2*p);d<=cvD;d+=2*p){const tick=(D+d)/2;if(tick%2===side)keys.add(D+":"+tick);}}
   }}
   if(cvSlotOracle<128){const oracle=new Set();for(let i=0;i<=cvS;i++){const D=2*M-2+2*i;for(let d=0;d<=cvD;d+=2){const tick=(D+d)/2,side=tick%2;if(fs(D/2+side).some(p=>p<=B&&2*i<=p-2&&mod(d-6*side,2*p)===0))oracle.add(D+":"+tick);}}
     ok(oracle.size===keys.size&&[...oracle].every(k=>keys.has(k)),"independent physical slot oracle");cvSlotOracle++;}
   cvSlots+=keys.size;cvSlotMax=Math.max(cvSlotMax,keys.size);for(const key of keys){const [C,t]=key.split(":").map(Number);if(2*t-C===6*(t%2))cvSlotReset++;else cvSlotNonreset++;}
   if(starQuery.has(M))cvSlotSets.set(M,keys);
 }
 // Consecutive nonreset low-deficit targets, including their predecessor.
 const cvZ=analytic?Math.max(3,Math.floor(Math.log(u)/4)):coverStress?7:5;let cvL=2;for(let p=3;p<=cvZ;p+=2)if(spf[p]===p)cvL*=p;
 let cvRuns=0,cvSteps=0,cvMaxGain=0,cvRoot=0,cvReset=0,cvDown=0;
 for(const ar of roots.values()){let front=null,active=false;
   for(const e of ar){const d=2*e.t-e.C;
     if(e.prev&&!resetV(e)&&d<=2*cvZ){if(!active){front=e.prev;active=true;cvRuns++;if(!front.prev)cvRoot++;else if(resetV(front))cvReset++;else{ok(2*front.t-front.C>2*cvZ&&2*front.t-front.C<=3*cvZ,"low deficit frontier");cvDown++;}}
       ok(e.prev.p<=cvZ&&e.C-front.C<cvL,"nonreset low-deficit primorial barrier");cvSteps++;cvMaxGain=Math.max(cvMaxGain,e.C-front.C);
     }else active=false;
   }
 }
 let cvPairs=0,cvShallow=0,cvSurv=0,cvShallowSurv=0,cvHBefore=0,cvMBefore=0,cvHPaid=0,cvMPaid=0,cvAPaid=0,cvNPaid=0,cvHClass=[0,0,0],cvHCounts=[0,0,0],cvMedThin=0,cvMC=analytic?Math.floor(mg/u**.25/(cvS*ell)):coverStress?5:3,cvHC=analytic?2*cvM:coverStress?8:4,cvStripChecks=0,cvUniqueChecks=0,cvRareShallow=0;
 for(const z of birthPairs.values()){
   const f=z.gridUnpaidHigh||0,b=z.gridUnpaidMed||0,h=z.pcHigh*f,m=z.pcMed*b;if(h<=1e-9&&m<=1e-12)continue;
   cvPairs++;cvHBefore+=h;cvMBefore+=m;const v=z.star.e.next,C0=2*z.Mp-2,ar=roots.get(z.M);
   const shallow=z.star.i<=cvS&&2*v.t-v.C<=cvD;
   if(shallow){cvShallow++;ok(cvSlotSets.get(z.Mp)?.has(renewId(v)),"actual shallow landing support");if(cvRareRoots.has(z.Mp))cvRareShallow++;}
   let branch=false,small=false;
   for(let j=v.multiIndex;j>=0&&ar[j].C>=C0-2*cvA;j--){const e=ar[j];if(e.C>C0+2*cvA)continue;const g=cvPhys.get(renewId(e));cvStripChecks++;if(g.es.length>=2*cvBM){if(g.mark)branch=true;else if(g.small.has(z.M))small=true;}}
   const hc=shallow&&v.histN<=cvHC?0:branch?1:small?2:-1;
   if(h>1e-9&&hc>=0){cvHPaid+=h;cvAPaid+=z.pcAsync*f;cvHClass[hc]+=h;cvHCounts[hc]++;z.pcHigh*=1-f;z.pcAsync*=1-f;}
   else if(h>1e-9){cvSurv++;if(shallow){cvShallowSurv++;ok(v.histN>cvHC,"shallow surviving rank");}
     if(v.thRank.C<=C0-2*cvA&&2**rankLev(v.histN)>=2*cvBM)for(let j=v.multiIndex;j>=0&&ar[j].C>=C0-2*cvA;j--){const e=ar[j];if(e.C>C0+2*cvA)continue;const g=cvPhys.get(renewId(e));ok(g.es.length>=2*cvBM&&g.thick===1&&!g.small.has(z.M),"unique thick physical strip");cvUniqueChecks++;}
   }
   if(m>1e-12&&shallow&&v.histN<=cvMC){cvMedThin++;cvMPaid+=m;cvNPaid+=z.pcNever*b;z.pcMed*=1-b;z.pcNever*=1-b;z.pcLo*=1-b;z.pcHi*=1-b;}
 }
 const cvFinalHigh=jointBirthFlow("high",true,false,true),cvFinalMed=jointBirthFlow("med",true,false,true);delete cvFinalHigh.cutIds;delete cvFinalMed.cutIds;
 ok(near(cvHBefore,thFinalHigh.residual)&&near(cvMBefore,thFinalMed.residual)&&near(cvFinalHigh.total+cvHPaid,thFinalHigh.total)&&near(cvFinalMed.total+cvMPaid,thFinalMed.total)&&cvFinalHigh.residual<=cvHBefore-cvHPaid+1e-6&&cvFinalMed.residual<=cvMBefore-cvMPaid+1e-6,"physical cover unpaid conservation");
 // Strong representative cover: dominate the Kth largest source at
 // EVERY thick start. Thus cover entire segments, not just vertices.
 const exK=analytic?cvM:excursionStress?4:3,exD0=Math.max(8,Math.ceil(analytic?B/u**.5:B/(excursionStress?32:16))),exLevels=[];
 for(let D=exD0;D<=5*H+6;D*=2)exLevels.push(D);
 const exStarts=new Map(),exGroups=new Map();let exMaxDef=0;
 const exDef=e=>2*e.t-e.C;
 for(const ar of roots.values()){
   let records=[];for(const e of ar)exMaxDef=Math.max(exMaxDef,exDef(e));
   for(let j=0;j<exLevels.length;j++){
     const D=exLevels[j],out=[];let side=0,last=ar[0],up=0,down=0,gain=0,prevEnd=-1;
     for(const e of ar){const d=exDef(e);
       if(d<=D){if(side===1){add(last,e,"down");}side=0;last=e;}
       else if(d>=2*D){if(side===0){add(last,e,"up");}side=1;last=e;}
     }
     function add(a,b,kind){ok(a.multiIndex<b.multiIndex&&a.multiIndex>=prevEnd,"disjoint hysteresis intervals");prevEnd=b.multiIndex;
       const g=b.C-a.C,dd=exDef(b)-exDef(a);ok(kind==="up"?dd>=D&&5*g>=D:dd<=-D&&g>=D,"excursion amplitude gain");
       if(kind==="up")up++;else down++;gain+=g;
       const id=j+":"+kind+":"+renewId(a)+":"+renewId(b);
       let rec=exGroups.get(id);if(!rec){rec={id,j,D,kind,a,b,ms:new Set(),g};exGroups.set(id,rec);}
       ok(!rec.ms.has(a.M),"unique source excursion");rec.ms.add(a.M);
       const z={id,j,a,b,kind};out.push(z);records.push(z);
     }
     ok(up*D<=5*(ar.at(-1).C-ar[0].C)&&down*D<=ar.at(-1).C-ar[0].C&&gain<=ar.at(-1).C-ar[0].C,"per-source excursion budget");
   }
   exStarts.set(ar[0].M,records);
 }
 // One simultaneous segment cover for ALL levels and both directions.
 function exCover(K){
   const owner=new Map(),seeds=new Set(),reps=new Set();let count=0,gain=0,checks=0;
   for(const [id,es] of cvSort)if(es.length>=K){const kth=es[es.length-K],max=es.at(-1);ok(max.M>=kth.M&&es.every((v,i)=>!i||es[i-1].M<v.M),"original fibre source order");
     if((owner.get(id)||0)<kth.M){
       ok(!reps.has(max.M),"new segment representative");
       for(const e of es.slice(-K)){ok(!seeds.has(e.M),"disjoint segment cover seeds");seeds.add(e.M);}
       reps.add(max.M);count++;const ar=roots.get(max.M);gain+=ar.at(-1).C-max.C;
       for(let i=max.multiIndex;i<ar.length;i++){const k=renewId(ar[i]);owner.set(k,Math.max(owner.get(k)||0,max.M));}
     }
     ok(owner.get(id)>=kth.M,"representative dominates Kth source");checks++;
   }
   ok(count*K===seeds.size&&seeds.size<=N&&gain<=count*H,"segment representative budget");
   let heavy=0,heavyUp=0,heavyDown=0,oracle=0,by=exLevels.map(D=>({D,up:0,down:0,heavyUp:0,heavyDown:0,tagUp:0,tagDown:0,repUp:0,repDown:0,gain:0}));
   for(const M of reps)for(const z of exStarts.get(M))by[z.j][z.kind==="up"?"repUp":"repDown"]++;
   for(const rec of exGroups.values()){
     const row=by[rec.j],n=rec.ms.size;row[rec.kind]++;row[rec.kind==="up"?"tagUp":"tagDown"]+=n;row.gain+=rec.g*n;
     if(n<K)continue;heavy++;if(rec.kind==="up"){heavyUp++;row.heavyUp++;}else{heavyDown++;row.heavyDown++;}
     const M=owner.get(renewId(rec.a));ok(M&&rec.ms.has(M),"representative shares complete canonical excursion");
     ok(rawByRoot.get(M).get(rec.b.C)?.t===rec.b.t,"independent complete segment endpoint");oracle++;
   }
   for(const row of by){ok(row.heavyUp<=row.repUp&&row.heavyDown<=row.repDown&&row.repUp*row.D<=5*count*H&&row.repDown*row.D<=count*H&&row.tagUp*row.D<=5*G&&row.tagDown*row.D<=G&&row.gain<=G,"level cover and weighted excursion count");}
   return {K,count,seedMass:seeds.size,gain,checks,heavy,heavyUp,heavyDown,oracle,by};
 }
 const exControl=[...new Set([2,8,exK])].map(exCover),exChosen=exControl.find(a=>a.K===exK);
 const exW=exLevels.map((D,j)=>analytic?Math.floor(D/B*u**1.5/(j+1)**2):Math.max(1,Math.floor(B/(excursionStress?8:32)/(j+1)))),exRareW=exLevels.map((D,j)=>analytic?Math.floor(D/B*u/(j+1)**2):Math.max(1,Math.floor(B/(excursionStress?16:64)/(j+1))));
 const exRare=new Set();let exRareInc=0,exRareBound=0,exEndpointCount=0;
 for(const rec of exGroups.values())if(rec.ms.size>=exK){const W=exRareW[rec.j],c=(rec.b.C+2)/2;exEndpointCount++;exRareBound+=2*W+1;
   for(let k=cvLB(cvPrimes,c-W);k<cvPrimes.length&&cvPrimes[k]<=c+W;k++){exRare.add(cvPrimes[k]);exRareInc++;}
 }
 ok(exRare.size<=exRareInc&&exRareInc<=exRareBound,"heavy excursion nearby root support");
 // Exact pair-weighted physical drift: signed flux between births and exits.
 const exFlux=[Infinity,...exLevels].map(D=>({D:Number.isFinite(D)?D:"full",birth:0,exit:0,up:0,down:0,rankBirth:0,rankExit:0,rankUp:0,rankDown:0}));
 for(const [id,g] of cvPhys){
   const n=g.es.length,b=g.out.length,inc=[...g.ins.values()],v=g.es[0],d=exDef(v),bn=choose2(n)-inc.reduce((s,a)=>s+choose2(a.length),0),ln=choose2(n)-choose2(b),br=cvF(n)-inc.reduce((s,a)=>s+cvF(a.length),0),lr=cvF(n)-cvF(b);
   const dest=b?cvPhys.get(g.dest).es[0]:null;
   for(const row of exFlux){const cap=row.D==="full"?Infinity:row.D,x=Math.min(cap,d),dd=dest?Math.min(cap,exDef(dest))-x:0;
     row.birth+=bn*x;row.exit+=ln*x;row.up+=choose2(b)*Math.max(0,dd);row.down+=choose2(b)*Math.max(0,-dd);
     row.rankBirth+=br*x;row.rankExit+=lr*x;row.rankUp+=cvF(b)*Math.max(0,dd);row.rankDown+=cvF(b)*Math.max(0,-dd);
   }
 }
 for(const row of exFlux)ok(row.birth+row.up===row.exit+row.down&&row.rankBirth+row.rankUp===row.rankExit+row.rankDown,"weighted clipped deficit flux identity");
 // Tail-weighted deficit flux for full natural synchronous high energy.
 // At each physical tag its descending rank minus one counts actual larger
 // partners; its rank increment counts first physical meetings at this tag.
 const exTail=[{D:"full",phi:d=>d},{D:"excess",phi:d=>Math.max(0,d-exD0)},...exLevels.map(D=>({D,phi:d=>Math.min(D,Math.max(0,d-D))}))].map(x=>({...x,birth:0,up:0,down:0,moment:0,largeEnergy:0,birthPairs:0}));
 let exTailSync=0,exTailBirthPairs=0,exTailOracle=0,exTailPairsOracle=0,exTailChecks=0;
 for(const ar of roots.values())for(const e of ar){
   const d=exDef(e),n=e.histN-1,birth=n-(e.prev?e.prev.histN-1:0);ok(birth>=0,"physical pair births per source");exTailBirthPairs+=birth;exTailSync+=2*n*e.w;
   let sum=0,du=0,dd=0;
   for(const row of exTail){const x=row.phi(d),y=e.next?row.phi(exDef(e.next)):x,delta=y-x;
     row.birth+=2*birth*x*e.tail;row.moment+=2*n*x*e.w;row.up+=2*n*Math.max(0,delta)*(e.next?e.next.tail:0);row.down+=2*n*Math.max(0,-delta)*(e.next?e.next.tail:0);
     if(typeof row.D==="number"){if(d>=2*row.D)row.largeEnergy+=2*n*e.w;sum+=x;du+=Math.max(0,delta);dd+=Math.max(0,-delta);}
   }
   const x=Math.max(0,d-exD0),y=e.next?Math.max(0,exDef(e.next)-exD0):x;
   ok(sum===x&&du===Math.max(0,y-x)&&dd===Math.max(0,x-y),"dyadic deficit band partition without overlap");exTailChecks++;
 }
 for(const row of exTail){ok(row.birth+row.up===row.moment+row.down,"tail-weighted deficit transport");if(typeof row.D==="number")ok(row.D*row.largeEnergy<=row.moment&&row.D*row.largeEnergy<=row.birth+row.up,"large deficit high energy upper bound");}
 ok(exTailSync===renewAllSync&&exTailBirthPairs===exFlux[0].birth*0+[...cvPhys.values()].reduce((v,g)=>v+choose2(g.es.length)-[...g.ins.values()].reduce((s,a)=>s+choose2(a.length),0),0),"physical birth and natural sync totals");
 for(const k of ["birth","up","down","moment"])ok(exTail.slice(2).reduce((v,x)=>v+x[k],0)===exTail[1][k],"dyadic tail flux exact additive partition");
 // Independently enumerate actual shared suffixes for small ensembles.
 if(X<=16384){
   const pairs=new Map();for(const [id,g] of cvPhys)if(g.es.length>1)for(let i=0;i<g.es.length;i++)for(let j=i+1;j<g.es.length;j++){const a=g.es[i],b=g.es[j],k=pairId(a.M,b.M);if(!pairs.has(k))pairs.set(k,a);}
   const rr=exTail.map(row=>({birth:0,up:0,down:0,moment:0,largeEnergy:0}));let energy=0;
   for(const a of pairs.values()){const ar=roots.get(a.M);exTailPairsOracle++;
     for(let i=a.multiIndex;i<ar.length;i++){const e=ar[i];energy+=2*e.w;for(let k=0;k<rr.length;k++){const f=exTail[k].phi,x=f(exDef(e)),d=e.next?f(exDef(e.next))-x:0;
       rr[k].moment+=2*x*e.w;rr[k].up+=2*Math.max(0,d)*(e.next?e.next.tail:0);rr[k].down+=2*Math.max(0,-d)*(e.next?e.next.tail:0);if(i===a.multiIndex)rr[k].birth+=2*x*e.tail;
       if(typeof exTail[k].D==="number"&&exDef(e)>=2*exTail[k].D)rr[k].largeEnergy+=2*e.w;
     }}
   }
   ok(energy===exTailSync&&pairs.size===exTailBirthPairs,"independent full synchronous pair enumeration");
   for(let k=0;k<rr.length;k++)for(const f of ["birth","up","down","moment","largeEnergy"]){ok(rr[k][f]===exTail[k][f],"independent tail flux pair oracle");exTailOracle++;}
 }
 for(const row of exTail){delete row.phi;delete row.birthPairs;}
 // Whole high pair mask using actual old hysteresis endpoints near the
 // younger initial horizon, ONLY the still-unpaid fraction.
 let exPairs=0,exBeforeH=0,exBeforeM=0,exPaidH=0,exPaidAsync=0,exPaidPairs=0,exSurv=0,exRarePairCount=0,exRareWeight=0,exOldUse=new Map(),exPaidBy=exLevels.map(D=>({D,up:0,down:0,w:0}));
 for(const z of birthPairs.values()){
   const f=z.gridUnpaidHigh||0,b=z.gridUnpaidMed||0,h=z.pcHigh*f,m=z.pcMed*b;if(h<=1e-9&&m<=1e-12)continue;
   exPairs++;exBeforeH+=h;exBeforeM+=m;
   const C0=2*z.Mp-2,v=z.star.e.next;
   if(exRare.has(z.Mp)){exRarePairCount++;exRareWeight+=h;}
   let witness=null;for(const e of exStarts.get(z.M))if(e.b.C<=v.C&&Math.abs(e.b.C-C0)<=2*exW[e.j]){witness=e;break;}
   if(h>1e-9&&witness){
     const key=z.M+":"+witness.id;if(!exOldUse.has(key))exOldUse.set(key,{j:witness.j,ms:new Set()});exOldUse.get(key).ms.add(z.Mp);
     exPaidH+=h;exPaidAsync+=z.pcAsync*f;exPaidPairs++;const row=exPaidBy[witness.j];row[witness.kind]++;row.w+=h;z.pcHigh*=1-f;z.pcAsync*=1-f;
   }else if(h>1e-9)exSurv++;
 }
 ok([...exOldUse.values()].every(z=>z.ms.size<=2*exW[z.j]+1),"excursion endpoint pair multiplicity");
 const exFinalHigh=jointBirthFlow("high",true,false,true),exFinalMed=jointBirthFlow("med",true,false,true);delete exFinalHigh.cutIds;delete exFinalMed.cutIds;
 ok(near(exBeforeH,cvFinalHigh.residual)&&near(exBeforeM,cvFinalMed.residual)&&near(exFinalHigh.total+exPaidH,cvFinalHigh.total)&&exFinalHigh.residual<=exBeforeH-exPaidH+1e-6&&near(exFinalMed.residual,cvFinalMed.residual),"excursion unpaid conservation");
 // Freeze the actual isolated high ledger at the CURRENT feasible flow,
 // preserving the original retained ordered hit weights and their holes.
 const reEps=analytic?Math.min(.125,u**(-.25)/8):residenceStress?.125:.0625;
 const reLevels=exLevels,reCaps=reLevels.map((D,j)=>analytic?Math.floor(B*u**1.5*D/H/(j+1)**2):residenceStress?8:3);
 const reRows=reLevels.map((D,j)=>({D,cap:reCaps[j],energy:0,birth:0,thin:0,short:0,maskedHigh:0,smallLabel:0,long:0,donors:0,birthRuns:0,thinRuns:0,shortRuns:0,layerChecks:0,upperBirth:0,upperUp:0,upperDown:0,moment:0}));
 let reAdaptiveBirth=0,reAdaptiveDonor=0,reBirthBudget=0,reAdaptiveBudget=0,reBirthMaxCap=0,reDonorMaxCap=0,reBirthPaidRuns=0,reDonorPaidRuns=0,reBirthUse=new Map(),reDonorUse=new Map(),reExactOrigins=0,reLabelStats=new Map(),reSweepChecks=0,reSweepGroups=0,reBirthSweepBudget=0,reDonorSweepBudget=0,reSweepPaid=0,reRemainingFixedPairs=0;
 let reBefore=0,reSync=0,reAsync=0,reLow=0,reBand=0,reThin=0,reShort=0,reBirth=0,reMasked=0,reSmall=0,reLong=0,rePairs=0,reHits=0,reIntervals=0,reOracle=0,reThinPairs=0,reDonorBound=0,reShortBound=0,reRelativeBase=0,reFullPositive=0,reRareDonors=0;
 const reUse=new Map(),rePairPayments=new Map(),reShortUse=new Map();
 function reRank(a,Mp){const es=cvPhys.get(renewId(a)).es;let n=0;for(const e of es)if(e.M>a.M&&e.M<=Mp)n++;return n;}
 for(const z of birthPairs.values()){
   const f=z.gridUnpaidHigh||0,h=z.pcHigh*f;if(h<=1e-9)continue;
   rePairs++;reBefore+=h;const alpha=h/z.orig.high,as=z.pcAsync*f,rs=h-as;reAsync+=as;reSync+=rs;
   ok(near(as,alpha*z.orig.async)&&near(rs,alpha*z.orig.sync),"frozen actual ordered pair fractions");
   const hits=z.resHits||new Map();ok([...hits.values()].reduce((a,b)=>a+b,0)===z.orig.sync,"exact retained synchronous hit ledger");reHits+=hits.size;
   if(!hits.size){ok(near(rs,0),"no sync hit");continue;}
   const ar=roots.get(z.M),br=rawByRoot.get(z.Mp);let start=ar.findIndex(e=>br.get(e.C)?.t===e.t);ok(start>=0,"actual physical birth");
   const a=ar.slice(start),raw=a.map(e=>hits.get(e.C)||0),thinByHit=new Float64Array(a.length),d=a.map(exDef),band=a.map((e,i)=>d[i]<2*reLevels[0]?-1:Math.floor(Math.log2(d[i]/(2*reLevels[0]))));
   for(let i=0;i<a.length;i++){const r=raw[i];ok(!r||r<=2*a[i].w,"actual retained hit bound");if(!r)continue;ok(br.get(a[i].C)?.t===a[i].t,"actual retained shared hit");if(band[i]<0)reLow+=alpha*r;else{ok(band[i]<reRows.length,"deficit hit band");reRows[band[i]].energy+=alpha*r;reBand+=alpha*r;}}
   let thin=0,short=0,all=0,birth=0,mask=0,small=0,long=0,birthThin=0,donorThin=0;
   // Independent actual tail-weighted identity with retained holes:
   // weights are raw ordered retained hits, times one pair scalar alpha.
   const tails=new Float64Array(a.length+1);for(let i=a.length-1;i>=0;i--)tails[i]=tails[i+1]+raw[i];
   for(let j=0;j<reLevels.length;j++){
     const D=reLevels[j],row=reRows[j],phi=x=>Math.min(D,Math.max(0,x-D));
     let Bf=phi(d[0])*tails[0],Uf=0,Df=0,Zf=0;
     for(let i=0;i<a.length;i++){Zf+=phi(d[i])*raw[i];if(i+1<a.length){const delta=phi(d[i+1])-phi(d[i]);Uf+=Math.max(0,delta)*tails[i+1];Df+=Math.max(0,-delta)*tails[i+1];}}
     ok(Bf+Uf===Df+Zf,"exact retained pair band flux");row.upperBirth+=alpha*Bf;row.upperUp+=alpha*Uf;row.upperDown+=alpha*Df;row.moment+=alpha*Zf;
     // Only levels within this band's range. Exact integration by slicing
     // at all recorded deficits; no per-integer-level expansion.
     if(!raw.some((w,i)=>w&&band[i]===j))continue;
     const cuts=[...new Set([D,2*D,...d.filter(x=>x>D&&x<2*D)])].sort((a,b)=>a-b);
     let local=0,localBirth=0,localUp=0;
     for(let k=1;k<cuts.length;k++){
       const lo=cuts[k-1],hi=cuts[k],lambda=(lo+hi)/2,len=hi-lo,weight=len/D;let begin=-1,mass=0,ends=-1;const originOf=new Map();
       function flush(){
         if(begin<0||!mass){begin=-1;mass=0;return;}
         const value=alpha*mass*weight;local+=value;all+=value;reIntervals++;row.layerChecks++;
         // Natural, full-original residence envelope, frozen per focal source, level and origin.
         let rho=0;for(let l=begin;l<=ends;l++)if(band[l]===j){rho+=2*a[l].w;if(raw[l])originOf.set(l,begin);}
         ok(rho>=mass&&rho>0&&rho<=3*H,"local natural residence envelope");
         function markThin(){for(let l=begin;l<=ends;l++)if(band[l]===j&&raw[l]){thinByHit[l]+=alpha*raw[l]*weight;if(!z.reLayerPaid)z.reLayerPaid=new Map();const C=a[l].C;if(!z.reLayerPaid.has(C))z.reLayerPaid.set(C,[]);z.reLayerPaid.get(C).push({lo,hi,density:alpha*raw[l]});z.reLayerBase=z.pcHigh/z.orig.high;}}
         const fee=1/(j+1)**2,LH=B*u**1.5;
         if(begin===0){localBirth+=mass*len;row.birthRuns++;
           const v=a[0],prior=v.prev?v.prev.histN:1,gg=Math.log(v.histN/prior),prevset=new Set(v.prev?(cvPhys.get(renewId(v.prev))?.es||[]).map(e=>e.M):[]);
           const newcomers=cvPhys.get(renewId(v)).es.filter(e=>e.M>z.M&&!prevset.has(e.M));const rank=newcomers.findIndex(e=>e.M===z.Mp)+1;
           ok(newcomers.length===v.histN-prior&&rank>0&&gg>0,"exact new physical companions");
           // Bounded summable budget per source and birth, averaged over the band.
           const budget=analytic?H*LH*fee*gg/u:(residenceStress?8:2)*H*gg,cap=Math.floor(budget/rho);reBirthMaxCap=Math.max(reBirthMaxCap,cap);
           if(rank<=cap){thin+=value;birthThin+=value;row.thin+=value;row.thinRuns++;reBirthPaidRuns++;markThin();const key=j+":"+z.M+":"+renewId(v)+":"+lo+":"+hi;let q=reBirthUse.get(key);if(!q){q={j,v,lo,hi,rho,budget,ms:new Set(),paid:0};reBirthUse.set(key,q);}ok(q.rho===rho&&near(q.budget,budget),"frozen birth residence capacity");q.ms.add(z.Mp);q.paid+=value;}
           else{birth+=value;row.birth+=value;}
         }
         else{
           const v=a[begin-1],w=a[begin];ok(d[begin-1]<lambda&&d[begin]>lambda&&w.C>v.C,"last genuine level ascent");
           const gain=w.C-v.C,wait=w.t-v.t,delta=d[begin]-d[begin-1];ok(delta===2*wait-gain&&delta<=4*v.r&&delta>0,"positive drift donor roughness");
           const rank=reRank(v,z.Mp);ok(rank>=1&&rank<v.histN,"full original relative larger rank");
           row.donors++;localUp+=mass*len;
           const budget=analytic?3*LH*D:3*H*reCaps[j],cap=Math.floor(budget/rho);reDonorMaxCap=Math.max(reDonorMaxCap,cap);
           if(rank<=cap){
             thin+=value;donorThin+=value;row.thin+=value;row.thinRuns++;reDonorPaidRuns++;markThin();
             const key=j+":"+z.M+":"+renewId(v)+":"+lo+":"+hi;let q=reDonorUse.get(key);if(!q){q={j,v,lo,hi,rho,budget,ms:new Set(),paid:0};reDonorUse.set(key,q);}ok(q.rho===rho&&near(q.budget,budget),"frozen donor residence capacity");q.ms.add(z.Mp);q.paid+=value;
           }else if(raw[begin-1]>0&&mass<=reEps*D){
             short+=value;row.short+=value;row.shortRuns++;
             const key=z.M+":"+z.Mp+":"+renewId(v),u0=reShortUse.get(key)||{charge:0,base:alpha*raw[begin-1],r:v.r,alpha};u0.charge+=value;reShortUse.set(key,u0);
           }else if(v.w&&raw[begin-1]===0){mask+=value;row.maskedHigh+=value;}
           else if(!v.w){small+=value;row.smallLabel+=value;const k=v.p+":"+v.r;reLabelStats.set(k,(reLabelStats.get(k)||0)+value);}
           else{long+=value;row.long+=value;}
         }
         begin=-1;mass=0;
       }
       for(let i=0;i<a.length;i++){
         if(d[i]>lambda){if(begin<0)begin=i;ends=i;if(band[i]===j)mass+=raw[i];}
         else if(begin>=0)flush();
       }flush();
       // Independent last-entry search for each retained hit at this layer.
       let check=0;for(let i=0;i<a.length;i++)if(raw[i]&&band[i]===j){ok(d[i]>lambda,"band high hit above all levels");let r=i;while(r>0&&d[r-1]>lambda)r--;ok((r===0||d[r-1]<lambda)&&originOf.get(i)===r,"independent last-entry search agrees with residence origin");check+=raw[i]*weight;reOracle++;reExactOrigins++;}
       ok(near(check*alpha,alpha*weight*raw.reduce((s,w,i)=>s+(band[i]===j?w:0),0)),"layer integral exact occupation");
     }
     const target=alpha*raw.reduce((s,w,i)=>s+(band[i]===j?w:0),0);
     ok(near(local,target)&&localBirth<=Bf+1e-6&&localUp<=Uf+1e-6,"positive residence partition and birth/up upper envelopes");
   }
   ok(near(all,thin+short+birth+mask+small+long),"pair residence class partition");
   reAdaptiveBirth+=birthThin;reAdaptiveDonor+=donorThin;
   reThin+=thin;reShort+=short;reBirth+=birth;reMasked+=mask;reSmall+=small;reLong+=long;
   if(h-thin>1e-9)reRemainingFixedPairs++;
   if(thin>1e-9){reThinPairs++;ok(near([...thinByHit].reduce((s,w)=>s+w,0),thin),"thin hit allocation conservation");const ledger=new Map();for(let i=0;i<a.length;i++)if(raw[i]){const remain=z.pcHigh/z.orig.high*raw[i]-thinByHit[i];ok(remain>=-1e-7&&thinByHit[i]<=alpha*raw[i]+1e-7,"actual unpaid per-hit deletion");if(remain>1e-10)ledger.set(a[i].C,remain);}rePairPayments.set(z,{amount:thin,ledger});}
 }
 for(const u0 of reUse.values()){
   const D=reLevels[u0.j],a=u0.v,b=a.next,amp=Math.min(D,Math.max(0,exDef(b)-D))-Math.min(D,Math.max(0,exDef(a)-D));
   ok(amp>0&&u0.ms.size<=reCaps[u0.j]&&[...u0.ms.values()].every(w=>w<=3*H*amp+1e-6),"actual donor rank/layer budget");reDonorBound+=3*H*amp*u0.ms.size/D;
 }
 for(const [map,isBirth] of [[reBirthUse,true],[reDonorUse,false]])for(const q of map.values()){const D=reLevels[q.j];ok(q.ms.size<=Math.floor(q.budget/q.rho)&&q.paid<=q.budget*(q.hi-q.lo)/D+1e-6,"adaptive local residue capacity");if(isBirth)reBirthBudget+=q.budget*(q.hi-q.lo)/D;else reAdaptiveBudget+=q.budget*(q.hi-q.lo)/D;}
 // Independent common refinement across all paid partner-layer intervals.
 // Overlapping partitions may differ because the first physical meeting differs.
 for(const [map,isBirth] of [[reBirthUse,true],[reDonorUse,false]]){
   const groups=new Map();for(const q of map.values()){const key=q.j+":"+q.v.M+":"+renewId(q.v);if(!groups.has(key))groups.set(key,[]);groups.get(key).push(q);}
   for(const qs of groups.values()){
     reSweepGroups++;const D=reLevels[qs[0].j],cuts=[...new Set(qs.flatMap(q=>[q.lo,q.hi]))].sort((a,b)=>a-b);
     for(let i=1;i<cuts.length;i++){
       const lo=cuts[i-1],hi=cuts[i],mid=(lo+hi)/2,active=qs.filter(q=>q.lo<mid&&mid<q.hi);if(!active.length)continue;
       const q=active[0],ms=new Set();let density=0;
       for(const w of active){ok(w.rho===q.rho&&near(w.budget,q.budget),"same natural envelope on common refined layer");for(const M of w.ms){ok(!ms.has(M),"one residence per pair per layer");ms.add(M);}density+=w.paid*D/(w.hi-w.lo);}
       ok(ms.size<=Math.floor(q.budget/q.rho)&&density<=q.budget+1e-6,"common-refinement aggregate budget");
       const cap=q.budget*(hi-lo)/D;if(isBirth)reBirthSweepBudget+=cap;else reDonorSweepBudget+=cap;reSweepPaid+=density*(hi-lo)/D;reSweepChecks++;
     }
   }
 }
 ok(near(reSweepPaid,reThin)&&reBirthSweepBudget<=reBirthBudget+1e-6&&reDonorSweepBudget<=reAdaptiveBudget+1e-6,"common layer budget conservation");
 reDonorBound=reBirthSweepBudget+reDonorSweepBudget;
 for(const x of reShortUse.values()){ok(x.charge<=4*reEps*x.base+1e-6,"short residence relative retained donor bound");reShortBound+=4*reEps*x.base;reRelativeBase+=x.base;}
 ok(near(reBefore,exFinalHigh.residual)&&near(reSync+reAsync,reBefore)&&near(reLow+reBand,reSync)&&near(reBand,reThin+reShort+reBirth+reMasked+reSmall+reLong)&&reThin<=reDonorBound+1e-6&&reShort<=reShortBound+1e-6&&reRelativeBase<=reSync+1e-6,"global retained residence conservation");
 for(const row of reRows)ok(near(row.energy,row.birth+row.thin+row.short+row.maskedHigh+row.smallLabel+row.long)&&near(row.upperBirth+row.upperUp,row.moment+row.upperDown),"retained band decomposition");
 // Only thin mass is an absolute new deletion. Short residence is a
 // relative bound and is not subtracted. Preserve previous paid capacities.
 for(const [z,{amount,ledger}] of rePairPayments){ok(amount<=z.pcHigh*(z.gridUnpaidHigh||0)-z.pcAsync*(z.gridUnpaidHigh||0)+1e-6,"thin mass only sync");z.pcHigh-=amount;z.resRemainingHits=ledger;ok(near([...ledger.values()].reduce((s,w)=>s+w,0),z.pcHigh-z.pcAsync),"nonproportional remaining sync hit ledger");}
 const reFinalHigh=jointBirthFlow("high",true,false,true),reFinalMed=jointBirthFlow("med",true,false,true);delete reFinalHigh.cutIds;delete reFinalMed.cutIds;
 ok(near(reFinalHigh.total+reThin,exFinalHigh.total)&&reFinalHigh.residual<=reBefore-reThin+1e-6&&near(reFinalMed.residual,exFinalMed.residual),"thin residence absolute feasible payment");
 // Hierarchical physical birth entropy: incoming selected labels,
 // then exact predecessor physical slots within each label.
 const beF=n=>n>0?n*Math.log(n):0;
 let beEntropy=0,beLoss=0,beMixEntropy=0,beSameEntropy=0,beChecks=0,beMixPairs=0,beSamePairs=0,beRootPairs=0,beBirthVertices=0;
 const beGroups=new Map();
 for(const [id,g] of cvPhys){
   const n=g.es.length,b=g.out.length,labels=new Map(),branches=new Map();
   for(const e of g.es)if(e.prev){const p=e.prev.p,k=renewId(e.prev);if(!labels.has(p))labels.set(p,[]);labels.get(p).push(e);if(!branches.has(k))branches.set(k,[]);branches.get(k).push(e);}
   if(!labels.size){ok(n===1,"singleton physical root");continue;}
   const mix=beF(n)-[...labels.values()].reduce((v,a)=>v+beF(a.length),0),same=[...labels.values()].reduce((v,a)=>v+beF(a.length),0)-[...branches.values()].reduce((v,a)=>v+beF(a.length),0);
   const loss=beF(n)-beF(b);
   ok(mix>=-1e-8&&same>=-1e-8&&near(mix+same,beF(n)-[...g.ins.values()].reduce((v,a)=>v+beF(a.length),0)),"hierarchical birth entropy");
   beEntropy+=mix+same;beLoss+=loss;beMixEntropy+=mix;beSameEntropy+=same;beChecks++;
   let sum=0,mixed=0;for(const a of labels.values())sum+=choose2(a.length);
   mixed=choose2(n)-sum;let sa=sum-[...branches.values()].reduce((v,a)=>v+choose2(a.length),0);
   beMixPairs+=mixed;beSamePairs+=sa;if(mixed+sa)beBirthVertices++;
   if(mixed+sa)beGroups.set(id,{g,labels,branches});
 }
 for(const g of cvPhys.values())if(g.es[0].prev===null)beLoss+=beF(g.es.length)-beF(g.out.length);
 ok(near(beEntropy,beLoss)&&beEntropy<=N*(1+Math.log(N))+1e-6&&beMixPairs+beSamePairs===exTailBirthPairs,"global physical entropy budget");
 // Reconstruct the actual current per-hit ledger after the nonproportional
 // residence deletion. Reoptimized fractions are applied to the updated map.
 const beQuery=new Map();let beBeforeH=0,beBeforeM=0,beSync=0,beAsync=0,bePairCount=0,beHitCount=0,beKindWeight=[0,0,0],beKindPairs=[0,0,0],beLow=0;
 for(const z of birthPairs.values()){
   const f=z.gridUnpaidHigh||0,h=z.pcHigh*f;beBeforeM+=z.pcMed*(z.gridUnpaidMed||0);if(h<=1e-9)continue;
   beBeforeH+=h;bePairCount++;const as=z.pcAsync*f;beAsync+=as;beSync+=h-as;
   const raw=z.resRemainingHits||new Map([...(z.resHits||[])].map(([C,w])=>[C,w*z.pcHigh/z.orig.high]));
   ok(near([...raw.values()].reduce((a,b)=>a+b,0),z.pcHigh-z.pcAsync),"updated prequota sync map");
   const ar=roots.get(z.M),br=rawByRoot.get(z.Mp),a=ar.find(e=>br.get(e.C)?.t===e.t);if(!a){ok(near(h,as),"no physical birth has no sync");continue;}
   const b=br.get(a.C),key=renewId(a),g=beGroups.get(key);ok(g&&a.prev&&b.prev&&renewId(a.prev)!==renewId(b.prev),"actual distinct incoming cohorts");
   const p=a.prev.p,q=b.prev.p,kind=p===q?1:0,d=exDef(a),side=a.t%2;
   if(kind===0){ok((a.C+2*side)%(p*q)===0&&mod(d-6*side,2*p*q)===0,"mixed label CRT at actual birth");}
   else{const lag=Math.abs(a.prev.t-b.prev.t);ok(a.prev.C===b.prev.C&&lag>0&&lag<2*a.prev.r&&a.prev.next.t===b.prev.next.t,"same label actual waiting birth");}
   if(!a.prev.prev||!b.prev.prev)beRootPairs++;
   beKindWeight[kind]+=h-as;beKindPairs[kind]++;
   const actual=new Map([...raw].map(([C,w])=>[C,w*f])),paid=new Map();
   beHitCount+=actual.size;for(const [C,w] of actual)if(exDef(rawByRoot.get(z.M).get(C))<2*reLevels[0])beLow+=w;
   if(!beQuery.has(key))beQuery.set(key,{...g,pairs:[]});beQuery.get(key).pairs.push({z,a,b,kind,actual,raw,paid,h,as,f,integral:new Map(),nextLayers:new Map()});
 }
 // All full reference tails are from the same physical birth, and are
 // nested by source order. Refine levels by the largest original suffix.
 let beBirth=0,beAscent=0,beGroupEnvelopeChecks=0,beMixedControl=0,beSameControl=0,beControlEnergy=[0,0],bePaid=0,bePaidKinds=[0,0],bePaidSides=[0,0,0],bePaidPairs=0,beRemainPairs=0,beLayers=0,beOracle=0,bePrefixChecks=0,beBudget=0,beBudgetMix=0,beBudgetSame=0,beNewHitChecks=0,beRhoChecks=0,beByBand=reLevels.map(D=>({D,birth:0,ascent:0,paid:0,mix:0,same:0})),beWorst=[],beLayerConservation=0,beCorePaid=0,beCoreEdges=0,beCoreChecks=0,beCoreBudget=0,beCoreRemaining=0,beFixedBirthRemain=0,beFixedAscentRemain=0,beLagMin=Infinity,beLagMax=0,beLagRows=new Map();
 const beBase=analytic?H*B*u**1.5/u:(entropyStress?8:2)*H;
 // Independent exact full-natural first-birth rectangle envelope for
 // sampled nontrivial groups of both types, even when unpaid ledger empty.
 for(const [id,g] of beGroups){if(beMixedControl>=32&&beSameControl>=32)break;
   const es=g.g.es,n=es.length,ref=es.at(-1),path=roots.get(ref.M).slice(ref.multiIndex),ends=new Map(es.map(e=>[e.M,roots.get(e.M).at(-1).C]));
   const hasMix=g.labels.size>1,hasSame=[...g.labels.values()].some(a=>new Set(a.map(e=>renewId(e.prev))).size>1);
   if(!(hasMix&&beMixedControl<32)&&!(hasSame&&beSameControl<32))continue;
   let E=[0,0],A=[0,0];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){const a=es[i],b=es[j];if(renewId(a.prev)===renewId(b.prev))continue;const k=a.prev.p===b.prev.p?1:0;E[k]+=2*a.tail;}
   for(const e of path)if(e.w){const live=es.filter(a=>ends.get(a.M)>e.C),labels=new Map(),branches=new Map();for(const a of live){const p=a.prev.p,k=renewId(a.prev);labels.set(p,(labels.get(p)||0)+1);branches.set(k,(branches.get(k)||0)+1);}
     const L=[...labels.values()].reduce((a,b)=>a+choose2(b),0),R=[...branches.values()].reduce((a,b)=>a+choose2(b),0);A[0]+=2*e.w*(choose2(live.length)-L);A[1]+=2*e.w*(L-R);}
   ok(E[0]===A[0]&&E[1]===A[1],"independent ordered-stop birth rectangle energy");beGroupEnvelopeChecks++;if(hasMix&&beMixedControl<32){beMixedControl++;beControlEnergy[0]+=E[0];}if(hasSame&&beSameControl<32){beSameControl++;beControlEnergy[1]+=E[1];}
 }
 for(const [key,g] of beQuery){
   const n=g.g.es.length,es=g.g.es,ref=es.at(-1),path=roots.get(ref.M).slice(ref.multiIndex),def=path.map(exDef),index=new Map(path.map((e,i)=>[e.C,i]));
   const ends=new Map();for(const e of es){const end=roots.get(e.M).at(-1);const i=index.get(end.C);ok(i!==undefined&&path[i].t===end.t,"nested original birth suffix");ends.set(e.M,i);}
   let before=0,paidTotal=0;
   for(let j=0;j<reLevels.length;j++){
     const D=reLevels[j],row=beByBand[j];if(!g.pairs.some(a=>[...a.actual].some(([C,w])=>w>0&&exDef(path[index.get(C)])>=2*D&&exDef(path[index.get(C)])<4*D)))continue;
     const cuts=[...new Set([D,2*D,...def.filter(x=>x>D&&x<2*D)])].sort((a,b)=>a-b);
     const sums=new Float64Array(path.length+1);for(let i=0;i<path.length;i++)sums[i+1]=sums[i]+(def[i]>=2*D&&def[i]<4*D?2*path[i].w:0);
     for(let k=1;k<cuts.length;k++){
       const lo=cuts[k-1],hi=cuts[k],lambda=(lo+hi)/2,scale=(hi-lo)/D;beLayers++;
       let stop=0;if(def[0]>lambda){stop=path.length;for(let i=1;i<path.length;i++)if(def[i]<=lambda){stop=i;break;}}
       // h on an exiting tag's terminal is zero even if the representative continues.
       const rho=new Map();let last=-1;for(const e of es){const r=sums[Math.min(stop,ends.get(e.M))];rho.set(e.M,r);ok(r>=last&&r<=3*H,"monotone natural birth residence");last=r;beRhoChecks++;}
       const lists=new Map(),paidAt=new Map(),edges=[];
       // On each side, use a global increasing-source prefix AND a
       // split-by-opposite-branch prefix; each has its own entropy budget.
       function refList(e,kind){
         const id=e.M+":"+kind;if(lists.has(id))return lists.get(id);
         const p=e.prev.p,branch=renewId(e.prev),ls=g.labels.get(p).length,bs=g.branches.get(branch).length,gg=kind===0?Math.log(n/ls):Math.log(ls/bs);
         const opp=es.filter(v=>kind===0?v.prev.p!==p:v.prev.p===p&&renewId(v.prev)!==branch);
         const budget=beBase*(analytic?1/(j+1)**2:1)*gg;
         const keep=new Set();let sum=0,prev=-1;
         for(const v of opp){const r=Math.min(rho.get(v.M),rho.get(e.M));ok(r>=prev,"opposite natural weights monotone");prev=r;if(sum+r>budget+1e-8)break;sum+=r;keep.add(v.M);}
         ok(sum<=budget+1e-6,"global natural prefix capacity");bePrefixChecks++;
         const cohorts=new Map();for(const v of opp){const id=kind===0?v.prev.p:renewId(v.prev);if(!cohorts.has(id))cohorts.set(id,[]);cohorts.get(id).push(v);}
         const split=new Set();let sum2=0;for(const vs of cohorts.values()){let a=0;for(const v of vs){const r=Math.min(rho.get(v.M),rho.get(e.M));if(a+r>budget/cohorts.size+1e-8)break;a+=r;split.add(v.M);}sum2+=a;}
         ok(sum2<=budget+1e-6,"split natural prefix capacity");
         const r={keep,split,budget,paid:0};lists.set(id,r);beBudget+=3*budget*scale;if(kind===0)beBudgetMix+=3*budget*scale;else beBudgetSame+=3*budget*scale;beCoreBudget+=budget*scale;return r;
       }
       for(const rec of g.pairs){
         let mass=0,asc=0;const hits=[];
         for(const [C,avg] of rec.actual){const i=index.get(C);if(def[i]<2*D||def[i]>=4*D)continue;
           const prior=rec.z.reLayerPaid?.get(C)||[],base=rec.z.reLayerBase===undefined?rec.raw.get(C):rec.z.resHits.get(C)*rec.z.reLayerBase;
           const w=rec.f*Math.max(0,base-prior.reduce((v,x)=>v+(x.lo<lambda&&lambda<x.hi?x.density:0),0));
           rec.integral.set(C,(rec.integral.get(C)||0)+w*scale);if(!w)continue;
           if(i<stop){mass+=w;hits.push([C,w]);let l=i;while(l>0&&def[l-1]>lambda)l--;ok(l===0,"independent birth origin");beOracle++;}else asc+=w;
         }
         row.birth+=mass*scale;beBirth+=mass*scale;row.ascent+=asc*scale;beAscent+=asc*scale;before+=(mass+asc)*scale;
         if(!mass)continue;ok(mass<=Math.min(rho.get(rec.a.M),rho.get(rec.b.M))+1e-6,"actual birth local envelope");
         const A=refList(rec.a,rec.kind),B0=refList(rec.b,rec.kind),ag=A.keep.has(rec.b.M)||A.split.has(rec.b.M),bg=B0.keep.has(rec.a.M)||B0.split.has(rec.a.M);
         const edge={rec,A,B:B0,mass,hits,dead:false};
         function pay(edge,which){const {rec,mass,hits}=edge;edge.dead=true;bePaid+=mass*scale;paidTotal+=mass*scale;row.paid+=mass*scale;bePaidKinds[rec.kind]+=mass*scale;if(rec.kind===0)row.mix+=mass*scale;else row.same+=mass*scale;
           for(const [C,w] of hits){rec.paid.set(C,(rec.paid.get(C)||0)+w*scale);if(!rec.nextLayers.has(C))rec.nextLayers.set(C,[]);rec.nextLayers.get(C).push({lo,hi,density:w});}
         }edge.pay=()=>pay(edge);
         if(ag||bg){const z=ag?A:B0;z.paid+=mass;bePaidSides[ag&&bg?2:ag?0:1]+=mass*scale;edge.pay();}else edges.push(edge);
       }
       for(const z of lists.values())ok(z.paid<=2*z.budget+1e-6,"actual two-prefix payments within budget");
       // Independently budgeted actual weighted core after both prefix masks.
       const nodes=new Map();for(const e of edges)for(const v of [e.A,e.B]){if(!nodes.has(v))nodes.set(v,[]);nodes.get(v).push(e);}
       const oracle=new Set(edges);while(true){const deg=new Map();for(const e of oracle)for(const v of [e.A,e.B])deg.set(v,(deg.get(v)||0)+e.mass);const bad=new Set([...deg].filter(([v,w])=>w<=v.budget+1e-8).map(([v])=>v));if(!bad.size)break;for(const e of oracle)if(bad.has(e.A)||bad.has(e.B))oracle.delete(e);}
       for(const [v,ee] of nodes){const w=ee.filter(e=>!e.dead).reduce((a,e)=>a+e.mass,0);if(w>0&&w<=v.budget+1e-8){for(const e of ee)if(!e.dead){e.pay();beCorePaid+=e.mass*scale;beCoreEdges++;}beCoreChecks++;}}
       // Repeat until stable, including nodes whose degree changed after their turn.
       let change=true;while(change){change=false;for(const [v,ee] of nodes){const w=ee.filter(e=>!e.dead).reduce((a,e)=>a+e.mass,0);if(w>0&&w<=v.budget+1e-8){for(const e of ee)if(!e.dead){e.pay();beCorePaid+=e.mass*scale;beCoreEdges++;}beCoreChecks++;change=true;}}}
       for(const e of edges){ok(oracle.has(e)===!e.dead,"independent weighted entropy core oracle");if(!e.dead){beCoreRemaining+=e.mass*scale;for(const v of [e.A,e.B])ok(nodes.get(v).filter(x=>!x.dead).reduce((a,x)=>a+x.mass,0)>v.budget-1e-7,"actual birth core degree");}}
     }
   }
   for(const rec of g.pairs){
     const z=rec.z,amt=[...rec.paid.values()].reduce((a,b)=>a+b,0);
     for(const [C,w] of rec.actual){if(exDef(rawByRoot.get(z.M).get(C))>=2*reLevels[0]){ok(near(w,rec.integral.get(C)||0),"preserved layer densities integrate to current actual hit");beLayerConservation++;}}
     if(rec.kind===1){const lag=Math.abs(rec.a.prev.t-rec.b.prev.t),k=rec.a.prev.p+":"+lag;beLagMin=Math.min(beLagMin,lag);beLagMax=Math.max(beLagMax,lag);beLagRows.set(k,(beLagRows.get(k)||0)+rec.h-amt);}
     if(amt>1e-9){if(z.reLayerBase===undefined)z.reLayerBase=z.pcHigh/z.orig.high;if(!z.reLayerPaid)z.reLayerPaid=new Map();for(const [C,aa] of rec.nextLayers){if(!z.reLayerPaid.has(C))z.reLayerPaid.set(C,[]);z.reLayerPaid.get(C).push(...aa);}}
     if(amt>1e-9){bePaidPairs++;const ledger=new Map(rec.raw);for(const [C,w] of rec.paid){const actual=rec.actual.get(C),remain=ledger.get(C)-w;ok(w<=actual+1e-6&&remain>=-1e-6,"unpaid birth hit only");if(remain>1e-10)ledger.set(C,remain);else ledger.delete(C);beNewHitChecks++;}z.pcHigh-=amt;z.resRemainingHits=ledger;ok(near([...ledger.values()].reduce((a,b)=>a+b,0),z.pcHigh-z.pcAsync),"updated birth entropy hit map");}
     if(rec.h-amt>1e-9){beRemainPairs++;beWorst.push({M:z.M,Mp:z.Mp,kind:rec.kind,C:rec.a.C,t:rec.a.t,p:rec.a.prev.p,q:rec.b.prev.p,mass:rec.h-amt,n,branchA:g.branches.get(renewId(rec.a.prev)).length,branchB:g.branches.get(renewId(rec.b.prev)).length});}
   }
 }
 beFixedBirthRemain=beBirth-bePaid;beFixedAscentRemain=beAscent;ok(near(beCoreRemaining,beFixedBirthRemain)&&beCorePaid<=beCoreBudget+1e-6,"birth core and payment conservation");
 ok(near(beBeforeH,reFinalHigh.residual)&&near(beBeforeM,reFinalMed.residual)&&near(beSync+beAsync,beBeforeH)&&near(beBirth+beAscent+beLow,beSync)&&bePaid<=beBudget+1e-6,"birth entropy retained decomposition and budget");
 const beFinalHigh=jointBirthFlow("high",true,false,true),beFinalMed=jointBirthFlow("med",true,false,true);delete beFinalHigh.cutIds;delete beFinalMed.cutIds;
 ok(near(beFinalHigh.total+bePaid,reFinalHigh.total)&&beFinalHigh.residual<=beBeforeH-bePaid+1e-6&&near(beFinalMed.residual,reFinalMed.residual),"birth entropy feasible reoptimization");
 beWorst.sort((a,b)=>b.mass-a.mass);
 // Simultaneous exact old key + layer origin flow on ALL current
 // prequota positive weights, not only the previous unpaid pairs.
 // A second independent buffered relayering uses the integrated hit map,
 // not the old layer origin classification. Never count both as payments.
 const jrZ=analytic?Math.max(3,Math.floor(Math.log(u)/32)):jointResidenceStress?7:5;let jrL=2;for(let p=3;p<=jrZ;p+=2)if(spf[p]===p)jrL*=p;
 const jrBeta=analytic?H*B*u**1.5/u:(jointResidenceStress?8:2)*H,jrDonor=analytic?3*B*u**1.5:0,jrFiniteDonor=3*H*(jointResidenceStress?8:3);
 // A fixed gain window, independent of the target deficit band.
 const bhP=analytic?jrL:6,bhZ=analytic?jrZ:3,bhW=Math.max(2*bhP,Math.floor(reLevels[0]/5)),bhL=analytic?B*u**1.5:boundaryHallStress?8:3;
 const bhPairBound=6*bhP*(1+B/bhW);
 const bhLongP=analytic?jrL:30,bhLongZ=analytic?jrZ:5,bhLongW=Math.max(2*bhLongP,Math.ceil(analytic?B*u**2:B/(boundaryHallStress?2:4)));
 function jrFlow(buffered,allowNew,scale=1,boundary=false){
   const allSync=boundary==="all",P=allSync?bhLongP:bhP,Z=allSync?bhLongZ:bhZ,Wgain=allSync?bhLongW:bhW,pairBound=6*P*(1+B/Wgain);
   const keys=new Map(),edges=new Map(),kinds={};const bhPerPair=new Map(),bhMeta=new Map(),bhShortPerPair=new Map();let bhWeight=0,bhShort=0,bhPieces=0,bhChecks=0;let total=0,async=0,oldUnpaid=0,oldBirth=0,oldUp=0,oldLow=0,oldAsync=0,allBirth=0,allUp=0,allLow=0,pairs=0,hits=0,checks=0,gapChecks=0,waitChecks=0,shortBirth=0,lowBirth=0,minGap=Infinity,donorStats=new Map(),birthStats=new Map(),oldKeysTotal=0,newKeysTotal=0,largeGapChecks=0,forcedLarge=0,minLargeRatio=Infinity,maxSmallRun=0,maxGap=0,minWaitRatio=Infinity;
   function key(id,cap,kind){cap*=scale;if(keys.has(id)){const z=keys.get(id);ok(near(z.cap,cap)&&z.kind===kind,"fixed simultaneous key capacity");return id;}keys.set(id,{id,cap,kind});if(kind==="old")oldKeysTotal+=cap;else newKeysTotal+=cap;return id;}
   function demand(ids,w,kind,unpaid,pair=null,bks=null){
     if(w<=1e-12)return;const list=[...new Set(ids)].sort(),id=kind+"|"+list.join("|");let e=edges.get(id);if(!e){e={ids:list,w:0,kind};edges.set(id,e);}e.w+=w;total+=w;if(bks){if(!e.bp)e.bp=new Map();e.bp.set(pair,(e.bp.get(pair)||0)+w);for(const k of bks){const id=k+"|"+pair;bhPerPair.set(id,(bhPerPair.get(id)||0)+w);}}
     if(kind==="birth"){allBirth+=w;oldBirth+=w*unpaid;}else if(kind==="up"){allUp+=w;oldUp+=w*unpaid;}else if(kind==="low"){allLow+=w;oldLow+=w*unpaid;}else{async+=w;oldAsync+=w*unpaid;}oldUnpaid+=w*unpaid;
   }
   function verifyGap(a,l,i,D){const G0=a[i].C-a[l].C,W0=a[i].t-a[l].t;ok(5*G0>=D&&2*W0>=D+G0&&i-l>=Math.ceil(D/(5*B)),"buffered gain/wait/step gap");
     let large=0,n=0,small=0;for(let k=l;k<i;k++){const e=a[k],g=e.next.C-e.C;if(e.p>jrZ){large+=g;n++;small=0;}else{small+=g;ok(small<jrL,"buffered small-label run barrier");maxSmallRun=Math.max(maxSmallRun,small);}}
     ok(G0<=large+(n+1)*jrL&&large*(1+jrL/jrZ)+jrL>=G0-1e-7,"intermediate large-label gain coercivity");
     if(D>5*jrL){ok(large>0&&large>=(D/5-jrL)/(1+jrL/jrZ)-1e-7,"forced intermediate larger label");forcedLarge++;minLargeRatio=Math.min(minLargeRatio,large/D);}
     largeGapChecks++;maxGap=Math.max(maxGap,G0/D);minWaitRatio=Math.min(minWaitRatio,W0/D);
   }
   for(const z of birthPairs.values()){
     if(z.pcHigh<=1e-9)continue;pairs++;const f=z.gridUnpaidHigh||0,old=[z.pr,...(z.ph?[z.ph]:[]),...z.ac,...(z.pcKey?[z.pcKey]:[])].map(k=>key("O:"+k.key,birthBaseHigh*k.factor,"old"));
     demand(old,z.pcAsync,"async",f);
     const raw=z.resRemainingHits||new Map([...(z.resHits||[])].map(([C,w])=>[C,w*z.pcHigh/z.orig.high]));
     ok(near([...raw.values()].reduce((a,b)=>a+b,0),z.pcHigh-z.pcAsync),"current prequota hit map sum");
     if(!raw.size)continue;
     const ar=roots.get(z.M),br=rawByRoot.get(z.Mp),start=ar.findIndex(e=>br.get(e.C)?.t===e.t);ok(start>=0,"actual physical birth for all sync weights");
     const a=ar.slice(start),index=new Map(a.map((e,i)=>[e.C,i])),d=a.map(exDef),v0=a[0],v1=br.get(v0.C),g=cvPhys.get(renewId(v0));
     ok(v1&&v1.t===v0.t&&v0.prev&&v1.prev&&renewId(v0.prev)!==renewId(v1.prev),"actual birth distinct predecessor");
     const kind=v0.prev.p===v1.prev.p?"same":"mix",n=g.es.length;
     function entropy(e){const p=e.prev.p,w=renewId(e.prev),np=g.es.filter(v=>v.prev.p===p).length,nw=g.es.filter(v=>renewId(v.prev)===w).length;return kind==="mix"?Math.log(n/np):Math.log(np/nw);}
     for(const [C,w] of raw){
       if(w<=1e-10)continue;hits++;const i=index.get(C);ok(i!==undefined&&br.get(C)?.t===a[i].t&&w<=2*a[i].w+1e-6,"actual shared natural hit envelope");
       const j=Math.floor(Math.log2(d[i]/(2*reLevels[0])));
       function route(ids,mass,type){
         if(!boundary||type==="low"&&!allSync){demand(ids,mass,type,f);return;}
         const pair=z.M+":"+z.Mp;
         if(C-v0.C<Wgain){bhShort+=mass;bhShortPerPair.set(pair,(bhShortPerPair.get(pair)||0)+mass);demand(ids,mass,type,f);if(!allSync&&buffered&&j>=0&&reLevels[j]>=5*Wgain)ok(type==="birth"&&d[0]>reLevels[j],"short buffered demand must be high-deficit birth");return;}
         const grids=[];for(let K=Math.ceil((C-Wgain)/P)*P;K<C;K+=P){let k=i-1;while(k>=0&&a[k].C>K)k--;ok(k>=0&&a[k].C<=K&&K<a[k+1].C&&a[k+1].C<=C,"strict preceding shared boundary crossing");const v=a[k],b=br.get(v.C);ok(b&&b.t===v.t&&b.next?.C===v.next.C&&b.next?.t===v.next.t&&v.p>Z,"actual strict primorial crossing");grids.push({K,v,b});}
         ok(grids.length>=Wgain/(2*P)&&grids.length<=Wgain/P+1,"uniform boundary count");
         for(const {K,v,b} of grids){const k0=K+":"+renewId(v),ks=[v,b].map(e=>{const id=key("G:"+K+":"+e.M,P*bhL,"boundary");const meta=bhMeta.get(id);if(meta)ok(meta.k0===k0,"unique actual crossing per tag and boundary");else bhMeta.set(id,{K,k0,M:e.M,v:e,n:cvPhys.get(renewId(e)).out.length});return id;});demand([...ids,...ks],mass/grids.length,type,f,pair,ks);bhPieces++;bhChecks++;}
         bhWeight+=mass;
       }
       if(j<0){route(old,w,"low");continue;}
       const D=reLevels[j],L=buffered?D/2:D,U=buffered?D:2*D,W=U-L;
       ok(d[i]>=2*D&&d[i]<4*D,"hit in unique band");
       const prior=z.reLayerPaid?.get(C)||[],base=z.reLayerBase===undefined?w:z.reLayerBase*z.resHits.get(C);
       const cuts=[...new Set([L,U,...d.slice(0,i+1).filter(x=>x>L&&x<U),...(!buffered?prior.flatMap(x=>[x.lo,x.hi]).filter(x=>x>L&&x<U):[])])].sort((a,b)=>a-b);
       let integral=0;
       for(let k=1;k<cuts.length;k++){
         const lo=cuts[k-1],hi=cuts[k],lambda=(lo+hi)/2,weight=(hi-lo)/W,density=buffered?w:Math.max(0,base-prior.reduce((v,x)=>v+(x.lo<lambda&&lambda<x.hi?x.density:0),0)),mass=density*weight;
         if(mass<=1e-12)continue;integral+=mass;let l=i;while(l>0&&d[l-1]>lambda)l--;
         ok(d[l]>lambda&&(l===0||d[l-1]<lambda),"exact last entry at layer midpoint");const ids=old.slice();
         if(l===0){
           const beta=jrBeta*(analytic?1/(j+1)**2:1);
           if(allowNew)for(const e of [v0,v1])ids.push(key("B:"+j+":"+kind+":"+e.M+":"+renewId(e),beta*entropy(e),"birth"));
           route(ids,mass,"birth");const id=renewId(v0)+":"+kind;birthStats.set(id,(birthStats.get(id)||0)+mass*f);
           if(buffered&&d[0]<=D){const G0=a[i].C-v0.C,W0=a[i].t-v0.t;ok(5*G0>=D&&2*W0>=D+G0,"buffered low-deficit birth gap");verifyGap(a,0,i,D);lowBirth++;}else if(buffered&&a[i].C-v0.C<D/5)shortBirth++;
         }else{
           const v=a[l-1],next=a[l],dd=d[l]-d[l-1],vB=br.get(v.C);
           ok(vB&&vB.t===v.t&&vB.next?.t===next.t&&dd>0&&dd<=4*v.r,"shared positive donor");
           const amp=Math.max(0,Math.min(U,d[l])-Math.max(L,d[l-1]));ok(amp>0,"positive band crossing amplitude");
           const cap=analytic?jrDonor*amp:jrFiniteDonor*amp/W;
           if(allowNew)for(const e of [v,vB])ids.push(key("U:"+j+":"+e.M+":"+renewId(e),cap,"up"));
           route(ids,mass,"up");
           const id=renewId(v)+":"+v.p+":"+v.r+":"+j;const row=donorStats.get(id)||{C:v.C,t:v.t,p:v.p,r:v.r,from:d[l-1],to:d[l],j,weight:0,hitC:C,occurrences:0};row.weight+=mass*f;row.occurrences++;donorStats.set(id,row);
           if(buffered){const G0=a[i].C-v.C,W0=a[i].t-v.t;ok(5*G0>=D&&2*W0>=D+G0&&i-l+1>=Math.ceil(D/(5*B)),"buffered ascent gain/wait/step gap");verifyGap(a,l-1,i,D);gapChecks++;waitChecks++;minGap=Math.min(minGap,G0/D);}
         }
       }
       ok(near(integral,w),"all prequota exact per-hit layer integral");checks++;
     }
   }
   ok(near(total,beFinalHigh.total)&&near(oldUnpaid,beFinalHigh.residual)&&near(oldBirth+oldUp+oldLow+oldAsync,oldUnpaid),"all prequota layer demand conserves prior flow");
   const capByKind={};for(const k of keys.values())capByKind[k.kind]=(capByKind[k.kind]||0)+k.cap;
   const birthCapBound=scale*jrBeta*beEntropy*(analytic?reLevels.reduce((s,D,j)=>s+1/(j+1)**2,0):reLevels.length),upCapBound=scale*5*G*(analytic?jrDonor:jrFiniteDonor/(reLevels[0]*(buffered?.5:1)));
   ok((capByKind.birth||0)<=birthCapBound+1e-6&&(capByKind.up||0)<=upCapBound+1e-6,"global integrated origin capacity budgets");
   for(const w of bhPerPair.values())ok(w<=pairBound+1e-6,"per pair boundary bounded reuse across all levels");
   ok((capByKind.boundary||0)<=scale*bhL*(G+N*P)+1e-6,"global per-source boundary capacity");
   if(boundary)ok(near(bhWeight+bhShort,allBirth+allUp+(allSync?allLow:0)),"boundary long/short exact partition");
   for(const w of bhShortPerPair.values())ok(w<=3*(Wgain+B)+1e-6,"short shared gain pair bound");
   ok(bhShort<=3*(Wgain+B)*choose2(N)+1e-6,"global short pair energy bound");
   // A whole prequota layer demand can use any of its old pair keys OR
   // either endpoint's integrated birth/donor key. Max-flow is joint.
   let nv=2;for(const k of keys.values())k.node=nv++;for(const e of edges.values())e.node=nv++;
   const adj=Array.from({length:nv},()=>[]),src=0,sink=1,EPS=1e-9;
   function add(a,b,c){const f={to:b,rev:adj[b].length,cap:c,initial:c},r={to:a,rev:adj[a].length,cap:0,initial:0};adj[a].push(f);adj[b].push(r);return f;}
   for(const k of keys.values())k.arc=add(k.node,sink,k.cap);
   for(const e of edges.values()){e.arc=add(src,e.node,e.w);e.arcs=e.ids.map(id=>add(e.node,keys.get(id).node,total+1));}
   const level=new Int32Array(nv),it=new Int32Array(nv);
   function bfs(){level.fill(-1);const q=[src];level[src]=0;for(let i=0;i<q.length;i++)for(const e of adj[q[i]])if(e.cap>EPS&&level[e.to]<0){level[e.to]=level[q[i]]+1;q.push(e.to);}return level[sink]>=0;}
   function dfs(v,f){if(v===sink)return f;for(;it[v]<adj[v].length;it[v]++){const e=adj[v][it[v]];if(e.cap<=EPS||level[e.to]!==level[v]+1)continue;const d=dfs(e.to,Math.min(f,e.cap));if(d>EPS){e.cap-=d;adj[e.to][e.rev].cap+=d;return d;}}return 0;}
   let flow=0,rounds=0;while(bfs()){it.fill(0);let d;while((d=dfs(src,total+1))>EPS)flow+=d;rounds++;}
   let cutCap=0,cutWeight=0,paid=0,rem={birth:0,up:0,low:0,async:0},usage={},cutKinds={},edgeChecks=0,cutN=0;
   const cut=new Set();for(const k of keys.values()){const w=k.arc.initial-k.arc.cap;ok(w>=-EPS&&w<=k.cap+EPS,"joint key capacity");usage[k.kind]=(usage[k.kind]||0)+w;if(level[k.node]>=0){cut.add(k.id);cutCap+=k.cap;cutKinds[k.kind]=(cutKinds[k.kind]||0)+1;}}
   for(const e of edges.values()){const w=e.w-e.arc.cap;ok(near(w,e.arcs.reduce((s,a)=>s+a.initial-a.cap,0)),"joint layer demand conservation");paid+=w;rem[e.kind]+=e.arc.cap;if(e.ids.every(k=>cut.has(k))){cutWeight+=e.w;cutN++;}edgeChecks++;}
   ok(near(flow,paid)&&near(flow,Object.values(usage).reduce((a,b)=>a+b,0))&&near(total-flow,cutWeight-cutCap)&&near(total-flow,Object.values(rem).reduce((a,b)=>a+b,0)),"joint layer max-flow min-cut certificate");
   if(scale===1)ok(allowNew?flow+1e-6>=beFinalHigh.paid:near(flow,beFinalHigh.paid),"old-key-only exact control or joint improvement");
   const bhInc=new Map(),allInc=new Map(),bhActive=new Map();let bhCutLong=0,bhCutShort=0,bhCutOther=0,bhCutBoundaryCap=0,bhMinPartners=Infinity,bhMinDegreeRatio=Infinity,bhStrict=0,bhStrictBoundary=0,bhCutCross=0,bhMinMass=Infinity,bhCrossUpper=0;
   for(const e of edges.values())if(e.ids.every(k=>cut.has(k))){for(const id of e.ids)allInc.set(id,(allInc.get(id)||0)+e.w);if(e.bp){bhCutLong+=e.w;for(const id of e.ids)if(bhMeta.has(id)){if(!bhInc.has(id))bhInc.set(id,new Map());const m=bhInc.get(id);for(const [p,w] of e.bp)m.set(p,(m.get(p)||0)+w);}}else if(e.kind==="birth"||e.kind==="up"||allSync&&e.kind==="low")bhCutShort+=e.w;else bhCutOther+=e.w;}
   for(const id of cut){const c=keys.get(id).cap,w=allInc.get(id)||0;ok(w>=c-1e-6,"maximizing Hall set cannot contain under-cap key");if(w>c+1e-7)bhStrict++;if(bhMeta.has(id)){bhCutBoundaryCap+=c;const meta=bhMeta.get(id),m=bhInc.get(id)||new Map();let sum=0;const partners=new Set();for(const [p,w] of m){const [a,b]=p.split(":").map(Number);ok(a===meta.M||b===meta.M,"actual endpoint boundary pair");partners.add(a===meta.M?b:a);ok(w<=pairBound+1e-6,"Hall boundary partner reuse bound");sum+=w;}ok(near(sum,w)&&partners.size<=meta.n-1&&partners.size*pairBound>=w-1e-6,"actual Hall boundary incidence and multiplicity");if(w>c+1e-7){bhStrictBoundary++;ok(partners.size>c/pairBound-1e-7,"strict boundary Hall partner lower bound");}bhMinPartners=Math.min(bhMinPartners,partners.size);bhMinMass=Math.min(bhMinMass,meta.n);bhMinDegreeRatio=Math.min(bhMinDegreeRatio,w/c);if(!bhActive.has(meta.k0))bhActive.set(meta.k0,{n:meta.n,keys:0});bhActive.get(meta.k0).keys++;}}
   for(const g of bhActive.values()){ok(g.keys<=g.n,"actual crossing distinct tags");bhCutCross++;bhCrossUpper+=Math.max(0,pairBound*g.n*(g.n-1)/2-scale*P*bhL*g.n);}
   if(boundary){ok(near(bhCutLong+bhCutShort+bhCutOther,cutWeight),"Hall cut mass by boundary eligibility");ok(bhCutLong-bhCutBoundaryCap<=bhCrossUpper+1e-6,"quadratic crossing Hall upper envelope");}
   const bhReport={scale,boundary,P,Z,Wgain,pairBound,shortPairs:bhShortPerPair.size,shortUpper:3*(Wgain+B)*choose2(N),weight:bhWeight,short:bhShort,pieces:bhPieces,checks:bhChecks,pairLoads:bhPerPair.size,cutLong:bhCutLong,cutShort:bhCutShort,cutOther:bhCutOther,cutBoundaryCap:bhCutBoundaryCap,cutCross:bhCutCross,cutKeys:cut.size,strict:bhStrict,strictBoundary:bhStrictBoundary,minPartners:Number.isFinite(bhMinPartners)?bhMinPartners:0,minMass:Number.isFinite(bhMinMass)?bhMinMass:0,minDegreeRatio:Number.isFinite(bhMinDegreeRatio)?bhMinDegreeRatio:0,crossUpper:bhCrossUpper};
   return {bhReport,buffered,allowNew,total,flow,residual:total-flow,rem,usage,cutCap,cutWeight,cutKinds,cutN,keys:keys.size,edges:edges.size,rounds,edgeChecks,oldKeysTotal,newKeysTotal,capByKind,birthCapBound,upCapBound,largeGapChecks,forcedLarge,minLargeRatio:Number.isFinite(minLargeRatio)?minLargeRatio:0,maxSmallRun,maxGap,minWaitRatio:Number.isFinite(minWaitRatio)?minWaitRatio:0,pairs,hits,checks,oldUnpaid,oldBirth,oldUp,oldLow,oldAsync,allBirth,allUp,allLow,async,gapChecks,waitChecks,lowBirth,shortBirth,minGap:Number.isFinite(minGap)?minGap:0,donors:[...donorStats.values()].filter(x=>x.weight>1e-9).sort((a,b)=>b.weight-a.weight).slice(0,16),births:[...birthStats].filter(x=>x[1]>1e-9).sort((a,b)=>b[1]-a[1]).slice(0,8)};
 }
 const jrOld=jrFlow(false,false),jrJoint=jrFlow(false,true),jrBuffered=jrFlow(true,true);
 const bhScale=1/16,bhControl=jrFlow(true,true,bhScale,false),bhJoint=jrFlow(true,true,bhScale,true),bhAll=jrFlow(true,true,bhScale,"all");
 ok(bhJoint.residual<=bhControl.residual+1e-6&&bhAll.residual<=bhControl.residual+1e-6,"scaled boundary flow extends control");
 // Independent buffered gap controls on full original physical suffixes
 // (even when analytic prequota support is empty). Sample first natural
 // high hit with d>=2D on each of up to 128 original paths.
 let jrControl=0,jrControlUp=0,jrControlBirth=0,jrControlChecks=0,jrControlMin=Infinity;
 for(const ar of roots.values()){
   if(jrControl>=128)break;const i=ar.findIndex(e=>e.w&&exDef(e)>=2*reLevels[0]);if(i<0)continue;jrControl++;
   const d=exDef(ar[i]),j=Math.floor(Math.log2(d/(2*reLevels[0]))),D=reLevels[j],lambda=.75*D;let l=i;while(l>0&&exDef(ar[l-1])>lambda)l--;
   if(l===0){jrControlBirth++;continue;}const a=ar[l-1],b=ar[i],G0=b.C-a.C,W=b.t-a.t;ok(exDef(a)<=lambda&&5*G0>=D&&2*W>=D+G0,"independent buffered original path gap");jrControlUp++;jrControlChecks++;jrControlMin=Math.min(jrControlMin,G0/D);
 }
 let anchorTagFactor=0,anchorCompressedFactor=0;
 for(const key of anchorKeySet.values())if(key.kind==="anchor-tag")anchorTagFactor+=key.factor;else anchorCompressedFactor+=key.factor;
 ok(anchorTagFactor<=anchorFactorScale*(anchorGainBudget+anchorRootBudget)+1e-6,"queried tag capacity budget");
 // Exact independent local masks: populate complete anchor cohorts, including
 // all LOW vertices and roots omitted by prior residual masks.
 for(const ar of roots.values())for(const e of ar){
   const g=anchorGroups.get(anchorCode(e));if(!g)continue;
   let z=g.roots.get(e.M);if(!z){z={mask:0n,tail:e.tail,first:e};g.roots.set(e.M,z);}
   const bit=BigInt((e.C-g.D)/2);z.mask|=1n<<bit;
 }
 for(const g of anchorGroups.values())anchorMaxLocalMasks=Math.max(anchorMaxLocalMasks,new Set([...g.roots.values()].map(z=>z.mask)).size);
 // For a fixed compressed key, test all pairs of original anchor groups using
 // translated masks; compare to the actual first-contact pair set. No global
 // prefix disjointness is assumed for mask-compatible pairs.
 const medCut=new Set(anchorJointMed.cutIds),highCut=new Set(anchorJointHigh.cutIds),cutHighPairs=new Set(),cutMedPairs=new Set();
 const anchorCross=new Map();
 for(const z of birthPairs.values()){
   const [a,b]=z.acRefs,aa=anchorCode(a),bb=anchorCode(b),ids=[aa,bb].sort(),id=ids.join("|");
   let v=anchorCross.get(id);if(!v){v={ids,actual:0,med:0,high:0};anchorCross.set(id,v);}
   const keys=[z.pr,...(z.ph?[z.ph]:[]),...z.ac].map(k=>k.key);if(z.orig.med>0&&keys.every(k=>medCut.has(k)))cutMedPairs.add(pairId(a.M,b.M));if(z.orig.high>0&&keys.every(k=>highCut.has(k)))cutHighPairs.add(pairId(a.M,b.M));
   v.actual++;v.med+=z.orig.med;v.high+=z.orig.high;
   const ga=anchorGroups.get(aa),gb=anchorGroups.get(bb),ra=ga.roots.get(a.M),rb=gb.roots.get(b.M);
   const D=Math.min(ga.D,gb.D),am=ra.mask<<BigInt((ga.D-D)/2),bm=rb.mask<<BigInt((gb.D-D)/2),common=am&bm;
   ok(common!==0n,"first contact belongs to exact LOW masks");
   let first=0,m=common;while((m&1n)===0n){first++;m>>=1n;}ok(D+2*first===a.C,"first shared LOW vertex equals first projected contact");anchorLocalChecks++;
 }
 let anchorCandidateProducts=0,anchorMaskProducts=0,anchorEarlierExcluded=0,anchorPrefixProducts=0,anchorEnvelope=0,anchorPairGroups=anchorCross.size;
 let anchorCutMedPairs=0,anchorCutHighPairs=0,anchorCutHighEnvelope=0,anchorLocalEnvelopeAtContact=0,anchorCutKeyChecks=0,anchorLocalLabelReject=0;
 const foundMed=new Set(),foundHigh=new Set(),multiStats=prefixDepths.map(depth=>({depth:Number.isFinite(depth)?depth:"full",med:0,high:0,tail:0,age:0,retained:0,combined:0}));let multiPrefixChecks=0,multiFalsePrior=0,multiHighAgeZero=0,multiCandidateCutMed=0,multiCandidateCutHigh=0;const multiMoments=prefixDepths.map(depth=>({depth:Number.isFinite(depth)?depth:"full",m1:0,m2:0,h1:0,h2:0,medRemoved:0,highRemoved:0}));const multiFoundMed=new Set(),multiFoundHigh=new Set();
 for(const v of anchorCross.values()){
   const [a,b]=v.ids.map(id=>anchorGroups.get(id)),D=Math.min(a.D,b.D),as=BigInt((a.D-D)/2),bs=BigInt((b.D-D)/2);
   const left=[...a.roots.values()],right=[...b.roots.values()];let raw=0,compatible=0,firstFilter=0,envelope=0;
   for(const x of left)for(const y of right){
     if(x.first.M===y.first.M)continue;raw++;
     if(((x.mask<<as)&(y.mask<<bs))===0n)continue;compatible++;
     // A later anchor's path visiting the earlier anchor gives an earlier
     // contact unless the earlier anchor IS the common LOW contact.
     const common=(x.mask<<as)&(y.mask<<bs);let k=0,m=common;while((m&1n)===0n){k++;m>>=1n;}const C=D+2*k;
     const later=a.D<b.D?y:x,early=Math.min(a.D,b.D);
     if(early<C&&rawByRoot.get(later.first.M).has(early))continue;
     firstFilter++;envelope+=2*Math.min(x.tail,y.tail);
     // At the first shared local vertex the incoming label is the previous
     // set-bit gap plus one, or the anchor label if there is no previous bit.
     function localLabel(g,z){const i=(C-g.D)/2;if(i===0)return g.q;let j=i-1;while(j>=0&&((z.mask>>BigInt(j))&1n)===0n)j--;ok(j>=0,"LOW predecessor bit");return 2*(i-j)+1;}
     const p=localLabel(a,x),q=localLabel(b,y),M=x.first.M,Mp=y.first.M;
     const rx=rawByRoot.get(M).get(C),ry=rawByRoot.get(Mp).get(C);
     ok(rx&&ry&&p===(rx.prev?.p||0)&&q===(ry.prev?.p||0),"mask reconstructs first-contact incoming labels");anchorCutKeyChecks++;
     if(p===q){anchorLocalLabelReject++;continue;}
     const pc=!p||!q?"PR:"+(!p?M:Mp):"PM:"+C+":"+Math.min(p,q)+":"+Math.max(p,q);
     let ac;if(!a.q||!b.q)ac="AR:"+(!a.q&&!b.q?Math.min(M,Mp):!a.q?M:Mp);
     else if(a.q===b.q)ac="AS:"+Math.min(a.D,b.D)+":"+Math.max(a.D,b.D)+":"+a.q;
     else{const ar=[a,b].sort((v,w)=>v.D-w.D||v.q-w.q);ac="AC:"+ar[0].D+":"+ar[0].q+":"+ar[1].D+":"+ar[1].q;}
     const keys=[pc,ac,"AT:"+M+":"+a.D,"AT:"+Mp+":"+b.D],tail=2*Math.min(rx.tail,ry.tail),id=pairId(M,Mp);anchorLocalEnvelopeAtContact+=tail;
     const mc=keys.every(k=>medCut.has(k))&&sourceCell(M)===sourceCell(Mp),hc=keys.every(k=>highCut.has(k));
     if(mc){anchorCutMedPairs++;foundMed.add(id);}
     if(hc){anchorCutHighPairs++;anchorCutHighEnvelope+=tail;foundHigh.add(id);}
     if(mc||hc){
       const age=hc?2*Math.max(0,Math.min(rx.tail,ry.tail)-2*ageCap(Math.abs(M-Mp)).K):0,ret=hc?2*Math.min(rx.multiRetTail,ry.multiRetTail):0,combined=Math.min(age,ret);
       if(hc&&combined===0)multiHighAgeZero++;
       let bad=false;for(let j=0;j<prefixDepths.length;j++){const earlier=multiPrefixOverlap(rx,ry,prefixDepths[j],true),mom=multiMoments[j];multiPrefixChecks++;
         if(mc){mom.m1+=earlier;mom.m2+=earlier*earlier;if(earlier)mom.medRemoved++;}if(hc){mom.h1+=combined*earlier;mom.h2+=combined*earlier*earlier;if(earlier)mom.highRemoved+=combined;}
         if(bad)ok(earlier>0,"nested reverse-prefix rejection");if(earlier>0){bad=true;continue;}
         const z=multiStats[j];if(mc)z.med++;if(hc){z.high++;z.tail+=tail;z.age+=age;z.retained+=ret;z.combined+=combined;}
         if(j===prefixDepths.length-1){if(mc)multiFoundMed.add(id);if(hc)multiFoundHigh.add(id);}
       }
       if(bad)multiFalsePrior++;
     }
   }
   ok(v.actual<=firstFilter&&v.high<=envelope+1e-6,"prefix-filtered local mask envelope");
   anchorCandidateProducts+=raw;anchorMaskProducts+=compatible;anchorEarlierExcluded+=compatible-firstFilter;anchorPrefixProducts+=firstFilter;anchorEnvelope+=envelope;
 }
 ok([...cutMedPairs].every(id=>foundMed.has(id))&&[...cutHighPairs].every(id=>foundHigh.has(id)),"all internal cut pairs included in mask envelope");
 ok(cutMedPairs.size===anchorJointMed.internalPairs&&cutHighPairs.size===anchorJointHigh.internalPairs&&anchorCutHighEnvelope+1e-6>=anchorJointHigh.cutWeight,"cutset envelope domination");
 ok([...cutMedPairs].every(id=>multiFoundMed.has(id))&&[...cutHighPairs].every(id=>multiFoundHigh.has(id)),"all actual internal pairs survive full prefix exclusion");
 for(const z of multiStats){ok(z.med>=cutMedPairs.size&&z.high>=cutHighPairs.size&&z.combined+1e-6>=anchorJointHigh.cutWeight,"multi-prefix cut envelope");}
 for(let i=0;i<multiMoments.length;i++){const z=multiMoments[i],m=z.m2?z.m1*z.m1/z.m2:0,h=z.h2?z.h1*z.h1/z.h2:0;
   ok(m<=z.medRemoved+1e-6&&h<=z.highRemoved+1e-6,"weighted witness second moment lower bound");z.medMomentRemoval=m;z.highMomentRemoval=h;ok(z.medRemoved+multiStats[i].med===anchorCutMedPairs,"exact witness count partition");
 }
 // Independent range-difference redistribution of every anchor's original weight.
 // This tests the direct block loops, including the truncated final window.
 let multiRedistributionChecks=0;
 for(const ar of roots.values()){const d=new Float64Array(ar.length+1),starts=ar[0].multiStarts;
   for(let j=0;j<starts.length-1;j++){const a=starts[j],q=ar[a].anchorQ,w=q?q-1:B;
     for(const k of multiDepths){const end=starts[Math.min(j+k,starts.length-1)],v=w/(end-a)/multiDepths.length;d[a]+=v;d[end]-=v;}}
   let v=0;for(let i=0;i<ar.length;i++){v+=d[i];ok(near(v,ar[i].multiMass),"independent gain redistribution");multiRedistributionChecks++;}
 }
 // Independent per-actual-pair age+retained upper bound (no rank accounting).
 for(const z of birthPairs.values())if(z.orig.high>0){const [a,b]=z.acRefs;const v=2*Math.min(a.multiRetTail,b.multiRetTail,Math.max(0,Math.min(a.tail,b.tail)-2*ageCap(Math.abs(a.M-b.M)).K));ok(z.orig.high<=v+1e-6,"individual age/retained tail intersection bound");}
 delete anchorJointMed.cutIds;delete anchorJointHigh.cutIds;
 anchorLocalPairs=anchorMaskProducts;anchorLocalReject=anchorCandidateProducts-anchorMaskProducts;
 // Arithmetic support oracle for all observed nonroot compressed key types:
 // enumerate distinct offset/label congruences, not observed contact horizons.
 const anchorTypes=new Map();for(const k of anchorKeySet.values()){
   if(k.kind!=="compressed-mixed"&&k.kind!=="compressed-same")continue;
   const v=k.info,d=v.E-v.D,id=k.kind+":"+v.p+":"+v.q+":"+d,z=anchorTypes.get(id)||{v,d,count:0};z.count++;anchorTypes.set(id,z);
 }
 let anchorSupportChecks=0,anchorSupportCount=0;
 for(const {v,d,count} of anchorTypes.values()){
   const md=v.p===v.q?v.p:v.p*v.q,rs=new Set();
   for(const a of [0,-2])for(const b of [0,-2]){
     if(v.p===v.q){if(mod(a+d-b,v.p)===0)rs.add(mod(a,v.p));}
     else rs.add(crtResid(v.p,v.q,a,b-d));
   }
   let cap=0;for(const r of rs)cap+=horizonCount(md,r);
   ok(count<=cap,"compressed offset CRT support");anchorSupportChecks++;anchorSupportCount+=cap;
 }
 // Controls from full natural shared pairs, independent of prior masks.
 // Keep the primary residual counters before this deliberately broader sample.
 const residualBirthCounts={pairChecks:birthPairChecks,physicalPairs:birthPhysicalPairs,projectedPairs:birthProjectedPairs,noPhysical:birthNoPhysical,root:birthRootContacts,mixed:birthMixed,same:birthSame,tick:birthTickChecks,lag:{...birthLagStats}};
 let birthControlPairs=0,birthControlPhys=0,birthControlNoPhys=0,birthControlKinds={},lowPhaseExceptions=0,lowPhaseTags=0;
 for(const ar of roots.values())for(const e of ar)if(e.prev&&2*e.t-e.C<=6){const z=phase(e);lowPhaseTags++;if(z.d0!==6*z.s)lowPhaseExceptions++;}
 const birthControlGroups=new Map();
 for(const [id,z] of [...sharedAge.entries()].sort((a,b)=>b[1].total-a[1].total).slice(0,128)){
   const [M,Mp]=id.split(":").map(Number),v={M,Mp,med:0,never:0,high:0,sync:0,async:0};classifyBirth(v);birthControlPairs++;
   if(v.ph){birthControlPhys++;birthControlKinds[v.ph.kind]=(birthControlKinds[v.ph.kind]||0)+1;addBirthGroup(birthControlGroups,v.ph,v,0,0);}else birthControlNoPhys++;
 }
 // Independently enumerate relaxed CRT key capacities for observed arithmetic TYPES.
 // No need to enumerate the entire X*T state strip; phase and horizon factors separate.
 for(const [stage,map] of [["physical",birthPhysical],["projected",birthProjected],["control",birthControlGroups]])for(const g of map.values()){
   const v=g.info;if(g.kind.includes("root"))continue;let type;
   if(stage==="projected")type=stage+":"+g.kind+":"+v.p+":"+v.q;
   else type=stage+":"+g.kind+":"+(v.p||0)+":"+v.q+":"+(v.j??-1);
   let a=birthTypes.get(type);if(!a){a={g,keys:0,med:0,high:0};birthTypes.set(type,a);}a.keys++;a.med+=Math.min(g.med,birthBaseMed*g.factor);a.high+=Math.min(g.high,birthBaseHigh*g.factor);
 }
 function horizonCount(modulus,residue){const lo=2*X-2,hi=7*X;return Math.max(0,Math.floor((hi-residue)/modulus)-Math.ceil((lo-residue)/modulus)+1);}
 function crtResid(p,q,a,b){let n=mod(a,p);while(mod(n,q)!==mod(b,q))n+=p;return n;}
 for(const a of birthTypes.values()){
   const g=a.g,v=g.info;let cap=0,plain=0;
   if(g.kind==="projected-mixed"){for(const i of [0,-2])for(const j of [0,-2])cap+=horizonCount(v.p*v.q,crtResid(v.p,v.q,i,j));}
   else{
     const m=(v.p||1)*v.q;
     for(const parity of [0,1]){
       const base=6*parity,hs=horizonCount(m,-2*parity);
       if(v.j===undefined){for(let d0=0;d0<=6;d0+=2)if(mod(d0-base,2*m)===0)cap+=hs;}
       else{
         const n=Math.max(0,Math.floor((v.D-base)/(2*m))-Math.max(1,Math.floor((v.D/2-base)/(2*m))+1)+1);cap+=hs*n;
       }
     }
   }
   ok(a.keys<=cap,"observed keys inside independent CRT support");birthSupportTotal+=cap;birthRelaxChecks++;
   if(v.rough&&birthRoughSupportChecks<32){
     // Enumerate actual even horizon congruence and roughness at the finite cutoff.
     let roughCap=0;
     for(const parity of [0,1]){
       let hs=0;for(let C=2*X-2+mod(-2*parity-(2*X-2),v.q);C<=7*X;C+=v.q){if(C%2)continue;const r=Math.min(...fs(C-1),...fs(C+1));if(2*r>birthY)hs++;}
       if(v.j===undefined){for(let d0=0;d0<=6;d0+=2)if(mod(d0-6*parity,2*v.q)===0)roughCap+=hs;}else{const base=6*parity,n=Math.max(0,Math.floor((v.D-base)/(2*v.q))-Math.max(1,Math.floor((v.D/2-base)/(2*v.q))+1)+1);roughCap+=hs*n;}
     }
     ok(a.keys<=roughCap&&roughCap<=cap,"observed rough key support");birthRoughSupportChecks++;
   }
 }
 // Independent pair oracle: merge the two frozen natural high lists, rather than
 // reading sharedAge's horizon accumulator. Includes a largest-mass sample.
 let ageOraclePairs=0,ageOracleHits=0,ageOraclePaid=0;
 const ageControls=[...sharedAge.entries()].sort((a,b)=>b[1].total-a[1].total);
 for(const [id,z] of (X<=1024?ageControls:ageControls.slice(0,128))){
   const [M,Mp]=id.split(":").map(Number),a=roots.get(M).filter(e=>e.w),b=roots.get(Mp).filter(e=>e.w),hits=[];
   let i=0,j=0;while(i<a.length&&j<b.length){if(a[i].C<b[j].C)i++;else if(b[j].C<a[i].C)j++;else{ok(a[i].r===b[j].r,"independent natural shared weight");hits.push(a[i].r);i++;j++;}}
   const total=hits.reduce((q,v)=>q+v,0);let pre=0,paid=0;
   for(const v of hits){if(pre<z.K||total-pre-v<z.K)paid+=v;pre+=v;}
   ok(total===z.total&&paid===z.paid,"independent two-list age oracle");ageOraclePairs++;ageOracleHits+=hits.length;ageOraclePaid+=2*paid;
 }
 // Deliberately puncture the retained natural incidence list by a fixed mask
 // before a fresh density gate. This is only an independent robustness control,
 // not a claimed negligible linear deletion or a second residual experiment.
 let holeInputR=0,holeDensityR=0,holeKeepR=0,holeE=0,holeRecent=0,holeGroups=0,holeGateGroups=0;
 for(const es of hh.values()){
   const groups=new Map();for(const e of es){if(!groups.has(e.t))groups.set(e.t,[]);groups.get(e.t).push(e);}
   let n=0;
   for(const ar of groups.values()){
     const r=ar[0].r,keep=ar.filter(e=>!e.histBad&&(Math.floor(e.M/2)+e.C/2)%5!==0);
     holeInputR+=r*keep.length;if(keep.length<historyZeta*ar.length){holeDensityR+=r*keep.length;if(keep.length)holeGateGroups++;continue;}
     n+=keep.length;holeKeepR+=r*keep.length;let recent=0;
     for(let i=0;i<keep.length;i++)for(let j=i+1;j<keep.length;j++){const a=keep[i].M<keep[j].M?keep[i]:keep[j],b=keep[i].M<keep[j].M?keep[j]:keep[i];if(!oldCompanion(a,b))recent+=2;}
     ok(recent<=historyCoef*keep.length**2+1e-6,"arbitrary holes retained-group relative budget");holeRecent+=r*recent;holeGroups++;
   }holeE+=es[0].r*n*n;
 }
 ok(holeInputR===holeDensityR+holeKeepR&&holeDensityR<=historyZeta*highRankR+1e-6&&holeRecent<=historyCoef*holeE+1e-6,"punctured incidence robustness");
 // Independently exercise full endpoint root leaves in ALL natural high groups (even no residual);
 // control sampled full projected vertices, not only medium/high endpoints.
 let reverseControlGroups=0,relaxChecks=0,relaxWords=0,relaxRootWords=0,relaxMaxRoot=0,relaxActualRoots=0,relaxMaxWords=0;
 function relaxed(C,Y,K,J){
   const keys=new Set(),rootWords=new Map();
   function visit(D,k,budget,prefix){for(let g=0;g<=budget;g+=2){const A=D-g;if(A<2*X-2)break;const w=[...prefix,g],M=A/2+1,inc=incoming(A).filter(q=>A-q+1>=2*X-2);
       if(roots.has(M)){const id="R:"+w.join(",");keys.add(id);rootWords.set(id,M);}
       if(inc.some(q=>q<Y&&q-1>budget-g))keys.add("S:"+w.join(","));
       if(k===K){if(inc.some(q=>q>=Y))keys.add("K:"+w.join(","));}
       else for(const q of inc)if(q>=Y)visit(A-q+1,k+1,budget-g,[...w,q]);
   }}
   visit(C,0,J,[]);ok(keys.size<=bound(Y,K,J),"relaxed arithmetic word count");
   return {keys,rootWords};
 }
 const controls=new Map();
 for(const es of vertices.values()){if(controls.size>=32)break;const g=es.filter(e=>e.next);if(g.length&&!controls.has(g[0].C))controls.set(g[0].C,g);}
 for(const es of [...hh.values()].sort((a,b)=>b.length-a.length).slice(0,32))controls.set(es[0].C,es);
 for(const es of controls.values()){
   const part=reversePartition(es);reverseControlGroups++;
   for(const [Y,K,J,key] of [[revY,revK,revJ,"z"],[physY,physK,physJ,"f"]]){
     const v=relaxed(es[0].C,Y,K,J);relaxWords+=v.keys.size;relaxRootWords+=v.rootWords.size;relaxMaxRoot=Math.max(relaxMaxRoot,v.rootWords.size);relaxMaxWords=Math.max(relaxMaxWords,v.keys.size);
     for(const a of part.byM.values()){const z=a[key];ok(v.keys.has(z.key),"independent relaxed reverse word inclusion");if(z.status==="R"){ok(v.rootWords.get(z.key)===a.e.M,"relaxed prime origin equality");relaxActualRoots++;}relaxChecks++;}
   }
 }
 return {mode,crtStress,gainStress,windowStress,reverseStress,ancestryStress,birthStress,anchorStress,multiStress,precutStress,gridStress,starStress,prefixStress,resetStress,thresholdStress,coverStress,excursionStress,residenceStress,entropyStress,jointResidenceStress,boundaryHallStress,bhP,bhZ,bhW,bhL,bhPairBound,bhScale,bhControl,bhJoint,bhLongP,bhLongZ,bhLongW,bhAll,jrZ,jrL,jrOld,jrJoint,jrBuffered,jrControl,jrControlUp,jrControlBirth,jrControlChecks,jrControlMin:Number.isFinite(jrControlMin)?jrControlMin:0,beEntropy,beLoss,beMixEntropy,beSameEntropy,beChecks,beMixPairs,beSamePairs,beRootPairs,beBirthVertices,beBeforeH,beBeforeM,beSync,beAsync,bePairCount,beHitCount,beKindWeight,beKindPairs,beLow,beBirth,beAscent,bePaid,bePaidKinds,bePaidSides,bePaidPairs,beRemainPairs,beLayers,beOracle,bePrefixChecks,beBudget,beBudgetMix,beBudgetSame,beNewHitChecks,beRhoChecks,beByBand,beGroupEnvelopeChecks,beMixedControl,beSameControl,beControlEnergy,beLayerConservation,beCorePaid,beCoreEdges,beCoreChecks,beCoreBudget,beCoreRemaining,beFixedBirthRemain,beFixedAscentRemain,beLagMin:Number.isFinite(beLagMin)?beLagMin:0,beLagMax,beLagRows:[...beLagRows].sort((a,b)=>b[1]-a[1]).slice(0,20),beWorst:beWorst.slice(0,12),beFinalHigh,beFinalMed,reEps,reCaps,reRows,reBefore,reSync,reAsync,reLow,reBand,reThin,reShort,reBirth,reMasked,reSmall,reLong,rePairs,reHits,reIntervals,reOracle,reThinPairs,reDonorBound,reShortBound,reRelativeBase,reAdaptiveBirth,reAdaptiveDonor,reBirthBudget,reAdaptiveBudget,reBirthMaxCap,reDonorMaxCap,reBirthPaidRuns,reDonorPaidRuns,reExactOrigins,reSweepChecks,reSweepGroups,reBirthSweepBudget,reDonorSweepBudget,reSweepPaid,reRemainingFixedPairs,reLabelStats:[...reLabelStats].sort((a,b)=>b[1]-a[1]).slice(0,20),reFinalHigh,reFinalMed,exK,exD0,exLevels,exMaxDef,exControl,exChosen,exGroups:exGroups.size,exW,exRareW,exRareRoots:exRare.size,exRareInc,exRareBound,exEndpointCount,exFlux,exTail,exTailSync,exTailBirthPairs,exTailOracle,exTailPairsOracle,exTailChecks,exPairs,exBeforeH,exBeforeM,exPaidH,exPaidAsync,exPaidPairs,exSurv,exRarePairCount,exRareWeight,exPaidBy,exFinalHigh,exFinalMed,cvM,cvBM,cvS,cvD,cvA,cvQ,cvChecks,cvDelta,cvLoss,cvAllSmall,cvBranch,cvSmall,cvBirthTags,cvExcess,cvExit,cvHeavy,cvSeeds,cvSeedMass:cvSeedTags.size,cvRepGain,cvRepLarge,cvExtraLarge,cvControl,cvHeavyHigh,cvHeavyLarge,cvRareInc,cvRareRoots:cvRareRoots.size,cvSlots,cvSlotReset,cvSlotNonreset,cvSlotOracle,cvSlotMax,cvZ,cvL,cvRuns,cvSteps,cvMaxGain,cvRoot,cvReset,cvDown,cvPairs,cvShallow,cvSurv,cvShallowSurv,cvHBefore,cvMBefore,cvHPaid,cvMPaid,cvAPaid,cvNPaid,cvHClass,cvHCounts,cvMedThin,cvMC,cvHC,cvStripChecks,cvUniqueChecks,cvRareShallow,cvFinalHigh,cvFinalMed,thM,thA,thScales,thStats,thBirthStates,thBranchStates,thSmallTags,thBirthTags,thPotential,thLoss,thMassBound,thMarkedTags,thChecks,thThresholdOracle,thActivationOracle,thCorridorPairs,thCorridorChecks,thPhysicalActivations,thResetActivations,thRankChecks,thMaxRank,thRH,thRM,thHBefore,thMBefore,thHPaid,thMPaid,thAPaid,thNPaid,thHClass,thMClass,thHCounts,thMCounts,thPairs,thSurvHigh,thSurvMed,thStalePhysical,thStaleReset,thStripVisits,thHeavyStrip,thUniqueStrip,thSmallStrip,thBranchStrip,thOracle,thFinalHigh,thFinalMed,renewK,renewEps,renewA,renewP,renewVisits,renewTransitions,renewRoots,renewShortEntries,renewShortChecks,renewLongEntries,renewGrowth,renewMarkCount,renewSpanSum,renewSpanMarks,renewGain,renewLoss,renewLossPairs,renewBirthPairs,renewArcEnergy,renewExitEnergy,renewArcGainPairs,renewExitGainPairs,renewArcChecks,renewExitChecks,renewSameEnergy,renewDifferentEnergy,renewAllSync,renewHitChecks,renewPairOracle,renewPairOracleGain,renewPairOracleCount,renewMaxMass,renewMaxIn,renewSuffixChecks,renewIndegreeChecks,renewWindowChecks,renewGroups:renewGroups.size,renewPairs,renewNear,renewFar,renewStable,renewOld,renewStableChecks,renewMinOldMass:Number.isFinite(renewMinOldMass)?renewMinOldMass:0,renewMaxBackSpan,renewInherited,renewThinH,renewThinM,renewHBefore,renewMBefore,renewHPaid,renewMPaid,renewAPaid,renewNPaid,renewHClass,renewMClass,renewHCounts,renewMCounts,renewByAge,renewOracleChecks,renewFinalHigh,renewFinalMed,absAgeLimit,absBackDepth,absBackCounts,absControlQueries,absPairCount,absOutside,absHighBefore,absMedBefore,absHighPaid,absMedPaid,absAsyncPaid,absNeverPaid,absRankChecks,absOldMembership,absRelaxMembership,absExactMembership,absSlotRaw,absSlotAllowed,absDAGNodes,absDAGEdges,absOracleChecks,absReverseWords,absMaxReverseWords,absPhysical,absNoPhysical,absReset,absNonreset,absNonresetBig,absPhysicalShallow,absConeChecks,absLagChecks,absMaxLag,absLargeP,absLargeS,absLargeCrossHigh,absLargeCrossPairs,absLargeControls,absLargeUpper,absLargeGain,absFinalHigh,absFinalMed,starY,starS,starRareCount,starRareWitnesses,starRareProxy,starRareActual,starRareOracle,starSupport0,starSupportShort,starAPSupport,starAPSupport0,starAPLarge,starAPRootContacts,starAPLargeRootContacts,starAPRootContactMax,starQueryPairs,starRootPairs,starNearPairs,starNearLargePairs,starNearLargeHigh,starNearLargeMed,starMaxAge,starMaxLanding,starPrefixChecks,starMembership,starSlotChecks,starMaxGroup,starActualGroups,starRankChecks,starHighRank,starMedRank,starNeverRank,starAsyncRank,starRankDirections,starAgeHist,starHighCore,starMedCore,starFinalHigh,starFinalMed,gridDs,gridInfo,gridShallow,gridRootContacts,gridAssignedPairs,gridSame,gridLanding,gridHighPaid,gridMedPaid,gridNeverPaid,gridAsyncPaid,gridMembership,gridOracle,gridDegreeChecks,gridAfterHigh,gridAfterMed,gridHighCore,gridMedCore,gridFinalHigh,gridFinalMed,pcMedLambda,pcMedDegree,pcMedDegreeBudget,pcMedMaxDegree,pcMedFullPaid,pcMedNeverPaid,pcMedDirections,pcMedRatioMax,pcMedAfterRanks,pcD,pcHighCap,pcMedCap,pcY,pcShallow,pcRootShallow,pcEligible,pcSame,pcMixed,pcLanding,pcMembership,pcDegreeChecks,pcDegreeMax,pcSlots,pcSlotBound,pcMaxSlots,pcFullHigh,pcFullMed,pcFullNever,pcFullAsync,pcPaidHighPairs,pcPaidMedDirections,pcSameProducts,pcSameHigh,pcSameMed,pcSameKeyChecks,pcIndependent,pcOracleSlots,pcOracleChecks,pcThinHigh,pcThinMed,pcThinChecks,pcControlCuts,pcHighKinds,pcMedKinds,pcFinalHigh,pcFinalMed,multiLambda,multiDepths,multiMass,multiExpected,multiRootChecks,multiDegreeChecks,multiDegreeMax,multiDegreeBudget,multiRankPairs,multiRankExtra,multiRankAsync,multiRankBefore,multiRankOnlyOld,multiRankOnlyComplex,multiRankOnlySource,multiHighResidual:anchorJointHigh.residual-multiRankExtra,multiAsyncResidual:anchorJointHigh.otherResidual-multiRankAsync,multiStats,multiMoments,multiRedistributionChecks,multiReoptHigh,multiFullPaid,multiPrefixChecks,multiFalsePrior,multiHighAgeZero,ay,aL,anchorJointMed,anchorJointHigh,anchorGainBudget,anchorRootBudget,anchorBlocks,anchorVertices,anchorMaxGain,anchorMaxWait,anchorBarrierChecks,anchorPairChecks,anchorRootPairs,anchorSamePairs,anchorMixedPairs,anchorCompressedPairs,anchorLongSameChecks,anchorSmallContactPairs,anchorSmallPromoted,anchorLocalChecks,anchorLocalReject,anchorLocalPairs,anchorMaxLocalMasks,anchorTagFactor,anchorCompressedFactor,anchorCandidateProducts,anchorMaskProducts,anchorEarlierExcluded,anchorPrefixProducts,anchorEnvelope,anchorCutMedPairs,anchorCutHighPairs,anchorCutHighEnvelope,anchorLocalEnvelopeAtContact,anchorCutKeyChecks,anchorLocalLabelReject,anchorPairGroups,anchorSupportChecks,anchorSupportCount,birthY,birthBaseMed,birthBaseHigh,jointMed,jointHigh,residualBirthCounts,birthControlPairs,birthControlPhys,birthControlNoPhys,birthControlKinds,lowPhaseExceptions,lowPhaseTags,birthPairChecks,birthPhysicalPairs,birthProjectedPairs,birthNoPhysical,birthPriorHigh,birthAfterHigh,birthMaxKeyPairs,birthMaxFullTail,birthTickChecks,birthRootContacts,birthMixed,birthSame,birthRelaxChecks,birthSupportTotal,birthRoughSupportChecks,birthLagStats,physicalPay,projectedPay,birthSummary,birthMedResidual,birthNeverResidual,birthHighResidual,birthSyncResidual,birthAsyncResidual,historyD,historyEps,historyZeta,historyCoef,histGlobalLog,histCellLog,histMarkedGain,histMarkedEvents,histGlobalMarks,histCellOnlyMarks,histMaxCells,histRootChecks,histCutChecks,histGrowthChecks,histMarkedActual,histMarkedMedium,histMarkedHighR,histMediumPaid,histNeverPaid,histMediumResidual:reverseResidual-histMediumPaid,histNeverResidual:reverseNeverResidual-histNeverPaid,histDensityR,histDensityGroups,histKeepR,histKeepE,histKeepSyncE,histRecentSyncE,histOldSyncE,histDensityChecks,histExactPairChecks,histMaxRecentRatio,histMarkedHighTags,histKeepHighTags,ageFullPaid,ageFullAsync,ageFullFront,ageFullBack,ageFullBoth,agePairBudget,agePairChecks,ageBands:[...ageBands.entries()],ageExtra,ageExtraAsync,ageExtraFront,ageExtraBack,histEnergyRemoved,histRecentExtra,histFinalResidual,histFinalAsync,histFinalSync,histAgeResidual,ageOraclePairs,ageOracleHits,ageOraclePaid,holeInputR,holeDensityR,holeKeepR,holeE,holeRecent,holeGroups,holeGateGroups,revY,physY,revK,revJ,physK,physJ,revBound,physBound,revChecks,revRootLeaves,revRootMax,revLabelChecks,revSmallChecks,revPhysChecks,revMaxCohorts,revMaxDegree,revDegreeChecks,revFullRootCount,revAnchorMassMax,reversePaid,reverseNeverPaid,reverseResidual,reverseNeverResidual,reversePaidKinds,reverseBlocks,reverseMedGroups,highReverseExtra,highReverseAsync,highReverseKinds,highReverseGroups,highReverseResidual,highReverseChecked,highReverseEligible,reverseControlGroups,relaxChecks,relaxWords,relaxRootWords,relaxMaxRoot,relaxActualRoots,relaxMaxWords,medStats,highStats,windowPaid,windowNeverPaid,windowBlocks,windowRankPaid,windowGapPaid,windowChainPaid,windowReverseOnly,windowSecondScaleOnly,windowExactOnly,endpointPaid,endpointNeverPaid,endpointChecks,endpointMaxDegree,windowResidual,windowNeverResidual,highWindowExtra,highWindowAsync,highWindowRank,highWindowGap,highWindowChain,highWindowReverseOnly,highFactorExtra,highFactorAsync,highFactorStats,weightedMembership,gainControlSamples,gainArithmeticChecks,gainArithmeticMax,gainArithmeticPositive,gainPaid,gainDisjointPaid,gainNeverPaid,gainNeverEdges,gainEdges,gainChecks,gainQueryCount,gainDegreeChecks,gainDegreeMax,gainSampledPairMeasure,gainEnvelope,gainGoodMeasure,gainCoveredKinds,gainCoverChecks,gainMuUnion,gainMuSelected,gainMuEndpoint,gainMaxCoefficient,highRankTotal,highRankPaid,highRankAsync,highRankSync,highRankCohortExtra,highRankCellExtra,highRankMax,highRankChecks,highRankGroups,highRankR,hcap,hqcap,hd,hdcap,extraSamples,X,B,T,Qm,N,literal,Z,big2,d2tick,rank2,keyBound2,degree2,crtChecks,crtOriented,crtSymmetric,crtQueryHits,crtNewTicks,crtPaid,crtEdges,gapBase,entD,entLoss,minorityTotal,gapCaps,gapCounts,gapNewCost,gapNewUnits,gapDeepUnits,postGap:keptWF-gapNewCost,physicalLayers,entryChecks,cohortDegreeChecks,localScoreChecks,localFormationPairs,rootStationaryPairs,cohortImprovedPairs,paidRawLocal,paidCohortOnly,maxCohorts,maxEligibleCohorts,regularCohorts,nearCohorts,sameCohorts,maxLocalScore,localPotentialChecks,paidBand,paidLocal,localOnlyLarge,bandUnits,localUnits,localFar,bandFar,localPairs:localPairSet.size,bandPairs:bandPairSet.size,bandLayerEnvelope,localLayerEnvelope,wfBase,H0,wp,waitingEvents,waitingVertices,waitingRootInjections,waitingExpirations,waitingFirstPairs,stationaryFirstPairs,jumpJumpFirstPairs,rootFirstPairs,rankChecks,queryCountWF,terminalQuery,stationaryQuery,oraclePairs,oracleOnlyCount,oracleRankChecks,oracleTerminal,oracleEarly,oracleNoPhysical,oracleStationary,paidMass,paidRank,keptWF,neverCost,farFuture,farPaid,syncPaid,immediatePaid,paidUnits,massUnits,rankUnits,maxCoefWF,ledgerCost,ledgerBlocks,meetingPairs,neverPairs,farFuturePairs:farFuturePairs.size,paidPairs:paidPairs.size,maxMeetingMass,maxRankWF,farMeetingChecks,largeMassPaid,layerSum,layerMass,layerRank,totalOrientedMassTime,totalSymmetricMassTime,sampledRootTime,degreeTimeEnvelope,allSampledGood,maxEndpointCoefficient,acceptedEndpointCost,occupationEdges:occupationEdges.length,occPaid,occKept,occEdgesPaid,occEdgesKept,occKinds,occCoverChecks,occUnion,occSelectedLength,occEndpointTime,occGoodUnion,occupationChecks,degreeChecksOcc,distinctWaitingChecks,clockChecks,queryTicks,maxActive,maxGroup,maxDegreeOcc,goodTicks,crossingChecks,positiveCrossings,thin,crowd,closeH,nearTick,largeP,wideH,sameJ,etaOcc,actualFinalAfterOccupation:ac.largeAlready+ac.largeImmediate+ac.farDisjointSlow+occKept,totalTime,deltaFinal,crossingRoots,G,R,initialActual,highActual,mediumActual,actualFirst,actualShort,actualLong,fastEdgeCost,fastEdges,rho,unionGain,coverGain,coverTime,endpointTime,coverN,coverRoots,depthChecks,unionChecks,upperDisjointChecks,actualRes,fastResidualCost,slowOverlapChecks,ac,actualFinal:ac.largeAlready+ac.largeImmediate+ac.farDisjointSlow+ac.farOverlapSlow,nearOriginFar,nearOriginChecks,farOriginFar,nearOriginEndpointBound,nearOriginEndpointCost,finalAfterOrigin:farOriginFar+largeAlready+largeImmediate,gapChecks,earlierTransfers,earlierMaxMult,maxLagRatio,fastDisjoint,fastChecks,driftChecks,capChecks,medium,first,short,long,edges,fullPairs,band,cellCost,phaseThin,phaseGroups,phaseChecks2,earlyClose,farDisjoint,farOverlap,farFlip,earlyDegreeChecks,maxPhaseCount,maxElapsed,maxDrift,earlyRefinement,res,tiny,close,far,heavy,already,immediate,smallAlready,smallImmediate,largeAlready,largeImmediate,final:far+largeAlready+largeImmediate,heavyFocal,smallFocal,tinyFocal,groups,keys,cellChecks,degreeChecks,partnerChecks,maxDegree,maxRatio,maxMult,maxKappa,endpointBound,tailChecks,immediateChecks,alreadyPairs,immediatePairs,oracleChecks,oracleLocal,pa,pb};
}

const stress=process.argv.includes("--crt-stress"),gs=process.argv.includes("--gain-stress"),ws=process.argv.includes("--window-stress"),rs=process.argv.includes("--reverse-stress"),hs=process.argv.includes("--ancestry-stress"),bs=process.argv.includes("--birth-stress"),as=process.argv.includes("--anchor-stress"),ms=process.argv.includes("--multi-stress"),ps=process.argv.includes("--precut-stress"),ds=process.argv.includes("--grid-stress"),ss=process.argv.includes("--star-stress"),xs0=process.argv.includes("--prefix-stress"),ts=process.argv.includes("--reset-stress"),ks=process.argv.includes("--threshold-stress"),cs=process.argv.includes("--cover-stress"),es=process.argv.includes("--excursion-stress"),zs=process.argv.includes("--residence-stress"),ys=process.argv.includes("--entropy-stress"),js=process.argv.includes("--joint-residence-stress"),hs0=process.argv.includes("--boundary-hall-stress"),xs=process.argv.slice(2).filter(x=>!x.startsWith("--")).map(Number);for(const mode of (stress||gs||ws||rs||hs||bs||as||ms||ps||ds||ss||xs0||ts||ks||cs||es||zs||ys||js||hs0?["concurrent"]:["short","wide","analytic","phase","stress","broad","concurrent"]))for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode,stress,gs,ws,rs,hs,bs,as,ms,ps,ds,ss,xs0,ts,ks,cs,es,zs,ys,js,hs0)));
