// Derived from multi_anchor audit at d31bbf0f901c. Reproduce: node research/min_prime_root_precontact_cut_audit.mjs
function audit(X,mode,crtStress=false,gainStress=false,windowStress=false,reverseStress=false,ancestryStress=false,birthStress=false,anchorStress=false,multiStress=false,precutStress=false){
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
       tested=true;highReverseEligible+=r;const k=reverseKinds(part,a.M,b.M,m);if(k>=0){highReverseExtra+=r;highReverseKinds[k]+=r;if(a.t!==b.t)highReverseAsync+=r;}else{highReverseResidual+=r;if(young){ageExtra+=r;if(a.t!==b.t)ageExtraAsync+=r;if(front)ageExtraFront+=r;else ageExtraBack+=r;}else{histAgeResidual+=r;if(!a.histKeep||!b.histKeep)histEnergyRemoved+=r;else{const sm=a.M<b.M?a:b,bg=a.M<b.M?b:a;if(a.t===b.t&&!oldCompanion(sm,bg))histRecentExtra+=r;else{histFinalResidual+=r;const q=birthPair(a.M,b.M);q.high+=r;if(a.t===b.t){histFinalSync+=r;q.sync+=r;}else{histFinalAsync+=r;q.async+=r;}}}}}
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
     const f=e.w-e.arc.cap;if(extended&&high&&!trimmed&&!custom)for(const z of e.tags)z.multiUnpaid=e.arc.cap/e.w;ok(f>=-EPS&&f<=e.w+EPS,"joint intersection flow");paidDirect+=f;paidOther+=e.other*f/e.w;
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
 const pcGroups=new Map();let pcShallow=0,pcEligible=0,pcSame=0,pcMixed=0,pcMembership=0,pcDegreeChecks=0,pcDegreeMax=[0,0],pcSlots=0,pcSlotBound=0,pcMaxSlots=0,pcFullHigh=0,pcFullMed=0,pcFullNever=0,pcFullAsync=0,pcPaidHighPairs=0,pcPaidMedDirections=0,pcSameKeys=new Map(),pcSameProducts=0,pcSameHigh=0,pcSameMed=0,pcSameKeyChecks=0,pcIndependent=0,pcHighKinds=[0,0,0,0,0],pcMedKinds=[0,0,0,0,0];
 for(const z of birthPairs.values())if(z.pcHigh>0||z.pcMed>0){
   const C=z.acRefs[0].C,x=pcD*Math.floor((C-B-1)/pcD);if(x<2*z.Mp-2){pcShallow++;continue;}
   z.pcX=x;if(!pcGroups.has(x))pcGroups.set(x,{es:[],map:new Map(),labels:new Map(),edges:new Map(),small:[],cells:new Map()});pcEligible++;
 }
 for(const ar of roots.values())for(const e of ar)if(e.next){
   for(let x=pcD*Math.ceil(e.C/pcD);x<e.next.C;x+=pcD){const g=pcGroups.get(x);if(!g)continue;ok(!g.map.has(e.M),"unique crossing edge");g.es.push(e);g.map.set(e.M,e);pcMembership++;}
 }
 ok(pcMembership<=N*(1+Math.ceil(H/pcD)),"grid membership budget");
 function pcGroup(es){const z={es:es.slice().sort((a,b)=>a.M-b.M),map:new Map(),labels:new Map(),edges:new Map(),small:[]};for(const e of z.es){z.map.set(e.M,e);const p=e.p,id=e.C+":"+p;if(!z.labels.has(p))z.labels.set(p,[]);z.labels.get(p).push(e.M);if(!z.edges.has(id))z.edges.set(id,[]);z.edges.get(id).push(e.M);if(p<=pcY)z.small.push(id);}z.small=[...new Set(z.small)];z.all=z.es.map(e=>e.M);return z;}
 const primesAll=[];for(let p=3;p<=B;p+=2)if(spf[p]===p)primesAll.push(p);
 for(const [x,g] of pcGroups){Object.assign(g,pcGroup(g.es));const cells=new Map();for(const e of g.es){const c=sourceCell(e.M);if(!cells.has(c))cells.set(c,[]);cells.get(c).push(e);}g.cells=new Map([...cells].map(([c,a])=>[c,pcGroup(a)]));
   // For each p, at most one even post-horizon on each CRT side.
   for(const [p,ms] of g.labels){const edges=[...new Set(ms.map(M=>g.map.get(M).C))].sort((a,b)=>a-b);ok(edges.length<=2,"at most two arithmetic crossing slots");if(edges.length===2)ok(edges[1]-edges[0]===2,"same-label opposite-side offset");}
   pcSlots+=g.edges.size;pcSlotBound+=2*primesAll.length;pcMaxSlots=Math.max(pcMaxSlots,g.edges.size);
 }
 function pcKind(g,a,b,m){if(m<=0||a.M===b.M||a.C===b.C||a.next.C===b.next.C)return -1;const key=b.C+":"+b.p;
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
   ok(a&&b&&a.C<=z.pcX&&z.pcX<a.next.C&&b.C<=z.pcX&&z.pcX<b.next.C&&a.next.C<C&&b.next.C<C,"strict prior crossing edges");
   ok(a.C!==b.C&&a.next.C!==b.next.C&&a.C!==b.next.C&&a.next.C!==b.C,"first-contact prior crossing disjoint");
   if(a.p===b.p){ok(Math.abs(a.C-b.C)===2&&Math.abs(a.next.t-b.next.t)>=a.p-2,"same-label prior crossing clock lag");pcSame++;
     const p=a.p,id="PC:"+z.pcX+":"+p,factor=pcD*u/B;
     z.pcKey=makeKey("precut-same",id,factor,{x:z.pcX,p});
     const rec=pcSameKeys.get(id)||{x:z.pcX,p,n:0,med:0,high:0};rec.n++;pcSameKeys.set(id,rec);
   }else pcMixed++;
   const ca=sourceCell(a.M),cb=sourceCell(b.M),mg0=ca===cb?g.cells.get(ca):null;
   const highA=pcKind(g,a,b,pcHighCap),highB=pcKind(g,b,a,pcHighCap);
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
 return {mode,crtStress,gainStress,windowStress,reverseStress,ancestryStress,birthStress,anchorStress,multiStress,precutStress,pcMedLambda,pcMedDegree,pcMedDegreeBudget,pcMedMaxDegree,pcMedFullPaid,pcMedNeverPaid,pcMedDirections,pcMedRatioMax,pcMedAfterRanks,pcD,pcHighCap,pcMedCap,pcY,pcShallow,pcEligible,pcSame,pcMixed,pcMembership,pcDegreeChecks,pcDegreeMax,pcSlots,pcSlotBound,pcMaxSlots,pcFullHigh,pcFullMed,pcFullNever,pcFullAsync,pcPaidHighPairs,pcPaidMedDirections,pcSameProducts,pcSameHigh,pcSameMed,pcSameKeyChecks,pcIndependent,pcHighKinds,pcMedKinds,pcFinalHigh,pcFinalMed,multiLambda,multiDepths,multiMass,multiExpected,multiRootChecks,multiDegreeChecks,multiDegreeMax,multiDegreeBudget,multiRankPairs,multiRankExtra,multiRankAsync,multiRankBefore,multiRankOnlyOld,multiRankOnlyComplex,multiRankOnlySource,multiHighResidual:anchorJointHigh.residual-multiRankExtra,multiAsyncResidual:anchorJointHigh.otherResidual-multiRankAsync,multiStats,multiMoments,multiRedistributionChecks,multiReoptHigh,multiFullPaid,multiPrefixChecks,multiFalsePrior,multiHighAgeZero,ay,aL,anchorJointMed,anchorJointHigh,anchorGainBudget,anchorRootBudget,anchorBlocks,anchorVertices,anchorMaxGain,anchorMaxWait,anchorBarrierChecks,anchorPairChecks,anchorRootPairs,anchorSamePairs,anchorMixedPairs,anchorCompressedPairs,anchorLongSameChecks,anchorSmallContactPairs,anchorSmallPromoted,anchorLocalChecks,anchorLocalReject,anchorLocalPairs,anchorMaxLocalMasks,anchorTagFactor,anchorCompressedFactor,anchorCandidateProducts,anchorMaskProducts,anchorEarlierExcluded,anchorPrefixProducts,anchorEnvelope,anchorCutMedPairs,anchorCutHighPairs,anchorCutHighEnvelope,anchorLocalEnvelopeAtContact,anchorCutKeyChecks,anchorLocalLabelReject,anchorPairGroups,anchorSupportChecks,anchorSupportCount,birthY,birthBaseMed,birthBaseHigh,jointMed,jointHigh,residualBirthCounts,birthControlPairs,birthControlPhys,birthControlNoPhys,birthControlKinds,lowPhaseExceptions,lowPhaseTags,birthPairChecks,birthPhysicalPairs,birthProjectedPairs,birthNoPhysical,birthPriorHigh,birthAfterHigh,birthMaxKeyPairs,birthMaxFullTail,birthTickChecks,birthRootContacts,birthMixed,birthSame,birthRelaxChecks,birthSupportTotal,birthRoughSupportChecks,birthLagStats,physicalPay,projectedPay,birthSummary,birthMedResidual,birthNeverResidual,birthHighResidual,birthSyncResidual,birthAsyncResidual,historyD,historyEps,historyZeta,historyCoef,histGlobalLog,histCellLog,histMarkedGain,histMarkedEvents,histGlobalMarks,histCellOnlyMarks,histMaxCells,histRootChecks,histCutChecks,histGrowthChecks,histMarkedActual,histMarkedMedium,histMarkedHighR,histMediumPaid,histNeverPaid,histMediumResidual:reverseResidual-histMediumPaid,histNeverResidual:reverseNeverResidual-histNeverPaid,histDensityR,histDensityGroups,histKeepR,histKeepE,histKeepSyncE,histRecentSyncE,histOldSyncE,histDensityChecks,histExactPairChecks,histMaxRecentRatio,histMarkedHighTags,histKeepHighTags,ageFullPaid,ageFullAsync,ageFullFront,ageFullBack,ageFullBoth,agePairBudget,agePairChecks,ageBands:[...ageBands.entries()],ageExtra,ageExtraAsync,ageExtraFront,ageExtraBack,histEnergyRemoved,histRecentExtra,histFinalResidual,histFinalAsync,histFinalSync,histAgeResidual,ageOraclePairs,ageOracleHits,ageOraclePaid,holeInputR,holeDensityR,holeKeepR,holeE,holeRecent,holeGroups,holeGateGroups,revY,physY,revK,revJ,physK,physJ,revBound,physBound,revChecks,revRootLeaves,revRootMax,revLabelChecks,revSmallChecks,revPhysChecks,revMaxCohorts,revMaxDegree,revDegreeChecks,revFullRootCount,revAnchorMassMax,reversePaid,reverseNeverPaid,reverseResidual,reverseNeverResidual,reversePaidKinds,reverseBlocks,reverseMedGroups,highReverseExtra,highReverseAsync,highReverseKinds,highReverseGroups,highReverseResidual,highReverseChecked,highReverseEligible,reverseControlGroups,relaxChecks,relaxWords,relaxRootWords,relaxMaxRoot,relaxActualRoots,relaxMaxWords,medStats,highStats,windowPaid,windowNeverPaid,windowBlocks,windowRankPaid,windowGapPaid,windowChainPaid,windowReverseOnly,windowSecondScaleOnly,windowExactOnly,endpointPaid,endpointNeverPaid,endpointChecks,endpointMaxDegree,windowResidual,windowNeverResidual,highWindowExtra,highWindowAsync,highWindowRank,highWindowGap,highWindowChain,highWindowReverseOnly,highFactorExtra,highFactorAsync,highFactorStats,weightedMembership,gainControlSamples,gainArithmeticChecks,gainArithmeticMax,gainArithmeticPositive,gainPaid,gainDisjointPaid,gainNeverPaid,gainNeverEdges,gainEdges,gainChecks,gainQueryCount,gainDegreeChecks,gainDegreeMax,gainSampledPairMeasure,gainEnvelope,gainGoodMeasure,gainCoveredKinds,gainCoverChecks,gainMuUnion,gainMuSelected,gainMuEndpoint,gainMaxCoefficient,highRankTotal,highRankPaid,highRankAsync,highRankSync,highRankCohortExtra,highRankCellExtra,highRankMax,highRankChecks,highRankGroups,highRankR,hcap,hqcap,hd,hdcap,extraSamples,X,B,T,Qm,N,literal,Z,big2,d2tick,rank2,keyBound2,degree2,crtChecks,crtOriented,crtSymmetric,crtQueryHits,crtNewTicks,crtPaid,crtEdges,gapBase,entD,entLoss,minorityTotal,gapCaps,gapCounts,gapNewCost,gapNewUnits,gapDeepUnits,postGap:keptWF-gapNewCost,physicalLayers,entryChecks,cohortDegreeChecks,localScoreChecks,localFormationPairs,rootStationaryPairs,cohortImprovedPairs,paidRawLocal,paidCohortOnly,maxCohorts,maxEligibleCohorts,regularCohorts,nearCohorts,sameCohorts,maxLocalScore,localPotentialChecks,paidBand,paidLocal,localOnlyLarge,bandUnits,localUnits,localFar,bandFar,localPairs:localPairSet.size,bandPairs:bandPairSet.size,bandLayerEnvelope,localLayerEnvelope,wfBase,H0,wp,waitingEvents,waitingVertices,waitingRootInjections,waitingExpirations,waitingFirstPairs,stationaryFirstPairs,jumpJumpFirstPairs,rootFirstPairs,rankChecks,queryCountWF,terminalQuery,stationaryQuery,oraclePairs,oracleOnlyCount,oracleRankChecks,oracleTerminal,oracleEarly,oracleNoPhysical,oracleStationary,paidMass,paidRank,keptWF,neverCost,farFuture,farPaid,syncPaid,immediatePaid,paidUnits,massUnits,rankUnits,maxCoefWF,ledgerCost,ledgerBlocks,meetingPairs,neverPairs,farFuturePairs:farFuturePairs.size,paidPairs:paidPairs.size,maxMeetingMass,maxRankWF,farMeetingChecks,largeMassPaid,layerSum,layerMass,layerRank,totalOrientedMassTime,totalSymmetricMassTime,sampledRootTime,degreeTimeEnvelope,allSampledGood,maxEndpointCoefficient,acceptedEndpointCost,occupationEdges:occupationEdges.length,occPaid,occKept,occEdgesPaid,occEdgesKept,occKinds,occCoverChecks,occUnion,occSelectedLength,occEndpointTime,occGoodUnion,occupationChecks,degreeChecksOcc,distinctWaitingChecks,clockChecks,queryTicks,maxActive,maxGroup,maxDegreeOcc,goodTicks,crossingChecks,positiveCrossings,thin,crowd,closeH,nearTick,largeP,wideH,sameJ,etaOcc,actualFinalAfterOccupation:ac.largeAlready+ac.largeImmediate+ac.farDisjointSlow+occKept,totalTime,deltaFinal,crossingRoots,G,R,initialActual,highActual,mediumActual,actualFirst,actualShort,actualLong,fastEdgeCost,fastEdges,rho,unionGain,coverGain,coverTime,endpointTime,coverN,coverRoots,depthChecks,unionChecks,upperDisjointChecks,actualRes,fastResidualCost,slowOverlapChecks,ac,actualFinal:ac.largeAlready+ac.largeImmediate+ac.farDisjointSlow+ac.farOverlapSlow,nearOriginFar,nearOriginChecks,farOriginFar,nearOriginEndpointBound,nearOriginEndpointCost,finalAfterOrigin:farOriginFar+largeAlready+largeImmediate,gapChecks,earlierTransfers,earlierMaxMult,maxLagRatio,fastDisjoint,fastChecks,driftChecks,capChecks,medium,first,short,long,edges,fullPairs,band,cellCost,phaseThin,phaseGroups,phaseChecks2,earlyClose,farDisjoint,farOverlap,farFlip,earlyDegreeChecks,maxPhaseCount,maxElapsed,maxDrift,earlyRefinement,res,tiny,close,far,heavy,already,immediate,smallAlready,smallImmediate,largeAlready,largeImmediate,final:far+largeAlready+largeImmediate,heavyFocal,smallFocal,tinyFocal,groups,keys,cellChecks,degreeChecks,partnerChecks,maxDegree,maxRatio,maxMult,maxKappa,endpointBound,tailChecks,immediateChecks,alreadyPairs,immediatePairs,oracleChecks,oracleLocal,pa,pb};
}

const stress=process.argv.includes("--crt-stress"),gs=process.argv.includes("--gain-stress"),ws=process.argv.includes("--window-stress"),rs=process.argv.includes("--reverse-stress"),hs=process.argv.includes("--ancestry-stress"),bs=process.argv.includes("--birth-stress"),as=process.argv.includes("--anchor-stress"),ms=process.argv.includes("--multi-stress"),ps=process.argv.includes("--precut-stress"),xs=process.argv.slice(2).filter(x=>!x.startsWith("--")).map(Number);for(const mode of (stress||gs||ws||rs||hs||bs||as||ms||ps?["concurrent"]:["short","wide","analytic","phase","stress","broad","concurrent"]))for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode,stress,gs,ws,rs,hs,bs,as,ms,ps)));
