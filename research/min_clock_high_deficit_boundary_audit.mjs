// High deficit predecessor descent debit and primorial boundary allocations.
function boundaryDebit(uses,B,L,expected,ok,close,P=6,Y=3){
 const pairs=new Map(),keys=new Map(),vertices=new Map(),debitKeys=new Map(),naturalKeys=new Map(),births=new Map(),out={P,Y,raw:0,pos:0,small:0,recent:0,old:0,gridSmall:0,gridRaw:0,gridAllocated:0,gridPositive:0,gridNegative:0,gridLowLabel:0,gridMedLabel:0,gridHighLabel:0,gridMaxMultiplicity:0,gridMaxPairKey:0,gridKeys:0,gridVertices:0,gridThinPaid:0,gridThinResidual:0,gridKeyPaid:0,gridKeyResidual:0,gridGain:0,gridNatural:0,gridDrop:0,gridSmallLabelNatural:0,gridSmallLabelDrop:0,oldNatural:0,oldDrop:0,oldBirthDebit:0,oldAscentDebit:0,oldAscentEnergy:0,oldAscentSmall:0,oldAscentLarge:0,oldAscentKeys:0,oldDropWeight:0,oldAscentWeight:0,oldBirthWeight:0,oldDirectWeight:0,oldAllocated:0,oldMinPost:Infinity,oldMaxCoef:0,checks:0};
 for(const u of uses){
   const A=u.a.P.records,Q=u.b.P.records,i0=A.findIndex((e,i)=>i>u.a.k&&e.C===u.recipient),j0=Q.findIndex((e,i)=>i>u.b.k&&e.C===u.recipient),T=A[i0],V=Q[j0],D=u.d-6,c=u.w*D;
   out.raw+=c;ok(i0>u.a.k&&j0>u.b.k&&T.C===V.C&&T.b===V.b&&T.v===V.v,"actual common target");
   if(2*(T.v-T.b)<=T.p-1)continue;out.pos+=c;
   if(D<2*L){out.small+=c;continue}
   let i=i0,j=j0;while(i>0&&j>0&&A[i-1].C===Q[j-1].C&&A[i-1].b===Q[j-1].b&&A[i-1].v===Q[j-1].v){i--;j--}
   let J=A[i].C,db=2*A[i].b-J,h=Math.ceil(Math.min(T.r/2,D/10)),pk=Math.min(u.a.P.M,u.b.P.M)+','+Math.max(u.a.P.M,u.b.P.M),G=T.C-J;
   if(G<h){out.recent+=c;continue}
   out.old+=c;let a=pairs.get(pk);if(!a){a={pk,ids:pk.split(',').map(Number),J,db,A,i,intervals:[]};pairs.set(pk,a)}
   ok(a.J===J&&a.db===db,"unique first common recorded state");
   a.intervals.push({lo:T.C-h,hi:T.C,r:T.r,D,c,coeff:c/h,A,i,idx:i0,anchor:A[u.a.k].C+A[u.a.k].p-1,anchorD:u.d});
 }
 for(const a of pairs.values()){
   const I=a.intervals,latest=I.reduce((x,y)=>x.idx-x.i>y.idx-y.i?x:y),A=latest.A,i=latest.i,idx=latest.idx;
   const hist=new Map(),birth=new Map(),asc=new Map(),einfo=new Map();
   for(let l=1;l<=a.db;l++)hist.set(l,-1);
   for(let k=i;k<idx;k++){
     const e=A[k],d0=2*e.b-e.C,d1=e.post,delta=Math.max(0,d0-d1);
     ok(hist.size===d0,"recorded level ledger");
     const dead=[];if(d1>d0){for(let l=d0+1;l<=d1;l++)hist.set(l,k)}else if(d1<d0){for(let l=d1+1;l<=d0;l++){ok(hist.has(l),"actual net descent level exists");dead.push({l,origin:hist.get(l)});hist.delete(l)}}
     einfo.set(e.C,{k,e,d0,d1,delta,dead,alpha:0});
   }
   allocateStrips(I,ok);
   for(const t of I){
     let k=t.i;
     for(const part of t.parts){
       while(t.A[k].C+t.A[k].p-1<=part.k)k++;
       const e=t.A[k],p=e.p-1,z=einfo.get(e.C);
       ok(z&&z.e.v===e.v&&k<t.idx,"actual allocated common edge");
       const amount=t.coeff*part.n,alpha=amount/p;
       z.alpha+=alpha;
       ok(e.post>=6+t.D/2-1e-7,"high deficit post of every allocated edge");
       out.oldMinPost=Math.min(out.oldMinPost,e.post);out.oldAllocated+=amount;out.checks++;
       if(z.delta>0){for(const d of z.dead){
         ok(d.l>6+t.D/2,"matched descent is above high floor");
         if(d.origin<0){ok(d.l<=a.db&&a.db>6+t.D/2,"high birth debit");birth.set(d.l,(birth.get(d.l)||0)+alpha);}
         else {ok(d.origin<z.k,"strictly earlier ascent");let v=asc.get(d.origin);if(!v){v=new Map();asc.set(d.origin,v)}v.set(d.l,(v.get(d.l)||0)+alpha);if(A[d.origin].p<t.r/4)out.oldAscentSmall+=alpha;else out.oldAscentLarge+=alpha;}
       }}
     }
   }
   for(const z of einfo.values())if(z.alpha>0){
     const e=z.e,w=e.v-e.b,n=w*w/(2*e.r);ok(z.alpha<=48+1e-7,"constant gain density");
     out.oldMaxCoef=Math.max(out.oldMaxCoef,z.alpha);out.oldNatural+=n;out.oldDrop+=z.delta;
     out.oldDirectWeight+=12*z.alpha*n;out.oldDropWeight+=z.alpha*z.delta;
     ok(e.p-1<=12*n+2*z.delta+1e-7,"gain coercivity");
   }
   for(const [l,w] of birth){ok(w<=48+1e-7,"unique consumed birth level");out.oldBirthWeight+=w}
   if(birth.size){out.oldBirthDebit+=Math.max(0,a.db-6);births.set(a.pk,a.db)}
   for(const [k,ls] of asc){const e=A[k],w=e.v-e.b,net=e.post-(2*e.b-e.C),n=w*w/(2*e.r);ok(net>0&&net<=3*n+1e-7&&ls.size<=net,"positive net ascent budget");
     out.oldAscentDebit+=net;out.oldAscentEnergy+=n;out.oldAscentKeys++;
     for(const [l,wt] of ls){ok(wt<=48+1e-7&&l>2*e.b-e.C&&l<=e.post,"unique consumed ascent level");out.oldAscentWeight+=wt}
   }
   // Independently allocate each sufficiently long strip to primorial
   // boundary crossings, with capacity three rather than two per boundary.
   const grid=I.filter(t=>{if(t.hi-t.lo<4*P){out.gridSmall+=t.c;return false}out.gridRaw+=t.c;return true}).sort((a,b)=>a.hi-b.hi),use=new Map(),perBoundary=new Map(),perEdge=new Map();
   for(const t of grid){
     const n=Math.floor((t.hi-t.lo)/P),coef=t.c/n;let left=n;
     ok(coef<=32*P+1e-7,"boundary charge density");
     for(let K=Math.ceil(t.lo/P)*P;K<t.hi&&left;K+=P){
       let m=Math.min(left,3-(use.get(K)||0));if(!m)continue;
       use.set(K,(use.get(K)||0)+m);out.gridMaxMultiplicity=Math.max(out.gridMaxMultiplicity,use.get(K));left-=m;
       let k=t.i;while(t.A[k].C+t.A[k].p-1<=K)k++;
       let e=t.A[k],q=e.p,amount=m*coef;
       ok(k<t.idx&&e.C<=K&&K<e.C+q-1&&q>Y&&K%P===0,"actual nonLOW boundary crossing");
       ok((e.C+2*(e.v%2)-1)%q===0&&(e.v-2*(e.v%2))%q===0&&e.post>=6+t.D/2,"high deficit boundary phase");
       let key=K+','+e.C+','+e.b+','+e.v+','+q,pe=e.C+','+e.b+','+e.v;
       perBoundary.set(key,(perBoundary.get(key)||0)+amount);
       if(!perEdge.has(pe))perEdge.set(pe,{e,n:0});perEdge.get(pe).n+=amount;
       out.gridAllocated+=amount;if(e.post>2*e.b-e.C)out.gridPositive+=amount;else out.gridNegative+=amount;
       if(q<P)out.gridLowLabel+=amount;else if(q<=B/4)out.gridMedLabel+=amount;else out.gridHighLabel+=amount;
     }
     ok(left===0,"capacity-three greedy grid allocation");
   }
   for(const [key,w] of perBoundary){ok(w<=96*P+1e-7,"pair boundary weight cap");out.gridMaxPairKey=Math.max(out.gridMaxPairKey,w);keys.set(key,(keys.get(key)||0)+w);for(const M of a.ids){const v=M+'|'+key;vertices.set(v,(vertices.get(v)||0)+w)}}
   for(const {e,n} of perEdge.values()){
     let g=e.p-1,w=e.v-e.b,en=w*w/(2*e.r),d=Math.max(0,g-2*w);
     ok(n<=96*(g+P)+1e-7,"boundary gain envelope");out.gridGain+=g;out.gridNatural+=en;out.gridDrop+=d;
     if(e.p<P){out.gridSmallLabelNatural+=en;out.gridSmallLabelDrop+=d}
   }
 }
 for(const [k,w] of keys){let p=Math.min(w,8*P);out.gridKeyPaid+=p;out.gridKeyResidual+=w-p}
 // Independent one-sided thin-role diagnostic, count each pair once by its smaller source.
 const thin=new Map(); // use both sides to bound the payment, not double count actual paid weight
 let sum=0;for(const w of vertices.values())sum+=w;
 out.gridKeys=keys.size;out.gridVertices=vertices.size;
 ok(close(sum,2*out.gridRaw),"boundary source membership moment");
 ok(close(out.raw,expected)&&close(out.pos,out.small+out.old+out.recent)&&close(out.old,out.gridSmall+out.gridRaw)&&close(out.gridRaw,out.gridAllocated)&&close(out.gridRaw,out.gridPositive+out.gridNegative)&&close(out.gridRaw,out.gridLowLabel+out.gridMedLabel+out.gridHighLabel)&&close(out.gridRaw,out.gridKeyPaid+out.gridKeyResidual),"boundary ledger");
 ok(close(out.old,out.oldAllocated)&&close(out.oldDropWeight,out.oldBirthWeight+out.oldAscentWeight)&&out.old<=out.oldDirectWeight+2*out.oldDropWeight+1e-5&&out.oldAscentWeight<=48*3*out.oldAscentEnergy+1e-6&&out.oldBirthWeight<=48*out.oldBirthDebit+1e-6,"strict prior ascent and birth debit");
 if(!Number.isFinite(out.oldMinPost))out.oldMinPost=null;
 return out;
}
// Positive rough target common-recorded-birth and backward gain strip audit.
function prefixAudit(uses,B,expected,ok,close,eta=1/4){
 const z={eta,raw:0,positive:0,low:0,old:0,recent:0,oldNatural:0,oldDrop:0,oldPositiveGain:0,oldNonpositiveGain:0,oldSmallGain:0,oldLargeGain:0,oldMass:0,recentBirth:0,recentNonTop:0,recentTop:0,recentNonTopBirth:0,recentTopBirth:0,checks:0,oldCount:0,recentCount:0,lowCount:0,maxBirthGain:0,maxBandOverlap:0,maxOverlap:0,maxRecentSum:0,maxNonTopSum:0,stripLength:0,keys:0,topCut:B/2,lowNatural:0,oldKeys:0,earliestBirths:0};
 const pairs=new Map(),strips=new Map(),upstream=new Map(),slots=new Map();
 // Use integer strip length h=ceil(eta*r/16); with rounding,
 // the exact recent high-birth comparison includes +5 and is checked below.
 for(const u of uses){
   const A=u.a.P.records,Q=u.b.P.records,idx=A.findIndex((e,i)=>i>u.a.k&&e.C===u.recipient),jdx=Q.findIndex((e,i)=>i>u.b.k&&e.C===u.recipient),T=A[idx],V=Q[jdx];
   ok(idx>u.a.k&&jdx>u.b.k&&T.C===V.C&&T.b===V.b&&T.v===V.v,"actual target");
   const r=T.r,w=T.v-T.b,p=T.p,delta=2*w-(p-1),D=u.d-6,x=u.w*B/r,c=u.w*D;
   z.raw+=c;if(delta<=0)continue;z.positive+=c;
   const pk=Math.min(u.a.P.M,u.b.P.M)+','+Math.max(u.a.P.M,u.b.P.M),key=pk+'|'+T.C;
   ok(!strips.has(key),"distinct pair target");strips.set(key,1);
   let i=idx,j=jdx;
   while(i>0&&j>0&&A[i-1].C===Q[j-1].C&&A[i-1].b===Q[j-1].b&&A[i-1].v===Q[j-1].v){i--;j--;}
   const S=A[i],S1=Q[j],J=S.C,t=S.b,db=2*t-J,G=T.C-J;
   ok(S.C===S1.C&&S.b===S1.b&&S.v===S1.v&&i<=u.a.k+1&&j<=u.b.k+1,"actual common recorded start");
   // u.F is the actual first physical contact. No previous shared recorded state
   // can be before that contact. The first common recorded state is either F or
   // the next event after F (possibly the end of a differing-arrival wait).
   ok(t>=u.F.t&&(t===u.F.t||A[i-1].v===t&&Q[j-1].v===t),"first common recorded state after true contact");
   if(t>u.F.t)ok(i>0&&j>0&&A[i-1].C===u.F.C&&Q[j-1].C===u.F.C&&Math.max(A[i-1].b,Q[j-1].b)===u.F.t,"first shared recorded departure");
   if(!pairs.has(pk))pairs.set(pk,{J,t,db,top:0,nontop:0,charge:0,topCharge:0,nonTopCharge:0,intervals:[]});
   const a=pairs.get(pk);ok(a.J===J&&a.t===t&&a.db===db,"unique pair recorded birth");z.checks++;z.maxBirthGain=Math.max(z.maxBirthGain,G);
   const sk=T.C+','+T.b+','+T.v;if(!slots.has(sk))slots.set(sk,{C:T.C,b:T.b,v:T.v,r,p,w,raw:0,old:0,recent:0,low:0,birthMin:Infinity,birthMax:0,gapMin:Infinity,gapMax:0,pairs:0});
   const s=slots.get(sk);s.raw+=c;s.pairs++;s.birthMin=Math.min(s.birthMin,db);s.birthMax=Math.max(s.birthMax,db);s.gapMin=Math.min(s.gapMin,G);s.gapMax=Math.max(s.gapMax,G);
   const e=w*w/(2*r);
   if(D<=eta*B){z.low+=c;z.lowCount++;s.low+=c;z.lowNatural+=x*e;ok(c<=18*eta*x*e+1e-7,"low anchor deficit transfer");continue}
   const h=Math.max(1,Math.ceil(eta*r/16));
   if(G<h){
     const anchor=A[u.a.k].C+A[u.a.k].p-1;
     ok(anchor>=J&&anchor<=T.C&&u.d-db<=5*(anchor-J)&&D>eta*B,"recent common birth deficit");
     ok(D<=db+5*G&&db>=(11/16)*eta*B-5,"recent high birth");
     // G<h and G integer imply G<eta*r/16 (ceil); so no rounding loss.
     ok(D<=db+5*eta*r/16&&D<=16/11*db+1e-7,"birth-relative charge");
     z.recent+=c;s.recent+=c;z.recentCount++;a.charge+=c;
     if(r<=B/2){a.nontop+=r/B;a.nonTopCharge+=c;z.recentNonTop+=c}
     else{a.top+=r/B;a.topCharge+=c;z.recentTop+=c}
     continue
   }
   z.old+=c;s.old+=c;z.oldCount++;z.stripLength+=h;
   const lo=T.C-h,hi=T.C,band=Math.floor(Math.log2(r)),coeff=c/h;
   ok(lo>=J&&coeff<=192/eta+1e-7,"old backward strip density");
   a.intervals.push({lo,hi,band,r});
   let covered=0;for(let k=i;k<idx;k++){
     const E=A[k],F=Q[j+k-i],g=E.p-1,H=E.C+g;
     ok(E.C===F.C&&E.b===F.b&&E.v===F.v&&E.p===F.p,"actual upstream shared edge");
     const l=Math.max(lo,E.C),v=Math.min(hi,H),n=Math.max(0,v-l);if(!n)continue;
     covered+=n;const f=n/g,ee=(E.v-E.b)**2/(2*E.r),dd=Math.max(0,g-2*(E.v-E.b));
     ok(g<=12*ee+2*dd+1e-7,"upstream selected gain coercivity");
     z.oldMass+=coeff*n;
     if(E.post>2*E.b-E.C)z.oldPositiveGain+=coeff*n;else z.oldNonpositiveGain+=coeff*n;
     if(E.p<r/4)z.oldSmallGain+=coeff*n;else z.oldLargeGain+=coeff*n;
     let k0=pk+'|'+E.C,up=upstream.get(k0);if(!up){up={g,ee,dd,weight:0,parts:[]};upstream.set(k0,up)}ok(up.g===g&&close(up.ee,ee)&&up.dd===dd,"unique upstream physical pair edge");
     up.weight+=f;up.parts.push({lo:l,hi:v,band});
   }
   ok(covered===h,"backward strip exactly covered");
 }
 for(const a of pairs.values()){
   z.maxRecentSum=Math.max(z.maxRecentSum,a.top+a.nontop);z.maxNonTopSum=Math.max(z.maxNonTopSum,a.nontop);
   ok(a.charge<=16/11*a.db*(a.top+a.nontop)+1e-6&&a.nonTopCharge<=16/11*a.db*a.nontop+1e-6,"recent birth total");
   // All recent target starts lie in [J,J+eta B/16). Their outgoing gains
   // are disjoint; except last, they are inside that interval.
   ok(a.top+a.nontop<=1.5*eta/16+1+1e-7,"recent gain packing");
   ok(a.nontop<=1.5*eta/32+.5+1e-7,"non-top recent gain packing");
   if(a.charge){z.recentBirth+=a.db;z.recentNonTopBirth+=a.nonTopCharge>0?a.db:0;z.recentTopBirth+=a.topCharge>0?a.db:0;z.earliestBirths++}
   let events=[];for(const I of a.intervals)events.push([I.lo,1,I.band],[I.hi,-1,I.band]);
   events.sort((a,b)=>a[0]-b[0]||a[1]-b[1]);let active=0,by=new Map();
   for(const [t,s,b] of events){active+=s;by.set(b,(by.get(b)||0)+s);z.maxBandOverlap=Math.max(z.maxBandOverlap,by.get(b));z.maxOverlap=Math.max(z.maxOverlap,active);ok(by.get(b)<=1,"disjoint same dyadic band strips")}
 }
 for(const u of upstream.values()){
   ok(u.weight<=z.maxOverlap+1e-7,"upstream strip multiplicity");
   z.oldNatural+=u.ee;z.oldDrop+=u.dd;
 }
 z.keys=slots.size;z.oldKeys=upstream.size;
 ok(close(z.raw,expected)&&close(z.positive,z.low+z.old+z.recent)&&close(z.old,z.oldMass)&&close(z.old,z.oldPositiveGain+z.oldNonpositiveGain)&&close(z.old,z.oldSmallGain+z.oldLargeGain)&&close(z.recent,z.recentNonTop+z.recentTop),"complete prefix ledger");
 ok(z.old<=192/eta*z.maxOverlap*(12*z.oldNatural+2*z.oldDrop)+1e-6,"old upstream transport");
 return {...z,details:[...slots.values()]};
}
function allocateStrips(I,ok){
 const sorted=I.slice().sort((a,b)=>a.hi-b.hi),use=new Map();let sum=0,union=0,end=-Infinity,max=0;
 for(const a of sorted){
   ok(a.hi>a.lo&&a.hi-a.lo<=Math.ceil(a.r/2),"strip length");
   sum+=a.hi-a.lo;
 }
 for(let i=1;i<sorted.length;i++)ok(sorted[i].hi>=sorted[i-1].hi+sorted[i-1].r-1,"disjoint forward target gains");
 for(const a of I.slice().sort((a,b)=>a.lo-b.lo)){
   union+=Math.max(0,a.hi-Math.max(a.lo,end));end=Math.max(end,a.hi);
 }
 ok(sum<=2*union,"backward strip union packing");
 for(const a of sorted){
   let need=a.hi-a.lo;a.parts=[];
   for(let k=a.lo;k<a.hi&&need;k++){
     let n=Math.min(need,2-(use.get(k)||0));if(!n)continue;
     use.set(k,(use.get(k)||0)+n);max=Math.max(max,use.get(k));need-=n;a.parts.push({k,n});
   }
   ok(need===0,"capacity-two interval allocation");
 }
 return {sum,union,max};
}
function adaptiveAudit(uses,B,expected,ok,close){
 const z={raw:0,positive:0,low:0,old:0,recent:0,oldNatural:0,oldDrop:0,oldPositiveGain:0,oldNonpositiveGain:0,oldSmallGain:0,oldLargeGain:0,oldMass:0,recentBirth:0,recentNonTop:0,recentTop:0,recentNonTopBirth:0,recentTopBirth:0,checks:0,oldCount:0,recentCount:0,lowCount:0,maxBirthGain:0,maxBandOverlap:0,maxOverlap:0,maxRecentSum:0,maxNonTopSum:0,stripLength:0,keys:0,topCut:B/2,lowNatural:0,oldKeys:0,earliestBirths:0};
 const pairs=new Map(),strips=new Map(),upstream=new Map(),slots=new Map();let packed=0,union=0,maxAllocated=0,allocationCharge=0,allocPositive=0,allocNonpositive=0,allocSmall=0,allocLarge=0,allocNatural=0,allocDrop=0;
 // Adaptive strip length ceil(min(r/2,D/10)); a recent birth has D<2*d_birth.
 for(const u of uses){
   const A=u.a.P.records,Q=u.b.P.records,idx=A.findIndex((e,i)=>i>u.a.k&&e.C===u.recipient),jdx=Q.findIndex((e,i)=>i>u.b.k&&e.C===u.recipient),T=A[idx],V=Q[jdx];
   ok(idx>u.a.k&&jdx>u.b.k&&T.C===V.C&&T.b===V.b&&T.v===V.v,"actual target");
   const r=T.r,w=T.v-T.b,p=T.p,delta=2*w-(p-1),D=u.d-6,x=u.w*B/r,c=u.w*D;
   z.raw+=c;if(delta<=0)continue;z.positive+=c;
   const pk=Math.min(u.a.P.M,u.b.P.M)+','+Math.max(u.a.P.M,u.b.P.M),key=pk+'|'+T.C;
   ok(!strips.has(key),"distinct pair target");strips.set(key,1);
   let i=idx,j=jdx;
   while(i>0&&j>0&&A[i-1].C===Q[j-1].C&&A[i-1].b===Q[j-1].b&&A[i-1].v===Q[j-1].v){i--;j--;}
   const S=A[i],S1=Q[j],J=S.C,t=S.b,db=2*t-J,G=T.C-J;
   ok(S.C===S1.C&&S.b===S1.b&&S.v===S1.v&&i<=u.a.k+1&&j<=u.b.k+1,"actual common recorded start");
   // u.F is the actual first physical contact. No previous shared recorded state
   // can be before that contact. The first common recorded state is either F or
   // the next event after F (possibly the end of a differing-arrival wait).
   ok(t>=u.F.t&&(t===u.F.t||A[i-1].v===t&&Q[j-1].v===t),"first common recorded state after true contact");
   if(t>u.F.t)ok(i>0&&j>0&&A[i-1].C===u.F.C&&Q[j-1].C===u.F.C&&Math.max(A[i-1].b,Q[j-1].b)===u.F.t,"first shared recorded departure");
   if(!pairs.has(pk))pairs.set(pk,{J,t,db,top:0,nontop:0,charge:0,topCharge:0,nonTopCharge:0,intervals:[]});
   const a=pairs.get(pk);ok(a.J===J&&a.t===t&&a.db===db,"unique pair recorded birth");z.checks++;z.maxBirthGain=Math.max(z.maxBirthGain,G);
   const sk=T.C+','+T.b+','+T.v;if(!slots.has(sk))slots.set(sk,{C:T.C,b:T.b,v:T.v,r,p,w,raw:0,old:0,recent:0,low:0,birthMin:Infinity,birthMax:0,gapMin:Infinity,gapMax:0,pairs:0});
   const s=slots.get(sk);s.raw+=c;s.pairs++;s.birthMin=Math.min(s.birthMin,db);s.birthMax=Math.max(s.birthMax,db);s.gapMin=Math.min(s.gapMin,G);s.gapMax=Math.max(s.gapMax,G);
   const e=w*w/(2*r);
   if(D<=0){z.low+=c;z.lowCount++;s.low+=c;z.lowNatural+=x*e;ok(c<=18*eta*x*e+1e-7,"low anchor deficit transfer");continue}
   const h=Math.max(1,Math.ceil(Math.min(r/2,D/10)));
   if(G<h){
     const anchor=A[u.a.k].C+A[u.a.k].p-1;
     ok(anchor>=J&&anchor<=T.C&&u.d-db<=5*(anchor-J)&&D>0,"recent common birth deficit");
     ok(D<=db+5*G&&db>D/2,'adaptive recent high birth');
     // Integer G<h implies G<min(r/2,D/10), so no rounding loss.
     ok(D<=2*db+1e-7,'adaptive birth-relative charge');
     z.recent+=c;s.recent+=c;z.recentCount++;a.charge+=c;
     if(r<=B/2){a.nontop+=r/B;a.nonTopCharge+=c;z.recentNonTop+=c}
     else{a.top+=r/B;a.topCharge+=c;z.recentTop+=c}
     continue
   }
   z.old+=c;s.old+=c;z.oldCount++;z.stripLength+=h;
   const lo=T.C-h,hi=T.C,band=Math.floor(Math.log2(r)),coeff=c/h;
   ok(lo>=J&&coeff<=24+1e-7,"old backward strip density");
   a.intervals.push({lo,hi,band,r,c,coeff,A,i,idx,pk});
   let covered=0;for(let k=i;k<idx;k++){
     const E=A[k],F=Q[j+k-i],g=E.p-1,H=E.C+g;
     ok(E.C===F.C&&E.b===F.b&&E.v===F.v&&E.p===F.p,"actual upstream shared edge");
     const l=Math.max(lo,E.C),v=Math.min(hi,H),n=Math.max(0,v-l);if(!n)continue;
     covered+=n;const f=n/g,ee=(E.v-E.b)**2/(2*E.r),dd=Math.max(0,g-2*(E.v-E.b));
     ok(g<=12*ee+2*dd+1e-7,"upstream selected gain coercivity");
     z.oldMass+=coeff*n;
     if(E.post>2*E.b-E.C)z.oldPositiveGain+=coeff*n;else z.oldNonpositiveGain+=coeff*n;
     if(E.p<r/4)z.oldSmallGain+=coeff*n;else z.oldLargeGain+=coeff*n;
     let k0=pk+'|'+E.C,up=upstream.get(k0);if(!up){up={g,ee,dd,weight:0,parts:[]};upstream.set(k0,up)}ok(up.g===g&&close(up.ee,ee)&&up.dd===dd,"unique upstream physical pair edge");
     up.weight+=f;up.parts.push({lo:l,hi:v,band});
   }
   ok(covered===h,"backward strip exactly covered");
 }
 for(const a of pairs.values()){
   z.maxRecentSum=Math.max(z.maxRecentSum,a.top+a.nontop);z.maxNonTopSum=Math.max(z.maxNonTopSum,a.nontop);
   ok(a.charge<=2*a.db*(a.top+a.nontop)+1e-6&&a.nonTopCharge<=2*a.db*a.nontop+1e-6,"recent birth total");
   // All recent target starts lie in [J,J+B/2). Their outgoing gains
   // are disjoint; except last, they are inside that interval.
   ok(a.top+a.nontop<=1.75+1e-7,"recent gain packing");
   ok(a.nontop<=.875+1e-7,"non-top recent gain packing");
   if(a.charge){z.recentBirth+=a.db;z.recentNonTopBirth+=a.nonTopCharge>0?a.db:0;z.recentTopBirth+=a.topCharge>0?a.db:0;z.earliestBirths++}
   const pack=allocateStrips(a.intervals,ok);packed+=pack.sum;union+=pack.union;maxAllocated=Math.max(maxAllocated,pack.max);
   for(const I of a.intervals){let k=I.i;for(const part of I.parts){while(I.A[k].C+I.A[k].p-1<=part.k)k++;let e=I.A[k],gain=e.p-1;ok(k<I.idx&&e.C<=part.k&&part.k<e.C+gain,'allocated earlier actual edge');let c=I.coeff*part.n;allocationCharge+=c;if(e.post>2*e.b-e.C)allocPositive+=c;else allocNonpositive+=c;if(e.p<I.r/4)allocSmall+=c;else allocLarge+=c;let u=upstream.get(I.pk+'|'+e.C);ok(u,'allocated supporting edge');u.allocated=(u.allocated||0)+part.n;}}
   let events=[];for(const I of a.intervals)events.push([I.lo,1,I.band],[I.hi,-1,I.band]);
   events.sort((a,b)=>a[0]-b[0]||a[1]-b[1]);let active=0,by=new Map();
   for(const [t,s,b] of events){active+=s;by.set(b,(by.get(b)||0)+s);z.maxBandOverlap=Math.max(z.maxBandOverlap,by.get(b));z.maxOverlap=Math.max(z.maxOverlap,active);ok(by.get(b)<=1,"disjoint same dyadic band strips")}
 }
 for(const u of upstream.values()){
   ok(u.weight<=z.maxOverlap+1e-7&&(!u.allocated||u.allocated<=2*u.g),'upstream allocated capacity');if(u.allocated){allocNatural+=u.ee;allocDrop+=u.dd;}
   z.oldNatural+=u.ee;z.oldDrop+=u.dd;
 }
 z.keys=slots.size;z.oldKeys=upstream.size;
 ok(close(z.raw,expected)&&close(z.positive,z.low+z.old+z.recent)&&close(z.old,z.oldMass)&&close(z.old,z.oldPositiveGain+z.oldNonpositiveGain)&&close(z.old,z.oldSmallGain+z.oldLargeGain)&&close(z.recent,z.recentNonTop+z.recentTop),"complete prefix ledger");
 ok(close(allocationCharge,z.old)&&close(allocPositive+allocNonpositive,z.old)&&close(allocSmall+allocLarge,z.old)&&z.old<=48*(12*allocNatural+2*allocDrop)+1e-6,'constant old upstream transport');
 return {...z,packed,union,maxAllocated,allocationCharge,allocPositive,allocNonpositive,allocSmall,allocLarge,allocNatural,allocDrop,details:[...slots.values()]};
}
// Rough target RESET/nonreset and near-neutral entry phase audit.
function targetPhaseAudit(uses,X,B,L,y,rr,expected,ok,close){
 const epsilons=[1/16,1/4,1/2],bands=epsilons.map(eps=>({eps,raw:0,strong:0,near:0,strongDrop:0,nearNatural:0,nearKeys:new Map(),minWait:Infinity}));
 const R=Math.max(y+1,Math.ceil(B/16)),keys=new Set(),records=new Map(),pairR=new Map();
 let raw=0,pos=0,reset=0,resetDrop=0,resetError=0,nonreset=0,nonresetDrop=0,nonresetSurvive=0,nonresetTail=0,nearPost=0,lowLoss=0,consumed=0,surviving=0,resetCount=0,nonresetCount=0,maxPhase=0,maxRatio=0,zero=0,lowResetPos=0,checkCount=0;
 for(const u of uses){
   const A=u.a.P.records,Q=u.b.P.records,idx=A.findIndex((e,i)=>i>u.a.k&&e.C===u.recipient),idx2=Q.findIndex((e,i)=>i>u.b.k&&e.C===u.recipient);
   ok(idx>u.a.k&&idx2>u.b.k,"actual recipient recorded slot");
   const T=A[idx],U=Q[idx2],q=A[idx-1].p,p=T.p,r=T.r,b=T.b,v=T.v,C=T.C,side=v%2,side0=b%2,w=v-b,d0=2*b-C,d1=T.post,delta=Math.max(0,d0-d1),a=u.d,x=u.w*B/r,c=u.w*(a-6);
   ok(T.C===U.C&&T.b===U.b&&T.v===U.v&&T.p===U.p&&q===Q[idx2-1].p&&q<=y&&q<r&&r>=R,"common target with LOW incoming label");
   ok((C+2*side-1)%p===0&&(v-2*side)%p===0&&(C+2*side0)%q===0&&(b-2*side0)%q===0,"both event congruences");
   const phase=(d1-6*side)/(2*p);ok(Number.isInteger(phase)&&phase>=0,"outgoing post phase");
   const J0=A[u.a.k].C+A[u.a.k].p-1,gain=C-J0;
   ok(gain>=2&&gain<L&&A.slice(u.a.k+1,idx).every(e=>e.p<=y)&&a-d0<=gain,"actual LOW tail net loss");
   let mu=a;for(let i=u.a.k+1;i<idx;i++)mu=Math.min(mu,A[i].post);
   const lowN=a-Math.max(6,mu),surv=Math.max(0,mu-6),endSurv=Math.min(surv,Math.max(0,d1-6)),dead=surv-endSurv;
   ok(lowN<=gain&&dead<=delta&&lowN+dead+endSurv===a-6,"LOW and target level survival");
   const pair=Math.min(u.a.P.M,u.b.P.M)+','+Math.max(u.a.P.M,u.b.P.M),key=C+','+b+','+v+','+p+','+q;
   ok(!keys.has(pair+'|'+key),"unique pair-target incidence");keys.add(pair+'|'+key);pairR.set(pair,(pairR.get(pair)||0)+r/B);
   if(!records.has(key))records.set(key,{C,b,v,p,q,r,phase,w,delta,charge:0,pairs:0});
   let rec=records.get(key);rec.charge+=c;rec.pairs++;
   raw+=c;lowLoss+=u.w*lowN;consumed+=u.w*dead;surviving+=u.w*endSurv;checkCount++;
   if(d1>d0){pos+=c;if(!phase)lowResetPos+=c;continue}
   if(d1===d0)zero+=c;
   if(phase===0){
     reset+=c;resetCount++;resetDrop+=x*delta;resetError+=u.w*gain;
     ok(c<=x*delta+u.w*gain+1e-7&&endSurv===0,"reset target direct drop transfer");
     continue;
   }
   nonreset+=c;nonresetCount++;nonresetDrop+=u.w*delta;nonresetSurvive+=u.w*Math.max(0,d1-6);nonresetTail+=u.w*gain;maxPhase=Math.max(maxPhase,phase);
   ok(d1>=2*p&&c<=u.w*(delta+Math.max(0,d1-6)+gain)+1e-7,"nonreset phase decomposition");
   for(const z of bands){
     z.raw+=c;
     if(delta>z.eps*(p-1)){
       z.strong+=c;z.strongDrop+=x*delta;
       ok(c<=18/z.eps*x*delta+1e-7,"strong descent transfer");
     }else{
       z.near+=c;z.nearNatural+=x*w*w/(2*r);
       ok(w>=(1-z.eps)*(p-1)/2-1e-7&&b>=v-(p-1)/2-1e-7&&b<=v-(1-z.eps)*(p-1)/2+1e-7,"near neutral entry interval");
       z.minWait=Math.min(z.minWait,w/r);
       if(!z.nearKeys.has(key))z.nearKeys.set(key,{...rec,charge:0,pairs:0});
       const k=z.nearKeys.get(key);k.charge+=c;k.pairs++;
       ok(c<=216/(1-z.eps)**2*x*w*w/(2*r)+1e-7,"near-neutral occupation transfer");
     }
   }
 }
 for(const w of pairR.values())ok(w<=1.5*(12*B+6)/B+1e-7,"pair target gain");
 ok(close(raw,expected)&&close(raw,pos+reset+nonreset)&&close(raw,lowLoss+consumed+surviving)&&reset<=resetDrop+resetError+1e-7,"complete target classification");
 // Relaxed support for realized (incoming q,outgoing p) pairs. Counts over
 // the entire horizon range, retaining actual roughness but not MIN selection.
 const out=bands.map(z=>{
   const pp=new Map();let paid=0,remain=0,support=0,full=0;
   for(const e of z.nearKeys.values()){let k=e.q+','+e.p;pp.set(k,(pp.get(k)||0)+1);let h=Math.min(e.charge,8*e.q);paid+=h;remain+=e.charge-h;if(h===e.charge)full++}
   for(const [key,n] of pp){
     const [q,p]=key.split(',').map(Number);let count=0;
     for(let C=2*X-2;C<7*X;C+=2){
       if(rr(C)<R)continue;
       for(let s=0;s<2;s++){
         if((C+2*s-1)%p!==0)continue;
         const res=s?p+2:0,lo=Math.ceil((C+p-1+2*p)/2),hi=Math.floor((C+p-1+12*B+6)/2);
         for(let v=res+2*p*Math.ceil((lo-res)/(2*p));v<=hi;v+=2*p){
           const d=2*v-(C+p-1);if(d<2*p)continue;
           for(let k=0;k<2;k++){
             if((C+2*k)%q!==0)continue;
             const rho=k?q+2:0,a=Math.ceil(v-(p-1)/2),b=Math.floor(v-(1-z.eps)*(p-1)/2);
             count+=Math.max(0,Math.floor((b-rho)/(2*q))-Math.ceil((a-rho)/(2*q))+1);
           }
         }
       }
     }
     ok(n<=count,"actual near neutral tuple support");support+=count;
   }
   ok(close(z.raw,z.strong+z.near)&&close(z.near,paid+remain),"phase band ledger");
   return {eps:z.eps,raw:z.raw,strong:z.strong,near:z.near,strongDrop:z.strongDrop,nearNatural:z.nearNatural,minWait:Number.isFinite(z.minWait)?z.minWait:null,keys:z.nearKeys.size,support,paid,remain,full,details:[...z.nearKeys.values()]};
 });
 return {R,L,y,raw,pos,reset,resetDrop,resetError,nonreset,nonresetDrop,nonresetSurvive,nonresetTail,lowLoss,consumed,surviving,resetCount,nonresetCount,maxPhase,zero,lowResetPos,checkCount,targets:records.size,bands:out,details:[...records.values()]};
}
// Unified donor ascent/inherited episode exits; bounded per-pair storage.
function exitAudit(uses,B,expected,ok,close){
 const byPair=new Map(),thin=[new Map(),new Map()],sourcePaths=new Map(),U=27,H=8;
 let target={raw:0,rMass:0,natural:0,drop:0,pos:0,nonpos:0,zero:0,short:0,keys:0,maxRatio:0},targets=new Set();
 let matched=0,terminal=0,matchedShared=0,matchedInherited=0,terminalShared=0,terminalInherited=0,raw=0,low=0,near=0,checks=0,literal=0,netCap=0,terminalCap=0,maxPairLevel=0,maxEpisodeWeight=0,matchedEdges=0,terminalPairs=0,episodes=0,repeatEpisodes=0,eligible=0,tokenMemberships=0;
 for(const u of uses){
   const key=Math.min(u.a.P.M,u.b.P.M)+','+Math.max(u.a.P.M,u.b.P.M);
   if(!byPair.has(key))byPair.set(key,[]);byPair.get(key).push(u);sourcePaths.set(u.a.P.M,u.a.P);sourcePaths.set(u.b.P.M,u.b.P);
 }
 function stateAt(P,t){let i=0,j=P.records.length;while(i<j){let k=(i+j)>>1;if(P.records[k].v<=t)i=k+1;else j=k;}return i<P.records.length?P.records[i].C:P.endC}
 for(const [pk,us] of byPair){
   const P=us[0].a.P,Q=us[0].b.P,stop=Math.min(P.end,Q.end),stopC=stateAt(P,stop),dStop=2*stop-stopC;
   ok(stateAt(Q,stop)===stopC,"actual common earlier endpoint");
   const dead=new Map(),tail=new Map(),episode=new Map();
   const maxD=Math.max(...us.map(u=>u.d)),pairLevel=new Float64Array(maxD+1);
   const short=Math.abs(P.M-Q.M)<=H;
   let gainWeight=us.reduce((a,u)=>a+u.w,0);ok(gainWeight<=U+1e-8,"pair target gain cap");
   let checkPair=literal<128;
   for(const u of us){
     const a=u.a,b=u.b,A=a.P.records,Q=b.P.records;
     const j0=A.findIndex((e,i)=>i>a.k&&e.C===u.recipient),j1=Q.findIndex((e,i)=>i>b.k&&e.C===u.recipient);
     ok(j0>a.k&&j1>b.k,"actual rough recipient visits");
     const T=A[j0],T1=Q[j1],r=T.r,wT=T.v-T.b,drop=Math.max(0,T.p-1-2*wT),E=wT*wT/(2*r);
     ok(T.C===T1.C&&T.b===T1.b&&T.v===T1.v&&T.p===T1.p&&r===T1.r&&r===u.r&&T.v<=stop,"shared recorded target wait");
     const key=pk+"|"+T.C+","+T.b+","+T.v;ok(!targets.has(key),"pair target counted once");targets.add(key);
     const x=u.w*B/r,charge=u.w*(u.d-6);ok(x<=1+1e-9&&charge<=12*r*x+1e-7&&r<=18*E+3*drop+1e-7,"direct target coercivity");
     target.raw+=charge;target.rMass+=r*x;target.natural+=E*x;target.drop+=drop*x;
     const drift=2*wT-(T.p-1);if(drift>0)target.pos+=charge;else{target.nonpos+=charge;if(!drift)target.zero+=charge;}
     if(wT<r/4)target.short+=charge;
     target.maxRatio=Math.max(target.maxRatio,charge/(x*(E+drop)));target.keys++;
     ok(A[a.k].v===Q[b.k].v&&A[a.k].post===Q[b.k].post&&A[a.k].v<=stop,"common actual anchor");
     const dl=new Int32Array(u.d+1);dl.fill(-1);
     let mu=u.d;
     for(let i=a.k+1,j=b.k+1;i<A.length&&j<Q.length&&A[i].v<=stop;i++,j++){
       const e=A[i],q=Q[j];ok(e.C===q.C&&e.b===q.b&&e.v===q.v&&e.p===q.p&&e.post===q.post,"actual shared recorded suffix");
       if(e.post<mu){for(let l=Math.max(7,e.post+1);l<=mu;l++)dl[l]=i;mu=e.post;}
     }
     for(let l=7;l<=u.d;l++){
       const x=a.levels[l],y=b.levels[l],w=u.w,ty=x.C===y.C&&x.z===y.z?0:1;
       ok(ty===(l<=u.mu?1:0),"exact donor coarea type");
       raw+=w;pairLevel[l]+=w;checks++;
       let e=dl[l]>=0?A[dl[l]]:null,code=e?e.C+','+e.b+','+e.v:'T';
       if(e){
         ok(2*e.b-e.C>=l&&e.post<l&&e.p-1-2*(e.v-e.b)>0,"actual net downcross");
         matched+=w;if(ty)matchedInherited+=w;else matchedShared+=w;
         if(!dead.has(code))dead.set(code,{e,levels:new Map()});const d=dead.get(code);
         d.levels.set(l,(d.levels.get(l)||0)+w);
       }else{
         ok(l<=dStop,"survives to original earlier cutoff");
         terminal+=w;if(ty)terminalInherited+=w;else terminalShared+=w;
         tail.set(l,(tail.get(l)||0)+w);
       }
       // Per-pair episode aggregation; no global quadratic episode storage.
       const [ox,oy]=a.P.M<b.P.M?[x,y]:[y,x];const ep=l+'|'+ox.z+','+ox.C+'|'+oy.z+','+oy.C;
       let c=episode.get(ep);if(!c){c={w:0,exit:code,ty};episode.set(ep,c)}ok(c.exit===code&&c.ty===ty,"episode exit independent of anchor");
       c.w+=w;
       if(l<=6+H)low+=w;
       else if(short)near+=w;
       else{
         eligible+=w;// use stable smaller source orientation below
         const lo=a.P.M<b.P.M?a:b,origin=lo===a?x:y;
         const key=lo.P.M+'|'+l+'|'+origin.z+','+origin.C;
         const m=thin[e?0:1];m.set(key,(m.get(key)||0)+w);
       }
       if(checkPair&&literal<128){
         let t=A[a.k].v+1;while(t<=stop&&2*t-stateAt(a.P,t)>=l)t++;
         ok(e?t===e.v:t===stop+1,"literal future first downcross");literal++;
       }
     }
   }
   for(const w of pairLevel){ok(w<=U+1e-8,"all episodes per pair level cap");maxPairLevel=Math.max(maxPairLevel,w)}
   for(const c of episode.values()){ok(c.w<=U+1e-8,"episode weight cap");maxEpisodeWeight=Math.max(maxEpisodeWeight,c.w)}
   episodes+=episode.size;repeatEpisodes+=us.reduce((s,u)=>s+Math.max(0,u.d-6),0)-episode.size;
   for(const d of dead.values()){const e=d.e,drop=e.p-1-2*(e.v-e.b);ok(d.levels.size<=drop,"actual distinct downcross levels");for(const w of d.levels.values())ok(w<=U+1e-8,"one level per net downcross");netCap+=drop;matchedEdges++;}
   if(tail.size){terminalPairs++;terminalCap+=Math.max(0,dStop-6);ok(tail.size<=Math.max(0,dStop-6),"terminal levels");for(const w of tail.values())ok(w<=U+1e-8,"terminal pair cap")}
 }
 const quota=m=>{let pay=[0,0],rem=[0,0];for(let i=0;i<2;i++)for(const w of thin[i].values()){if(w<=m+1e-10)pay[i]+=w;else rem[i]+=w}ok(close(eligible,pay[0]+pay[1]+rem[0]+rem[1]),"token quota ledger");return {m,pay,rem,capacity:m*(thin[0].size+thin[1].size)}};
 tokenMemberships=thin[0].size+thin[1].size;
 const tokenCounts=new Map();for(const t of thin)for(const k of t.keys()){let M=Number(k.split('|')[0]);tokenCounts.set(M,(tokenCounts.get(M)||0)+1)}for(const [M,n] of tokenCounts){let P=sourcePaths.get(M);ok(n<=4*(P.end-P.s),'actual token membership bound')}
 ok(close(target.raw,raw)&&raw<=216*target.natural+36*target.drop+1e-6&&close(target.raw,target.pos+target.nonpos),'direct target ledger');
 ok(close(raw,expected)&&close(raw,matched+terminal)&&close(matched,matchedShared+matchedInherited)&&close(terminal,terminalShared+terminalInherited)&&close(raw,low+near+eligible)&&matched<=U*netCap+1e-7&&terminal<=U*terminalCap+1e-7,"global exit ledger");
 return {target,raw,matched,terminal,matchedShared,matchedInherited,terminalShared,terminalInherited,low,near,eligible,netCap,terminalCap,maxPairLevel,maxEpisodeWeight,matchedEdges,terminalPairs,episodes,repeatEpisodes,checks,literal,pairs:byPair.size,tokenMemberships,thinCounts:thin.map(x=>x.size),quota:[quota(1),quota(8)]};
}
// Actual origin-class transport on unbalanced inherited same-slot cores.
function originTransport(edges,B,ok,close,kappa=1){
 const nodes=new Map(),targets=new Map(),groups=new Map(),tokens=new Set(),seen=new Set();
 function get(key,r,record,l){
   if(!nodes.has(key))nodes.set(key,{key,r,l,vs:new Set(),ins:new Set(),outs:new Set(),record});
   const g=nodes.get(key);ok(g.r===r&&g.l===l&&g.record.C===record.C&&g.record.v===record.v,"unique upcross slot");return g;
 }
 let raw=0;
 for(const e of edges){
   const a=get(e.A,e.rA,e.recA,e.l),o=get(e.O,e.rO,e.recO,e.l);
   ok(o.record.C<a.record.C&&o.l===a.l,"strict origin order");
   a.vs.add(e.i);a.ins.add(e);o.vs.add(e.j);o.outs.add(e);
   tokens.add(e.A+"|"+e.i);tokens.add(e.O+"|"+e.j);
   let key=e.O+"|"+e.A;if(!groups.has(key))groups.set(key,{o,a,es:[],left:new Set(),right:new Set(),w:0});
   let g=groups.get(key);g.es.push(e);g.left.add(e.i);g.right.add(e.j);g.w+=e.w;
   ok(!seen.has(e.i+','+e.j+','+e.l),"unique directed pair-level");seen.add(e.i+','+e.j+','+e.l);raw+=e.w;
 }
 let Q=0,initialOutQ=0,initialInQ=0,repeatOrigins=0,maxDegree=0,maxTargets=0,maxOrigins=0,maxLeftRatio=0,maxRepeat=0,weightedQ=0,rawClassBalanced=0,rawClassUnbalanced=0,rawGainTransfer=0,maxGroupRatio=0,originFull=0;
 for(const n of nodes.values()){
   Q+=n.vs.size**2;
   const ins=new Set([...n.ins].map(e=>e.i)),outs=new Set([...n.outs].map(e=>e.j));
   initialInQ+=ins.size**2;initialOutQ+=outs.size**2;
   if(!n.outs.size)continue;
   const tg=new Map(),left=new Map(),right=new Set();
   for(const e of n.outs){
     right.add(e.j);
     if(!tg.has(e.A))tg.set(e.A,{r:e.rA,right:new Set(),left:new Set()});
     const g=tg.get(e.A);g.right.add(e.j);g.left.add(e.i);
     ok(!left.has(e.i)||left.get(e.i)===e.A,"one left source per persistent right-origin class");left.set(e.i,e.A);
   }
   const rsum=[...tg.values()].reduce((a,g)=>a+g.r,0);
   if(tg.size>1)repeatOrigins++;
   const latest=[...n.outs].sort((a,b)=>b.recA.v-a.recA.v)[0];
   for(const key of tg.keys()){
     const t=nodes.get(key).record;
     ok(latest.path.records.some(e=>e.C===t.C&&e.v===t.v&&e.r===t.r),"one actual longest right continuation covers every target");
   }
   maxDegree=Math.max(maxDegree,[...tg.values()].reduce((a,g)=>a+g.left.size,0));
   ok(left.size===[...tg.values()].reduce((a,g)=>a+g.left.size,0),"disjoint opposite source sets");
   // All target slots are on the one deterministic continuation of this origin.
   ok(rsum<=1.5*(12*B+6),"origin target gain bound");
   maxTargets=Math.max(maxTargets,tg.size);maxRepeat=Math.max(maxRepeat,rsum/B);maxLeftRatio=Math.max(maxLeftRatio,left.size/right.size);
   const weight=[...n.outs].reduce((s,e)=>s+e.w,0);
   if(left.size<=kappa*right.size){rawClassBalanced+=weight;ok(weight<=27*kappa*right.size**2+1e-7,"origin total partner transport")}else rawClassUnbalanced+=weight;
   if(weight<=27*kappa*right.size**2)originFull+=weight;
   for(const [key,g] of tg){
     const alpha=g.r/rsum;
     weightedQ+=alpha*g.right.size**2;
     const w=groups.get(n.key+"|"+key).w;
     if(g.left.size<=kappa*alpha*g.right.size){rawGainTransfer+=w;ok(w<=27*kappa*alpha*g.right.size**2+1e-7,"gain allocated class transfer")}
   }
 }
 for(const n of nodes.values())maxOrigins=Math.max(maxOrigins,new Set([...n.ins].map(e=>e.O)).size);
 ok(tokens.size===[...nodes.values()].reduce((s,n)=>s+n.vs.size,0)&&weightedQ<=initialOutQ+1e-7,"origin square reuse");
 // Both role capacities use only actual tokens of that role, fixed before deletion.
 const cs=new Map(),inc=new Map(),alive=new Set(edges);
 function add(key,e,n){let c=cs.get(key);if(!c){c={cap:kappa*27*n*n,d:0,es:[],done:false};cs.set(key,c)}c.d+=e.w;c.es.push(e);if(!inc.has(e))inc.set(e,[]);inc.get(e).push(c)}
 for(const n of nodes.values()){
   let a=new Set([...n.ins].map(e=>e.i)).size,b=new Set([...n.outs].map(e=>e.j)).size;
   for(const e of n.ins)add("in|"+n.key,e,a);
   for(const e of n.outs)add("out|"+n.key,e,b);
 }
 let paid=0,remaining=0;
 const queue=[...cs.values()].filter(c=>c.d<=c.cap+1e-10);
 for(let i=0;i<queue.length;i++){let c=queue[i];if(c.done||c.d>c.cap+1e-10)continue;c.done=true;for(const e of c.es){if(!alive.delete(e))continue;paid+=e.w;for(const t of inc.get(e)){let old=t.d;t.d-=e.w;if(old>t.cap+1e-10&&t.d<=t.cap+1e-10)queue.push(t)}}}
 for(const e of alive){remaining+=e.w;for(const c of inc.get(e))ok(c.d>c.cap-1e-8,"origin role weighted core")}
 const cap=[...cs.values()].reduce((s,c)=>s+c.cap,0);
 ok(cap<=54*kappa*Q+1e-7&&paid<=cap+1e-7&&close(raw,paid+remaining)&&close(raw,rawClassBalanced+rawClassUnbalanced),"global origin role ledger");
 // A second independent comparison uses actual out-role weighted degree only:
 // allocate at most kappa*U0*n^2 even at a heavy origin, without deleting all edges.
 let partial=0;for(const n of nodes.values()){let nr=new Set([...n.outs].map(e=>e.j)).size;partial+=Math.min([...n.outs].reduce((a,e)=>a+e.w,0),27*kappa*nr*nr)}
 let oracle=new Set(edges),changed=true;while(changed){changed=false;let degrees=new Map();for(const e of oracle)for(const c of inc.get(e))degrees.set(c,(degrees.get(c)||0)+e.w);let del=[...oracle].filter(e=>inc.get(e).some(c=>degrees.get(c)<=c.cap+1e-10));for(const e of del){oracle.delete(e);changed=true}}ok(oracle.size===alive.size&&[...oracle].every(e=>alive.has(e)),"independent origin graph core");
 let maxGroupWeight=0;for(const g of groups.values()){maxGroupWeight=Math.max(maxGroupWeight,g.w);maxGroupRatio=Math.max(maxGroupRatio,g.right.size/g.left.size);ok(g.w<=27*g.right.size*g.left.size+1e-7,"actual class pair envelope")}
 return {kappa,raw,Q,initialOutQ,initialInQ,nodes:nodes.size,tokens:tokens.size,groups:groups.size,maxTargets,maxOrigins,maxLeftRatio,maxRepeat,repeatOrigins,maxDegree,weightedQ,rawClassBalanced,rawClassUnbalanced,rawGainTransfer,originFull,paid,remaining,cap,partial,maxGroupWeight,maxGroupRatio};
}
// Sharp same-slot inherited hit caps and positive/nonpositive occupation transfer.
function slotAudit(pairs,B,expected,ok,close,ell=4,m=8){
 const S=new Map(),pairsSeen=new Set(),transportEdges=[],originRecords=new Map(),tot={same:0,distinct:0,skip:0,low:0,recent:0,small:0,smallDrift:0,smallAge:0,smallEnd:0,smallR:0,pos:0,nonpos:0,zero:0,negative:0,short:0,longNonpos:0,posMoment:0,mixedMoment:0,mixedNatural:0,mixedDrop:0,distinctPos:0,distinctNonpos:0,keys:0,fully:0,oracle:0,maxPairRatio:0,heavyEvents:0,heavyRaw:0,balancedRaw:0,balancedBound:0,unbalancedRaw:0,rawPositiveSquares:0,rawNonpositiveSquares:0,slotRolePaid:0,slotRoleResidual:0,slotRoleCap:0,slotRoleKeys:0,maxRoles:0};
 function lower(P,C){let a=0,b=P.records.length;while(a<b){let k=(a+b)>>1;if(P.records[k].C<C)a=k+1;else b=k}return a}
 for(const [pk,v] of pairs){
   let a=v.a,b=v.b;
   for(let l=7;l<=v.hi;l++){
     let w=0;for(const c of v.uses)if(c.hi>=l)w+=c.w;if(w<=0)continue;
     if(l<=6+ell){tot.low+=w;continue}
     let E=a.levels[l].z<b.levels[l].z?a:b,L=E===a?b:a,Z=L.levels[l],C=Z.C;
     if(v.F.t-Z.z<ell){tot.recent+=w;continue}
     let k=lower(E.P,C),H=E.P.records[k],A=L.P.records[Z.i];
     if(H.C!==C){tot.skip+=w;continue}
     let dE=2*(H.v-H.b)-(H.p-1);
     if(H.v!==A.v){tot.distinct+=w;if(dE>0)tot.distinctPos+=w;else tot.distinctNonpos+=w;continue}
     tot.same+=w;
     ok(H.b===v.F.t&&A.b<Z.z&&Z.z<H.b&&H.p===A.p&&H.r===A.r,"same-slot geometry");
     let p=H.p,r=H.r,wL=A.v-A.b,wE=H.v-H.b,dL=2*wL-(p-1),dV=2*H.v-(C+p-1),age=H.b-A.b,pre=2*A.b-C;
     ok(l>pre&&l<=dV&&l<=2*(H.b-1)-C&&dL>0&&dL-dE===2*age,"surviving inherited level interval");
     const key=C+','+H.v;let s=S.get(key);if(!s){s={C,v:H.v,p,r,edges:new Map(),rec:new Map(),levels:new Map()};S.set(key,s)}
     for(const [M,e] of [[E.P.M,H],[L.P.M,A]]){let old=s.rec.get(M);ok(!old||old===e,"unique actual slot membership");s.rec.set(M,e)}
     let edge=s.edges.get(pk);if(!edge){ok(!pairsSeen.has(pk),"same-slot hit unique per pair");pairsSeen.add(pk);edge={i:L.P.M,j:E.P.M,w:0,n:0,wL,wE,dL,dE,dV,age,pre};s.edges.set(pk,edge)}
     ok(edge.i===L.P.M&&edge.j===E.P.M,"fixed role");edge.w+=w;edge.n++;if(!s.levels.has(l))s.levels.set(l,[]);s.levels.get(l).push({edge,w,origin:E.levels[l],originRec:E.P.records[E.levels[l].i],leftRec:A,path:E.P});
   }
 }
 const lev={raw:0,paid:0,remaining:0,balanced:0,unbalanced:0,positiveSquare:0,balancedSquare:0,fullPositiveSquare:0,membership:0,capacity:0,keys:0,fully:0,maxRatio:0,maxBalancedRatio:0,oracle:0};
 for(const s of S.values()){
   let raw=0,paid=0,remain=0,es=[],gains=new Map(),P=0,N=0;
   for(const [M,e] of s.rec){let w=e.v-e.b,d=2*w-(e.p-1);gains.set(M,{w,d});if(d>0)P+=w/(2*s.r);else N+=(s.p-1)/(4*s.r)}
   for(const e of s.edges.values()){
     ok(e.n<=Math.min(e.dL,2*e.age-2,Math.max(0,e.dV-6))&&e.w<=27*e.n+1e-7,"sharp same-slot pair-level cap");
     let small=e.dL<=ell||e.age<=ell||e.dV<=6+ell||s.r<=ell/4;
     e.small=small;
     if(small){tot.small+=e.w;if(e.dL<=ell)tot.smallDrift+=e.w;else if(e.age<=ell)tot.smallAge+=e.w;else if(e.dV<=6+ell)tot.smallEnd+=e.w;else tot.smallR+=e.w;continue}
     raw+=e.w;es.push(e);
     if(e.dE>0){let a=e.wL*e.wE/(2*s.r);ok(e.w<=324*a+1e-7,"positive-positive same-slot bound");tot.pos+=e.w;tot.posMoment+=a;tot.maxPairRatio=Math.max(tot.maxPairRatio,e.w/a)}
     else{
       let nat=e.wL*e.wE/(2*s.r),down=e.wL*(-e.dE)/(2*s.r),mix=nat+down/2;
       ok(close(mix,e.wL*(s.p-1)/(4*s.r))&&e.w<=324*mix+1e-7,"positive nonpositive mixed bound");
       tot.nonpos+=e.w;tot.mixedMoment+=mix;tot.mixedNatural+=nat;tot.mixedDrop+=down;
       if(e.dE===0)tot.zero+=e.w;else tot.negative+=e.w;
       if(e.wE<s.r/4)tot.short+=e.w;else tot.longNonpos+=e.w;
     }
   }
   if(!es.length)continue;
   const posFull=[...s.rec.values()].filter(e=>2*(e.v-e.b)>e.p-1);
   const allFull=[...s.rec.values()];
   const lo=Math.min(...posFull.map(e=>2*e.b-s.C))+1,hi=2*s.v-(s.C+s.p-1);
   ok(hi-lo+1<=4*s.r,"positive surviving level window");
   let fullSq=0;for(let l=Math.max(7,lo);l<=hi;l++){let n=posFull.filter(e=>2*e.b-s.C<l).length;fullSq+=n*n;}
   lev.fullPositiveSquare+=fullSq;
   let localMembership=0,localSquare=0;
   for(const [l,arr] of s.levels){
     const edges=arr.filter(a=>!a.edge.small);if(!edges.length)continue;
     const left=new Set(edges.map(a=>a.edge.i)),right=new Set(edges.map(a=>a.edge.j));
     const z=Math.ceil((s.C+l)/2);
     for(const M of left){const e=s.rec.get(M);ok(e.b<z&&z<e.v&&2*e.b-s.C<l&&l<=hi,"actual surviving stationary class")}
     for(const M of right){const e=s.rec.get(M);ok(e.b>=z+ell,"late independent arrival");ok(!left.has(M),"disjoint level roles")}
     const nv=left.size+right.size;localMembership+=nv;lev.membership+=nv;lev.keys++;
     lev.capacity+=m*nv;lev.raw+=edges.reduce((a,e)=>a+e.w,0);
     const inc=new Map(),d=new Map(),alive=new Set(edges);
     for(const e of edges)for(const k of [e.edge.i,e.edge.j]){if(!inc.has(k))inc.set(k,[]);inc.get(k).push(e);d.set(k,(d.get(k)||0)+e.w)}
     const queue=[...d.keys()].filter(k=>d.get(k)<=m+1e-10);
     for(let j=0;j<queue.length;j++){const k=queue[j];if(d.get(k)>m+1e-10)continue;for(const e of inc.get(k)){if(!alive.delete(e))continue;lev.paid+=e.w;for(const v of [e.edge.i,e.edge.j]){let old=d.get(v);d.set(v,old-e.w);if(old>m+1e-10&&d.get(v)<=m+1e-10)queue.push(v)}}}
     if(!alive.size){lev.fully++;}
     const a=new Set(),b=new Set();let weight=0;
     for(const e of alive){a.add(e.edge.i);b.add(e.edge.j);weight+=e.w;ok(d.get(e.edge.i)>m-1e-8&&d.get(e.edge.j)>m-1e-8,"level both-role core")}
     let ratio=a.size?b.size/a.size:0;lev.maxRatio=Math.max(lev.maxRatio,ratio);
     localSquare+=a.size*a.size;lev.positiveSquare+=a.size*a.size;lev.remaining+=weight;
     if(alive.size&&ratio<=1){lev.balanced+=weight;lev.balancedSquare+=a.size*a.size;lev.maxBalancedRatio=Math.max(lev.maxBalancedRatio,ratio);ok(weight<=27*a.size*a.size+1e-7,"balanced level bound")}
     else if(alive.size){
       lev.unbalanced+=weight;
       for(const e of alive){
         const O=e.origin,rec=e.originRec,A=e.leftRec,post=2*rec.v-(rec.C+rec.p-1);
         ok(rec.C===O.C&&rec.b<O.z&&O.z<rec.v&&2*rec.b-rec.C<l&&post>=l&&O.z<z,"right independent positive net ascent");
         const akey=z+','+s.C+','+l,okey=O.z+','+O.C+','+l;
         for(const [key,rec0,M] of [[akey,A,e.edge.i],[okey,rec,e.edge.j]]){if(!originRecords.has(key))originRecords.set(key,new Map());originRecords.get(key).set(M,rec0)}
         transportEdges.push({A:akey,O:okey,i:e.edge.i,j:e.edge.j,l,w:e.w,rA:s.r,rO:rec.r,recA:A,recO:rec,path:e.path});
       }
     }
     if(lev.oracle<64){const aa=new Set(edges);let changed=true;while(changed){changed=false;const ds=new Map();for(const e of aa)for(const k of [e.edge.i,e.edge.j])ds.set(k,(ds.get(k)||0)+e.w);for(const e of aa)if(ds.get(e.edge.i)<=m+1e-10||ds.get(e.edge.j)<=m+1e-10){aa.delete(e);changed=true}}ok(aa.size===alive.size&&[...aa].every(e=>alive.has(e)),"independent level core");lev.oracle++}
   }
   ok(localMembership<=4*s.r*allFull.length&&localSquare<=fullSq,"level membership and square envelope");
   let wp=posFull.reduce((a,e)=>a+(e.v-e.b)/(2*s.r),0);
   ok(fullSq<=6*s.r*wp*wp+1e-7,"full ascent-square occupation transport");
   tot.keys++;tot.rawPositiveSquares+=s.r*P*P;tot.rawNonpositiveSquares+=s.r*N*N;
   const mixed=es.filter(e=>e.dE<=0).reduce((v,e)=>v+e.w,0);
   if(N<=P){tot.balancedRaw+=mixed;tot.balancedBound+=648*s.r*P*P;ok(mixed<=648*s.r*P*P+1e-7,"balanced mixed mass")}
   else{tot.unbalancedRaw+=mixed;tot.heavyEvents++;tot.heavyRaw+=raw}
   // two role constraints, capacities proportional to actual receiver drift
   // and to the donor's actual outgoing r (one per source/slot).
   const inc=new Map(),cs=new Map(),alive=new Set(es);
   function add(key,e,cap){let c=cs.get(key);if(!c){c={cap,d:0,edges:[],done:false};cs.set(key,c)}ok(close(cap,c.cap),"fixed cap");c.d+=e.w;c.edges.push(e);if(!inc.has(e))inc.set(e,[]);inc.get(e).push(c)}
   for(const e of es){add("L"+e.i,e,m*e.dL/B);add("E"+e.j,e,m*s.r/B)}
   const q=[...cs.values()].filter(c=>c.d<=c.cap+1e-10);
   for(let i=0;i<q.length;i++){let c=q[i];if(c.done||c.d>c.cap+1e-10)continue;c.done=true;for(const e of c.edges){if(!alive.delete(e))continue;paid+=e.w;for(const z of inc.get(e)){let old=z.d;z.d-=e.w;if(old>z.cap+1e-10&&z.d<=z.cap+1e-10)q.push(z)}}}
   for(const e of alive){remain+=e.w;for(const c of inc.get(e))ok(c.d>c.cap-1e-8,"fixed role core")}
   let cap=[...cs.values()].reduce((n,c)=>n+c.cap,0);
   ok(close(raw,paid+remain)&&paid<=cap+1e-7,"slot role ledger");
   tot.slotRolePaid+=paid;tot.slotRoleResidual+=remain;tot.slotRoleCap+=cap;tot.slotRoleKeys+=cs.size;tot.maxRoles=Math.max(tot.maxRoles,cs.size);if(!alive.size)tot.fully++;
   if(tot.oracle<64){let a=new Set(es),change=true;while(change){change=false;let d=new Map();for(const e of a)for(const c of inc.get(e))d.set(c,(d.get(c)||0)+e.w);let del=[...a].filter(e=>inc.get(e).some(c=>d.get(c)<=c.cap+1e-10));for(const e of del){a.delete(e);change=true}}ok(a.size===alive.size&&[...a].every(e=>alive.has(e)),"independent slot core");tot.oracle++}
 }
 ok(close(expected,tot.low+tot.recent+tot.same+tot.distinct+tot.skip)&&close(tot.same,tot.small+tot.pos+tot.nonpos)&&close(tot.same,tot.small+tot.slotRolePaid+tot.slotRoleResidual)&&close(tot.nonpos,tot.balancedRaw+tot.unbalancedRaw),"complete same-slot ledger");
 ok(close(lev.raw,tot.pos+tot.nonpos)&&close(lev.raw,lev.paid+lev.remaining)&&close(lev.remaining,lev.balanced+lev.unbalanced)&&lev.paid<=lev.capacity+1e-7&&lev.positiveSquare<=lev.fullPositiveSquare+1e-7,'global level ledger');
 const origin=originTransport(transportEdges,B,ok,close,1),originSmall=originTransport(transportEdges,B,ok,close,1/64),originTiny=originTransport(transportEdges,B,ok,close,1/1024);
 let restrictedQ=0;for(const [key,vs] of originRecords){let l=Number(key.split(',')[2]);for(const e of vs.values())ok(2*e.b-e.C<l&&l<=2*e.v-(e.C+e.p-1),"origin-square actual positive visit");restrictedQ+=vs.size**2}
 ok(close(origin.raw,lev.unbalanced)&&close(originSmall.raw,lev.unbalanced)&&close(origin.Q,restrictedQ),"origin transport ledger");
 return {...tot,level:lev,origin,originSmall,originTiny,ell,m,distinctPairs:pairsSeen.size,actualSlots:S.size};
}
// Inherited-level later-origin horizon crossing and overtaking audit.
function crossingAudit(pairs,X,B,rr,expected,ok,close,eps=1/4,delay=4){
 const z={total:0,low:0,recent:0,eligible:0,hit:0,hitSame:0,hitDistinct:0,hitGood:0,hitShort:0,skip:0,skipLow:0,skipHigh:0,hitEnergy:0,hitDownEnergy:0,hitDownRatio:0,hitDownKeys:0,hitRatio:0,flip:0,flipStationary:0,flipDouble:0,firstBefore:0,firstAfter:0,checks:0,literal:0,maxGap:0,maxLag:0,maxReuse:0,maxSkip:0,byP:{},byR:{},hitGoodKeys:0,hitAllKeys:0,skipKeys:0,skipCrossMoment:0,skipThinPaid:0,skipResidual:0,skipCap:0,skipVertex:0};
 const hitGroups=new Map(),skips=new Map(),skipPairKeys=new Map(),skipTokenGroups=new Map(),roughTuples=new Map();const R=Math.ceil(B/16);
 function state(P,t){let a=0,b=P.records.length;while(a<b){let m=(a+b)>>1;if(P.records[m].v<=t)a=m+1;else b=m}if(a<P.records.length)return {C:P.records[a].C,k:a};return {C:P.endC,k:a}}
 function lower(P,C){let a=0,b=P.records.length;while(a<b){let m=(a+b)>>1;if(P.records[m].C<C)a=m+1;else b=m}return a}
 function getFlips(v){
   let P=v.a.P,Q=v.b.P,F=v.F,t0=Math.max(P.s,Q.s),a=state(P,t0),b=state(Q,t0),diff=a.C-b.C,flips=[];
   ok(diff!==0||t0===F.t,"first state distinct");
   while(t0<F.t){
     let at=Math.min(P.records[a.k].v,Q.records[b.k].v,F.t);
     let x=state(P,at),y=state(Q,at),next=x.C-y.C;
     if(at<F.t&&diff*next<0){
       let pa=x.C-a.C+1,pb=y.C-b.C+1,win=diff<0?pa:pb,lose=diff<0?pb:pa;
       ok(win>=5&&win-lose>Math.abs(diff)&&win-lose===Math.abs(diff)+Math.abs(next),"strict overtake gain inequality");
       flips.push({t:at,p:win,q:lose,D:diff,N:next});
     }
     if(at===F.t)ok(next===0,"first contact equality");else ok(next!==0,"no earlier equality");
     t0=at;a=x;b=y;diff=next;
   }
   return flips;
 }
 for(const [pk,v] of pairs){
   const flips=getFlips(v),P=v.a.P,Q=v.b.P,F=v.F;
   const beforeA=state(P,F.t-1).C,beforeB=state(Q,F.t-1).C;
   ok(beforeA!==beforeB,"distinct precontact horizons");
   
   for(let l=7;l<=v.hi;l++){
     let w=0;for(const u of v.uses)if(u.hi>=l)w+=u.w;
     if(w<=0)continue;
     z.total+=w;z.maxReuse=Math.max(z.maxReuse,w);
     let x=v.a.levels[l],y=v.b.levels[l],early=x.z<y.z?v.a:v.b,late=early===v.a?v.b:v.a,E=early.P,T=late.P,a=early.levels[l],b=late.levels[l],C=b.C;
     ok(a.C<C&&C-a.C===2*(b.z-a.z),"ordered independent upcross");
     if(l<=6+delay){z.low+=w;continue}
     if(F.t-b.z<delay){z.recent+=w;continue}
     z.eligible+=w;
     const ea=state(E,b.z),eb=state(T,b.z);
     ok(eb.C===C&&ea.C<C,"early upcross remains behind at later upcross");
     // First crossing of the LATER origin horizon C: event cannot precede
     // b.z, and cannot occur after first contact.
     let k=lower(E,C);
     ok(k>0&&k<E.records.length,"actual crossing and subsequent completed wait");
     let event=E.records[k-1],land=E.records[k].C,arrival=event.v;
     ok(event.C<C&&land>=C&&land===event.C+event.p-1&&arrival>b.z&&arrival<=F.t,"exact late-origin crossing");
     ok(2*arrival-land>=l,"persistent early donor at crossing");
     ok(2*(arrival-b.z)>=(land-C),"crossing clock cone");
     const Lwait=T.records[b.i],wL=Lwait.v-Lwait.b;
     ok(Lwait.C===C&&Lwait.b<b.z&&b.z<Lwait.v&&2*wL>Lwait.p-1,"late upcross full positive wait");
     const sign=early===v.a?-1:1,reversed=(beforeA-beforeB)*sign<0;
     // sign is the early path's relative ordering at later upcross (A behind -> -1).
     if(reversed){
       const g=flips.filter(s=>s.t>b.z).at(-1);
       ok(g&&g.t<F.t&&g.N*sign<0,"last strict reversal after later upcross");
       z.flip+=w;if(g.q===1)z.flipStationary+=w;else z.flipDouble+=w;
       
     }
     if(v.type===1){
       const earlyIsRecipient=state(E,F.t-1).C===F.C;
       ok(earlyIsRecipient===reversed,"JS role reversal equivalence");
       if(earlyIsRecipient)z.firstAfter+=w;else z.firstBefore+=w;
     }
     z.maxGap=Math.max(z.maxGap,b.z-a.z);z.maxLag=Math.max(z.maxLag,arrival-b.z);z.checks++;
     if(z.literal<128){
       let t=b.z+1;while(state(E,t).C<C)t++;
       ok(t===arrival,"literal first horizon crossing");z.literal++;
     }
     if(land===C){
       z.hit+=w;let H=E.records[k],wH=H.v-H.b,r=H.r;
       ok(H.C===C&&H.b===arrival&&H.r===Lwait.r,"same horizon visit");
       if(H.v===Lwait.v){ok(arrival===F.t,"same-slot hit is first contact");z.hitSame+=w;}else{ok(Lwait.v<=arrival,"distinct slots disjoint");z.hitDistinct+=w;}
       const key=pk+'|'+C;
       let h=hitGroups.get(key);
       const energy=wL*wH/(2*r),drop=Math.max(0,H.p-1-2*wH),downEnergy=wL*drop/(2*r);
       if(!h){h={weight:0,good:0,short:0,r,wL,wH,energy,downEnergy,drop,arrival,late:Lwait.v,levels:0};hitGroups.set(key,h)}
       ok(h.arrival===arrival&&h.late===Lwait.v&&close(h.energy,energy),"fixed orientation per pair/horizon");
       h.weight+=w;h.levels++;
       if(wH>=eps*r){h.good+=w;z.hitGood+=w;}else {ok(drop>=r/6&&downEnergy>=wL/12,'short hit net descent');z.hitShort+=w;h.short+=w;}
       let rb=r<=B/16?"low":r<=B/4?"mid":"high";z.byR[rb]=(z.byR[rb]||0)+w;
     }else{
       z.skip+=w;ok(event.p>=5&&C<=land-2,"skip needs p>=5");
       if(event.p<=Math.sqrt(B))z.skipLow+=w;else z.skipHigh+=w;
       z.maxSkip=Math.max(z.maxSkip,land-C);
       const p=event.p,key=event.v+','+land+','+p;
       z.byP[p]=(z.byP[p]||0)+w;
       let s=skips.get(key);if(!s){s={w:0,p,land,t:event.v,origins:new Set(),tags:new Set()};skips.set(key,s)}
       s.w+=w;s.origins.add(C);s.tags.add(E.M);
       if(Lwait.r>=R){
         const tuple=key+'|'+C,side=event.v%2,delta=land-C;
         ok(delta>=2&&delta<=p-3&&delta%2===0&&(C+delta+2*side)%p===0&&(event.v-2*side)%p===0,"rough skip tuple arithmetic");
         if(!roughTuples.has(tuple))roughTuples.set(tuple,{p,w:0,C,land,t:event.v});
         roughTuples.get(tuple).w+=w;
       }
       const tok=late.P.M+'|'+b.z+'|'+l,opp=early.P.M;
       if(!skipTokenGroups.has(tok))skipTokenGroups.set(tok,new Map());const opps=skipTokenGroups.get(tok);
       ok(!opps.has(opp),"unique skip pair-level");opps.set(opp,{w,key});
       let u=skipPairKeys.get(pk+'|'+key+'|'+C);
       if(!u){u={w:0,wL,count:0};skipPairKeys.set(pk+'|'+key+'|'+C,u)}
       u.w+=w;u.count++;ok(u.wL===wL,"unique later origin wait at skipped C");
     }
   }
 }
 for(const h of hitGroups.values()){
   ok(h.levels<=2*h.wL&&h.weight<=27*2*h.wL+1e-7,"pair horizon level bound");
   if(h.good>0){ok(h.good<=108/eps*h.energy+1e-7,"hit transfer inequality");z.hitEnergy+=h.energy;z.hitGoodKeys++;z.hitRatio=Math.max(z.hitRatio,h.good/h.energy)}
   if(h.short>0){ok(h.short<=648*h.downEnergy+1e-7,'short hit downward transfer');z.hitDownEnergy+=h.downEnergy;z.hitDownKeys++;z.hitDownRatio=Math.max(z.hitDownRatio,h.short/h.downEnergy)}
 }
 z.hitAllKeys=hitGroups.size;z.skipKeys=skips.size;
 for(const s of skips.values())ok(s.origins.size<=(s.p-3)/2,"skip interior horizon count");
 for(const u of skipPairKeys.values()){ok(u.count<=2*u.wL&&u.w<=54*u.wL+1e-7,"skip per pair horizon budget");z.skipCrossMoment+=u.wL;}
 // Independent token-thin skip peeling: one capacity per late birth token,
 // regardless of how many crossing keys its opposite sources use.
 for(const opps of skipTokenGroups.values()){
   const val=[...opps.values()].reduce((s,e)=>s+e.w,0),cap=8;
   z.skipVertex++;z.skipCap+=cap;
   if(val<=cap+1e-10)z.skipThinPaid+=val;else z.skipResidual+=val;
 }
 ok(close(z.skip,z.skipThinPaid+z.skipResidual)&&z.skipThinPaid<=z.skipCap+1e-7,"skip token quota");
 ok(close(z.total,expected)&&close(z.total,z.low+z.recent+z.eligible)&&close(z.eligible,z.hit+z.skip)&&close(z.hit,z.hitSame+z.hitDistinct)&&close(z.hit,z.hitGood+z.hitShort)&&close(z.skip,z.skipLow+z.skipHigh),"exact crossing ledger");
 const roughSupport=new Map(),actualByP=new Map();let roughRaw=0,roughPaid=0,roughRemain=0,fullKeys=0;
 for(const o of roughTuples.values()){
   actualByP.set(o.p,(actualByP.get(o.p)||0)+1);
   roughRaw+=o.w;const pay=Math.min(8,o.w);roughPaid+=pay;roughRemain+=o.w-pay;if(pay===o.w)fullKeys++;
 }
 // Enumerate the relaxed support only for realized labels; use all even
 // horizons in the original O(X) strip, not only sampled origins.
 for(const [p,n] of actualByP){
   let count=0;
   for(let C=2*X-2;C<7*X;C+=2){
     if(rr(C)<R)continue;
     for(let side=0;side<2;side++){
       let delta=((-(C+2*side))%p+p)%p;
       if(delta<2||delta>p-3||delta%2!==0)continue;
       let J=C+delta,res=side?p+2:0,lo=J/2,hi=(J+12*B+6)/2;
       count+=Math.max(0,Math.floor((hi-res)/(2*p))-Math.ceil((lo-res)/(2*p))+1);
     }
   }
   ok(n<=count,"realized rough skip tuple support");roughSupport.set(p,count);
 }
 ok(close(roughRaw,roughPaid+roughRemain)&&roughRaw<=z.skip+1e-7,"rough tuple quota ledger");
 return {...z,epsilon:eps,delay,roughTuple:{R,raw:roughRaw,paid:roughPaid,remaining:roughRemain,keys:roughTuples.size,fullyPaid:fullKeys,actualByP:Object.fromEntries(actualByP),relaxedSupportByP:Object.fromEntries(roughSupport)}};
}
// Inherited deficit level excursion forest and near-origin energy comparison.
function inheritedForest(pairs,X,B,paths,expected,ok,close,base=1,delay=4){
 const width=16*B,shift=8*B,byCell=new Map(),Dmax=12*B+6;
 const caps={total:0,paid:0,remaining:0,low:0,recent:0,eligible:0,capacity:0,log:0,tokens:0,initialGroups:0,events:0,full:0,edges:0,kept:0,maxInitial:0,maxFinal:0,maxReuse:0,maxLevel:0,byType:[0,0,0,0],remainingType:[0,0,0,0],near:[0,0,0],remainingNear:[0,0,0],oracle:0,maxLight:0,firstContactKeys:0};
 const allTokens=new Set(),firstKeys=new Set();
 for(const v of pairs.values()){
   const [i,j]=[v.a.P.M,v.b.P.M],c0=Math.floor((i-X)/width),c1=Math.floor((j-X)/width),p=c0===c1?0:1,k=Math.floor((i-X+p*shift)/width);
   ok(Math.abs(i-j)<=6*B&&k===Math.floor((j-X+p*shift)/width),"internal pair cell");
   const key=p+','+k;if(!byCell.has(key))byCell.set(key,[]);byCell.get(key).push(v);
 }
 for(const [cell,ps] of byCell){
   const hi=Math.max(...ps.map(v=>v.hi));
   for(let l=7;l<=hi;l++){
     const es=[],tokens=new Map();
     function token(a){
       const z=a.levels[l].z,C=a.levels[l].C,key=a.P.M+'|'+z;
       if(!tokens.has(key))tokens.set(key,{key,M:a.P.M,z,C});else ok(tokens.get(key).C===C,"one token horizon");
       return tokens.get(key)
     }
     for(const v of ps){
       if(v.hi<l)continue;
       let w=0;for(const c of v.uses)if(c.hi>=l)w+=c.w;
       if(w<=0)continue;
       const a=v.a.levels[l],b=v.b.levels[l];ok(a.z!==b.z&&a.C!==b.C&&2*(a.z-b.z)===a.C-b.C,"distinct last upcross keys at fixed level");
       // The odd/even level convention is identical for both keys, so the horizon gap is exactly twice the time gap.
       ok(a.z<=v.F.t&&b.z<=v.F.t&&l<=v.F.d,"inherited at contact");
       ok(w<=1.5*(12*B+6)/B+1e-8,'aggregate inherited pair-level cap');caps.total+=w;caps.maxReuse=Math.max(caps.maxReuse,w);caps.maxLevel=Math.max(caps.maxLevel,l);
       caps.byType[v.type]+=w;let sep=Math.abs(a.z-b.z),nb=sep<=delay?0:sep<=8*delay?1:2;caps.near[nb]+=w;
       if(l<=6+delay){caps.low+=w;continue}
       if(v.F.t-Math.max(a.z,b.z)<delay){caps.recent+=w;continue}
       const x=token(v.a),y=token(v.b);es.push({x:x.key,y:y.key,w,t:v.F.t,J:v.F.C,type:v.type,nb});caps.eligible+=w;caps.edges++;
       firstKeys.add(v.F.t+','+v.F.C+','+l);
     }
     if(!es.length)continue;
     const parent=new Map(),members=new Map(),initial=new Map(),growth=new Map(),light=new Map(),byOrigin=new Map();
     for(const x of tokens.values()){
       const key=x.z+','+x.C;if(!byOrigin.has(key))byOrigin.set(key,[]);byOrigin.get(key).push(x.key);
       allTokens.add(cell+'|'+l+'|'+x.key);
     }
     for(const vs of byOrigin.values()){
       const lead=vs[0];members.set(lead,vs.slice());caps.maxInitial=Math.max(caps.maxInitial,vs.length);caps.initialGroups++;
       for(const v of vs){parent.set(v,lead);initial.set(v,vs.length);growth.set(v,0);light.set(v,0)}
     }
     caps.tokens+=tokens.size;
     function find(v){let p=parent.get(v);while(p!==v){let q=parent.get(p);parent.set(v,q);v=p;p=q}return v}
     const events=new Map();
     for(const e of es){if(!events.has(e.t))events.set(e.t,new Map());const a=events.get(e.t);if(!a.has(e.J))a.set(e.J,[]);a.get(e.J).push(e)}
     for(const [t,batch] of [...events].sort((a,b)=>a[0]-b[0])){
       const used=new Set(),items=[];
       for(const [J,edges] of batch){
         const roots=new Set();for(const e of edges){const a=find(e.x),b=find(e.y);ok(a!==b,"first inherited contact joins distinct excursion components");roots.add(a);roots.add(b)}
         for(const a of roots){ok(!used.has(a),"one active component target per tick");used.add(a)}
         items.push({roots,edges});
       }
       for(const {roots,edges} of items){
         caps.events++;
         const n=[...roots].reduce((s,v)=>s+members.get(v).length,0),sizes=new Map([...roots].map(v=>[v,members.get(v).length]));
         // A physical component cannot contain two different surviving excursions of one source.
         const seen=new Set();for(const a of roots)for(const v of members.get(a)){const x=tokens.get(v);ok(x.z<=t&&!seen.has(x.M),"active excursion tokens and unique sources");seen.add(x.M);growth.set(v,growth.get(v)+Math.log(n/sizes.get(a)));if(2*sizes.get(a)<=n)light.set(v,light.get(v)+1)}
         caps.maxFinal=Math.max(caps.maxFinal,n);
         const constraints=new Map(),inc=new Map(),alive=new Set(edges);
         function add(v,e){let c=constraints.get(v);if(!c){c={cap:base*Math.log(n/sizes.get(find(v))),d:0,es:[],done:false};constraints.set(v,c)}c.d+=e.w;c.es.push(e);if(!inc.has(e))inc.set(e,[]);inc.get(e).push(c)}
         for(const e of edges){add(e.x,e);add(e.y,e)}
         for(const c of constraints.values())caps.capacity+=c.cap;
         const queue=[...constraints.values()].filter(c=>c.d<=c.cap+1e-10);
         for(let i=0;i<queue.length;i++){const c=queue[i];if(c.done||c.d>c.cap+1e-10)continue;c.done=true;
           for(const e of c.es){if(!alive.delete(e))continue;caps.paid+=e.w;for(const z of inc.get(e)){const prev=z.d;z.d-=e.w;if(prev>z.cap+1e-10&&z.d<=z.cap+1e-10)queue.push(z)}}
         }
         if(!alive.size)caps.full++;
         for(const e of alive){caps.remaining+=e.w;caps.kept++;caps.remainingType[e.type]+=e.w;caps.remainingNear[e.nb]+=e.w;for(const c of inc.get(e))ok(c.d>c.cap-1e-8,"fixed excursion core")}
         if(caps.oracle<128){
           const a=new Set(edges);let changed=true;while(changed){changed=false;const deg=new Map();for(const e of a)for(const c of inc.get(e))deg.set(c,(deg.get(c)||0)+e.w);const del=[...a].filter(e=>inc.get(e).some(c=>deg.get(c)<=c.cap+1e-10));for(const e of del){a.delete(e);changed=true}}
           ok(a.size===alive.size&&[...a].every(e=>alive.has(e)),"independent excursion peeling");caps.oracle++;
         }
         const lead=[...roots][0];for(const a of roots)if(a!==lead){parent.set(a,lead);members.get(lead).push(...members.get(a));members.delete(a)}
         ok(members.get(lead).length===n,"actual excursion union");
       }
     }
     for(const [v,g] of growth){const n=members.get(find(v)).length;ok(close(g,Math.log(n/initial.get(v))),"initial class entropy telescopes");caps.log+=g;caps.maxLight=Math.max(caps.maxLight,light.get(v));}
   }
 }
 caps.firstContactKeys=firstKeys.size;
 ok(allTokens.size===caps.tokens,"unique excursion membership");
 // Every token (M,z,lambda) is an actual stationary crossing in the original prefix.
 const counts=new Map();for(const k of allTokens){const a=k.split('|');const M=Number(a[2]);counts.set(M,(counts.get(M)||0)+1)}
 for(const [M,n] of counts){let p=paths.get(M);ok(n<=4*(p.end-p.s),"stationary excursion token budget");}
 ok(close(caps.total,expected)&&close(caps.total,caps.low+caps.recent+caps.paid+caps.remaining),"inherited level ledger");
 ok(caps.paid<=caps.capacity+1e-6&&caps.capacity<=base*caps.log+1e-6&&caps.log<=caps.tokens*Math.log(8*B+1)+1e-6,"excursion entropy capacity");
 return caps;
}
// Actual donor last-upcross partitions, common-minimum decomposition and upstream positive-energy transfer.
function ascentAudit(ledger,X,B,L,y,paths,rr,ok,close){
 const U=6*B+3,R=Math.max(y+1,Math.ceil(B/16)),groups=new Map(),pairUses=new Map(),pairR=new Map(),edgeUses=new Map(),inheritedPairs=new Map(),exitUses=[];let nearMoment=0,nearBound=0,nearDiagonal=0,nearShared=0;let raw=0;
 for(const [pk,w] of ledger.pairs){
   const a=ledger.contacts.get(pk);if(a.type!==1||Math.max(a.p,a.q)>y||a.age<=3*L+3||rr(a.J)<R)continue;
   const P=paths.get(a.i),Q=paths.get(a.j),i=P.records.findIndex(e=>e.C===a.J),j=Q.records.findIndex(e=>e.C===a.J);
   const D=P.records[i].b===a.t?P:Q,S=D===P?Q:P,idx=D===P?i:j;
   let k=idx-1;while(k>=0&&D.records[k].p<=y)k--;ok(k>=0,"actual nonreset anchor");
   const e=D.records[k],J=e.C+e.p-1,t=e.v,d=2*t-J,key=J+','+t+','+e.p;
   ok(d>6&&d>=2*a.age-5*L,"actual anchor deficit");
   let g=groups.get(key);if(!g){g={J,t,q:e.p,d,recipient:a.J,r:rr(a.J),arrival:a.t,donors:new Map(),receivers:new Set(),w:0,minAge:Infinity,maxAge:0};groups.set(key,g)}
   ok(g.recipient===a.J&&g.arrival===a.t,"unique anchor target");
   g.w+=w;raw+=w;g.receivers.add(S.M);g.minAge=Math.min(g.minAge,a.age);g.maxAge=Math.max(g.maxAge,a.age);
   let v=g.donors.get(D.M);if(!v){v={P:D,k,w:0};g.donors.set(D.M,v)}ok(v.k===k,"same anchor index");v.w+=w;
 }
 function first(a,b){
   let i=0,j=0;const A=a.P.records,Q=b.P.records;
   while(i<=a.k&&j<=b.k){const x=A[i],y=Q[j];if(x.C<y.C){i++;continue}if(x.C>y.C){j++;continue}
     const t=Math.max(x.b,y.b);if(t<Math.min(x.v,y.v))return {t,C:x.C,i,j};
     i++;j++;
   }throw Error("missing donor internal contact");
 }
 let shared=0,inherited=0,diagonal=0,unweightedShared=0,unweightedInherited=0,weightedKeyEnergy=0,maxReuse=0,checks=0,literal=0,globalBound=0,scaledShared=0,scaledInherited=0,scaledDiag=0,scaledTotal=0,scaledUnweightedShared=0,scaledUpstream=0,maxReuseR=0;
 const out=[];
 for(const g of groups.values()){
   const {d}=g,D=d-6,nR=g.receivers.size,vs=[...g.donors.values()],rowCap=Math.max(...vs.map(a=>a.w));ok(rowCap<=U*nR+1e-8,'actual row cap');
   const lambdaSums=new Float64Array(d+1),lambdaSquares=new Float64Array(d+1);
   let mass=0,diag=0;
   for(const a of vs){
     a.x=a.w/rowCap;ok(a.x>0&&a.x<=1+1e-9,"normalized row mass");
     mass+=a.x;diag+=a.x*a.x;
     const levels=Array(d+1).fill(null);
     for(let i=0;i<=a.k;i++){
       const e=a.P.records[i],post=e.post;
       for(let z=e.b+1;z<e.v;z++){
         for(const l of [2*z-e.C-1,2*z-e.C])if(l>=7&&l<=d)levels[l]={z,C:e.C,v:e.v,i};
       }
     }
     for(let l=7;l<=d;l++){ok(levels[l],"all high levels reached");}
     a.levels=levels;
   }
   ok(close(g.w,rowCap*mass),"row normalization");
   let s=0,h=0,s0=0,h0=0,minCommon=Infinity,maxCommon=0,earlyPairs=0,highPairs=0,localEnergy=0;
   for(let l=7;l<=d;l++){
     const gs=new Map();for(const a of vs){const k=a.levels[l].z+','+a.levels[l].C;let b=gs.get(k);if(!b){b={x:0,n:0,xx:0};gs.set(k,b)}b.x+=a.x;b.n++;b.xx+=a.x*a.x}
     for(const b of gs.values()){lambdaSums[l]+=(b.x*b.x-b.xx)/2;lambdaSquares[l]+=b.n*(b.n-1)/2;nearBound+=g.r/B*4*b.x*b.x;nearDiagonal+=g.r/B*b.xx;nearShared+=g.r/B*(b.x*b.x-b.xx)/2}
     const ns=[...gs].map(([k,b])=>({z:Number(k.split(',')[0]),x:b.x})).sort((a,b)=>a.z-b.z);
     for(let i=0;i<ns.length;i++)for(let j=i+1;j<ns.length&&ns[j].z-ns[i].z<=4;j++)nearMoment+=g.r/B*ns[i].x*ns[j].x;
   }
   for(let i=0;i<vs.length;i++)for(let j=i+1;j<vs.length;j++){
     const a=vs[i],b=vs[j],F=first(a,b),A=a.P.records,Q=b.P.records;
     let mu=2*F.t-F.C;for(let k=F.i;k<=a.k;k++)mu=Math.min(mu,A[k].post);
     ok(a.k-F.i===b.k-F.j,"common recorded suffix");
     for(let k=0;k<=a.k-F.i;k++)ok(A[F.i+k].C===Q[F.j+k].C&&A[F.i+k].v===Q[F.j+k].v,"shared donor suffix");
     let sh=d-Math.max(6,mu),inh=D-sh;ok(sh>=0&&inh>=0,"level split");
     const wt=a.x*b.x,pk=Math.min(a.P.M,b.P.M)+','+Math.max(a.P.M,b.P.M);
     pairUses.set(pk,(pairUses.get(pk)||0)+1);maxReuse=Math.max(maxReuse,pairUses.get(pk));pairR.set(pk,(pairR.get(pk)||0)+g.r);
     exitUses.push({a,b,F,mu,d,w:g.r/B*wt,r:g.r,recipient:g.recipient});
     let actual=0;const perWait=new Map();
     if(inh>0){const p=a.P.records[F.i].b===F.t?(F.i?a.P.records[F.i-1].p:0):-1,q=b.P.records[F.j].b===F.t?(F.j?b.P.records[F.j-1].p:0):-1;const d0=2*F.t-F.C;let type=p===0||q===0?0:p===-1||q===-1?1:d0===6*(F.t%2)?3:2;ok(type!==0&&d0>6,'high inherited excludes root and reset');let v=inheritedPairs.get(pk);if(!v){v={a,b,F:{...F,d:d0},type,hi:mu,uses:[]};inheritedPairs.set(pk,v)}else{ok(v.F.t===F.t&&v.F.C===F.C&&v.type===type,'unique inherited first contact');if(mu>v.hi){v.a=a;v.b=b;v.hi=mu}}v.uses.push({hi:mu,w:g.r/B*wt});}

     for(let l=7;l<=d;l++){
       const x=a.levels[l],y=b.levels[l],same=x.z===y.z&&x.C===y.C;
       ok(same===(l>mu),"exact common last-upcross iff above common minimum");
       if(!same){ok(x.z<=F.t&&y.z<=F.t,'inherited crossing precedes contact');continue;}
       actual++;const e=A[x.i],f=Q[y.i];ok(e.post>=l&&f.post>=l&&2*(e.v-e.b)>e.p-1&&2*(f.v-f.b)>f.p-1,"surviving crossing implies positive net wait both");
       const k=e.C+','+e.v;let o=perWait.get(k);if(!o){o={n:0,e,f};perWait.set(k,o)}o.n++;
     }
     ok(actual===sh,"direct level scan");checks++;
     let pe=0;for(const [k,{n,e,f}] of perWait){const E=(e.v-e.b)*(f.v-f.b)/(2*e.r);ok(n<=12*E+1e-8,"full positive upstream energy payment");pe+=E;
       const K=pk+'|'+k;let z=edgeUses.get(K);if(!z){z={sum:0,E,uses:0,weighted:0,unweighted:0,rsum:0};edgeUses.set(K,z)}ok(close(z.E,E),"same upstream pair wait");z.sum+=wt*n;z.uses++;z.weighted+=g.r/B*wt*n;z.unweighted+=g.r/B*n;z.rsum+=g.r;
     }
     ok(sh<=12*pe+1e-8,"per donor pair transfer");localEnergy+=pe;
     s+=wt*sh;h+=wt*inh;s0+=sh;h0+=inh;
     minCommon=Math.min(minCommon,mu);maxCommon=Math.max(maxCommon,mu);if(mu<=6)earlyPairs++;if(mu>=6+D/2)highPairs++;
     if(literal<128){
       let m=Infinity,ia=F.i,ib=F.j;
       for(let t=F.t;t<=g.t;t++){
         let C;if(t===g.t)C=g.J;else {while(A[ia].v<=t)ia++;while(Q[ib].v<=t)ib++;ok(A[ia].C===Q[ib].C,"literal shared tick");C=A[ia].C}
         m=Math.min(m,2*t-C);
       }
       ok(m===mu,"literal minimum oracle");literal++;
     }
   }
   ok(close(s,lambdaSums.reduce((a,b)=>a+b,0))&&close(s0,lambdaSquares.reduce((a,b)=>a+b,0)),"independent level partition moment");
   ok(close(D*mass*mass,D*diag+2*(s+h)),"exact weighted square identity");
   const recEnergy=g.minAge*g.minAge*nR*nR/(4*g.r);
   const sharedFrac=2*s/(D*mass*mass),inheritedFrac=2*h/(D*mass*mass);
   if(s>0)ok(close(g.w*g.w,2*rowCap*rowCap*s/(D*sharedFrac)),"conditional shared mass bound");
   // For every recipient, its actual full wait includes the preceding minAge ticks.
   let recSum=0;for(const M of g.receivers){let e=paths.get(M).records.find(e=>e.C===g.recipient);ok(e&&e.b<=g.arrival-g.minAge,"recipient interval");recSum+=(e.v-e.b)/(2*e.r)}
   ok(g.r*recSum*recSum+1e-8>=recEnergy,"recipient occupation lower bound");
   shared+=s;inherited+=h;diagonal+=D*diag;unweightedShared+=s0;unweightedInherited+=h0;scaledShared+=g.r/B*s;scaledInherited+=g.r/B*h;scaledDiag+=g.r/B*D*diag;scaledTotal+=g.r/B*D*mass*mass;scaledUnweightedShared+=g.r/B*s0;
   out.push({J:g.J,t:g.t,q:g.q,d,recipient:g.recipient,r:g.r,arrival:g.arrival,nD:vs.length,nR,w:g.w,minAge:g.minAge,maxAge:g.maxAge,rowCap,mass,diag:D*diag,shared:s,inherited:h,sharedFrac,inheritedFrac,s0,h0,earlyPairs,highPairs,minCommon:Number.isFinite(minCommon)?minCommon:null,maxCommon,localEnergy,recEnergy,fullRecipientEnergy:g.r*recSum*recSum});
 }
 // A donor pair can share at most O(B/R) distinct rough target slots; every such
 // target contributes a completed jump of at least R-1 to BOTH actual gains.
 const maxTargets=Math.ceil((12*B+6)/(R-1));
 for(const [pk,n] of pairUses){ok(n<=maxTargets,"global pair target multiplicity");const [i,j]=pk.split(',').map(Number),gain=Math.min(...[i,j].map(M=>paths.get(M).records.reduce((s,e)=>s+e.p-1,0)));ok(pairR.get(pk)<=1.5*gain+1e-8,'actual weighted target multiplicity');maxReuseR=Math.max(maxReuseR,pairR.get(pk)/B);}
 for(const z of edgeUses.values()){ok(z.uses<=maxTargets&&z.sum<=12*maxTargets*z.E+1e-7,"weighted upstream reuse");weightedKeyEnergy+=z.E;globalBound+=12*maxTargets*z.E;ok(z.weighted<=z.unweighted+1e-8&&z.unweighted<=12*z.rsum/B*z.E+1e-7,'scaled upstream reuse');scaledUpstream+=z.unweighted;}
 ok(shared<=globalBound+1e-7,"global upstream moment");ok(close(scaledTotal,scaledDiag+2*(scaledShared+scaledInherited))&&close(scaledUpstream,scaledUnweightedShared)&&scaledShared<=scaledUnweightedShared+1e-7&&scaledUnweightedShared<=12*maxReuseR*weightedKeyEnergy+1e-7,'global gain-weighted shared moment');
 ok(nearMoment<=nearBound+1e-7&&close(nearBound,4*(nearDiagonal+2*nearShared)),'near-origin band quadratic bound');
 const exit=exitAudit(exitUses,B,scaledShared+scaledInherited,ok,close),phase=targetPhaseAudit(exitUses,X,B,L,y,rr,scaledShared+scaledInherited,ok,close);
 return {L,y,R,raw,anchors:groups.size,exit,phase,prefix:prefixAudit(exitUses,B,scaledShared+scaledInherited,ok,close,1/4),prefixWide:prefixAudit(exitUses,B,scaledShared+scaledInherited,ok,close,1/2),adaptive:adaptiveAudit(exitUses,B,scaledShared+scaledInherited,ok,close),boundary6:boundaryDebit(exitUses,B,L,scaledShared+scaledInherited,ok,close,6,3),boundary30:boundaryDebit(exitUses,B,L,scaledShared+scaledInherited,ok,close,30,5),scaledShared,scaledInherited,scaledDiag,scaledTotal};
}
// Long-age low-jump donor cones and weighted stationary recipient slot cores.
function recipientAudit(ledger,X,B,L,y,f,paths,rr,fac,base,ok,close){
 const R=Math.max(y+1,Math.ceil(B/16)),P=Math.max(y+1,Math.floor(Math.sqrt(B)/2)),Q=Math.max(y+1,Math.ceil(B/4)),U=6*B+3;
 const slots=new Map(),anchors=new Map(),recCache=new Map(),allR=new Map(),ageBins=[0,0,0,0],wKinds=[0,0,0,0],remainKinds=[0,0,0,0];
 let js=0,rough=0,longLow=0,longComp=0,shortLow=0,cutChecks=0,rootOnly=0,reset=0,maxAge=0,maxDef=0;
 function record(M,J){
   const key=M+','+J;if(recCache.has(key))return recCache.get(key);
   const P=paths.get(M),i=P.records.findIndex(e=>e.C===J);ok(i>=0,"actual first contact slot");const a={e:P.records[i],i,P};recCache.set(key,a);return a;
 }
 function at(P,t){let i=0;while(i<P.records.length&&P.records[i].v<=t)i++;return i<P.records.length?P.records[i].C:P.endC}
 function firstCross(P,K){if(2*P.M-2>K)return {root:true,t:P.s,J:2*P.M-2};for(const e of P.records){let J=e.C+e.p-1;if(J>K)return {t:e.v,J,p:e.p,D:e.C,root:false}}throw Error("missing actual crossing")}
 for(const [pk,w] of ledger.pairs){
   const a=ledger.contacts.get(pk);if(a.type!==1)continue;js+=w;
   const x=record(a.i,a.J),z=record(a.j,a.J);
   const D=x.e.b===a.t?x:z,S=D===x?z:x,p=Math.max(a.p,a.q),age=a.t-S.e.b,r=rr(a.J),v=D.e.v;
   ok(D.e.b===a.t&&S.e.b<a.t&&v===S.e.v&&a.t<v&&age===a.age,"distinct arrival cohorts same completed slot");
   const prev=D.P.records[D.i-1];ok(prev&&prev.p===p&&prev.v===a.t&&prev.v-prev.b<=2*p,"actual donor last wait");
   maxAge=Math.max(maxAge,age);
   if(age>=15){
     const h=2*Math.floor((age-3)/12),K=a.J-h,t0=S.e.b+3;
     ok(h>0&&D.P.s<=t0&&t0<a.t&&at(D.P,t0)<=K,"donor separated at receiver arrival+3");
     const dc=firstCross(D.P,K),sc=firstCross(S.P,K);
     ok(!dc.root&&dc.t>t0&&dc.t>=a.t-3*h&&dc.t-sc.t>=age-3*h,"late donor crossing clock separation");
     cutChecks++;
   }
   if(r<R)continue;rough+=w;
   const sk=a.J+','+v;let g=slots.get(sk);if(!g){g={J:a.J,v,r,es:[],comp:new Set(),arrivals:new Map()};slots.set(sk,g)}
   for(const c of [D,S]){
     const old=g.arrivals.get(c.P.M);ok(old===undefined||old===c.e.b,"unique source arrival");
     g.arrivals.set(c.P.M,c.e.b);
   }
   let anchor=null,ty=0;
   if(p<=y){
     if(age>3*L+3){
       longLow+=w;ty=1;
       let e=null;for(let i=D.i-1;i>=0;i--)if(D.P.records[i].p>y){e=D.P.records[i];break}
       ok(e!==null,"long recipient age excludes root-only donor");
       const J=e.C+e.p-1,t=e.v,q=e.p,d=2*t-J,delta=a.J-J;
       ok(delta>=p-1&&delta<L&&a.t-t<=3*delta&&d>=2*age-5*delta&&d>6,"nonreset donor LOW-tail cone");
       ok((J+2*(t%2))%q===0&&(d-6*(t%2))%(2*q)===0,"donor anchor congruence");
       maxDef=Math.max(maxDef,d);
       const key=J+','+t+','+q;
       let h=anchors.get(key);if(!h){h={J,t,q,target:sk,arrival:a.t,w:0,pairs:0,comp:q*f>=r,donors:new Set()};anchors.set(key,h)}
       ok(h.target===sk&&h.arrival===a.t,"unique LOW-tail rough recipient slot and entry time");h.w+=w;h.pairs++;h.donors.add(D.P.M);anchor=h;
       if(q*f>=r){ty=2;longComp+=w;g.comp.add(key)}
       else if(q<=P){ty=3}
     }else{
       shortLow+=w;
       let e=null;for(let i=D.i-1;i>=0;i--)if(D.P.records[i].p>y){e=D.P.records[i];break}
       if(!e)rootOnly+=w;else if(2*e.v-(e.C+e.p-1)===6*(e.v%2))reset+=w;
     }
   }
   wKinds[ty]+=w;ageBins[age<=p?0:age<=2*p?1:age<=8*p?2:3]+=w;
   g.es.push({D:D.P.M,S:S.P.M,w,ty,key:anchor?anchor.J+','+anchor.t+','+anchor.q:null,t:a.t,age});
 }
 let capTotal=0,paid=0,remaining=0,events=0,fully=0,kept=0,compRemain=0,maxComp=0,maxArrival=0,slotMemberships=0,weightedMemberships=0,rawCrossPairs=0,rawCrossCap=0,oracle=0;
 for(const g of slots.values()){
   // Verify the entire sampled slot is a subset of the actual cross-arrival product.
   const hist=new Map();for(const b of g.arrivals.values())hist.set(b,(hist.get(b)||0)+1);
   let n=0,np=0;for(const [b,c] of [...hist].sort((a,b)=>a[0]-b[0])){np+=n*c;n+=c}
   ok(g.es.length<=np,"cross-arrival pair cap");rawCrossPairs+=np;rawCrossCap+=U*np;
   maxArrival=Math.max(maxArrival,hist.size);maxComp=Math.max(maxComp,g.comp.size);slotMemberships+=n;weightedMemberships+=g.r*n;
   for(const v of g.arrivals.keys())allR.set(v,(allR.get(v)||0)+g.r);
   let envelope=0;
   for(let J=g.J-L+2;J<=g.J-2;J+=2)for(let s=0;s<2;s++)for(const q of fac(J+2*s)){
     if(q<=y||q>B||q*f<g.r)continue;
     const rho=s?q+2:0,lo=g.v-2*g.r-3*L,hi=g.v-1;
     envelope+=Math.max(0,Math.floor((hi-rho)/(2*q))-Math.ceil((lo-rho)/(2*q))+1);
   }
   ok(g.comp.size<=envelope,"actual comparable donor anchor count");
   const alive=new Set(g.es),constraints=new Map(),inc=new Map(),b=base*g.r/B;
   function add(k,e,c){let z=constraints.get(k);if(!z){z={cap:c,degree:0,es:[],done:false};constraints.set(k,z)}ok(close(c,z.cap),"fixed recipient capacity");z.degree+=e.w;z.es.push(e);if(!inc.has(e))inc.set(e,[]);inc.get(e).push(z)}
   for(const e of g.es){
     add("donor:"+e.D,e,b);
     add("recv:"+e.S+"|"+(e.ty===2?e.key:"other"),e,e.ty===2?b/Math.max(1,g.comp.size):b);
   }
   const queue=[...constraints.values()].filter(c=>c.degree<=c.cap+1e-10);let localPaid=0;
   for(let i=0;i<queue.length;i++){const c=queue[i];if(c.done||c.degree>c.cap+1e-10)continue;c.done=true;for(const e of c.es){if(!alive.delete(e))continue;localPaid+=e.w;for(const z of inc.get(e)){let old=z.degree;z.degree-=e.w;if(old>z.cap+1e-10&&z.degree<=z.cap+1e-10)queue.push(z)}}}
   let localCap=0;for(const c of constraints.values())localCap+=c.cap;
   ok(localCap<=3*b*n+1e-7&&localPaid<=localCap+1e-7,"slot role capacity");
   capTotal+=localCap;paid+=localPaid;events++;if(!alive.size)fully++;
   for(const e of alive){kept++;remaining+=e.w;remainKinds[e.ty]+=e.w;if(e.ty===2)compRemain+=e.w;for(const c of inc.get(e))ok(c.degree>c.cap-1e-8,"both role degrees")}
   if(oracle<64){const a=new Set(g.es);let change=true;while(change){change=false;const deg=new Map();for(const e of a)for(const c of inc.get(e))deg.set(c,(deg.get(c)||0)+e.w);for(const e of a)if(inc.get(e).some(c=>deg.get(c)<=c.cap+1e-10)){a.delete(e);change=true}}ok(a.size===alive.size&&[...a].every(e=>alive.has(e)),"independent slot core");oracle++}
 }
 for(const [M,s] of allR){let gain=paths.get(M).records.reduce((a,e)=>a+e.p-1,0);ok(s<=1.5*gain+1e-8,"per-root weighted slot visits");}
 ok(capTotal<=3*base*weightedMemberships/B+1e-7&&close(rough,paid+remaining),"global slot ledger");
 // Independent relaxed support for nonreset donor anchor-target tuples. Finite direct enumeration, not a sieve estimate.
 const support=[0,0,0],actual=[0,0,0],anchorRaw=[0,0,0],anchorPaid=[0,0,0],anchorRemain=[0,0,0],seen=new Set();
 function band(q){return q>=Q?2:q<=P?0:1}
 for(let J=2*X-2;J<7*X;J+=2){
   if(rr(J)<R)continue;
   for(let d=2;d<L;d+=2){let A=J-d;if(A<2*X-2)continue;
     for(let s=0;s<2;s++)for(const q of fac(A+2*s)){
       if(q<=y||q>B)continue;
       const rho=s?q+2:0,lo=Math.ceil((A+7)/2),hi=Math.floor((A+12*B+6)/2);
       support[band(q)]+=Math.max(0,Math.floor((hi-rho)/(2*q))-Math.ceil((lo-rho)/(2*q))+1);
     }
   }
 }
 for(const h of anchors.values()){
   const i=band(h.q),cap=base*h.q/B;
   actual[i]++;anchorRaw[i]+=h.w;anchorPaid[i]+=Math.min(h.w,cap);anchorRemain[i]+=Math.max(0,h.w-cap);
 }
 for(let i=0;i<3;i++)ok(actual[i]<=support[i]&&close(anchorRaw[i],anchorPaid[i]+anchorRemain[i]),"donor anchor support and ledger");
 ok(close(longLow,anchorRaw.reduce((a,b)=>a+b,0))&&close(rough,wKinds.reduce((a,b)=>a+b,0)),"long low ledger");
 return {base,fComp:f,R,P,Q,js,rough,longLow,longComp,shortLow,rootOnly,reset,cutChecks,maxAge,maxDef,ageBins,wKinds,remainKinds,capTotal,paid,remaining,events,fully,kept,compRemain,maxComp,maxArrival,slotMemberships,weightedMemberships,rawCrossPairs,rawCrossCap,oracle,anchor:{count:anchors.size,support,actual,raw:anchorRaw,paid:anchorPaid,remaining:anchorRemain,details:[...anchors.values()].map(a=>({...a,donors:a.donors.size}))}};
}
// Global actual first-contact forest and entropy quotas; rough stationary recipient control.
function entropyAudit(ledger,X,B,paths,rr,fac,sp,base,ok,close){
 const U=6*B+3,H=4*B,width=10*B,shift=5*B;
 const groups=new Map(),kinds=[0,0,0,0],rawKinds=[0,0,0,0],ageBands=[0,0,0,0],roughSmall=new Map(),R=Math.max(3,Math.ceil(B/16)),P=Math.max(3,Math.floor(Math.sqrt(B)/2));
 let total=0,jump=0,smallJump=0,receiverRough=0,smallRough=0;
 for(const [pk,w] of ledger.pairs){
   const a=ledger.contacts.get(pk);ok(a&&w>0&&w<=U+1e-8,"actual aggregate pair");total+=w;rawKinds[a.type]+=w;
   const i=a.i,j=a.j,k0=Math.floor((i-X)/width),k1=Math.floor((j-X)/width),part=k0===k1?0:1,k=Math.floor((i-X+part*shift)/width);
   ok(k===Math.floor((j-X+part*shift)/width),"shifted cell pair cover");
   const key=part+','+k;if(!groups.has(key))groups.set(key,[]);groups.get(key).push({...a,w});
   if(a.type===1){
     const p=Math.max(a.p,a.q),r=rr(a.J),age=a.age;ok(age>=1&&age<2*r,"recipient age");
     jump+=w;if(p<=P)smallJump+=w;if(r>=R)receiverRough+=w;
     ageBands[age<=p?0:age<=2*p?1:age<=8*p?2:3]+=w;
     if(p<=P&&r>=R){
       smallRough+=w;const key=a.t+','+a.J+','+p;let z=roughSmall.get(key);if(!z){z={w:0,p};roughSmall.set(key,z)}z.w+=w;
     }
   }
 }
 // Relaxed recipient support, independent of actual contacts. The finite
 // thresholds can overlap; no asymptotic CRT count inferred from them.
 const sup=new Map();
 for(let J=2*X-2;J<7*X;J+=2){
   const r=rr(J);if(r<R)continue;
   for(let s=0;s<2;s++)for(const p of fac(J+2*s)){
     if(p<3||p>P||p>B)continue;
     const rho=s?p+2:0,t0=Math.ceil(J/2),t1=Math.floor((J+12*B+6)/2);
     const n=Math.max(0,Math.floor((t1-rho)/(2*p))-Math.ceil((t0-rho)/(2*p))+1);
     sup.set(p,(sup.get(p)||0)+n);
   }
 }
 let arithmeticPaid=0,arithKeys=0,arithRemain=0;const arithByP=new Map();
 for(const z of roughSmall.values()){
   const pay=Math.min(z.w,base*z.p);arithmeticPaid+=pay;arithRemain+=z.w-pay;arithKeys++;arithByP.set(z.p,(arithByP.get(z.p)||0)+1);
 }
 for(const [p,n] of arithByP)ok(n<=(sup.get(p)||0),"rough stationary key support");
 ok(close(smallRough,arithmeticPaid+arithRemain),"stationary arithmetic ledger");
 let capTotal=0,paid=0,remain=0,events=0,mergingChildren=0,maxChildren=0,maxSize=0,maxGrowth=0,maxVertexLog=0,lightEventsMax=0,thinEvents=0,allPaidEvents=0,keptPairs=0,bigSide=0,smallSide=0,lightPaid=0,rootCount=0,independent=0;
 const rootLogs=new Map(),samplePairCap=Math.max(0,...ledger.pairs.values());
 for(const es of groups.values()){
   const vs=[...new Set(es.flatMap(e=>[e.i,e.j]))],parent=new Map(vs.map(v=>[v,v])),members=new Map(vs.map(v=>[v,[v]])),growth=new Map(vs.map(v=>[v,0])),light=new Map(vs.map(v=>[v,0]));
   rootCount+=vs.length;ok(vs.length<=5*B+1,"cell width bound");
   function find(v){while(parent.get(v)!==v){let a=parent.get(v);parent.set(v,parent.get(a));v=parent.get(v)}return v}
   const timeline=new Map();for(const e of es){let a=timeline.get(e.t);if(!a){a=new Map();timeline.set(e.t,a)}if(!a.has(e.J))a.set(e.J,[]);a.get(e.J).push(e)}
   for(const [t,byJ] of [...timeline].sort((a,b)=>a[0]-b[0])){
     const seen=new Set(),batch=[];
     for(const [J,ee] of byJ){
       const roots=new Set();for(const e of ee){let a=find(e.i),b=find(e.j);ok(a!==b,"first contact not already connected");roots.add(a);roots.add(b)}
       for(const a of roots){ok(!seen.has(a),"one component one physical target per tick");seen.add(a)}
       batch.push({J,ee,roots});
     }
     for(const {J,ee,roots} of batch){
       events++;mergingChildren+=roots.size;maxChildren=Math.max(maxChildren,roots.size);
       const ns=[...roots].reduce((s,a)=>s+members.get(a).length,0),sizes=new Map([...roots].map(a=>[a,members.get(a).length]));
       maxSize=Math.max(maxSize,ns);
       for(const a of roots){
         let n=sizes.get(a),d=Math.log(ns/n);maxGrowth=Math.max(maxGrowth,d);
         for(const v of members.get(a)){growth.set(v,growth.get(v)+d);if(n*2<=ns)light.set(v,light.get(v)+1)}
       }
       const constraints=new Map(),inc=new Map(),alive=new Set(ee);
       function add(v,e){
         let c=constraints.get(v);if(!c){let n=sizes.get(find(v));c={v,cap:base*Math.log(ns/n),es:[],degree:0,done:false};constraints.set(v,c)}
         c.es.push(e);c.degree+=e.w;if(!inc.has(e))inc.set(e,[]);inc.get(e).push(c);
       }
       for(const e of ee){add(e.i,e);add(e.j,e);let a=sizes.get(find(e.i)),b=sizes.get(find(e.j));ok(Math.min(a,b)*2<=ns,"light orientation");}
       const before=ee.reduce((s,e)=>s+e.w,0);
       const queue=[...constraints.values()].filter(c=>c.degree<=c.cap+1e-10);
       for(let i=0;i<queue.length;i++){
         let c=queue[i];if(c.done||c.degree>c.cap+1e-10)continue;c.done=true;
         for(const e of c.es){if(!alive.delete(e))continue;paid+=e.w;kinds[e.type]+=e.w;if(sizes.get(find(c.v))*2<=ns)lightPaid+=e.w;
           for(const z of inc.get(e)){let old=z.degree;z.degree-=e.w;if(old>z.cap+1e-10&&z.degree<=z.cap+1e-10)queue.push(z)}
         }
       }
       let left=[...alive].reduce((s,e)=>s+e.w,0);remain+=left;keptPairs+=alive.size;
       for(const c of constraints.values())capTotal+=c.cap;
       if(left<=1e-10)allPaidEvents++;
       if(samplePairCap>0&&ns<=1+base*Math.log(2)/samplePairCap){thinEvents++;ok(left<=1e-8,"small union complete payment");}
       for(const e of alive){
         for(const c of inc.get(e))ok(c.degree>c.cap-1e-8,"actual entropy core");
         const a=sizes.get(find(e.i)),b=sizes.get(find(e.j));
         if(Math.max(a,b)>2*Math.min(a,b))bigSide+=e.w;else smallSide+=e.w;
       }
       if(independent<64){
         const A=new Set(ee);let changed=true;
         while(changed){changed=false;const deg=new Map();for(const e of A){deg.set(e.i,(deg.get(e.i)||0)+e.w);deg.set(e.j,(deg.get(e.j)||0)+e.w)}
           const del=new Set([...deg].filter(([v,d])=>d<=constraints.get(v).cap+1e-10).map(x=>x[0]));
           for(const e of A)if(del.has(e.i)||del.has(e.j)){A.delete(e);changed=true}
         }
         ok(A.size===alive.size&&[...A].every(e=>alive.has(e)),"independent entropy fixed core");independent++;
       }
       const leader=[...roots].sort((a,b)=>sizes.get(b)-sizes.get(a)||a-b)[0];
       for(const a of roots)if(a!==leader){parent.set(a,leader);members.get(leader).push(...members.get(a));members.delete(a)}
       ok(members.get(leader).length===ns,"exact union mass");
     }
   }
   for(const v of vs){const n=members.get(find(v)).length,d=growth.get(v);ok(close(d,Math.log(n))&&light.get(v)<=Math.log2(n)+1e-8,"telescoping individual growth");maxVertexLog=Math.max(maxVertexLog,d);lightEventsMax=Math.max(lightEventsMax,light.get(v))}
   rootLogs.set(rootLogs.size,[...growth.values()].reduce((s,x)=>s+x,0));
 }
 const entropy=[...rootLogs.values()].reduce((s,x)=>s+x,0);
 ok(capTotal<=base*entropy+1e-6&&paid<=capTotal+1e-6&&close(total,paid+remain),"global entropy capacity");
 ok(entropy<=rootCount*Math.log(5*B+1)+1e-6,"cell entropy");
 return {base,samplePairCap,total,paid,remain,rawKinds,paidKinds:kinds,events,mergingChildren,maxChildren,maxSize,maxGrowth,maxVertexLog,lightEventsMax,rootCount,entropy,capTotal,allPaidEvents,thinEvents,keptPairs,bigSide,smallSide,lightPaid,independent,stationary:{jump,smallJump,receiverRough,smallRough,ageBands,R,P,arithKeys,arithmeticPaid,arithRemain,support:[...sup.values()].reduce((s,x)=>s+x,0)}};
}
// Multiscale actual first-contact cuts and summable opposite-cohort peeling.
function multiscale(g,live,z,edges,L,y,B,X,f,m,ok,close,fac,ledger){
 const base=L*Math.floor((g.C-1)/L),cuts=[],levels=[],minRoot=Math.min(...live.map(e=>2*e.P.M-2));
 for(let j=0;;j++){let K=base-L*(2**j-1);cuts.push(K);if(K<minRoot)break}
 const entries=new Map(live.map(e=>[e.P.M,e]));
 function at(e,K){
   const P=e.P,root=2*P.M-2;
   if(root>K)return {key:"root:"+P.M,q:0,J:root,t:P.s,root:true};
   for(let k=0;k<e.i;k++){const h=P.records[k],J=h.C+h.p-1;
     if(J>K){ok(h.C<=K&&h.p>y,"primorial crossing");return {key:J+','+h.v+','+h.p,q:h.p,J,t:h.v,root:false}}}
   throw Error("missing cut crossing");
 }
 for(const K of cuts)levels.push(new Map(live.map(e=>[e.P.M,at(e,K)])));
 for(let j=1;j<levels.length;j++){
   const parent=new Map();for(const e of live){const a=levels[j].get(e.P.M).key,b=levels[j-1].get(e.P.M).key;ok(!parent.has(a)||parent.get(a)===b,"nested cut partitions");parent.set(a,b)}
 }
 function first(a,b){
   let i=0,j=0,A=a.P.records,Q=b.P.records;
   while(i<=a.i&&j<=b.i){
     const x=A[i],y=Q[j];if(x.C<y.C){i++;continue}if(x.C>y.C){j++;continue}
     const t=Math.max(x.b,y.b);
     if(t<Math.min(x.v,y.v)){
       const p=x.b===t?(i?A[i-1].p:0):-1,q=y.b===t?(j?Q[j-1].p:0):-1;
       ok(p!==q,"first contact incoming labels");
       let type=p===0||q===0?0:p===-1||q===-1?1:2;
       if(type===2){const s=t%2,d=2*t-x.C-6*s;ok(p>=3&&q>=3&&d%p===0&&d%q===0,"two jump divisor");if(d!==0)ok(p*q<=Math.abs(d)&&Math.abs(d)<=12*B+6,"nonreset product");else type=3}
       return {J:x.C,t,type,p,q,age:type===1?t-(p===-1?x.b:y.b):0}
     }i++;j++;
   }throw Error("no original common tick");
 }
 const shellRaw=cuts.map(()=>0),shellPaid=cuts.map(()=>0),shellRemain=cuts.map(()=>0),shellPairs=cuts.map(()=>0),types=[0,0,0,0],remTypes=[0,0,0,0],constraints=new Map(),inc=new Map(),alive=new Set(),parents=new Map();let oracle=0;
 for(const e of edges){
   const a=entries.get(e.i),b=entries.get(e.j),F=first(a,b);
   let j=levels.findIndex(l=>l.get(e.i).key!==l.get(e.j).key);ok(j>=0,"separation at root singleton");
   for(let k=0;k<cuts.length;k++)ok((levels[k].get(e.i).key===levels[k].get(e.j).key)===(F.J<=cuts[k]),"exact contact-cut equivalence");
   const upper=j?cuts[j-1]:g.C;ok(cuts[j]<F.J&&F.J<=upper,"first contact shell");
   const parent=j?levels[j-1].get(e.i).key:"TOP";if(j)ok(parent===levels[j-1].get(e.j).key,"common upper cohort");
   const pmax=Math.max(F.p,F.q),Q=Math.max(5,Math.ceil(B/4));
   const pk=Math.min(e.i,e.j)+','+Math.max(e.i,e.j),pl=pk+','+(2*z-g.C);
   ok(!ledger.seen.has(pl),"no duplicate old pair-level across sampled origins");ledger.seen.add(pl);
   ledger.pairs.set(pk,(ledger.pairs.get(pk)||0)+e.w);
   const old=ledger.contacts.get(pk);ok(!old||(old.t===F.t&&old.J===F.J&&old.type===F.type&&Math.max(old.p,old.q)===Math.max(F.p,F.q)&&old.age===F.age),"unique pair first-contact across origins");
   if(!old)ledger.contacts.set(pk,{...F,i:Math.min(e.i,e.j),j:Math.max(e.i,e.j)});
   if(pmax>=Q){
     const s=F.t%2,d=2*F.t-F.J-6*s;
     ok(d>=0&&d%(2*pmax)===0&&(F.J+2*s)%pmax===0,"large first-contact phase");
     const key=F.t+','+F.J+','+pmax;let c=ledger.keys.get(key);
     if(!c){c={w:0,reset:d===0,pairs:new Set()};ledger.keys.set(key,c)}
     c.w+=e.w;c.pairs.add(pk);
   }
   e.shell=j;e.first=F;e.parent=parent;shellRaw[j]+=e.w;shellPairs[j]++;types[F.type]+=e.w;
   const k=j+"|"+parent;let p=parents.get(k);if(!p){p={j,parent,groups:[new Set(),new Set(),new Set()]};parents.set(k,p)}
   for(const v of [e.i,e.j]){
     const a0=levels[j].get(v),ty=a0.root?0:a0.q*f>=g.r?1:2;
     ok(a0.J<=F.J&&a0.J<=upper&&a0.t<=F.t,"precontact entry");
     if(!a0.root)ok(z-a0.t<=2*g.r+3*(g.C-cuts[j]),"entry phase window");
     p.groups[ty].add(a0.key);
   }
   if(oracle<64){
     const from=Math.max(a.P.s,b.P.s),to=z-1;let ia=0,ib=0,hit=null;
     for(let t=from;t<=to;t++){while(a.P.records[ia].v<=t)ia++;while(b.P.records[ib].v<=t)ib++;if(a.P.records[ia].C===b.P.records[ib].C){hit={J:a.P.records[ia].C,t};break}}
     ok(hit&&hit.J===F.J&&hit.t===F.t,"literal first contact oracle");oracle++;
   }
 }
 function add(k,e,cap){
   let c=constraints.get(k);if(!c){c={cap,es:[],degree:0,done:false};constraints.set(k,c)}ok(close(c.cap,cap),"fixed quota");c.es.push(e);c.degree+=e.w;
   if(!inc.has(e))inc.set(e,[]);inc.get(e).push(c);
 }
 let maxComp=0,maxSmall=0,maxParent=0,compBound=0;
 for(const p of parents.values()){
   const j=p.j,upper=j?cuts[j-1]:g.C,K=cuts[j],n=upper-K;let envelope=0;
   for(let J=Math.max(K+2,2*X-2);J<=upper;J+=2)for(let s=0;s<2;s++)for(const q of fac(J+2*s)){
     if(q<=y||q>B||q*f<g.r)continue;let res=s?q+2:0,lo=z-2*g.r-3*(g.C-K),hi=z-1;
     envelope+=Math.max(0,Math.floor((hi-res)/(2*q))-Math.ceil((lo-res)/(2*q))+1)
   }
   ok(p.groups[1].size<=envelope,"comparable shell envelope");ok(p.groups[0].size<=Math.floor(n/2)+1,"root singleton shell envelope");
   maxComp=Math.max(maxComp,p.groups[1].size);maxSmall=Math.max(maxSmall,p.groups[2].size);maxParent=Math.max(maxParent,...p.groups.map(s=>s.size));compBound=Math.max(compBound,envelope);
 }
 for(const e of edges){
   alive.add(e);const j=e.shell,p=parents.get(j+"|"+e.parent),theta=1/(j+1)**2;
   for(const [v,o] of [[e.i,e.j],[e.j,e.i]]){const a=levels[j].get(o),ty=a.root?0:a.q*f>=g.r?1:2;add(v+"|"+j+"|"+a.key,e,m*theta/Math.max(1,p.groups[ty].size))}
 }
 const queue=[...constraints.values()].filter(c=>c.degree<=c.cap+1e-10);
 for(let i=0;i<queue.length;i++){const c=queue[i];if(c.done||c.degree>c.cap+1e-10)continue;c.done=true;
   for(const e of c.es){if(!alive.delete(e))continue;shellPaid[e.shell]+=e.w;
     for(const a of inc.get(e)){let before=a.degree;a.degree-=e.w;if(before>a.cap+1e-10&&a.degree<=a.cap+1e-10)queue.push(a)}}
 }
 let budget=0;for(const c of constraints.values())budget+=c.cap;let minCompPartners=null,keptPairs=0;
 for(const e of alive){
   keptPairs++;shellRemain[e.shell]+=e.w;remTypes[e.first.type]+=e.w;for(const c of inc.get(e))ok(c.degree>c.cap-1e-9,"multiscale core");
   for(const [v,o] of [[e.i,e.j],[e.j,e.i]]){const a=levels[e.shell].get(o);if(!a.root&&a.q*f>=g.r){const cs=constraints.get(v+"|"+e.shell+"|"+a.key),n=cs.es.filter(x=>alive.has(x)).length;ok(n>2*cs.cap-1e-8,"actual opposite partners");minCompPartners=minCompPartners===null?n:Math.min(minCompPartners,n)}}
 }
 const vertices=new Set(edges.flatMap(e=>[e.i,e.j]));
 ok(budget<=6*m*vertices.size+1e-7,"summable capacity");ok(shellPaid.reduce((a,b)=>a+b,0)<=budget+1e-7,"absolute multiscale budget");
 for(let j=0;j<cuts.length;j++)ok(close(shellRaw[j],shellPaid[j]+shellRemain[j]),"shell ledger");
 return {cuts,shellRaw,shellPaid,shellRemain,shellPairs,types,remTypes,oracle,budget,vertices:vertices.size,keptPairs,parents:parents.size,maxComp,maxSmall,maxParent,compBound,minCompPartners};
}
// Exact compressed inverse stationary intervals, primorial entry cuts and cohort quotas.
function audit(X,stress=true,scaleCap=4,entropyCap=1,fComp=null){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,u=Math.log(B),D=Math.max(1,Math.floor(stress?B/4:B/u**2)),rmin=Math.max(3,Math.ceil(D/4)),eta=stress?1/8:u**(-1/4),f=stress?4:u**(1/16),m=stress?4:u**(11/4),L=stress?30:2,y=stress?5:2;
 const ok=(x,s)=>{if(!x)throw Error(s)},close=(a,b)=>Math.abs(a-b)<1e-7*Math.max(1,Math.abs(a),Math.abs(b));
 const sp=new Int32Array(8*X+100);for(let i=2;i<sp.length;i++)if(!sp[i])for(let j=i;j<sp.length;j+=i)if(!sp[j])sp[j]=i;
 function gcd(a,b){while(b){let z=a%b;a=b;b=z}return a}
 function fac(n){let a=[];while(n>1){let p=sp[n];a.push(p);while(n%p===0)n/=p}return a}
 function rr(C){let p=Math.min(sp[C-1]||Infinity,sp[C+1]||Infinity);return p<=B?p:0}
 function select(t,C){let k=t%2,p=sp[gcd(t-2*k,C+2*k-1)]||0;return p<=B?p:0}
 const slots=new Map(),paths=new Map();let clock=0,roughVisits=0;
 for(let M=X+1;M<2*X;M+=2){
   let s=M+2,t=s,C=2*M-2,records=[];
   ok(s+H+2*B<=Math.floor((7*M-1)/4),"gate");
   const P={M,s,records,end:0,min:null};paths.set(M,P);
   while(t<s+H){
     let r=rr(C);if(!r)break;
     let b=t,p=0;while(!p){t++;p=select(t,C)}
     ok(t-b<=2*r,"wait");
     const e={C,b,v:t,p,r,P,i:records.length,post:2*t-(C+p-1)};records.push(e);
     if(r>=rmin&&r>L+1){
       let key=C+','+t,g=slots.get(key);if(!g){g={C,v:t,p,r,entries:[]};slots.set(key,g)}g.entries.push(e);roughVisits++;
     }
     C+=p-1;ok(C<=2*t,"deficit");
   }
   P.end=t;P.endC=C;clock+=t-s;
   const min=new Int32Array(records.length);let d=2*t-C;for(let i=records.length-1;i>=0;i--){d=Math.min(d,records[i].post);min[i]=d}P.min=min;
 }
 function previous(C,t){
   let a=Math.ceil(C/2);
   for(let k=0;k<2;k++)for(const p of fac(C+2*k-1)){
     if(p>B)continue;let res=k?p+2:0,b=res+2*p*Math.floor((t-res)/(2*p));a=Math.max(a,b);
   }
   return a;
 }
 function inv(C,t,lo){
   const a=previous(C,t),out=[];
   ok(a<=t,"stationary interval");
   for(let k=0;k<2;k++)for(const p of fac(C+2*k)){
     if(p>B||p===2)continue;
     let res=k?p+2:0,b=res+2*p*Math.ceil((a-res)/(2*p));
     for(;b<=t;b+=2*p){
       let J=C-p+1;if(J<2*lo-2||J>2*(b-1))continue;
       if(select(b,J)===p)out.push({b,J,p,side:k});
     }
   }
   return {a,out};
 }
 function reverse(g,z,cut=null){
   const C0=g.C,t0=z-1,low0=Math.max(X+1,g.v-2*g.r-H-1);
   const memo=new Map(),found=new Set(),front=[],stats={queries:0,edges:0,stationaryTicks:0,maxInterval:0,frontiers:0,intervalOracle:0};
   // Exact partial exploration: stop below/at a horizon cut, retain a safe original-source interval.
   function go(C,t,lo,top=false){
     lo=Math.max(lo,X+1,t-H-2*B-2);
     const hi=Math.min(2*X-1,C/2+1,t-2);
     if(lo>hi||C>2*t||C<2*X-2)return;
     const k=C+','+t+','+lo+','+Number(top);
     if(memo.has(k))return;memo.set(k,1);
     if(!top&&cut!==null&&C<=cut){front.push([lo,hi]);stats.frontiers++;return}
     stats.queries++;
     const {a,out}=inv(C,t,lo);
     stats.stationaryTicks+=t-a+1;stats.maxInterval=Math.max(stats.maxInterval,t-a+1);
     if(stats.intervalOracle<64){
       let literal=Math.ceil(C/2);for(let b=t;b>=Math.ceil(C/2);b--)if(select(b,C)){literal=b;break}
       ok(a===literal,"stationary last eligible tick oracle");
       // All actual one-step incoming events across the compressed interval.
       const expected=new Set();
       for(let b=a;b<=t;b++){
         let side=b%2,h=gcd(b-2*side,C+2*side);
         for(const p of fac(h)){
           if(p===2||p>B)continue;let J=C-p+1;
           if(J<2*lo-2||J>2*(b-1))continue;
           if(select(b,J)===p)expected.add(b+','+J+','+p);
         }
       }
       ok(expected.size===out.length&&out.every(e=>expected.has(e.b+','+e.J+','+e.p)),"incoming arithmetic oracle");
       stats.intervalOracle++;
     }
     const M=C/2+1,s=M+2;
     if(M%2===1&&M>=lo&&M<=hi&&s>=a&&s<=t)found.add(M);
     for(const e of out){
       stats.edges++;
       // Only the top target arrival needs the original nominal stop condition.
       const nextLo=top?Math.max(lo,e.b-H-1):lo;
       go(e.J,e.b-1,nextLo);
     }
   }
   go(C0,t0,low0,true);
   const possible=new Set(found);
   for(const [a,b] of front)for(let M=Math.ceil(a);M<=b;M++)if(M%2===1)possible.add(M);
   return {found,possible,stats};
 }
 // The first entry into the final even-primorial block is independent of the later last nonLOW anchor.
 function entry(e,K){
   const P=e.P;
   if(2*P.M-2>K)return {key:"root",q:0,J:2*P.M-2,t:P.s};
   for(let j=0;j<e.i;j++){
     const x=P.records[j],J=x.C+x.p-1;
     if(J>K){ok(x.C<=K&&x.p>y,"primorial block entry");return {key:J+','+x.v+','+x.p,q:x.p,J,t:x.v}}
   }
   throw Error("missing block entry");
 }
 function capGroup(edges,groups){
   const alive=new Set(edges),inc=new Map(),constraints=new Map();
   function add(k,e,cap){if(!constraints.has(k))constraints.set(k,{es:[],degree:0,cap,done:false});let z=constraints.get(k);z.es.push(e);z.degree+=e.w;if(!inc.has(e))inc.set(e,[]);inc.get(e).push(z)}
   const comp=new Set([...groups.values()].filter(g=>g.q&&g.q*f>=g.r).map(g=>g.key));
   const small=new Set([...groups.values()].filter(g=>g.q&&g.q*f<g.r).map(g=>g.key));
   for(const e of edges)for(const [v,o] of [[e.i,e.j],[e.j,e.i]]){
     let own=groups.get(v),other=groups.get(o);
     let cap=own.key===other.key?m:m/Math.max(1,comp.has(other.key)?comp.size:small.size);
     add(v+'|'+other.key,e,cap);
   }
   const queue=[...constraints.values()].filter(c=>c.degree<=c.cap+1e-10);
   let paid=0;
   for(let i=0;i<queue.length;i++){
     const c=queue[i];if(c.done||c.degree>c.cap+1e-10)continue;c.done=true;
     for(const e of c.es){
       if(!alive.delete(e))continue;paid+=e.w;
       for(const z of inc.get(e)){let prev=z.degree;z.degree-=e.w;if(prev>z.cap+1e-10&&z.degree<=z.cap+1e-10)queue.push(z)}
     }
   }
   let budget=0,minCompPartners=Infinity,kept=[...alive];
   for(const c of constraints.values())budget+=c.cap;
   for(const e of kept)for(const c of inc.get(e))ok(c.degree>c.cap-1e-9,"entry-cohort fixed core");
   for(const e of kept)for(const [v,o] of [[e.i,e.j],[e.j,e.i]])if(groups.get(v).key!==groups.get(o).key&&comp.has(groups.get(o).key)){
     const z=constraints.get(v+'|'+groups.get(o).key);minCompPartners=Math.min(minCompPartners,z.es.filter(e=>alive.has(e)).length);
   }
   ok(paid<=budget+1e-7&&budget<=3*m*groups.size+1e-7,"entry quota capacity");
   return {paid,remaining:kept.reduce((s,e)=>s+e.w,0),budget,edges:kept.length,comp:comp.size,small:small.size,minCompPartners:Number.isFinite(minCompPartners)?minCompPartners:null};
 }
 const sorted=[...slots.values()].sort((a,b)=>b.entries.length-a.entries.length||a.C-b.C||a.v-b.v);
 const pick=new Map();for(const g of sorted.slice(0,6))pick.set(g.C+','+g.v,g);
 for(let j=1;j<=6;j++){const g=sorted[Math.floor((sorted.length-1)*j/7)];if(g)pick.set(g.C+','+g.v,g)}
 const ledgers=[0,1].map(()=>({seen:new Set(),pairs:new Map(),keys:new Map(),contacts:new Map()}));
 const out=[];let checks=0,maxRoots=0,totalQuery=0,totalEdges=0,totalStationary=0;
 for(const g of pick.values()){
   const z=Math.min(g.v-1,Math.max(...g.entries.map(e=>e.b))+1);
   if(z<=Math.min(...g.entries.map(e=>e.b)))continue;
   const live=g.entries.filter(e=>e.b<z),expected=new Set(live.map(e=>e.P.M));
   const K=L*Math.floor((g.C-1)/L),lam=2*z-g.C,ell=Math.max(1,Math.floor(eta*g.r));
   if(lam<1)continue;
   const ex=reverse(g,z);
   ok(ex.found.size===expected.size&&[...expected].every(M=>ex.found.has(M)),"exact compressed inverse vs original forward roots");
   const partial=[K,K-4*L,K-16*L].map(c=>{let q=reverse(g,z,c);ok([...expected].every(M=>q.possible.has(M)),"partial reverse support");return {cut:c,upper:q.possible.size,known:q.found.size,queries:q.stats.queries,frontiers:q.stats.frontiers}});
   ok(partial[1].upper<=partial[0].upper&&partial[2].upper<=partial[1].upper,"nested frontier upper envelopes");
   checks++;maxRoots=Math.max(maxRoots,expected.size);totalQuery+=ex.stats.queries;totalEdges+=ex.stats.edges;totalStationary+=ex.stats.stationaryTicks;
   const groups=new Map(),actualComp=new Set();let rootsInside=0,largestGroup=0;const counts=new Map();
   for(const e of live){
     let a=entry(e,K);a.r=g.r;groups.set(e.P.M,a);
     ok(a.J>K&&a.J<=g.C&&a.t<=z-1&&z-a.t<=2*g.r+3*L,"block entry window");
     if(!a.q)rootsInside++;else if(a.q*f>=g.r)actualComp.add(a.key);
     counts.set(a.key,(counts.get(a.key)||0)+1);largestGroup=Math.max(largestGroup,counts.get(a.key));
   }
   ok(rootsInside<=L/2+1,"inside roots");
   let compEnvelope=0;
   for(let J=K+2;J<=g.C;J+=2)for(let side=0;side<2;side++)for(const p of fac(J+2*side)){
     if(p<=y||p>B||p*f<g.r)continue;
     let res=side?p+2:0,lo=z-2*g.r-3*L,hi=z-1;
     compEnvelope+=Math.max(0,Math.floor((hi-res)/(2*p))-Math.ceil((lo-res)/(2*p))+1);
   }
   ok(actualComp.size<=compEnvelope,"comparable entry arithmetic envelope");
   // Same original delayed masks, one charged level lambda at sampled origin.
   const byClass=[[],[],[]];
   for(const e of g.entries){
     let q=0;for(let j=e.i-1;j>=0;j--)if(e.P.records[j].p>y){q=e.P.records[j].p;break}
     byClass[q===0?0:q*f>=g.r?1:2].push(e);
   }
   const gates=byClass.map(a=>{a.sort((x,y)=>x.b-y.b);return a.length>(stress?12:u**2.75)?a[Math.floor(stress?12:u**2.75)].b:Infinity});
   const modes=[];
   for(let mode=0;mode<2;mode++){
     let ret=[];
     for(let c=0;c<3;c++)for(const e of byClass[c]){
       if(e.b>=z||g.p>f*g.r||(mode===0?g.p<=Math.ceil(B**.25):2*(g.v-e.b)<=g.p-1))continue;
       let lo=Math.max(e.b+ell+1,gates[c]+ell,mode===0?e.P.s+2*B:e.b),hi=mode===0?Math.min(g.v,e.P.s+H):g.v;
       if(lo>=hi)continue;ret.push({e,lo,hi,w:(hi-lo)/(2*g.r)});
     }
     let raw=0,inside=0,edges=[],allEdges=[],same=0,cross=0;
     for(let i=0;i<ret.length;i++)for(let j=i+1;j<ret.length;j++){
       let a=ret[i],b=ret[j],F=a.e.b>=b.e.b?a:b,O=F===a?b:a,early=a.e.P.end<=b.e.P.end?a.e:b.e;
       if(z+ell<F.lo||z+ell>=F.hi||lam>early.P.min[early.i])continue;
       let w=O.w/2,ii=a.e.P.M,jj=b.e.P.M;raw+=w;allEdges.push({i:ii,j:jj,w});
       if(!groups.get(ii).q||!groups.get(jj).q){inside+=w;continue}
       edges.push({i:ii,j:jj,w});
       if(groups.get(ii).key===groups.get(jj).key)same+=w;else cross+=w;
     }
     const vertices=new Map();for(const e of edges){vertices.set(e.i,groups.get(e.i));vertices.set(e.j,groups.get(e.j))}
     let c=capGroup(edges,vertices);
     ok(close(raw,inside+c.paid+c.remaining)&&close(same+cross,c.paid+c.remaining),"sample origin energy ledger");
     const ms=multiscale(g,live,z,allEdges,L,y,B,X,f,stress?scaleCap:u**2.75,ok,close,fac,ledgers[mode]);
     ok(close(raw,ms.shellRaw.reduce((a,b)=>a+b,0)),"all original charges assigned once");
     modes.push({mode:mode?"full-positive":"late-high",raw,inside,same,cross,...c,multiscale:ms});
   }
   out.push({C:g.C,v:g.v,z,lambda:lam,r:g.r,roots:expected.size,exact:ex.stats,partial,entryGroups:counts.size,largestGroup,rootsInside,actualComp:actualComp.size,compEnvelope,modes});
 }
 const Q=Math.max(5,Math.ceil(B/4)),support=[0,0];
 for(let p=Q;p<=B;p++)if(sp[p]===p)for(let s=0;s<2;s++)for(let k=0;6*s+2*p*k<=12*B+6;k++){
   const d=6*s+2*p*k;
   const j0=2*p*Math.ceil((2*X-2+2*s)/(2*p))-2*s;
   for(let J=j0;J<7*X;J+=2*p){
     let t=(J+d)/2;
     if(t%2!==s||(t-2*s)%p)continue;
     support[k===0?0:1]++;
   }
 }
 const firstContact=ledgers.map(g=>{
   let stats=[0,1].map(ty=>({keys:0,weight:0,quotaPaid:0,remaining:0,maxPairs:0}));
   for(const v of g.pairs.values())ok(v<=6*B+3+1e-6,"aggregate original terminal pair budget");
   for(const c of g.keys.values()){const i=c.reset?0:1,z=stats[i],cap=i===0?32:8;z.keys++;z.weight+=c.w;z.quotaPaid+=Math.min(c.w,cap);z.remaining+=Math.max(0,c.w-cap);z.maxPairs=Math.max(z.maxPairs,c.pairs.size)}
   for(let i=0;i<2;i++)ok(stats[i].keys<=support[i],"large first-contact key arithmetic envelope");
   return {Q,support,pairLevels:g.seen.size,distinctPairs:g.pairs.size,stats};
 });
 const entropy=ledgers.map(g=>entropyAudit(g,X,B,paths,rr,fac,sp,entropyCap,ok,close));
 const recipient=ledgers.map(g=>recipientAudit(g,X,B,L,y,fComp??f,paths,rr,fac,entropyCap,ok,close));
 const ascent=ledgers.map(g=>ascentAudit(g,X,B,L,y,paths,rr,ok,close)),ascentLow3=ledgers.map(g=>ascentAudit(g,X,B,6,3,paths,rr,ok,close));
 return {X,B,L,y,rmin,f,m,scaleCap,entropyCap,entropy,recipient,ascent,ascentLow3,firstContact,clock,roughVisits,slots:slots.size,checks,maxRoots,totalQuery,totalEdges,totalStationary,out};
}
{const test=[];let C=100;for(let i=0;i<8;i++){let r=3*4**i+2;test.push({lo:C-Math.ceil(r/2),hi:C,r});C+=r-1}allocateStrips(test,(x,msg)=>{if(!x)throw Error(msg)});}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[4096,16384,65536]))console.log(JSON.stringify(audit(X,true,16,8)));
