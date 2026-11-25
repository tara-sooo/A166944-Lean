// Primitive projected diamonds and close-label arithmetic halos; original exit-rank controls.
function audit(X, mode="diagnostic"){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),T=mode==="analytic"?Math.floor(X/u**.25):4*B,H=T+B,Q=Math.max(5,Math.ceil(B/(mode==="analytic"?u:8))),delta=mode==="analytic"?Math.min(.5,Math.sqrt(B*u/H)):mode==="stress"?.5:.2,lim=7*X+5;
 const spf=new Int32Array(lim+1),ok=(b,s)=>{if(!b)throw Error(`${X}/${mode}: ${s}`)},mod=(a,b)=>((a%b)+b)%b,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c;}return a;},ch=n=>n*(n-1)/2,phys=e=>`${e.C}:${e.t}`;
 for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n*n<=lim)for(let k=n*n;k<=lim;k+=n)spf[k]=spf[k]||n;}
 const fs=n=>{const a=[];while(n>1){const p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const roots=[],rootMap=new Map(),visits=new Map(),cont=new Map(),original=new Map(),groups=new Map();
 let N=0,G=0,R=0,literal=0,events=0,rankChecks=0,rankLog=0,rankMarked=0,rankCost=0,rankActual=0,rawHigh=0,rawActual=0,rawHits=0,stableHigh=0,stableActual=0,stableHits=0,arrivalPairsBefore=0,arrivalWeightBefore=0,arrivalPairsStable=0,arrivalWeightStable=0;
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){
   N++;const a=[];let C=2*M-2,t=M+2,cut=Math.floor((7*M-1)/4);
   while(true){
     const e={M,C,t,p:0,r:0,w:0};a.push(e);
     if(C-(2*M-2)>=T)break;
     const f1=fs(C-1),f2=fs(C+1);let s=Infinity,p=Infinity;
     for(const [sig,f] of [[-1,f1],[1,f2]])for(const q of f){
       const tick=t+1+mod((sig===-1?0:q+2)-(t+1),2*q);
       if(tick<s||(tick===s&&q<p)){s=tick;p=q;}
     }
     if(X<=1024){let lt=Infinity,lp=Infinity;for(let j=t+1;j<=cut;j++){const f=fs(gcd(j%2?j-2:j,C+(j%2?1:-1)));if(f.length){lt=j;lp=f[0];break;}}ok((s>cut&&lt===Infinity)||(s===lt&&p===lp),"literal clock");literal++;}
     if(s>cut)break;
     const r=Math.min(...f1,...f2);e.p=p;e.r=r;e.w=s-t;e.J=C+p-1;e.s=s;
     ok(e.w>0&&e.w<=2*r&&r<=p&&e.J<=2*s,"original clock");
     e.high=p>=Q&&r>p/(mode==="analytic"?Math.sqrt(Math.log(p)):2);
     if(e.high){rawHigh+=r;rawActual+=e.w;rawHits++;const k=`${e.J}:${s}:${p}`;if(!original.has(k))original.set(k,[]);original.get(k).push(e);}
     R+=r;events++;C=e.J;t=s;
   }
   const gain=C-(2*M-2);ok(gain<T+B,"gain stop");G+=gain;roots.push(a);rootMap.set(M,a);
 }
 // Frozen original natural high centre support, independent of all later masks.
 const J0=mode==="analytic"?Math.max(2,Math.floor(u**.125)):mode==="stress"?32:8,kappa=mode==="analytic"?Math.max(2,Math.floor(u**.25)):mode==="stress"?4:2;
 const centerKey=e=>e.C+":"+e.p,centers=new Map(),bad=new Set();
 for(const a of roots)for(const e of a)if(e.high&&e.r>3){ok(e.C%6===0,"rough high horizon");const k=centerKey(e);if(!centers.has(k))centers.set(k,{C:e.C,p:e.p,count:0});centers.get(k).count++;}
 const cs=[...centers.values()].sort((a,b)=>a.C-b.C||a.p-b.p);
 let conflictPairs=0,conflictPairWeight=0,conflictChecks=0,badWeight=0,badTagWeight=0,maxConflictGap=0,maxConflictLabelGap=0;
 for(let i=0;i<cs.length;i++)for(let j=i+1;j<cs.length&&cs[j].C-cs[i].C<=J0;j++){
   const x=cs[i],y=cs[j];conflictChecks++;
   if(x.p===y.p||Math.abs(x.p-y.p)>J0)continue;
   const sx=(x.C-1)%x.p===0?-1:1,sy=(y.C-1)%y.p===0?-1:1;
   ok(mod(x.C+sx,x.p)===0&&mod(x.C+(y.C-x.C)+sy,y.p)===0,"actual shifted CRT center");
   bad.add(centerKey(x));bad.add(centerKey(y));conflictPairs++;conflictPairWeight+=x.p+y.p;
   maxConflictGap=Math.max(maxConflictGap,y.C-x.C);maxConflictLabelGap=Math.max(maxConflictLabelGap,Math.abs(x.p-y.p));
 }
 for(const k of bad){const c=centers.get(k);badWeight+=c.p;badTagWeight+=c.p*c.count;}
 ok(badWeight<=conflictPairWeight,"unique support weighted bound");
 let haloProxyAll=0,haloActualAll=0,haloGainAll=0,haloHitsAll=0,haloCenterTags=0,haloBound=0,haloRootChecks=0,haloCenterChecks=0;
 for(const a of roots){
   const b=a.filter(e=>e.high&&e.r>3&&bad.has(centerKey(e)));let mass=0,cost=0;
   for(const e of b){mass+=e.p;haloCenterTags++;}
   for(const e of a)if(e.high&&b.some(f=>e.C>=f.C-kappa*f.p&&e.J<=f.C+kappa*f.p)){
     e.halo=true;haloProxyAll+=e.r;haloActualAll+=e.w;haloGainAll+=e.p-1;haloHitsAll++;cost+=e.p-1;
   }
   for(const e of b){ok(e.halo,"marked center itself");haloCenterChecks++;}
   ok(cost<=2*kappa*mass,"disjoint gain intervals in union of center halos");haloBound+=2*kappa*mass;haloRootChecks++;
 }
 ok(haloBound===2*kappa*badTagWeight&&haloProxyAll<=1.5*haloGainAll&&haloActualAll<=3*haloGainAll&&haloGainAll<=haloBound,"global halo linear bound");
 // Independent original source order; terminal snapshots counted in rank, not in completed mass.
 for(let k=roots.length-1;k>=0;k--){
   const a=roots[k];let prev=1,sum=0,marks=0;
   for(const e of a){const id=phys(e);e.d=(visits.get(id)||0)+1;visits.set(id,e.d);ok(e.d>=prev,"rank monotone");rankChecks++;prev=e.d;if(e.p)cont.set(id,(cont.get(id)||0)+1);}
   for(let i=0;i+1<a.length;i++){
     const e=a[i],f=a[i+1],inc=Math.log(f.d/e.d);
     ok(f.C===e.J&&f.t===e.s&&inc>=0,"actual successor rank");sum+=inc;
     if(!e.high)continue;
     if(inc>delta){rankMarked++;rankCost+=e.r;rankActual+=e.w;marks++;continue;}
     stableHigh+=e.r;stableActual+=e.w;stableHits++;e.stable=true;
     const k=`${e.J}:${e.s}:${e.p}`;if(!groups.has(k))groups.set(k,[]);groups.get(k).push(e);
   }
   rankLog+=sum;ok(Math.abs(sum-Math.log(a.at(-1).d/a[0].d))<1e-8&&a[0].d===1&&marks*delta<=sum+1e-8,"telescoped rank log");
 }
 ok(rankLog<=N*Math.log(N)+1e-6&&rankCost<=B*rankLog/delta+1e-6&&rawHigh===rankCost+stableHigh&&rawActual===rankActual+stableActual,"rank budget");
 function births(ar){
   const by=new Map();for(const e of ar)by.set(phys(e),(by.get(phys(e))||0)+1);
   const pairs=ch(ar.length)-[...by.values()].reduce((s,n)=>s+ch(n),0);return {pairs,weight:2*ar[0].r*pairs};
 }
 for(const ar of original.values()){const b=births(ar);arrivalPairsBefore+=b.pairs;arrivalWeightBefore+=b.weight;}
 let foreignCost=0,foreignActual=0,foreignHits=0,retainedHigh=0,retainedActual=0,retainedHits=0,foreignBound=0,foreignGroups=0,groupChecks=0,maxForeign=0,postFibres=new Map(),horizons=new Map(),selectedPre=new Set(),terminalMixed=0;
 for(const [key,ar] of groups){
   const b=births(ar);arrivalPairsStable+=b.pairs;arrivalWeightStable+=b.weight;
   ar.sort((a,b)=>a.M-b.M);
   const e=ar[0],id=phys(e),r=e.r,post=`${e.J}:${e.s}`,dpre=e.d;
   const a=rootMap.get(e.M);
   const f=a.find(f=>f.C===e.J);
   ok(f&&f.t===e.s&&dpre<=cont.get(id),"pre/post original membership");
   let bad=0;for(const q of ar){
     ok(q.r===r&&q.C===e.C&&q.p===e.p&&q.J===e.J&&q.s===e.s,"same-label exit key");
     if(phys(q)!==id){bad++;foreignCost+=r;foreignActual+=q.w;foreignHits++;continue;}
     retainedHigh+=r;retainedActual+=q.w;retainedHits++;
     if(!horizons.has(q.C))horizons.set(q.C,new Map());
     const m=horizons.get(q.C),k=phys(q);if(!m.has(k))m.set(k,{p:q.p,s:q.s,r,n:0,t:q.t,after:0,rep:q.M});m.get(k).n++;m.get(k).rep=Math.max(m.get(k).rep,q.M);if(!q.halo)m.get(k).after++;
     if(!postFibres.has(key))postFibres.set(key,new Set());postFibres.get(key).add(phys(q));
   }
   ok(!selectedPre.has(id),"each chosen pre state once");selectedPre.add(id);
   ok(bad<=f.d-dpre&&f.d-dpre<=Math.expm1(delta)*dpre+1e-7,"foreign rank bound");
   foreignBound+=r*Math.expm1(delta)*cont.get(id);
   groupChecks++;if(bad){foreignGroups++;maxForeign=Math.max(maxForeign,bad);}
   if(visits.get(post)> (cont.get(post)||0))terminalMixed++;
 }
 ok([...postFibres.values()].every(s=>s.size===1),"post fibres single predecessor");
 ok(foreignCost<=foreignBound+1e-6&&foreignBound<=Math.expm1(delta)*R+1e-6,"global foreign budget");
 ok(stableHigh===foreignCost+retainedHigh&&stableActual===foreignActual+retainedActual&&stableHits===foreignHits+retainedHits,"priority partition");
 let diamondChecks=0,diamondShort=0,diamondWithHigh=0,diamondBothHigh=0,diamondSharedLabel=0,sharedLabelChecks=0,sameLabelSpacingChecks=0,oneEach=0,oneEachSmall=0,oneEachClose=0,oneEachNearCurrent=0,oneEachCurrentMasked=0,dominantMultisetChecks=0,dominantMultisetEqual=0,diamondMaxSpan=0,farBucketChecks=0,farWithDiamond=0,farWithShort=0,farWithOneEach=0,farWithOneEachSmall=0,farWithNear=0,farWithSharedLabel=0,farNoReturn=0,farSameAfter=0,postHaloProxy=0,haloRetainedHits=0,haloRetainedProxy=0,farBothRepresentativesMasked=0;
 const sample=[];
 function scan(x,y,C,weight){
   const a=rootMap.get(x.rep),b=rootMap.get(y.rep);let i=a.findIndex(e=>e.C===C),j=b.findIndex(e=>e.C===C);ok(i>=0&&j>=0&&a[i].p===b[j].p,"actual far start");
   const initialA=a[i],initialB=b[j];let any=false,short=false,one=false,small=false,near=false,shared=false,unreturned=false;
   while(i+1<a.length&&j+1<b.length){
     const l=i,m=j,D=a[l].C;ok(D===b[m].C,"common projected anchor");
     i++;j++;while(i<a.length&&j<b.length&&a[i].C!==b[j].C){if(a[i].C<b[j].C)i++;else j++;}
     if(i===a.length||j===b.length){if(a[l].p!==b[m].p)unreturned=true;break;}
     const end=a[i].C,L=end-D;ok(L>0,"strict common projection");
     if(a[l].p===b[m].p){ok(i===l+1&&j===m+1,"same projected outgoing edge");continue;}
     any=true;diamondChecks++;diamondMaxSpan=Math.max(diamondMaxSpan,L);
     const aa=a.slice(l,i),bb=b.slice(m,j),sa=new Set(aa.slice(1).map(e=>e.C));
     ok(!bb.slice(1).some(e=>sa.has(e.C))&&aa.at(-1).p!==bb.at(-1).p,"primitive projected diamond disjoint interiors and distinct incoming");
     ok(aa.reduce((s,e)=>s+e.p-1,0)===L&&bb.reduce((s,e)=>s+e.p-1,0)===L,"equal selected gain sums");
     const ha=aa.filter(e=>e.high&&e.r>3),hb=bb.filter(e=>e.high&&e.r>3);
     if(L<3*(Q-1)){short=true;diamondShort++;}
     if(ha.length||hb.length)diamondWithHigh++;if(ha.length&&hb.length)diamondBothHigh++;
     const ma=new Map(),mb=new Map();
     for(const [hh,mm] of [[ha,ma],[hb,mb]])for(const e of hh){if(!mm.has(e.p))mm.set(e.p,[]);mm.get(e.p).push(e.C);}
     let thisShared=false;
     for(const [p,ca] of ma)if(mb.has(p)){
       thisShared=true;shared=true;sharedLabelChecks++;
       const vals=ca.concat(mb.get(p)).sort((a,b)=>a-b);
       for(let k=1;k<vals.length;k++){const h=vals[k]-vals[k-1];ok(h>=2*(p-1),"shared rough label spacing in diamond");sameLabelSpacingChecks++;}
       ok(L>=(2*vals.length-1)*(p-1),"multiplicity diamond gain lower bound");
       ok(L>=3*(p-1),"shared high label forbidden in short diamond");
     }
     if(thisShared)diamondSharedLabel++;
     if(L<3*(Q-1))ok(!thisShared,"short diamond disjoint high alphabets");
     if(ha.length&&ha.length===hb.length){
       dominantMultisetChecks++;
       const va=ha.map(e=>e.p).sort((a,b)=>a-b),vb=hb.map(e=>e.p).sort((a,b)=>a-b);
       if(va.every((p,k)=>p===vb[k])){dominantMultisetEqual++;const P=va.at(-1);ok(L>=3*(P-1),"equal multiset largest label barrier");}
     }
     if(ha.length===1&&hb.length===1){
       one=true;oneEach++;const p=ha[0].p,q=hb[0].p,ga=L-(p-1),gb=L-(q-1);
       if(ga<=J0&&gb<=J0&&J0<Math.min(p,q)-1){
         small=true;oneEachSmall++;ok(p!==q&&Math.abs(p-q)<=J0&&Math.abs(ha[0].C-hb[0].C)<=J0,"one-high small-background close distinct centers");
         ok(bad.has(centerKey(ha[0]))&&bad.has(centerKey(hb[0]))&&ha[0].halo&&hb[0].halo,"both actual center incidences masked");oneEachClose++;
         const na=initialA.C>=ha[0].C-kappa*p&&initialA.J<=ha[0].C+kappa*p,nb=initialB.C>=hb[0].C-kappa*q&&initialB.J<=hb[0].C+kappa*q;
         if(na&&nb){near=true;oneEachNearCurrent++;ok(initialA.halo&&initialB.halo,"nearby prior common high gain covered by both actual halos");oneEachCurrentMasked++;}
         if(sample.length<6)sample.push({C,start:D,end,p,q,ga,gb,centers:[ha[0].C,hb[0].C],near});
       }
     }
     if(a[i].t===b[j].t)break; // after physical synchronization there cannot be a later primitive divergence.
   }
   if(unreturned)farNoReturn+=weight;if(any)farWithDiamond+=weight;if(short)farWithShort+=weight;if(one)farWithOneEach+=weight;if(small)farWithOneEachSmall+=weight;if(near)farWithNear+=weight;if(shared)farWithSharedLabel+=weight;
   if(initialA.halo&&initialB.halo)farBothRepresentativesMasked+=weight;farBucketChecks++;
 }
 let E=0,diag=0,sync=0,same=0,cross=0,maxLabels=0,exitPairChecks=0,closeCounts=[0,0,0],nearSame=[0,0,0],nearAll=[0,0,0],farSame=[0,0,0],Ks=[1,2,4],byLabelEnergy=0,exitCongruences=0,actualLagChecks=0;
 for(const [C,m] of horizons){
   const a=[...m.values()],r=a[0].r,n=a.reduce((s,x)=>s+x.n,0),pops=new Map();
   E+=r*n*n;
   for(const e of a){
     ok(e.r===r,"common least factor");postHaloProxy+=r*e.after;haloRetainedHits+=e.n-e.after;haloRetainedProxy+=r*(e.n-e.after);diag+=r*e.n;sync+=r*e.n*e.n;pops.set(e.p,(pops.get(e.p)||0)+e.n);
     const sig=(C-1)%e.p===0?-1:1;
     ok(mod(e.s-(sig===-1?0:e.p+2),2*e.p)===0,"exit phase");exitCongruences++;
   }
   const cap=fs(C-1).concat(fs(C+1)).filter(p=>p>=Q).length;
   ok(pops.size<=cap,"available high labels");if(Q**3>7*X+2)ok(cap<=4,"four-label arithmetic bound");
   maxLabels=Math.max(maxLabels,pops.size);let localSame=0;
   for(const k of pops.values())localSame+=r*k*k;
   byLabelEnergy+=localSame;ok(r*n*n<=pops.size*localSame,"local label Cauchy");
   for(let i=0;i<a.length;i++)for(let j=i+1;j<a.length;j++){
     const x=a[i],y=a[j],d=Math.abs(x.s-y.s),w=2*r*x.n*y.n;exitPairChecks++;
     if(x.p===y.p){ok(d>0&&d%(2*x.p)===0,"same-label exits distinct and spaced");same+=w;ok(Math.abs(x.t-y.t)>=d-2*r,"arrival lag transfer");actualLagChecks++;if(d>2*x.p){farSameAfter+=2*r*x.after*y.after;scan(x,y,C,w);}}
     else cross+=w;
     for(let k=0;k<Ks.length;k++){const L=Ks[k];if(d<=2*L*Math.min(x.p,y.p)){nearAll[k]+=w;closeCounts[k]++;}if(x.p===y.p){if(d<=2*L*x.p)nearSame[k]+=w;else farSame[k]+=w;}}
   }
 }
 ok(diag===retainedHigh&&E===sync+same+cross&&byLabelEnergy===sync+same&&E<=maxLabels*byLabelEnergy+1e-7,"energy partition");
 for(let k=0;k<Ks.length;k++){
   ok(nearSame[k]+farSame[k]===same&&nearSame[k]<=2*Ks[k]*sync&&nearAll[k]<=maxLabels*(2*Ks[k]+1)*sync,"bounded degree lag energy");
   ok(E<=maxLabels*((2*Ks[k]+1)*sync+farSame[k])+1e-6,"far same-label sufficient envelope");
 }
 ok(postHaloProxy+haloRetainedProxy===retainedHigh&&farSameAfter<=farSame[0]&&farWithNear<=farWithOneEachSmall&&farWithOneEachSmall<=farWithOneEach&&farWithOneEach<=farWithDiamond,"halo and far partitions");
 return {X,mode,B,T,Q,delta,J0,kappa,centerCount:cs.length,conflictChecks,conflictPairs,conflictPairWeight,badCenters:bad.size,badWeight,badTagWeight,maxConflictGap,maxConflictLabelGap,haloProxyAll,haloActualAll,haloGainAll,haloHitsAll,haloCenterTags,haloBound,haloRootChecks,haloCenterChecks,diamondChecks,diamondShort,diamondWithHigh,diamondBothHigh,diamondSharedLabel,sharedLabelChecks,sameLabelSpacingChecks,oneEach,oneEachSmall,oneEachClose,oneEachNearCurrent,oneEachCurrentMasked,dominantMultisetChecks,dominantMultisetEqual,diamondMaxSpan,farBucketChecks,farWithDiamond,farWithShort,farWithOneEach,farWithOneEachSmall,farWithNear,farWithSharedLabel,farNoReturn,farSameAfter,postHaloProxy,haloRetainedHits,haloRetainedProxy,farBothRepresentativesMasked,sample,N,G,R,events,literal,rankChecks,rankLog,rawHits,rawHigh,rawActual,rankMarked,rankCost,rankActual,stableHits,stableHigh,stableActual,foreignHits,foreignCost,foreignActual,foreignBound,foreignGroups,maxForeign,groupChecks,terminalMixed,arrivalPairsBefore,arrivalWeightBefore,arrivalPairsStable,arrivalWeightStable,retainedHits,retainedHigh,retainedActual,E,diag,sync,same,cross,byLabelEnergy,maxLabels,exitPairChecks,exitCongruences,actualLagChecks,Ks,closeCounts,nearSame,nearAll,farSame};
}
const argv=process.argv.slice(2),mode=argv[0]||'diagnostic',xs=argv.slice(1).map(Number);for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
