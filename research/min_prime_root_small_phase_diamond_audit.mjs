// Broad selected-label close-centre halos and finite primorial phase reduction.
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
 // All selected labels above Y, not only relative-expensive natural high.
 const ell=1+Math.log(u),Y=mode==="analytic"?Math.max(5,Math.ceil(u*u)):mode==="stress"?5:Math.max(5,Math.floor(Q/4)),J0=mode==="analytic"?Math.max(1,Math.floor(ell**.125)):mode==="stress"?32:8,kappa=mode==="analytic"?Math.max(2,Math.floor(ell**.25)):mode==="stress"?4:2;
 const key=e=>e.C+":"+e.p,centers=new Map(),bad=new Set();
 for(const a of roots)for(const e of a)if(e.p>=Y){const k=key(e);if(!centers.has(k))centers.set(k,{C:e.C,p:e.p,n:0});centers.get(k).n++;}
 const cs=[...centers.values()].sort((a,b)=>a.C-b.C||a.p-b.p);
 let conflicts=0,conflictWeight=0,badWeight=0,badTagWeight=0,highBad=0,lowBad=0;
 for(let i=0;i<cs.length;i++)for(let j=i+1;j<cs.length&&cs[j].C-cs[i].C<=J0;j++){
   const a=cs[i],b=cs[j];if(a.p===b.p||Math.abs(a.p-b.p)>J0)continue;
   bad.add(key(a));bad.add(key(b));conflicts++;conflictWeight+=a.p+b.p;
 }
 for(const k of bad){const a=centers.get(k);badWeight+=a.p;badTagWeight+=a.p*a.n;if(a.p<Q)lowBad++;else highBad++;}
 ok(badWeight<=conflictWeight,"bad centre support");
 // Independent exact relaxed CRT envelope, both horizon signs, integer horizons.
 function inv(a,m){let x=1,y=0,b=m;while(b){const q=Math.floor(a/b);[a,b]=[b,a-q*b];[x,y]=[y,x-q*y];}ok(a===1,"distinct prime CRT");return mod(x,m);}
 let arithmeticPairs=0,arithmeticWeight=0,primePairs=0,crtChecks=0;
 for(let p=Y;p<=B;p++)if(spf[p]===p)for(let q=p+1;q<=Math.min(B,p+J0);q++)if(spf[q]===q){
   primePairs++;const v=inv(p,q);
   for(let h=-J0;h<=J0;h++)for(const a of [-1,1])for(const b of [-1,1]){
     const z=-a+p*mod((a-h-b)*v,q),m=p*q,lo=Math.max(2*X-2,2*X-2-h),hi=Math.min(7*X,7*X-h);
     const k0=Math.ceil((lo-z)/m),k1=Math.floor((hi-z)/m),n=Math.max(0,k1-k0+1);
     if(n){const c=z+k0*m;ok(c>=lo&&c<=hi&&mod(c+a,p)===0&&mod(c+h+b,q)===0,"literal arithmetic CRT endpoint");crtChecks++;}
     arithmeticPairs+=n;arithmeticWeight+=n*(p+q);
   }
 }
 ok(conflicts<=arithmeticPairs&&conflictWeight<=arithmeticWeight,"actual support inside arithmetic envelope");
 let haloGain=0,haloActual=0,haloProxy=0,haloHits=0,haloHighActual=0,haloMediumActual=0,haloLowActual=0,haloBound=0,haloHighHits=0;
 for(const a of roots){
   const b=a.filter(e=>e.p>=Y&&bad.has(key(e)));let cap=0,cost=0;
   for(const e of b)cap+=2*kappa*e.p;
   for(const e of a)if(e.p&&b.some(f=>e.C>=f.C-kappa*f.p&&e.J<=f.C+kappa*f.p)){
     e.halo=true;cost+=e.p-1;haloGain+=e.p-1;haloActual+=e.w;haloProxy+=e.r;haloHits++;
     if(e.high){haloHighActual+=e.w;haloHighHits++;}else if(e.p>=Y)haloMediumActual+=e.w;else haloLowActual+=e.w;
   }
   ok(cost<=cap&&b.every(e=>e.halo),"all-event halo budget");haloBound+=cap;
 }
 ok(haloBound===2*kappa*badTagWeight&&haloGain<=haloBound&&haloActual<=3*haloGain&&haloProxy<=1.5*haloGain&&haloActual===haloHighActual+haloMediumActual+haloLowActual,"halo global budget");
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
 const ys=[3,5,7,11],Ps=[6,30,210,2310],phaseEnergy=ys.map(()=>0),phaseAsync=ys.map(()=>0),phaseFar=ys.map(()=>0),phasePairs=ys.map(()=>0),phaseNoDefect=ys.map(()=>0),phaseDefectSame=ys.map(()=>0),phaseDefectSplit=ys.map(()=>0),phaseSmallDiamond=ys.map(()=>0),phaseSmallAfterDefect=ys.map(()=>0),phaseTranslatedSteps=ys.map(()=>0),phaseHighDivisorChecks=ys.map(()=>0),phaseMaxGain=ys.map(()=>0),phaseMinGap=ys.map(()=>Infinity);
 let translationChecks=0,firstDefectChecks=0,diamondChecks=0,broadDiamond=0,broadMediumOnly=0,broadWholeGain=0,broadNearHigh=0,allSmallDiamond=0,farAfter=0,postHaloProxy=0,haloRetainedProxy=0,haloRetainedHits=0,nonzeroConstantLags=0,divisorHighChecks=0;
 const samples=[],virtualChecks=ys.map(()=>0),virtualBothSmall=ys.map(()=>0),virtualDefect=ys.map(()=>0);
 let broadStrictMedium=0,equalLabelSmallBackground=0,haloStrictMediumActual=0,equalPositiveGap=0,equalSamples=[];
 for(const a of roots)for(const e of a)if(e.halo&&e.p>=Y&&e.p<Q)haloStrictMediumActual+=e.w;
 // Independent shifted-time one-step controls on actual horizons; these are NOT extra root tags.
 for(const a of roots.slice(0,128))for(const e of a)if(e.p)for(let k=0;k<ys.length;k++){
   const P=Ps[k],t=e.t+P;let best=Infinity,q=Infinity;
   for(const [sig,ff] of [[-1,fs(e.C-1)],[1,fs(e.C+1)]])for(const p of ff){
     const z=t+1+mod((sig===-1?0:p+2)-(t+1),2*p);if(z<best||(z===best&&p<q)){best=z;q=p;}
   }
   ok(Number.isFinite(best),"shifted clock exists");virtualChecks[k]++;
   if(e.p<=ys[k]&&q<=ys[k]){
     ok(e.p===q&&best-e.s===P,"independent positive small phase translation");virtualBothSmall[k]++;
   }
   if(P%(2*e.p)===0&&P%(2*q)===0)ok(e.p===q&&best-e.s===P,"independent general translation");
   else{virtualDefect[k]++;ok(e.p!==q||best-e.s!==P,"independent first-step defect");}
 }
 function scan(x,y,C,w){
   const a=rootMap.get(x.rep),b=rootMap.get(y.rep),i0=a.findIndex(e=>e.C===C),j0=b.findIndex(e=>e.C===C),D=y.s-x.s;
   let i=i0+1,j=j0+1,steps=0,defect=null;const seen=new Set([x.p]);
   ok(a[i].C===b[j].C&&b[j].t-a[i].t===D&&D!==0&&D%2===0,"actual common high exit");
   while(i+1<a.length&&j+1<b.length){
     const e=a[i],f=b[j];ok(e.C===f.C&&f.t-e.t===D,"translated prefix exact");
     if(D%(2*e.p)===0&&D%(2*f.p)===0){
       ok(e.p===f.p&&e.w===f.w&&e.J===f.J&&f.s-e.s===D,"both periodic labels force same earliest event");translationChecks++;steps++;if(e.high)seen.add(e.p);i++;j++;continue;
     }
     defect={C:e.C,p:e.p,q:f.p,split:e.p!==f.p};
     if(!defect.split)ok(f.s-e.s!==D,"same-label first defect changes lag");
     firstDefectChecks++;break;
   }
   for(const p of seen){ok(D%(2*p)===0,"constant lag high divisor");divisorHighChecks++;}
   if(seen.size>=3&&Q**3>2*H)throw Error("three high divisors of nonzero lag");
   if(!defect)nonzeroConstantLags++;
   const phase=Ps.map(P=>D%P===0);
   for(let k=0;k<ys.length;k++)if(phase[k]){
     phasePairs[k]++;phaseTranslatedSteps[k]+=steps;phaseHighDivisorChecks[k]+=seen.size;
     if(defect){ok(Math.max(defect.p,defect.q)>ys[k],"first defect requires non-small label");
       if(defect.split)phaseDefectSplit[k]+=w;else phaseDefectSame[k]+=w;
       phaseMaxGain[k]=Math.max(phaseMaxGain[k],defect.C-a[i0+1].C);
     }else phaseNoDefect[k]+=w;
   }
   i=i0+1;j=j0+1;
   while(i+1<a.length&&j+1<b.length){
     const l=i,m=j,A=a[i].C;ok(A===b[j].C,"common projected anchor");
     i++;j++;while(i<a.length&&j<b.length&&a[i].C!==b[j].C){if(a[i].C<b[j].C)i++;else j++;}
     if(i===a.length||j===b.length)break;
     const L=a[i].C-A,aa=a.slice(l,i),bb=b.slice(m,j);
     if(a[l].p===b[m].p){ok(i===l+1&&j===m+1,"common projected edge");continue;}
     diamondChecks++;ok(aa.at(-1).p!==bb.at(-1).p,"different incoming labels");
     for(let k=0;k<ys.length;k++)if(Math.max(...aa.map(e=>e.p),...bb.map(e=>e.p))<=ys[k]){
       if(k===1)allSmallDiamond++;
       const gap=b[m].t-a[l].t;ok(gap%Ps[k]!==0,"all-small diamond impossible at equal initial phase");
       if(phase[k]){phaseSmallDiamond[k]++;ok(defect&&defect.C<=A,"initial equal phase requires earlier defect");phaseSmallAfterDefect[k]++;}
     }
     const ha=aa.filter(e=>e.p>=Y),hb=bb.filter(e=>e.p>=Y);
     if(ha.length===1&&hb.length===1){
       const e=ha[0],f=hb[0],ga=L-e.p+1,gb=L-f.p+1;
       if(ga<=J0&&gb<=J0&&J0<Math.min(e.p,f.p)-1){
         // Without roughness, equal labels at distance 2 can occur; only distinct-label diamonds are covered.
         if(e.p!==f.p){
           ok(Math.abs(e.p-f.p)<=J0&&Math.abs(e.C-f.C)<=J0&&aa.every(e=>e.halo)&&bb.every(e=>e.halo),"broad one-large distinct-label whole diamond");
           broadDiamond++;broadWholeGain+=2*L;if(!aa.some(e=>e.high)&&!bb.some(e=>e.high))broadMediumOnly++;if(aa.every(e=>e.p<Q)&&bb.every(e=>e.p<Q))broadStrictMedium++;
           if(a[i0].halo&&b[j0].halo)broadNearHigh++;
           if(samples.length<8)samples.push({C,A,D:a[i].C,p:e.p,q:f.p,ga,gb,mediumOnly:!aa.some(e=>e.high)&&!bb.some(e=>e.high),strictMedium:aa.every(e=>e.p<Q)&&bb.every(e=>e.p<Q)});
         }else{
           equalLabelSmallBackground++;ok(Math.abs(e.C-f.C)===2,"same-label close background opposite sides");
           const p=e.p,ret=b[j].t-a[i].t,z=f.s-e.s,ea=a[i].t-e.s,eb=b[j].t-f.s;
           ok(Math.abs(eb-ea)<=3*J0&&ea>=0&&eb>=0&&ea<=3*ga&&eb<=3*gb,"equal-label actual postclock background");
           ok(mod(z-(p+2),2*p)===0||mod(z+(p+2),2*p)===0,"equal-label opposite parity exit residue");
           const dist=Math.min(mod(ret,2*p),mod(-ret,2*p)),lb=p-2-3*J0;
           ok(dist>=lb,"equal-label return lag separated from lattice");if(lb>0){ok(ret!==0,"equal-label nonphysical return");equalPositiveGap++;}
           const at=b[m].t-a[l].t;
           if(at%(2*p)===0&&aa.concat(bb).every(e=>at%(2*e.p)===0))throw Error("periodic complete equal-label diamond");
           if(equalSamples.length<4)equalSamples.push({C,A,D:a[i].C,p,centres:[e.C,f.C],ga,gb,ret,dist,lb,ea,eb});
         }
       }
     }
     if(a[i].t===b[j].t)break;
   }
 }
 let E=0,diag=0,sync=0,same=0,cross=0,maxLabels=0,exitPairChecks=0,closeCounts=[0,0,0],nearSame=[0,0,0],nearAll=[0,0,0],farSame=[0,0,0],Ks=[1,2,4],byLabelEnergy=0,exitCongruences=0,actualLagChecks=0;
 for(const [C,m] of horizons){
   const a=[...m.values()],r=a[0].r,n=a.reduce((s,x)=>s+x.n,0),pops=new Map();
   E+=r*n*n;
   for(const e of a){
     ok(e.r===r,"common least factor");postHaloProxy+=r*e.after;haloRetainedProxy+=r*(e.n-e.after);haloRetainedHits+=e.n-e.after;diag+=r*e.n;sync+=r*e.n*e.n;pops.set(e.p,(pops.get(e.p)||0)+e.n);
     const sig=(C-1)%e.p===0?-1:1;
     ok(mod(e.s-(sig===-1?0:e.p+2),2*e.p)===0,"exit phase");exitCongruences++;
   }
   const cap=fs(C-1).concat(fs(C+1)).filter(p=>p>=Q).length;
   ok(pops.size<=cap,"available high labels");if(Q**3>7*X+2)ok(cap<=4,"four-label arithmetic bound");
   maxLabels=Math.max(maxLabels,pops.size);let localSame=0;
   for(const k of pops.values())localSame+=r*k*k;
   byLabelEnergy+=localSame;ok(r*n*n<=pops.size*localSame,"local label Cauchy");
   for(let k=0;k<ys.length;k++){
     const groups=new Map();for(const e of a){const key=e.p+":"+mod(e.s,Ps[k]);groups.set(key,(groups.get(key)||0)+e.n);}
     let e0=0;for(const n of groups.values())e0+=r*n*n;phaseEnergy[k]+=e0;
     ok(localSame<=Ps[k]/2*e0+1e-7,"phase Cauchy, fixed exit parity");
   }
   for(let i=0;i<a.length;i++)for(let j=i+1;j<a.length;j++){
     const x=a[i],y=a[j],d=Math.abs(x.s-y.s),w=2*r*x.n*y.n;exitPairChecks++;
     if(x.p===y.p){ok(d>0&&d%(2*x.p)===0,"same-label exits distinct and spaced");same+=w;ok(Math.abs(x.t-y.t)>=d-2*r,"arrival lag transfer");actualLagChecks++;
       for(let k=0;k<ys.length;k++)if(d%Ps[k]===0){phaseAsync[k]+=w;phaseMinGap[k]=Math.min(phaseMinGap[k],d/(2*x.p));ok(d%(2*x.p*Ps[k]/gcd(2*x.p,Ps[k]))===0,"lcm lag spacing");}
       if(d>2*x.p){farAfter+=2*r*x.after*y.after;for(let k=0;k<ys.length;k++)if(d%Ps[k]===0)phaseFar[k]+=w;scan(x,y,C,w);}
     }
     else cross+=w;
     for(let k=0;k<Ks.length;k++){const L=Ks[k];if(d<=2*L*Math.min(x.p,y.p)){nearAll[k]+=w;closeCounts[k]++;}if(x.p===y.p){if(d<=2*L*x.p)nearSame[k]+=w;else farSame[k]+=w;}}
   }
 }
 ok(diag===retainedHigh&&E===sync+same+cross&&byLabelEnergy===sync+same&&E<=maxLabels*byLabelEnergy+1e-7,"energy partition");
 for(let k=0;k<Ks.length;k++){
   ok(nearSame[k]+farSame[k]===same&&nearSame[k]<=2*Ks[k]*sync&&nearAll[k]<=maxLabels*(2*Ks[k]+1)*sync,"bounded degree lag energy");
   ok(E<=maxLabels*((2*Ks[k]+1)*sync+farSame[k])+1e-6,"far same-label sufficient envelope");
 }
 ok(postHaloProxy+haloRetainedProxy===retainedHigh&&farAfter<=farSame[0],"actual halo intersection");
 for(let k=0;k<ys.length;k++){
   ok(phaseEnergy[k]===sync+phaseAsync[k]&&byLabelEnergy<=Ps[k]/2*phaseEnergy[k]+1e-7,"global phase energy partition");
   ok(phaseFar[k]===phaseNoDefect[k]+phaseDefectSame[k]+phaseDefectSplit[k],"exact first-defect partition");
   ok(phaseSmallDiamond[k]===phaseSmallAfterDefect[k],"all-small diamond provenance");
 }
 return {X,mode,B,T,Q,delta,Y,J0,kappa,centerCount:cs.length,virtualChecks,virtualBothSmall,virtualDefect,broadStrictMedium,equalLabelSmallBackground,equalPositiveGap,equalSamples,haloStrictMediumActual,conflicts,conflictWeight,badCenters:bad.size,badWeight,badTagWeight,lowBad,highBad,primePairs,arithmeticPairs,arithmeticWeight,crtChecks,haloGain,haloActual,haloProxy,haloHits,haloHighActual,haloMediumActual,haloLowActual,haloBound,haloHighHits,postHaloProxy,haloRetainedProxy,haloRetainedHits,farAfter,ys,Ps,phaseEnergy,phaseAsync,phaseFar,phasePairs,phaseNoDefect,phaseDefectSame,phaseDefectSplit,phaseSmallDiamond,phaseSmallAfterDefect,phaseTranslatedSteps,phaseHighDivisorChecks,phaseMaxGain,phaseMinGap,translationChecks,firstDefectChecks,diamondChecks,broadDiamond,broadMediumOnly,broadWholeGain,broadNearHigh,allSmallDiamond,nonzeroConstantLags,divisorHighChecks,samples,N,G,R,events,literal,rankChecks,rankLog,rawHits,rawHigh,rawActual,rankMarked,rankCost,rankActual,stableHits,stableHigh,stableActual,foreignHits,foreignCost,foreignActual,foreignBound,foreignGroups,maxForeign,groupChecks,terminalMixed,arrivalPairsBefore,arrivalWeightBefore,arrivalPairsStable,arrivalWeightStable,retainedHits,retainedHigh,retainedActual,E,diag,sync,same,cross,byLabelEnergy,maxLabels,exitPairChecks,exitCongruences,actualLagChecks,Ks,closeCounts,nearSame,nearAll,farSame};
}
const argv=process.argv.slice(2),mode=argv[0]||'diagnostic',xs=argv.slice(1).map(Number);for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
