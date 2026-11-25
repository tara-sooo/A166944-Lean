// Exit-rank stability, actual same-label arrival groups and lag energy audit.
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
     const m=horizons.get(q.C),k=phys(q);if(!m.has(k))m.set(k,{p:q.p,s:q.s,r,n:0,t:q.t});m.get(k).n++;
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
 let E=0,diag=0,sync=0,same=0,cross=0,maxLabels=0,exitPairChecks=0,closeCounts=[0,0,0],nearSame=[0,0,0],nearAll=[0,0,0],farSame=[0,0,0],Ks=[1,2,4],byLabelEnergy=0,exitCongruences=0,actualLagChecks=0;
 for(const [C,m] of horizons){
   const a=[...m.values()],r=a[0].r,n=a.reduce((s,x)=>s+x.n,0),pops=new Map();
   E+=r*n*n;
   for(const e of a){
     ok(e.r===r,"common least factor");diag+=r*e.n;sync+=r*e.n*e.n;pops.set(e.p,(pops.get(e.p)||0)+e.n);
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
     if(x.p===y.p){ok(d>0&&d%(2*x.p)===0,"same-label exits distinct and spaced");same+=w;ok(Math.abs(x.t-y.t)>=d-2*r,"arrival lag transfer");actualLagChecks++;}
     else cross+=w;
     for(let k=0;k<Ks.length;k++){const L=Ks[k];if(d<=2*L*Math.min(x.p,y.p)){nearAll[k]+=w;closeCounts[k]++;}if(x.p===y.p){if(d<=2*L*x.p)nearSame[k]+=w;else farSame[k]+=w;}}
   }
 }
 ok(diag===retainedHigh&&E===sync+same+cross&&byLabelEnergy===sync+same&&E<=maxLabels*byLabelEnergy+1e-7,"energy partition");
 for(let k=0;k<Ks.length;k++){
   ok(nearSame[k]+farSame[k]===same&&nearSame[k]<=2*Ks[k]*sync&&nearAll[k]<=maxLabels*(2*Ks[k]+1)*sync,"bounded degree lag energy");
   ok(E<=maxLabels*((2*Ks[k]+1)*sync+farSame[k])+1e-6,"far same-label sufficient envelope");
 }
 return {X,mode,B,T,Q,delta,N,G,R,events,literal,rankChecks,rankLog,rawHits,rawHigh,rawActual,rankMarked,rankCost,rankActual,stableHits,stableHigh,stableActual,foreignHits,foreignCost,foreignActual,foreignBound,foreignGroups,maxForeign,groupChecks,terminalMixed,arrivalPairsBefore,arrivalWeightBefore,arrivalPairsStable,arrivalWeightStable,retainedHits,retainedHigh,retainedActual,E,diag,sync,same,cross,byLabelEnergy,maxLabels,exitPairChecks,exitCongruences,actualLagChecks,Ks,closeCounts,nearSame,nearAll,farSame};
}
const argv=process.argv.slice(2),mode=argv[0]||'diagnostic',xs=argv.slice(1).map(Number);for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
