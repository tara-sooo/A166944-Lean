// Reproduce: node research/min_prime_root_rare_contact_audit.mjs
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),l=Math.max(1,Math.log(u)),analytic=mode==="gain",T=analytic?Math.floor(X/u**.25):mode==="two"?4*B:B,Q=Math.ceil(B/u),P=analytic?Math.max(5,Math.ceil(B*Math.exp(-(u**.25)))):Math.max(5,Math.ceil(B/3)),V=analytic?Math.max(5,Math.ceil(B*Math.exp(-Math.sqrt(u)))):Math.max(5,Math.ceil(B/6)),Qasym=analytic?Q:Math.max(P,Math.ceil(B/2)),Pstar=analytic?Math.ceil(B/l**.125):Math.max(P,Math.ceil(B/2)),y=3,L=6,degreeLimit=analytic?Math.ceil(20*l):8,g=Math.max(2,L*degreeLimit),k=analytic?Math.floor(l/(4*Math.log(g))):2,Z=Math.min(B,Math.max(3,analytic?Math.floor(B**.25):17)),low=2*X-2,hi=7*X,lim=hi+5;
 const ok=(b,m)=>{if(!b)throw Error(m);},mod=(a,m)=>((a%m)+m)%m,gcd=(a,b)=>{while(b){const c=a%b;a=b;b=c;}return a;};
 const spf=new Int32Array(lim+1);for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)if(!spf[j])spf[j]=n;}
 const fs=n=>{const a=[];while(n>1){const p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const labels=J=>[...fs(J),...fs(J+2)].filter(p=>p>y);
 const rough=C=>!fs(C-1).some(p=>p<=Z)&&!fs(C+1).some(p=>p<=Z);
 const base=new Uint8Array(hi+1),twoSet=new Uint8Array(hi+1),asymSet=new Uint8Array(hi+1),deg=new Uint8Array(hi+1),layerSizes=[],layerEdges=[];let nTwo=0,nAsym=0,nRough=0,nExceptional=0,edgeMass=0,nA=0,sameOnly=0,maxDegree=0;
 for(let J=low;J<=hi;J+=2){deg[J]=labels(J).length;maxDegree=Math.max(maxDegree,deg[J]);if(deg[J]>degreeLimit){nExceptional++;edgeMass+=deg[J];}}
 let layer=[];
 for(let C=low;C<=hi;C+=2){
   const hs=new Set(),vs=new Set(),keys=new Set();for(let e=0;e<L&&C-e>=low;e+=2)for(const p of labels(C-e)){if(p>=V||p>=Qasym)vs.add(p);if(p>=P){hs.add(p);keys.add((C-e)+":"+p);}}
   if(keys.size>=2&&hs.size===1)sameOnly++;
   const two=hs.size>=2,asym=[...vs].some(p=>p>=Qasym&&[...vs].some(q=>q!==p&&q>=V)),rr=rough(C),ex=deg[C]>degreeLimit;
   if(asym){asymSet[C]=1;nAsym++;}
   if(two){twoSet[C]=1;nTwo++;}if(rr)nRough++;
   const chosen=ex||((mode!=="rough")&&(two||asym))||((mode!=="two")&&rr);
   if(chosen){base[C]=1;layer.push(C);nA++;}
 }
 const rootCandidates=new Uint8Array(hi+1);let rootsRelax=0;
 for(let depth=0;depth<=k;depth++){
   layerSizes.push(layer.length);
   for(const C of layer)for(let e=0;e<L&&C-e>=low;e+=2)rootCandidates[C-e]=1;
   if(depth===k)break;
   const pred=new Uint8Array(hi+1),jset=new Uint8Array(hi+1),next=[];let candidates=0;
   for(const C of layer)for(let e=0;e<L&&C-e>=low;e+=2){let J=C-e;if(jset[J])continue;jset[J]=1;for(const p of labels(J)){candidates++;const H=J-p+1;if(H>=low&&!pred[H]){pred[H]=1;next.push(H);}}}
   ok(candidates<=g*layer.length+edgeMass&&next.length<=candidates,"reverse layer");layerEdges.push(candidates);layer=next;
 }
 const cap=q=>q===0?1:analytic?Math.max(1,Math.floor(l**.125*Math.log(q)/l)):Math.max(1,Math.floor(2*Math.log(q)));
 const horizons=new Map(),removed=new Set(),rootFlags=new Map(),Wbefore=new Map(),Wafter=new Map();let N=0,events=0,visits=0,R=0,G=0,literal=0,cross=0,twins=0,marked=0,markedTwo=0,markedAsym=0,markedRough=0,markedDeg=0,markedCost=0,keptR=0,highRBefore=0,highRAfter=0,superVisits=0,superArrivals=0,eligibleRoot=0,shallowKept=0,pruneWitness=0;
 function add(e){if(!horizons.has(e.C))horizons.set(e.C,[]);horizons.get(e.C).push(e);}
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){
   N++;const C0=2*M-2;if(rootCandidates[C0])rootsRelax++;
   let C=C0,t=M+2,cut=Math.floor((7*M-1)/4),depth=0,lastq=0,lastD=C0,lastTime=t,incoming=0,cost=0,flag=0,all=[];
   while(true){
     const e={M,C,t,depth,lastq,lastD,lastTime,incoming,p:0,r:0};all.push(e);add(e);visits++;
     ok(C-lastD<L&&C>=lastD&&t-lastTime<=3*(C-lastD),"compressed LOW offset/time");
     if(lastq)ok(lastD%lastq===0||(lastD+2)%lastq===0,"compressed post divisor");
     if(lastq>=Pstar)superVisits++;
     if(depth<=k){if(twoSet[C])flag|=1;if(asymSet[C])flag|=8;if(rough(C))flag|=2;if(deg[C]>degreeLimit)flag|=4;if(base[C]){ok(rootCandidates[C0]===1,"actual shallow root in reverse union");pruneWitness++;}}
     if(C-C0>=T){cross++;break;}
     let tt=Infinity,p=Infinity;const active=[...fs(C-1),...fs(C+1)];
     for(const sg of [-1,1])for(const q of fs(C+sg)){const tick=t+1+mod((sg===-1?0:q+2)-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;}}
     if(X<=1024){let lt=Infinity,lp=Infinity;for(let w=t+1;w<=cut;w++){const f=fs(gcd(w%2?w-2:w,C+(w%2?1:-1)));if(f.length){lt=w;lp=f[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal");literal++;}
     if(tt>cut){if(spf[C-1]===C-1&&spf[C+1]===C+1)twins++;break;}
     const r=Math.min(...active);ok(r<=p&&tt-t<=2*r,"clock");e.p=p;e.r=r;events++;cost+=r;
     t=tt;C+=p-1;incoming=p;ok(C<=2*t,"horizon");
     if(p>y){depth++;lastq=p;lastD=C;lastTime=t;if(p>=Pstar)superArrivals++;}
   }
   const gain=C-C0;R+=cost;G+=gain;ok(gain<T+B&&2*cost<=3*gain,"prefix budget");
   const isMarked=!!((flag&4)||((mode!=="rough")&&(flag&9))||((mode!=="two")&&(flag&2)));
   rootFlags.set(M,flag);
   if(flag&1)markedTwo++;if(flag&8)markedAsym++;if(flag&2)markedRough++;if(flag&4)markedDeg++;
   if(isMarked){ok(rootCandidates[C0],"root containment");removed.add(M);marked++;markedCost+=cost;}
   else{eligibleRoot++;keptR+=cost;for(const e of all)if(e.depth<=k){ok(!base[e.C],"kept shallow avoids rare sets");shallowKept++;}}
   for(const e of all){e.end=C;if(e.p>=Q){highRBefore+=e.r;Wbefore.set(e.C,(Wbefore.get(e.C)||0)+1);if(!isMarked){highRAfter+=e.r;Wafter.set(e.C,(Wafter.get(e.C)||0)+1);}}}
 }
 const seen=new Map(),cls=["pruned","superThin","remaining"],first=[0,0,0],ener=[0,0,0],bud=[0,0,0];let pairs=0,thinIndependent=0,thinMixedSmall=0,thinSameScale=0,twoDistinct=0,asymDistinct=0,asymShallow=0,asymShallowKept=0,asymDeepKept=0,twoSame=0,sameLagChecks=0,twoShallow=0,twoDeepKept=0,twoShallowKept=0,highRoughShallow=0,maxCapSum=0,maxKeys=0,maxThinMass=0,diag=0,oracle=0;
 for(const C of [...horizons.keys()].sort((a,b)=>a-b)){
   const es=horizons.get(C),groups=new Map(),key=e=>e.lastD+":"+e.lastq;
   for(const e of es){const k=key(e);groups.set(k,(groups.get(k)||0)+1);}
   // Relaxed key capacity is independent of actual group mass. Include possible root+LOW keys.
   let capSum=0,keyCount=0;for(let offset=0;offset<L&&C-offset>=low;offset+=2){capSum+=1;keyCount++;for(const q of labels(C-offset)){capSum+=cap(q);keyCount++;}}
   let thinMass=0;for(const [s,m] of groups){const [J,q]=s.split(":").map(Number);ok(J<=C&&C-J<L&&(q===0||labels(J).includes(q)),"actual group candidate");if(m<=cap(q))thinMass+=m;}
   ok(thinMass<=capSum&&groups.size<=keyCount,"thin capacity");maxCapSum=Math.max(maxCapSum,capSum);maxKeys=Math.max(maxKeys,groups.size);maxThinMass=Math.max(maxThinMass,thinMass);
   const active=es.filter(e=>e.p>=Q);if(active.length){const r=active[0].r;ok(active.every(e=>e.r===r),"common clock");diag+=r*active.length;oracle+=r*active.length**2;}
   for(let i=0;i<es.length;i++)for(let j=i+1;j<es.length;j++){
     const a=es[i],b=es[j],id=(Math.min(a.M,b.M)-X)*X+Math.max(a.M,b.M)-X;let v=seen.get(id);
     if(!v){
       pairs++;ok(key(a)!==key(b),"distinct compressed keys at first contact");
       const tw=a.lastq>=P&&b.lastq>=P,distinct=tw&&a.lastq!==b.lastq;
       if(tw&&!distinct){twoSame++;ok(a.lastD!==b.lastD,"same-label exception");const q=a.lastq;if(q>L+2){ok(Math.abs(a.lastD-b.lastD)===2,"same-label shifted post horizons");ok(Math.abs(a.lastTime-b.lastTime)>=q-2&&Math.abs(a.t-b.t)>=q-2-3*L,"same-label asynchronous lag");sameLagChecks++;}}
       if(distinct){twoDistinct++;ok(twoSet[C]===1,"two distinct high contact exposed");if(Math.min(a.depth,b.depth)<=k){twoShallow++;if(!removed.has(a.M)&&!removed.has(b.M))twoShallowKept++;if(mode!=="rough")ok(removed.has(a.M)||removed.has(b.M),"one-sided shallow contact pruned");}else if(!removed.has(a.M)&&!removed.has(b.M))twoDeepKept++;}
       const asym=a.lastq!==b.lastq&&((a.lastq>=Qasym&&b.lastq>=V)||(b.lastq>=Qasym&&a.lastq>=V));
       if(asym){asymDistinct++;ok(asymSet[C]===1,"asymmetric exposure");if(Math.min(a.depth,b.depth)<=k){asymShallow++;if(!removed.has(a.M)&&!removed.has(b.M))asymShallowKept++;if(mode!=="rough")ok(removed.has(a.M)||removed.has(b.M),"asymmetric shallow contact pruned");}else if(!removed.has(a.M)&&!removed.has(b.M))asymDeepKept++;}
       const thin=(a.lastq>=Pstar&&groups.get(key(b))<=cap(b.lastq))||(b.lastq>=Pstar&&groups.get(key(a))<=cap(a.lastq));
       if(thin){thinIndependent++;if(Math.min(a.lastq,b.lastq)<P)thinMixedSmall++;else thinSameScale++;}
       const cl=removed.has(a.M)||removed.has(b.M)?0:thin?1:2;
       v={cl,w:0,budget:3*Math.min(a.end-C,b.end-C)};seen.set(id,v);first[cl]++;bud[cl]+=v.budget;
     }
     if(a.p>=Q&&b.p>=Q){v.w+=2*a.r;ener[v.cl]+=2*a.r;ok(v.w<=v.budget,"pair remaining gain");}
   }
   if(rough(C))for(const e of es)if(e.p>=Q&&e.depth<=k){highRoughShallow++;if(mode!=="two")ok(removed.has(e.M),"rough shallow root pruned");}
 }
 const energy=m=>{let s=0;for(const [C,n] of m){const r=Math.min(...fs(C-1),...fs(C+1));s+=r*n*n;}ok(Number.isSafeInteger(s),"integer energy");return s;};
 const E=energy(Wbefore),Ekept=energy(Wafter);
 ok(marked+eligibleRoot===N&&R===markedCost+keptR&&marked<=rootsRelax,"root partition");ok(superVisits<=(L/2+1)*superArrivals&&superArrivals*(Pstar-1)<=G,"super visit budget");ok(thinIndependent<=superVisits*maxCapSum,"thin pair count");ok(pairs===first.reduce((s,x)=>s+x,0)&&E===oracle&&diag===highRBefore&&E===diag+ener.reduce((s,x)=>s+x,0)&&Ekept===highRAfter+ener[1]+ener[2],"energy partition");ok(ener.every((x,i)=>x<=bud[i]&&bud[i]<=3*(T+B)*first[i]),"whole pair budgets");
 return {mode,X,B,T,P,V,Qasym,Pstar,Q,Z,L,degreeLimit,k,N,nA,nTwo,nAsym,nRough,nExceptional,edgeMass,sameOnly,maxDegree,layerSizes,layerEdges,rootsRelax,marked,markedTwo,markedAsym,markedRough,markedDeg,markedCost,keptR,events,visits,R,G,cross,twins,literal,pruneWitness,shallowKept,superVisits,superArrivals,maxCapSum,maxKeys,maxThinMass,pairs,thinIndependent,thinMixedSmall,thinSameScale,twoDistinct,asymDistinct,asymShallow,asymShallowKept,asymDeepKept,twoSame,sameLagChecks,twoShallow,twoShallowKept,twoDeepKept,highRoughShallow,first:Object.fromEntries(cls.map((c,i)=>[c,first[i]])),energy:Object.fromEntries(cls.map((c,i)=>[c,ener[i]])),E,Ekept,highRBefore,highRAfter};
}
const xs=process.argv.slice(2).map(Number);for(const mode of ['two','rough','gain'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
