// Reproduce: node research/min_prime_root_mass_dispersion_audit.mjs
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),l=Math.max(1,Math.log(u)),analytic=mode==="gain",T=analytic?Math.floor(X/u**.25):(mode==="four"||mode==="skew")?4*B:B,Q=Math.ceil(B/u),P=analytic?Math.ceil(B/Math.sqrt(u)):Math.max(5,Math.ceil(B/4)),L=6,y=3,h=analytic?Math.ceil(20*l):8,g=h*L,k=analytic?Math.floor(l/(8*Math.log(g))):2,w=analytic?k:2,H=analytic?Math.ceil(B*Math.sqrt(u)):(mode==="four"||mode==="skew")?12:5;
 const d0=analytic?B:Math.max(4,Math.floor(B/8)),d1=d0*(analytic?Math.ceil(u):4),m0=analytic?Math.max(1,Math.floor(u**.75)):2,m1=analytic?Math.max(1,Math.floor(u**1.75)):3,K0=analytic?Math.max(1,Math.floor(u**1.5)):mode==="skew"?4:2,K1=analytic?Math.max(1,Math.floor(Math.sqrt(u))):mode==="skew"?2:1;
 const low=2*X-2,hi=7*X,lim=hi+5,ok=(b,msg)=>{if(!b)throw Error(msg);},mod=(a,m)=>((a%m)+m)%m,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c;}return a;};
 const spf=new Int32Array(lim+1);for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)if(!spf[j])spf[j]=n;}
 const fs=n=>{let a=[];while(n>1){let p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;},labels=J=>[...fs(J),...fs(J+2)].filter(p=>p>y);
 const horizons=new Map(),roots=new Map(),recMass=new Uint32Array(hi+1);
 let N=0,R=0,G=0,events=0,visits=0,literal=0,cross=0,twins=0,recent=0,highArrivals=0,shallow=0,positiveRecent=0;
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){
   N++;let C=2*M-2,t=M+2,cut=Math.floor((7*M-1)/4),depth=0,anchorDepth=-1,anchor=0,ar=[],cost=0,rv=0,sv=0,ha=0;
   while(true){
     const rec=anchorDepth>=0&&depth-anchorDepth<=w,e={M,C,t,depth,rec,anchor,age:rec?depth-anchorDepth:-1,p:0,r:0};ar.push(e);visits++;if(!horizons.has(C))horizons.set(C,[]);horizons.get(C).push(e);
     if(rec){recent++;rv++;recMass[C]++;if(e.age>0)positiveRecent++;}if(depth<=k){shallow++;sv++;}
     if(C-(2*M-2)>=T){cross++;break;}
     let tt=Infinity,p=Infinity;
     for(const sg of [-1,1])for(const q of fs(C+sg)){let tick=t+1+mod((sg===-1?0:q+2)-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;}}
     if(X<=1024){let lt=Infinity,lp=Infinity;for(let s=t+1;s<=cut;s++){const f=fs(gcd(s%2?s-2:s,C+(s%2?1:-1)));if(f.length){lt=s;lp=f[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal");literal++;}
     if(tt>cut){if(spf[C-1]===C-1&&spf[C+1]===C+1)twins++;break;}
     const r=Math.min(...fs(C-1),...fs(C+1));ok(r<=p&&tt-t<=2*r,"clock");e.p=p;e.r=r;cost+=r;events++;t=tt;C+=p-1;ok(C<=2*t,"horizon");
     if(p>y){depth++;if(p>=P){anchorDepth=depth;anchor=C;ha++;highArrivals++;}}
   }
   const gain=C-(2*M-2);R+=cost;G+=gain;ok(gain<T+B&&2*cost<=3*gain,"gain budget");ok(rv<=ha*(w+1)*(L/2+1)&&sv<=(k+1)*(L/2+1)&&ha*(P-1)<=gain,"recent/shallow packing");
   for(const e of ar)e.end=C;roots.set(M,{ar,cost,gain});
 }
 const heavy=new Uint8Array(hi+1),candRoot=new Uint8Array(hi+1);let layer=[],edgeMass=0,nHeavy=0,maxRecentMass=0,degExc=0;
 for(let C=low;C<=hi;C+=2){let dd=labels(C).length;if(dd>h){edgeMass+=dd;degExc++;}if(recMass[C]>H){heavy[C]=1;layer.push(C);nHeavy++;}maxRecentMass=Math.max(maxRecentMass,recMass[C]);}
 ok(nHeavy*(H+1)<=recent,"heavy support count");let layers=[],edges=[];
 for(let j=0;j<=k;j++){
   layers.push(layer.length);for(const C of layer)for(let e=0;e<L&&C-e>=low;e+=2)candRoot[C-e]=1;
   if(j===k)break;
   const seenJ=new Uint8Array(hi+1),seenP=new Uint8Array(hi+1),next=[];let ct=0;
   for(const C of layer)for(let e=0;e<L&&C-e>=low;e+=2){const J=C-e;if(seenJ[J])continue;seenJ[J]=1;for(const p of labels(J)){ct++;const D=J-p+1;if(D>=low&&!seenP[D]){seenP[D]=1;next.push(D);}}}
   ok(ct<=g*layer.length+edgeMass&&next.length<=ct,"reverse edge bound");edges.push(ct);layer=next;
 }
 const removed=new Set();let removedR=0,relaxed=0,removedWitness=0;
 for(const [M,{ar,cost}] of roots){if(candRoot[2*M-2])relaxed++;if(ar.some(e=>e.depth<=k&&heavy[e.C])){ok(candRoot[2*M-2],"actual root reverse containment");removed.add(M);removedR+=cost;removedWitness+=ar.filter(e=>e.depth<=k&&heavy[e.C]).length;}}
 ok(removed.size<=relaxed,"candidate cap");
 const W0=new Map(),W1=new Map(),W2=new Map(),W3=new Map();
 let diag0=0,diag1=0,thin0=0,thin1=0,thinHits0=0,thinHits1=0,disp=0,dispHits=0,finalR=0,E0=0,E1=0,E2=0,E3=0,cellE0=0,cellE1=0,dispE0=0,dispE1=0,dispCellE0=0,dispCellE1=0,support=0,thinBound0=0,thinBound1=0,fullSupport=0,nFinalHorizons=0,concentratedMany=0,concentratedManyClock=0,maxCells0=0,maxCells1=0,maxCellMass0=0,maxCellMass1=0;
 const bin=(M,d)=>Math.floor((M-X)/d),groups=(es,d)=>{const m=new Map();for(const e of es){const j=bin(e.M,d);if(!m.has(j))m.set(j,[]);m.get(j).push(e);}return m;};
 for(const [C,es] of horizons){
   const full=es.filter(e=>e.p>=Q);if(!full.length)continue;const r=full[0].r;ok(full.every(e=>e.r===r),"common r");W0.set(C,full.length);E0+=r*full.length**2;diag0+=r*full.length;fullSupport+=r;
   const kept=full.filter(e=>!removed.has(e.M));if(!kept.length)continue;W1.set(C,kept.length);E1+=r*kept.length**2;diag1+=r*kept.length;support+=r;
   const f0=groups(kept,d0),f1=groups(kept,d1);for(const a of f0.values())cellE0+=r*a.length**2;for(const a of f1.values())cellE1+=r*a.length**2;
   ok(f0.size<=Math.ceil(T/(2*d0))+2&&f1.size<=Math.ceil(T/(2*d1))+2,"localized cell support");
   thinBound0+=r*m0*(Math.ceil(T/(2*d0))+2);thinBound1+=r*m1*(Math.ceil(T/(2*d1))+2);
   const a0=[];for(const a of f0.values())if(a.length<=m0){thin0+=r*a.length;thinHits0+=a.length;}else a0.push(...a);
   const a1=[];for(const a of groups(a0,d1).values())if(a.length<=m1){thin1+=r*a.length;thinHits1+=a.length;}else a1.push(...a);
   if(!a1.length)continue;W2.set(C,a1.length);E2+=r*a1.length**2;
   const g0=groups(a1,d0),g1=groups(a1,d1);ok([...g0.values()].every(a=>a.length>m0)&&[...g1.values()].every(a=>a.length>m1),"nested thickness");
   maxCells0=Math.max(maxCells0,g0.size);maxCells1=Math.max(maxCells1,g1.size);
   const s0=[...g0.values()].reduce((s,a)=>s+a.length**2,0),s1=[...g1.values()].reduce((s,a)=>s+a.length**2,0),sq=a1.length**2;
   ok(sq<=g0.size*s0&&sq<=g1.size*s1,"effective cell count bounded by actual count");
   if(sq<=K0*s0||sq<=K1*s1){
     if(g0.size>K0&&g1.size>K1){concentratedMany++;concentratedManyClock+=r*a1.length;}
     disp+=r*a1.length;dispHits+=a1.length;
     if(sq<=K0*s0){dispE0+=r*a1.length**2;dispCellE0+=r*[...g0.values()].reduce((s,a)=>s+a.length**2,0);}
     else{dispE1+=r*a1.length**2;dispCellE1+=r*[...g1.values()].reduce((s,a)=>s+a.length**2,0);}
     continue;
   }
   ok(sq>K0*s0&&sq>K1*s1,"effective dispersion residual");W3.set(C,a1.length);E3+=r*a1.length**2;finalR+=r*a1.length;nFinalHorizons++;for(const a of a1)a.keep=true;
   maxCellMass0=Math.max(maxCellMass0,...[...g0.values()].map(a=>a.length));maxCellMass1=Math.max(maxCellMass1,...[...g1.values()].map(a=>a.length));
 }
 ok(thin0<=thinBound0&&thin1<=thinBound1&&dispE0<=K0*dispCellE0&&dispE1<=K1*dispCellE1&&dispCellE0<=cellE0&&dispCellE1<=cellE1,"cell upper bounds");
 ok(diag1===thin0+thin1+disp+finalR&&E2===E3+dispE0+dispE1,"linear and dispersion partition");
 const seen=new Map(),first=[0,0,0],en=[0,0,0],budget=[0,0,0],finalEn=[0,0,0];let independentMixed=0,shallowRecentHeavy=0,shallowRecentHeavyKept=0,positiveMixed=0,pairs=0,nearPairs0=0,nearPairs1=0,nearE0=0,nearE1=0;
 for(const C of [...horizons.keys()].sort((a,b)=>a-b)){
   const es=horizons.get(C);for(let i=0;i<es.length;i++)for(let j=i+1;j<es.length;j++){
     const a=es[i],b=es[j],id=(Math.min(a.M,b.M)-X)*X+Math.max(a.M,b.M)-X;let v=seen.get(id);
     if(!v){pairs++;const shRec=(a.depth<=k&&b.rec)||(b.depth<=k&&a.rec),pruned=removed.has(a.M)||removed.has(b.M);
       if(shRec){independentMixed++;if((a.depth<=k&&b.age>0)||(b.depth<=k&&a.age>0))positiveMixed++;if(heavy[C]){shallowRecentHeavy++;if(!pruned)shallowRecentHeavyKept++;ok(pruned,"heavy shallow/recent contact pruned");}}
       const cl=pruned?0:shRec?1:2,bud=3*Math.min(a.end-C,b.end-C);v={cl,bud,w:0,final:0};seen.set(id,v);first[cl]++;budget[cl]+=bud;
       if(!pruned){if(bin(a.M,d0)===bin(b.M,d0))nearPairs0++;if(bin(a.M,d1)===bin(b.M,d1))nearPairs1++;}
     }
     if(a.p>=Q&&b.p>=Q){v.w+=2*a.r;en[v.cl]+=2*a.r;ok(v.w<=v.bud,"whole pair budget");if(v.cl!==0){if(bin(a.M,d0)===bin(b.M,d0))nearE0+=2*a.r;if(bin(a.M,d1)===bin(b.M,d1))nearE1+=2*a.r;}}
     if(a.keep&&b.keep){v.final+=2*a.r;finalEn[v.cl]+=2*a.r;ok(v.final<=v.w&&v.cl!==0,"retained pair");}
   }
 }
 ok(first[1]<=shallow*H&&shallowRecentHeavyKept===0,"mixed whole-pair count");
 ok(E0===diag0+en.reduce((s,n)=>s+n,0)&&E1===diag1+en[1]+en[2]&&E3===finalR+finalEn[1]+finalEn[2],"pair energy oracle");
 ok(cellE0===diag1+nearE0&&cellE1===diag1+nearE1&&nearE0<=3*(T+B)*nearPairs0&&nearE1<=3*(T+B)*nearPairs1,"same cell pair budget");
 return {mode,X,B,T,Q,P,L,h,k,w,H,d0,d1,m0,m1,K0,K1,N,R,G,events,visits,literal,cross,twins,recent,positiveRecent,highArrivals,shallow,nHeavy,maxRecentMass,degExc,edgeMass,layers,edges,relaxed,removed:removed.size,removedR,removedWitness,pairs,independentMixed,positiveMixed,shallowRecentHeavy,shallowRecentHeavyKept,first,en,finalEn,budget,diag0,diag1,E0,E1,E2,E3,thin0,thin1,thinHits0,thinHits1,disp,dispHits,dispE0,dispE1,cellE0,cellE1,nearPairs0,nearPairs1,finalR,nFinalHorizons,concentratedMany,concentratedManyClock,maxCells0,maxCells1,maxCellMass0,maxCellMass1};
}
const xs=process.argv.slice(2).map(Number);for(const mode of ['short','four','gain','skew'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
