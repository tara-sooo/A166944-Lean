// Cohort mass ledger, common-clock coalescence energy, efficient high-wait capacity, and canonical stars.
function audit(){
 const ck=(b,m)=>{if(!b)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=1200000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)spf[n]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
 function ev(a,v){let p=Infinity,w=Infinity,e=0,q=Infinity;for(let [d,s] of [[a+1,-1],[a-1,1]])for(let r of fs(d)){q=Math.min(q,r);let t=mod((s===-1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e,q}}
 let z={slabs:[],roots:0,events:0,commonEvents:0,terminalChecks:0,energyChecks:0,eventMassChecks:0,roughChecks:0,capacityChecks:0,cauchyChecks:0,starChecks:0,starRoots:0,starCenters:0,starRows:[],syntheticStarControls:0,sweepEvents:0,sweepRetirements:0,sweepMergeChecks:0,sweepBirthMerges:0,sweepEventMerges:0,sweepEnergyChecks:0,fixedStarTicks:0,fixedStarPrimeChecks:0,fixedStarRows:[]};
 for(let R of [3000,12000,48000,192000,480000]){
  let T=Math.floor(R/8),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nEnd=3-lo/2+T,roots=[],events=new Map(),end=new Map(),twins=new Map(),sumG=0,sumW=0,sumIdle=0,sumTwinG=0,S=Math.sqrt(2*R+1),B=0;
  for(let A=lo;A<=hi;A+=6){
   let a=A,v=3-A/2,v0=v,ret=v+T,record=[],W=0;
   while(true){let x=ev(a,v);if(v+x.w>ret)break;ck(x.q<=Math.sqrt(a+1),"no completed twin");let n=v+x.w,key=a+":"+n,old=events.get(key)||{a,n,p:x.p,e:x.e,waits:[],roots:[]};ck(old.p===x.p&&old.e===x.e,"same physical event");old.waits.push(x.w);old.roots.push(roots.length);events.set(key,old);record.push(key);
    a-=x.p-1;v=n;W+=x.w;z.events++;
   }
   let G=A-a,I=T-W,x=ev(a,v),twin=x.q>Math.sqrt(a+1);
   ck(G<=2*T+6&&I>=0&&v===v0+W&&I<x.w,"horizon");
   if(twin){B++;sumTwinG+=G;twins.set(a,(twins.get(a)||0)+1);ck(ret>3-a&&nEnd<0,"twin absorption window")}
   else ck(I<=2*S,"non-twin idle");
   let atRet=a;while(true){let y=ev(a,v);if(v+y.w>nEnd)break;a-=y.p-1;v+=y.w;z.commonEvents++}
   if(twin)ck(a===atRet,"twin persists");
   end.set(a,(end.get(a)||0)+1);roots.push({A,G,W,I,twin,atRet,end:a,record});sumG+=G;sumW+=W;sumIdle+=I;z.roots++;z.terminalChecks++;
  }
  let n=roots.length,C=[...end.values()].reduce((a,b)=>a+b*b,0),Ct=[...twins.values()].reduce((a,b)=>a+b*b,0);
  ck(sumW+sumIdle===n*T&&sumIdle<=T*B+2*S*(n-B)+1e-7,"idle total");
  ck(B*B<=twins.size*Ct&&Ct<=C&&sumTwinG>=3*(Ct-B),"basin moment");
  ck(sumG+1e-6>=(4/9)*(T-2*S-8)*(n-B)+3*(Ct-B),"combined lower");
  z.energyChecks++;
  for(let e of events.values()){let final=roots[e.roots[0]].end;ck(e.roots.every(i=>roots[i].end===final)&&e.roots.length<=end.get(final),"coalescence");z.eventMassChecks++}
  let row={R,n,T,meanG:sumG/n,meanGOverR:sumG/n/R,meanW:sumW/n,meanIdle:sumIdle/n,twinRoots:B,twinFraction:B/n,twinCenters:twins.size,energyPerRoot:C/n,twinEnergyPerRoot:Ct/n,maxMass:Math.max(...end.values()),distinctEvents:events.size,high:[]};
  for(let cut of [7,17,47,113,Math.max(127,Math.floor(Math.sqrt(R)/2))]){
   let delta=1/Math.log(cut)**2,eff=[],ineff=0,high=0,low=0,light=0,second=0,capacity=0;
   const by=new Map();
   for(let e of events.values()){
    let w=e.waits.reduce((a,b)=>a+b,0);
    if(e.p<cut){low+=w;continue}
    high+=w;let good=e.waits.filter(w=>w>=delta*(e.p-1)),bad=w-good.reduce((a,b)=>a+b,0);ineff+=bad;if(!good.length)continue;
    let cap=2*Math.min(e.p,S),m=e.roots.length,ww=good.reduce((a,b)=>a+b,0);
    ck(good.every(w=>w<=cap+1e-9),"wait cap");
    let q=Math.min(...fs(e.a-1),...fs(e.a+1));ck(q>=delta*(e.p-1)/2,"rough");z.roughChecks++;
    if(m<=8)light+=ww;second+=ww*ww/cap;capacity+=cap;eff.push(ww);
    let k=e.p+":"+e.e,o=by.get(k)||{p:e.p,e:e.e,n:0};o.n++;by.set(k,o)
   }
   for(let o of by.values()){
    let p=o.p,e=o.e,count=0,start=2*Math.ceil((3*R/4-6)/2),r=mod((e-start)*((p+1)/2),p),first=start+2*r;
    for(let a=first;a<=2*R;a+=2*p){let q=Math.min(...fs(a-1),...fs(a+1));if(q>=delta*(p-1)/2)count++}
    let times=Math.floor((nEnd-(3-R))/(2*p))+1;
    ck(o.n<=count*times,"space time rough capacity");z.capacityChecks++;
   }
   let good=eff.reduce((a,b)=>a+b,0);
   ck(high+low===sumW&&ineff<=delta*sumG+1e-7&&second<=T*C+1e-6&&good*good<=capacity*T*C+1e-4&&light<=8*capacity+1e-6,"energy wait");
   z.cauchyChecks++;row.high.push({cut,waitFraction:sumW?high/sumW:0,lightFraction:sumW?light/sumW:0,efficientKeys:eff.length,capacity,secondOverTC:second/(T*C)})
  }
  z.slabs.push(row)
 }
 // Independent common-clock mass transport sweep with active-cohort
 // retirement and persistent full-cohort DSU, no per-root event list.
 for(let row of z.slabs){
  let R=row.R,T=row.T,lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),n0=3-hi/2,n1=3-lo/2+T,N=(hi-lo)/6+1;
  let par=Array.from({length:N},(_,i)=>i),size=new Int32Array(N),act=new Int32Array(N),pos=new Int32Array(N),state=new Map(),buckets=Array.from({length:n1-n0+1},()=>[]);
  let C=0,gain=0,retGain=0,retCount=0,moved=0,birthMerge=0,eventMerge=0;
  function find(x){while(par[x]!==x){par[x]=par[par[x]];x=par[x]}return x}
  function insert(a,id,n,birth){
   let old=state.get(a);if(old!==undefined){old=find(old);id=find(id);ck(old!==id,"different clusters");
    C+=2*size[id]*size[old];par[id]=old;size[old]+=size[id];act[old]+=act[id];pos[old]=a;if(birth)birthMerge++;else eventMerge++;z.sweepMergeChecks++;return old;
   }
   state.set(a,id);pos[id]=a;let e=ev(a,n),due=n+e.w;if(due<=n1)buckets[due-n0].push({a,p:e.p});return id;
  }
  for(let n=n0;n<=n1;n++){
   let arr=[];for(let e of buckets[n-n0]){let id=state.get(e.a);ck(id!==undefined,"occupied firing");id=find(id);ck(pos[id]===e.a,"source");state.delete(e.a);gain+=act[id]*(e.p-1);arr.push({a:e.a-e.p+1,id});moved++;z.sweepEvents++}
   for(let e of arr)insert(e.a,e.id,n,false);
   let A=6-2*n;if(A>=lo&&A<=hi&&A%6===0){let id=(A-lo)/6;size[id]=1;act[id]=1;C++;insert(A,id,n,true)}
   let B=6-2*(n-T);if(B>=lo&&B<=hi&&B%6===0){let id=find((B-lo)/6);retGain+=B-pos[id];act[id]--;ck(act[id]>=0,"retire");retCount++;z.sweepRetirements++}
  }
  ck(retCount===N&&gain===retGain&&Math.abs(retGain/N-row.meanG)<1e-10,"mass gain ledger");
  let c0=[...state.values()].reduce((a,id)=>a+size[find(id)]**2,0);ck(C===c0&&C===Math.round(N*row.energyPerRoot),"energy identity");ck([...state.values()].every(id=>act[find(id)]===0),"retired");
  z.sweepBirthMerges+=birthMerge;z.sweepEventMerges+=eventMerge;z.sweepEnergyChecks++;row.sweep={moved,birthMerge,eventMerge,finalGroups:state.size};
 }
 // Independent direct canonical star search: a target B divisible by12,
 // parents B+p-1 for p|B-2, p=1 mod6. Arrival at its canonical time.
 for(let R of [12000,48000,192000,480000]){
  let row={R,centers:0,candidates:0,parents:0,stars:0,maxParents:0,hist:{},examples:[]};
  for(let B=12*Math.ceil(R/12);B<=2*R-1000;B+=12){
   let parents=[];for(let p of fs(B-2)){if(p%6!==1||p>Math.sqrt(R)*2)continue;let A=B+p-1,v=3-A/2,x=ev(A,v);row.candidates++;
    let yes=x.p===p&&x.e===1&&x.w===(p-1)/2;if(yes){ck(A%6===0&&v+x.w===3-B/2&&A-x.p+1===B,"return");parents.push(p);z.starChecks++}
   }row.centers++;z.starCenters++;row.parents+=parents.length;z.starRoots+=parents.length;row.hist[parents.length]=(row.hist[parents.length]||0)+1;
   if(parents.length){row.stars++;row.maxParents=Math.max(row.maxParents,parents.length);if(parents.length>=2&&row.examples.length<4)row.examples.push({B,parents})}
  }z.starRows.push(row)
 }
 // Formal residue environments for stars with target idle tail.
 // All fixed primes pin B=0; selected labels pin B=2. Other primes
 // avoid both neighbors of every parent and target.
 let primeList=[];for(let p=5;p<=N;p+=2)if(!spf[p])primeList.push(p);
 for(let r of [1,2,3,4]){
  let small=primeList.filter(p=>p<=2*(r+1)),L=12*small.reduce((a,b)=>a*b,1),Y=r<=2?1000:r===3?10000:20000;
  let P=primeList.filter(p=>p>=Y&&p<2*Y&&p%L===1).slice(0,r);ck(P.length===r,"band");
  let H=Math.max(...P),K=2*H,zmax=2*K+7,C=new Map(small.map(p=>[p,0]));
  for(let p of P)C.set(p,2);
  let offsets=[0,...P.map(p=>p-1)];
  for(let q of primeList){if(q>zmax)break;let B=new Set(offsets.flatMap(g=>[mod(-g-1,q),mod(-g+1,q)]));if(C.has(q)){let v=C.get(q);for(let g of offsets){let eligible=mod(v+g,q)===1||mod(v+g,q)===q-1;ck(eligible===(P.includes(q)&&g===q-1),"pinned star");z.fixedStarPrimeChecks++}}else{let v=0;while(B.has(v))v++;ck(v<q,"free star");C.set(q,v);z.fixedStarPrimeChecks++}}
  function inv6(q){return q%6===1?(5*q+1)/6:(q+1)/6}
  for(let g of offsets){let jpar=mod(g/6,2),h=3,G=0,fire=[],limit=g===0?K:g/2+K;
   for(let t=1;t<=limit;t++){let b=h+1,e=mod(3-3*jpar+t,2)===0?-1:1,p=0;
    for(let q of fs(Math.abs(e===-1?2*b+1:2*b-5))){let c=e===-1?0:q+2,yes=q===3?mod(3+t-c,3)===0:mod(3+t-c-3*mod((C.get(q)+g)*inv6(q),q),q)===0;if(yes){p=q;break}}
    h=b-(p?(p-1)/2:0);if(p){G+=p-1;fire.push([t,p,e]);}ck(h===3+t-G/2&&h>=0,"star height");z.fixedStarTicks++
   }
   ck(JSON.stringify(fire)===JSON.stringify(g===0?[]:[[g/2,g+1,1]]),"star trajectory");
  }
  z.syntheticStarControls++;z.fixedStarRows.push({r,P,K,zmax,roots:r+1})
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
