// Physical clock-block entropy ledger, separating canonical births and stationary arrival mixing.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=4000005,spf=new Int32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)if(!spf[a])spf[a]=p;
 function fs(n){let v=[];while(n>1){let p=spf[n]||n;v.push(p);while(n%p===0)n/=p}return v}
 function next(a,n){let p=Infinity,w=Infinity,s=0;for(let e of [-1,1])for(let q of fs(a-e)){let d=mod((e===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d;s=e}}return {p,w,s}}
 const f=x=>x?x*Math.log(x):0,phi=(a,b)=>f(a+b)-f(a)-f(b),g=x=>f(1+x)-f(x);
 let z={roots:0,selected:0,events:0,blocks:0,arrivalGroups:0,trafficChecks:0,entropyChecks:0,clockChecks:0,rootsAtBirthChecks:0,rows:[]};
 for(let R of [12000,48000,192000,480000,1000000,2000000]){
  let K=Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),T=4*K,J=Math.floor(T/5),H=Math.floor(3+T-J/2),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nr=(hi-lo)/6+1,blocks=new Map(),endpoints=new Map(),ns=0,visits=0,totalEvents=0;
  for(let A=lo;A<=hi;A+=6){let a=A,n=3-A/2,end=n+T,arr=0,side=0,path=[];
   for(;;){let e=next(a,n);if(n+e.w>end)break;path.push({a,n,u:n+e.w-1,arr,side,out:e.p});a-=e.p-1;n+=e.w;arr=e.p;side=e.s;z.events++}
   z.roots++;if(A-a>J)continue;let u=H-a/2;ck(n<=u&&u<=end,"cut");path.push({a,n,u,arr,side,out:0});ns++;z.selected++;totalEvents+=path.length-1;endpoints.set(a,(endpoints.get(a)||0)+1);
   for(let b of path){
    let key=b.a+":"+b.u,v=blocks.get(key)||{a:b.a,u:b.u,out:b.out,in:new Map(),mass:0};ck(v.out===b.out,"same block exit");let k=b.n+":"+b.arr+":"+b.side;v.in.set(k,(v.in.get(k)||0)+1);v.mass++;blocks.set(key,v);
   }
  }
  let row={R,K,T,J,H,nr,ns,L:0,stationary:0,simultaneous:0,birth:0,resetStationary:0,nonresetStationary:0,resetSimultaneous:0,nonresetSimultaneous:0,birthTraffic:0,birthKeys:0,stationaryIncoming:0,stationaryBase:0,resetIncoming:0,nonresetIncoming:0,simultaneousMass:0,labelWithinBlock:0,timeWithinBlock:0,blockBirth:0,blockBirthTraffic:0,blockBirthKeys:0,timeUpper:0,nonresetLabelEntropy:0,resetLabelEntropy:0,meanEvents:totalEvents/ns,physicalHighMix:0,blockHighMix:0,birthVisitsAll:0,maxBirthTraffic:0,terminalEntropy:0,terminalBlockBirth:0,terminalLabel:0,terminalTime:0,nonterminalLabel:0,nonterminalTime:0,nonterminalBlockBirth:0,touchLabelMass:0,touchTimeMass:0,tightTimeUpper:0,tightLabelUpper:0,terminalBlocks:0,terminalArrivalGroups:0,birthCodeBound:0,liveClockEntropy:0,terminalClockEntropy:0,terminalClockRank:0,nonterminalClockRank:0,resetLabelUpper:0,nonresetLabelUpper:0};
  for(let v of blocks.values()){
   z.blocks++;let byTime=new Map(),byLabel=new Map(),total=0,birth=0;let lastClock=-Infinity;
   for(let [k,m] of v.in){let [n,p,s]=k.split(":").map(Number);ck(n<=v.u,"interval");let a=v.a,h=n+a/2;z.arrivalGroups++;
    if(!p){ck(m===1&&h===3&&a%6===0,"birth");birth=m;row.birthKeys++;}else{ck(mod(a-(s+1),p)===0&&mod(n-(s===-1?0:p+2),2*p)===0,"incoming");z.clockChecks++;let key=p+":"+s,l=byLabel.get(key)||{m:0,age:0,entries:[],times:[]};l.m+=m;l.age+=m*Math.floor((v.u-n)/(2*p));l.entries.push(m);l.times.push(Math.floor((v.u-n)/(2*p)));byLabel.set(key,l)}
    let t=byTime.get(n)||{birth:0,arr:[]};if(p)t.arr.push({m,p,s});else t.birth=m;byTime.set(n,t);total+=m;
   }
   ck(total===v.mass,"block mass");z.trafficChecks++;
   let labTotal=total-birth,labH=f(labTotal),timeH=0,timeUpper=0,tightTime=0;
   for(let l of byLabel.values()){labH-=f(l.m);timeH+=f(l.m)-l.entries.reduce((s,m)=>s+f(m),0);timeUpper+=l.m*g(l.age/l.m);if(l.entries.length>1){let kmin=Math.min(...l.times);tightTime+=l.m*g(l.age/l.m-kmin);row.touchTimeMass+=l.m}}
   if(byLabel.size>1){row.touchLabelMass+=labTotal;row.tightLabelUpper+=labTotal*Math.log(byLabel.size)}row.tightTimeUpper+=tightTime;ck(timeH<=tightTime+1e-7,'tight time');if(v.out===0){row.terminalBlocks++;row.terminalArrivalGroups+=v.in.size;row.terminalLabel+=labH;row.terminalTime+=timeH;row.terminalBlockBirth+=birth?phi(1,labTotal):0;row.terminalEntropy+=f(total)-[...v.in.values()].reduce((s,m)=>s+f(m),0)}else{row.nonterminalLabel+=labH;row.nonterminalTime+=timeH;row.nonterminalBlockBirth+=birth?phi(1,labTotal):0}row.labelWithinBlock+=labH;row.timeWithinBlock+=timeH;row.timeUpper+=timeUpper;ck(timeH<=timeUpper+1e-7,"time bound");
   if(birth){row.blockBirth+=phi(1,labTotal);row.blockBirthTraffic+=labTotal;row.blockBirthKeys++}
   let m=0,entropy=0,first=0;
   for(let [n,t] of [...byTime].sort((a,b)=>a[0]-b[0])){
    let h=n+v.a/2,reset=h===0||h===3,I=t.arr.reduce((s,e)=>s+e.m,0),bm=phi(m,I),sim=f(I)-t.arr.reduce((s,e)=>s+f(e.m),0);
    row.stationary+=bm;row.simultaneous+=sim;if(t.arr.length>1){let r=reset?fs(v.a-(mod(n,2)?2:0)).length:fs(Math.abs(h-(mod(n,2)?3:0))).length;ck(r>=t.arr.length,'clock factor count');if(reset)row.resetLabelUpper+=I*Math.log(r);else row.nonresetLabelUpper+=I*Math.log(r)}
    if(reset){row.resetStationary+=bm;row.resetSimultaneous+=sim;if(m)row.resetIncoming+=I}else{row.nonresetStationary+=bm;row.nonresetSimultaneous+=sim;if(m)row.nonresetIncoming+=I}
    if(m&&I){row.stationaryIncoming+=I;row.stationaryBase+=m}
    if(t.arr.length>1)row.simultaneousMass+=I;
    let q=t.arr.filter(e=>e.p>=Math.max(5,J/8));let mass=q.reduce((s,e)=>s+e.m,0);row.physicalHighMix+=f(mass)-q.reduce((s,e)=>s+f(e.m),0);
    m+=I;
    if(t.birth){row.birth+=phi(1,m);row.birthTraffic+=m;row.maxBirthTraffic=Math.max(row.maxBirthTraffic,m);m++;z.rootsAtBirthChecks++}
    entropy+=bm+sim+(t.birth?phi(1,m-1):0);
   }
   if(v.a%6===0&&v.a>=lo&&v.a<=hi&&3-v.a/2<=v.u){let n=3-v.a/2;row.birthVisitsAll+=[...byTime].filter(([x,t])=>x<=n).reduce((s,[x,t])=>s+t.birth+t.arr.reduce((q,e)=>q+e.m,0),0)}
   let exact=f(total)-[...v.in.values()].reduce((s,m)=>s+f(m),0);ck(Math.abs(entropy-exact)<1e-7&&Math.abs(labH+timeH+(birth?phi(1,labTotal):0)-exact)<1e-7,"entropy decomposition");z.entropyChecks++;
  }
  let L=[...endpoints.values()].reduce((s,m)=>s+f(m),0);ck(Math.abs(L-row.stationary-row.simultaneous-row.birth)<1e-6&&Math.abs(L-row.labelWithinBlock-row.timeWithinBlock-row.blockBirth)<1e-6,"global");ck(row.birthKeys===ns,"birth count");row.L=L;
  row.birthCodeBound=ns*g(totalEvents/ns);row.birthUpper=ns*g(row.birthTraffic/ns);ck(row.birth<=row.birthCodeBound+1e-7,'birth events');row.blockBirthUpper=ns*g(row.blockBirthTraffic/ns);ck(row.birth<=row.birthUpper+1e-7&&row.blockBirth<=row.blockBirthUpper+1e-7,"birth Jensen");
  for(let k of Object.keys(row))if(!["R","K","T","J","H","nr","ns","meanEvents","maxBirthTraffic","birthKeys","blockBirthKeys"].includes(k))row[k]/=ns;
  z.rows.push(row)
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
