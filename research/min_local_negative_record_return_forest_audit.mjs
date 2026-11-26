// Record-height return forests, exact traffic/energy/weighted-displacement ledger.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=400010,spf=new Uint32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)if(!spf[a])spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity,side=0;for(let e of [-1,1])for(let q of fs(a-e)){let t=mod((e===-1?0:q+2)-n,2*q)||2*q;if(t<w||t===w&&q<p){p=q;w=t;side=e}}return {p,w,side}}
 let out={roots:0,survivors:0,events:0,recordIntervals:0,edgeIncidences:0,edgeKeys:0,trafficChecks:0,shortChecks:0,repeatChecks:0,crossChecks:0,energyChecks:0,gainChecks:0,pairChecks:0,earlySharedPairs:0,rows:[]};
 for(let [R,Hmax] of [[3000,64],[12000,128],[48000,256],[192000,512]]){
  let T=Math.ceil(8*Math.sqrt(2*R+1)),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),Nroots=(hi-lo)/6+1,sites=new Map(),levels=Array.from({length:Hmax+1},()=>new Map()),saved=[],gain=0,nKeep=0;
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,h=3,record=3,end=n+T,ar=[],er=[],pending=null,ok=false;
   for(;;){let e=next(a,n),pre=h+e.w,f=n+e.w;
    if(pending&&pre>=pending.b){let ret=n+pending.b-h;if(ret>end)break;let D=pending.a-a;ck(D>=pending.p-1&&ret-pending.n===D/2,"return clock");er.push({...pending,c:a,D});pending=null}
    if(pre>record){let cap=Math.min(pre,Hmax+1),t=n+cap-h;if(t>end)break;ar.push(a,record+1,cap);record=cap;if(record===Hmax+1){ok=true;break}}
    if(f>end)break;
    if(pre===record){ck(!pending,"one pending");pending={b:pre,a,n:f,p:e.p,side:e.side}}
    a-=e.p-1;n=f;h=pre-(e.p-1)/2;out.events++;ck(a>0,"physical");
   }
   out.roots++;if(!ok)continue;nKeep++;out.survivors++;gain+=A-a;
   for(let i=0;i<ar.length;i+=3){let a=ar[i],v=sites.get(a)||[];v.push(ar[i+1],ar[i+2]);sites.set(a,v);out.recordIntervals++}
   let dsum=0;for(let e of er){let map=levels[e.b],r=map.get(e.a)||{...e,m:0};ck(r.c===e.c&&r.p===e.p&&r.side===e.side,"deterministic edge");r.m++;map.set(e.a,r);dsum+=e.D;out.edgeIncidences++}
   ck(dsum===A-a,"gain partition");out.gainChecks++;if(R===3000)saved.push({A,a,er,ar});
  }
  let uEnergy=new Float64Array(Hmax+2),uMass=new Float64Array(Hmax+2),dif=new Int32Array(Hmax+3);
  for(let [a,v] of sites){dif.fill(0);for(let i=0;i<v.length;i+=2){dif[v[i]]++;dif[v[i+1]+1]--}let m=0;for(let b=4;b<=Hmax+1;b++){m+=dif[b];uEnergy[b]+=m*m;uMass[b]+=m}}
  function u(a,b){let v=sites.get(a)||[],m=0;for(let i=0;i<v.length;i+=2)m+=+(v[i]<=b&&b<=v[i+1]);return m}
  let row={R,Hmax,T,Nroots,nKeep,meanGain:gain/nKeep,initialEnergy:uEnergy[4],finalEnergy:uEnergy[Hmax+1],delta:0,baseCross:0,branchCross:0,shortBase:0,longBase:0,shortShort:0,shortLong:0,longLong:0,shortShortSameLabel:0,shortShortDifferentLabels:0,topBase:0,topBranchTouch:0,oldBase:0,freshBase:0,initialMovingEnergy:0,trafficEnergy:0,edgeGain:0,weightedTraffic:0,repeats:0,maxRepeatRatio:0,shortEdges:0,longEdges:0,returnKeys:0,returnEvents:0,levels:[]},cum=0;
  for(let b=4;b<=Hmax;b++){
   let map=levels[b],incoming=new Map(),d=0,locationMoment=0,eBefore=0,eAfter=0,flowMoment=0,base=0,branch=0;
   for(let [a,e] of map){let v=incoming.get(e.c)||[];v.push(e);incoming.set(e.c,v);out.edgeKeys++;row.returnKeys++;row.returnEvents+=e.m;row.trafficEnergy+=e.m**2;row.initialMovingEnergy+=u(a,b)**2;row.edgeGain+=e.m*e.D;row.weightedTraffic+=e.m**2*e.D;flowMoment+=e.m**2*e.D;
    ck((e.side===-1?2*b+1:2*b-5)%e.p===0&&mod(a-e.side,e.p)===0&&mod(b-a/2,2)===(e.side===-1?0:1),"record congruence");
    e.short=e.D-(e.p-1)<=3*e.p;e.top=e.p>=b/4;if(e.short)row.shortEdges++;else row.longEdges++;
    if(map.has(e.c)){let f=map.get(e.c);if(e.p===f.p&&e.side===f.side){ck(e.D>=4*e.p&&e.D%(4*e.p)===0&&!e.short,"same label repeat");out.repeatChecks++;row.repeats+=e.m;row.maxRepeatRatio=Math.max(row.maxRepeatRatio,e.D/e.p)}}
   }
   for(let a of new Set([...map.keys(),...incoming.keys()])){
    let m=u(a,b),v=incoming.get(a)||[],I=v.reduce((s,x)=>s+x.m,0),F=m+I,ss=v.filter(x=>x.short),ls=v.filter(x=>!x.short),si=ss.reduce((s,x)=>s+x.m,0),li=I-si;
    if(map.has(a)){ck(map.get(a).m===F,{R,b,a,m,I,actual:map.get(a).m});out.trafficChecks++}else{ck(u(a,b+1)===F,"terminal traffic");out.trafficChecks++}
    let bc=2*m*I,cc=I*I-v.reduce((s,x)=>s+x.m*x.m,0),delta=bc+cc;d+=delta;base+=bc;branch+=cc;locationMoment+=a*delta;eBefore+=a*m*m;if(!map.has(a))eAfter+=a*F*F;
    row.shortBase+=2*m*si;row.longBase+=2*m*li;row.shortShort+=si*si-ss.reduce((s,x)=>s+x.m*x.m,0);row.longLong+=li*li-ls.reduce((s,x)=>s+x.m*x.m,0);row.shortLong+=2*si*li;
    let seen=new Set();for(let e of ss){let k=e.p+":"+e.side;ck(!seen.has(k),"same-label short injection");seen.add(k);out.shortChecks++}
    for(let e of v){if(e.top)row.topBase+=2*m*e.m;if(e.p===2*b+1)row.freshBase+=2*m*e.m;else row.oldBase+=2*m*e.m}
    for(let i=0;i<v.length;i++)for(let j=i+1;j<v.length;j++){let e=v[i],f=v[j],w=2*e.m*f.m;if(e.top||f.top)row.topBranchTouch+=w;if(e.short&&f.short){if(e.p===f.p)row.shortShortSameLabel+=w;else row.shortShortDifferentLabels+=w}out.crossChecks++}
   }
   ck(uMass[b]===nKeep&&uMass[b+1]===nKeep&&d===uEnergy[b+1]-uEnergy[b],"energy exact");ck(flowMoment===locationMoment+eBefore-eAfter,{R,b,flowMoment,locationMoment,eBefore,eAfter});out.energyChecks++;
   row.delta+=d;row.baseCross+=base;row.branchCross+=branch;cum+=d;
   if([8,16,32,64,128,256,512].includes(b))row.levels.push({b,energy:uEnergy[b+1]/nKeep,cumulative:cum/nKeep});
  }
  ck(row.delta===row.baseCross+row.branchCross&&row.delta===row.finalEnergy-row.initialEnergy&&row.edgeGain===gain,"global");ck(row.weightedTraffic<=(2*T+6)*row.finalEnergy,"weighted budget");ck(row.shortShort===row.shortShortSameLabel+row.shortShortDifferentLabels,"short cross partition");
  if(R===3000){let pairSum=0;
   for(let i=0;i<saved.length;i++)for(let j=i;j<saved.length;j++){
    let A=saved[i],B=saved[j],shared=0,first=null,map=new Map(A.er.map(e=>[e.b+":"+e.a,e.D]));
    for(let e of B.er)if(map.has(e.b+":"+e.a)){ck(map.get(e.b+":"+e.a)===e.D,"pair edge");shared+=e.D;if(first===null)first=e.a}
    if(A.a!==B.a)ck(shared===0,"shared implies final");
    else {ck(shared===(first===null?0:first-A.a),"shared suffix");let cut=null;for(let k=4;k<=Hmax+1;k++){function at(x){for(let t=0;t<x.ar.length;t+=3)if(x.ar[t+1]<=k&&k<=x.ar[t+2])return x.ar[t];throw Error("cut")};let x=at(A),y=at(B);if(x===y){cut=x;break}}ck(cut!==null&&shared>=cut-A.a,"first cut lower bound");if(shared>cut-A.a)out.earlySharedPairs++}
    pairSum+=(i===j?1:2)*shared;out.pairChecks++;
   }ck(pairSum===row.weightedTraffic,"pair weighted ledger");
  }
  row.baseFraction=row.baseCross/row.delta;row.shortBaseFraction=row.shortBase/row.delta;row.weightedRatio=row.weightedTraffic/((2*T+6)*row.finalEnergy);out.rows.push(row);
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
