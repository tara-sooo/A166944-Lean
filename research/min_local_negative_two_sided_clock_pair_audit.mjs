// Mass-capped source/successor pairs: height pins, five-root sieve, arbitrary scales,
// and clipped minimum band-count cohort. Node >=18.
// node research/min_local_negative_two_sided_clock_pair_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+10),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity,e=0;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d;e=s}}return {p,w,e}}
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},add=(m,k,v=1)=>m.set(k,(m.get(k)||0)+v),q=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1);
 let rows=[],densityChecks=0;
 // All local product-residue patterns, including zeros and collisions.
 for(let l of [7,11,13,17,19]){
  for(let a=0;a<l;a++)for(let b=0;b<l;b++)for(let c=0;c<l;c++){
   let nonzero=new Set([a,b,c].filter(x=>x!==0)),f=2*l-1+(l-1)*nonzero.size;
   let actual=0;for(let r=0;r<l;r++)for(let v=0;v<l;v++)
    if(!r||!v||mod(r*v,l)===a||mod(r*v,l)===b||mod(r*v,l)===c)actual++;
   ck(actual===f,"local product exclusion");if(a&&b&&c&&new Set([a,b,c]).size===3)ck(actual===5*l-4,"dimension five");densityChecks++;
  }
 }
 for(let R of Rs){
  const S=Math.sqrt(2*R+1),T=Math.ceil(S),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1,L=Math.log(R),B0=Math.ceil((3*T+6)/W)+2;
  const M=Math.ceil(L**2.1),smallM=Math.ceil(L**1.8),B=Math.max(1,Math.floor(L**1.25)),delta=.8,z=5,Y=Math.max(11,Math.floor(Math.exp(L**.65))),horizon=T;
  let checks=0,events=0,replayEvents=0,roots=0,groups=new Map(),byRoot=new Map();
  function trace(A,visit){
   let j=Math.floor((A-lo)/W),n0=3-(lo+j*W)/2,end=n0+T,a=A,n=3-A/2,E=[],seen=0,band=0,repBand=0,used=new Set(),gain=0,lowGain=0,repeatLowGain=0;
   for(;;){
    let e=next(a,n),fire=n+e.w,last=fire>end,dt=Math.max(0,Math.min(fire,end)-Math.max(n,n0));
    if(dt)seen+=dt;
    E.push({a,n,j,fire,dt,last,p:e.p,w:e.w,e:e.e});
    if(last)break;
    if(e.p>z&&e.p<Y){band++;if(used.has(e.p))repBand++}
    if(e.p<Y){lowGain+=e.p-1;if(used.has(e.p))repeatLowGain+=e.p-1}
    used.add(e.p);gain+=e.p-1;a-=e.p-1;n=fire;
   }
   ck(seen===T&&gain===A-a&&gain<=3*T+6,"synchronized horizon");checks++;
   return {A,Yend:a,j,n0,end,E,band,repBand,gain,lowGain,repeatLowGain,events:E.length-1};
  }
  for(let A=lo;A<=hi;A+=6){
   let tr=trace(A),key=tr.j+":"+tr.Yend;
   let v=groups.get(key)||[];v.push({A,band:tr.band,repBand:tr.repBand,events:tr.events,Yend:tr.Yend,j:tr.j});groups.set(key,v);
   events+=tr.events;roots++;
  }
  // At the final fiber, keep the cheapest M additive band histories.
  for(let v of groups.values()){
   v.sort((a,b)=>a.band-b.band||a.A-b.A);
   for(let i=0;i<Math.min(M,v.length);i++)byRoot.set(v[i].A,{...v[i],small:i<smallM});
  }
  let kept=byRoot.size,keptSmall=0,terminalBad=0,terminalTwin=0,repTime=0,repCount=0,bandCount=0,lowGain=0,repLowGain=0;
  let phases=new Map(),terminalMap=new Map(),sourcePairs=new Map(),sourcePhases=new Map();
  let thresholds=[7,11,23,47,97,193,389].filter(x=>x<=T).map(P=>({P,B:Math.min(B,P-4),pairs:0,fast:0,slow:0,comparable:0,fastWeight:0,slowWeight:0,longWeight:0,lastWeight:0,keys:new Map(),phaseKeys:new Map(),roughTests:0,goodFive:0,heightTests:0,relays:0,relayRep:0,longInter:0}));
  let arbitrary={short:0,long:0,terminal:0,sourceFast:0,targetFast:0,bothRough:0,pairCount:0,fastCount:0,slowCount:0,distinctFast:0,distinctSlow:0,keys:new Map(),fastKeys:new Map(),fastPrefix:new Map()};
  // p<=5 runs cannot leave a width-30 common-multiple cell.
  const width=30;
  for(let [A,info] of byRoot){
   let tr=trace(A);replayEvents+=tr.events;ck(tr.Yend===info.Yend&&tr.band===info.band&&tr.j===info.j,"replay");
   keptSmall+=+info.small;bandCount+=tr.band;repCount+=tr.repBand;lowGain+=tr.lowGain;repLowGain+=tr.repeatLowGain;
   let used=new Set(),tinyGain=0,highCount=0,intermediateFirst=0,intermediateRepeat=0;
   for(let e of tr.E){
    if(e.dt){
     let phase=e.j+":"+e.a+":"+(e.last?"T":e.fire),v=phases.get(phase)||{m:0,y:tr.Yend,weight:0,p:e.p,last:e.last};
     ck(v.y===tr.Yend,"phase endpoint");v.m++;v.weight+=e.dt/T;phases.set(phase,v);
     ck(e.dt<=2*q(e.a),"dwell");
     if(e.last){
      if(q(e.a)<=S){terminalBad+=e.dt/T;let k=e.j+":"+e.a;add(terminalMap,k,e.dt/T)}
      else terminalTwin+=e.dt/T;
     }else if(e.p<Y&&used.has(e.p))repTime+=e.dt/T;
    }
    if(e.last)break;
    if(e.p<=z){tinyGain+=e.p-1;ck(Math.floor(e.a/width)===Math.floor((e.a-e.p+1)/width),"tiny barrier");}
    else if(e.p>=Y)highCount++;
    else if(used.has(e.p))intermediateRepeat++;else intermediateFirst++;
    used.add(e.p);
   }
   ck(intermediateRepeat===tr.repBand&&intermediateFirst+intermediateRepeat===tr.band&&tinyGain<=width*(1+highCount+intermediateFirst+intermediateRepeat),"tiny gain runs");
   for(let c of thresholds){
    let prev=null,seen=new Set(),relayHasRepeat=false,relayHasInter=false;
    for(let e of tr.E){
     if(e.last)break;
     if(e.p<c.P){
      if(e.p>z){relayHasInter=true;if(seen.has(e.p))relayHasRepeat=true}
      seen.add(e.p);continue;
     }
     if(prev&&prev.dt){
      let E=prev.a-prev.p+1-e.a,D=e.fire-prev.fire,h=prev.fire+(prev.a-prev.p+1)/2,f=e.e;
      let u=(prev.a-prev.e)/prev.p,v=(e.a-f)/e.p,a=prev.e+1-E-f;
      ck(E>=0&&E%2===0&&D>0&&D<=3*E+e.w,"relay clock budget");
      ck(h>=0&&h<=2*T+5&&mod(h-(prev.e===-1?0:3),prev.p)===0,"source postheight");
      let H=2*h+2*D-E+(f===-1?1:-5);
      ck(H>0&&H%e.p===0&&e.p*v===prev.p*(u-1)+a,"target nonzero height factor");
      c.heightTests++;checks++;
      let w=prev.dt/T;
      if(E>c.B){c.longWeight+=w;c.relays++;c.longInter+=+relayHasInter;c.relayRep+=+relayHasRepeat;}
      else if(prev.dt>=prev.p**delta){
       ck(prev.p!==e.p&&a%2!==0&&Math.abs(a)<prev.p,"nonzero modular hyperbola");
       c.pairs++;c.comparable+=+(e.p<=4*prev.p&&prev.p<=4*e.p);arbitrary.pairCount++;
       let tuple=[prev.a,prev.p,prev.e,e.p,f,E].join(":"),phase=[prev.a,prev.j,prev.fire].join(":");
       c.keys.set(tuple,prev.a);add(c.phaseKeys,phase);
       if(e.w<e.p**delta){
        c.fast++;c.fastWeight+=w;arbitrary.fastCount++;arbitrary.targetFast+=w;
        let key=[prev.p,h,E,D,e.p,prev.e,f].join(":"),g=arbitrary.fastKeys.get(key)||{p:prev.p,r:e.p,x:new Set(),ph:new Map(),w:0};
        g.x.add(prev.a);g.w+=w;add(g.ph,phase);arbitrary.fastKeys.set(key,g);
        let k=[prev.p,h,E,D,prev.e,f].join(":"),r=arbitrary.fastPrefix.get(k)||{H,rs:new Set()};
        ck(r.H===H,"height factor fixed");r.rs.add(e.p);arbitrary.fastPrefix.set(k,r);
       }else{
        c.slow++;c.slowWeight+=w;arbitrary.slowCount++;arbitrary.bothRough+=w;
        ck(q(prev.a)>=prev.p**delta/2&&q(e.a)>=e.p**delta/2,"two rough waits");
        let A1=-2*f,A2=a-prev.p,A3=a-prev.p-2*prev.e;
        for(let l of [7,11,13,17,19,23,29,31,37])if(l<Math.min(prev.p**delta/2,e.p**delta/2,prev.p,e.p)){
         ck(e.p%l!==0&&v%l!==0&&mod(e.p*v-A1,l)!==0&&mod(e.p*v-A2,l)!==0&&mod(e.p*v-A3,l)!==0,"five exclusions");
         let r=[mod(A1,l),mod(A2,l),mod(A3,l)];if(r.every(x=>x!==0)&&new Set(r).size===3)c.goodFive++;
         c.roughTests++;checks++;
        }
        arbitrary.keys.set(tuple,prev.a);
       }
      }
     }
     prev=e;seen.add(e.p);relayHasRepeat=false;relayHasInter=false;
    }
    if(prev&&prev.dt)c.lastWeight+=prev.dt/T;
   }
  }
  for(let [k,v] of phases){
   ck(v.m<=M&&v.weight<=M*Math.min(1,2*v.p/T)+1e-8||v.last&&v.m<=M&&v.weight<=M+1e-8,"capped departure phase");
   checks++;
  }
  let badCap=0,allCap=0,twinCount=0;
  for(let a=2*Math.ceil((lo-3*T-6)/2);a<=hi;a+=2){let w=Math.min(1,2*q(a)/T);allCap+=w;if(q(a)<=S)badCap+=w;else twinCount++;}
  for(let [k,w] of terminalMap){let a=Number(k.split(":")[1]);ck(w<=M*Math.min(1,2*q(a)/T)+1e-8,"terminal weighted cap");checks++}
  ck(terminalBad<=B0*M*badCap+1e-6*N,"terminal sieve input");
  for(let c of thresholds){
   // A source phase can occur once per root in this threshold's pair census.
   for(let m of c.phaseKeys.values()){ck(m<=M,"pair source phase cap");checks++;}
   ck(c.fast+c.slow===c.pairs,"fast/slow partition");
  }
  // Fast keys repeat across threshold controls, so compare unique spatial
  // counts and per-threshold weights with an explicit multiplicity factor.
  for(let g of arbitrary.fastKeys.values()){
   ck(g.p!==g.r&&g.x.size<=Math.floor((hi-(lo-3*T-6))/(g.p*g.r))+1,"spatial CRT count");
   for(let m of g.ph.values())ck(m<=M*thresholds.length,"fast phase cap");
   ck(g.w<=thresholds.length*B0*M*Math.min(1,2*g.p/T)*g.x.size+1e-7,"fast key weight");
   checks++;
  }
  for(let g of arbitrary.fastPrefix.values()){
   ck(g.H>0&&[...g.rs].every(r=>g.H%r===0),"fast successor factor count");checks++;
  }
  rows.push({R,N,T,M,smallM,B,z,Y,roots,events,replayEvents,checks,kept,keptSmall,retention:kept/N,smallRetention:keptSmall/N,terminalBad:terminalBad/N,terminalTwin:terminalTwin/N,repTime:repTime/N,bandCount:bandCount/N,repCount:repCount/N,lowGain:lowGain/N,repLowGain:repLowGain/N,badCap,twinCount,phaseCount:phases.size,fastKeys:arbitrary.fastKeys.size,fastPrefixes:arbitrary.fastPrefix.size,slowKeys:arbitrary.keys.size,controls:thresholds.map(c=>({P:c.P,B:c.B,pairs:c.pairs,fast:c.fast,slow:c.slow,comparable:c.comparable,fastWeight:c.fastWeight/N,slowWeight:c.slowWeight/N,longWeight:c.longWeight/N,lastWeight:c.lastWeight/N,roughTests:c.roughTests,goodFive:c.goodFive,heightTests:c.heightTests,relays:c.relays,relayRep:c.relayRep,longInter:c.longInter}))});
 }
 return {densityChecks,rows};
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000]),null,2));
