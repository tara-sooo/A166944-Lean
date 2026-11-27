// Greedy clipped minimum history costs, disjoint relay charging, exact forest replay.
// node research/min_local_negative_minimum_band_history_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+10),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},f=x=>x?x*Math.log(x):0;
 const rows=[];
 for(let R of Rs){
  const T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1,L=Math.log(R);
  const M=Math.max(1,Math.floor(L**2.1)),z=5,Q=30,Y=47,B=32,Pmax=Math.max(Y+1,Math.floor(T/2));
  const controls=[1,4,16,64,256],byCost=controls.map(H=>({H,retained:0,births:0,twins:0}));
  let events=0,merges=0,checks=0,rootEvents=0,retained=0,actualCost=0,greedyCost=0,traffic=0,deletedCost=0,deletedMass=0,greedyLow=0,greedyRelay=0,greedyRepeat=0,twinRetained=0;
  for(let l=lo;l<=hi;l+=W){
   let maxA=Math.min(hi,l+W-6),start=3-maxA/2,n0=3-l/2,end=n0+T,active=new Map(),buckets=new Map(),byEnd=new Map();
   function sched(a,n,v){const e=next(a,n),t=n+e.w;if(t<=end){let b=buckets.get(t)||[];b.push({a,p:e.p,v});buckets.set(t,b)}}
   for(let n=start;n<=end;n++){
    let arrivals=new Map();
    function push(a,group){let v=arrivals.get(a)||[];v.push(group);arrivals.set(a,v)}
    for(let e of buckets.get(n)||[]){
     let v=active.get(e.a);if(v!==e.v)continue;
     active.delete(e.a);let inc=+(e.p>z&&e.p<Y);
     traffic+=v.cost.length*inc;
     push(e.a-e.p+1,{m:v.m,cost:v.cost.map(c=>c+inc)});events++;
    }
    let A=2*(3-n);if(A>=l&&A<=maxA&&A%6===0)push(A,{m:1,cost:[0]});
    for(let [a,gs] of arrivals){
     let v=active.get(a);if(v)gs.push(v);
     let m=gs.reduce((s,g)=>s+g.m,0),all=gs.flatMap(g=>g.cost).sort((a,b)=>a-b),cost=all.slice(0,M),discard=all.slice(M);
     ck(cost.length===Math.min(M,m),"clipped mass invariant");
     deletedCost+=discard.reduce((s,c)=>s+c,0);deletedMass+=discard.length;
     if(gs.length>1)merges++;
     let x={m,cost};active.set(a,x);sched(a,n,x);checks++;
    }
   }
   // independent root replay and exact per-fiber minimum cost list.
   for(let A=l;A<=maxA;A+=6){
    let a=A,n=3-A/2,cost=0,low=0,relay=0,rep=0,tiny=0,nHigh=0,nBand=0,runHigh=null,seen=new Set(),used=new Set(),gain=0;
    for(;;){
     let e=next(a,n),fire=n+e.w;
     if(fire>end)break;
     const dt=Math.max(0,fire-Math.max(n,n0)),p=e.p;
     if(p<Y)low+=dt/T;
     if(p<=z){ck(Math.floor(a/Q)===Math.floor((a-p+1)/Q),"barrier");tiny+=p-1;}
     else if(p<Y){cost++;nBand++;if(used.has(p))rep++;}
     else{
      nHigh++;
      if(runHigh){
       let E=runHigh.a-runHigh.p+1-a;
       if(E>B&&runHigh.p<=Pmax){
        ck(cost>runHigh.cost,"intermediate label in long relay");
        relay+=runHigh.dt/T;
       }
      }
      runHigh={a,p,dt,cost};
     }
     used.add(p);gain+=p-1;a-=p-1;n=fire;rootEvents++;
    }
    ck(gain===A-a&&gain<=3*T+6&&tiny<=Q*(1+nHigh+nBand),"tiny run bound");
    ck(low<=3*(Q*(1+nHigh+nBand)+(Y-1)*nBand)/T+1e-8,"low time bound");
    ck(relay<=2*Pmax/T*nBand+1e-8&&nBand-rep<=Y,"disjoint long-relay charge");
    let v=byEnd.get(a)||[];v.push({A,cost,low,relay,rep});byEnd.set(a,v);checks++;
   }
   ck(active.size===byEnd.size,"endpoint support");
   for(let [a,rs] of byEnd){
    const v=active.get(a);rs.sort((a,b)=>a.cost-b.cost||a.A-b.A);
    const sel=rs.slice(0,M),actual=sel.map(x=>x.cost);
    ck(v.m===rs.length&&v.cost.length===actual.length&&v.cost.every((x,i)=>x===actual[i]),"greedy optimal costs");
    retained+=v.cost.length;actualCost+=actual.reduce((s,c)=>s+c,0);greedyCost+=v.cost.reduce((s,c)=>s+c,0);
    greedyLow+=sel.reduce((s,x)=>s+x.low,0);greedyRelay+=sel.reduce((s,x)=>s+x.relay,0);greedyRepeat+=sel.reduce((s,x)=>s+x.rep,0);
    let twin=Math.min(spf[a-1]||a-1,spf[a+1]||a+1)>Math.sqrt(2*R+1);
    if(twin)twinRetained+=actual.length;
    for(let c of byCost){let n=rs.filter(x=>x.cost<=c.H).length,m=Math.min(n,M);ck(v.cost.filter(x=>x<=c.H).length===m,"threshold clipped mass");c.retained+=m;c.births+=n;if(twin)c.twins+=m;}
    checks++;
   }
  }
  ck(retained+deletedMass===N&&traffic===greedyCost+deletedCost&&greedyCost===actualCost,"exact cost and mass telescope");
  rows.push({R,N,T,M,z,Q,Y,B,Pmax,events,merges,rootEvents,checks,retention:retained/N,twinRetention:twinRetained/N,meanMinCost:greedyCost/N,meanMinRepeat:greedyRepeat/N,meanTraffic:traffic/N,meanDeletedCost:deletedCost/N,low:greedyLow/N,longRelay:greedyRelay/N,thresholds:byCost.map(c=>({H:c.H,retained:c.retained/N,roots:c.births/N,twin:c.twins/N}))});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000,1000000,2000000]),null,2));
