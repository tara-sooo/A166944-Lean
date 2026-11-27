// Weighted online cheap-history flow: asymmetric relay counts and common-state rough dwell costs.
// node research/min_local_negative_weighted_live_flow_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+10),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const q=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1),ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 const f=(a,b)=>a.cost-b.cost||a.A-b.A;
 const rows=[];
 for(let R of Rs){
  let S=Math.sqrt(2*R+1),T=Math.ceil(S),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1,z=5,Y=23,P=97,Q=30,Pmax=T/2,k=2;
  const weight=(p,a)=>p>z&&p<Y?8:p>=Y&&p<P&&4*q(a)**2>=p?2*q(a):0;
  const cs=[[4,32],[16,128],[64,128],[64,256]].map(([M,H])=>({M,H,merge:0,cross:0,ret:0,liveTicks:0,termBad:0,termTwin:0,low:0,high:0,near:0,last:0,short:0,long:0,band:0,roughCost:0,fastMedium:0,otherMedium:0,checks:0,events:0,phaseChecks:0,early:0,quarter:0,half:0,threeQuarter:0,retwin:0}));
  let rootEvents=0;
  for(let l=lo;l<=hi;l+=W){
   let maxA=Math.min(hi,l+W-6),start=3-maxA/2,n0=3-l/2,end=n0+T,traces=new Map();
   for(let A=l;A<=maxA;A+=6){
    let a=A,n=3-A/2,trace=[],cost=0;
    for(;;){let e=next(a,n),fire=n+e.w,last=fire>end;trace.push({a,n,fire,p:e.p,last});
     if(last)break;
     cost+=weight(e.p,a);a-=e.p-1;n=fire;rootEvents++;}
    traces.set(A,{trace,y:a,cost});
   }
   for(let c of cs){
    let active=new Map(),buckets=new Map(),death=new Map(),diff=new Int32Array(T+1),expected=new Map(),phase=new Map();
    const add=(m,k,v)=>m.set(k,(m.get(k)||0)+v);
    function schedule(a,n,v){let e=next(a,n),t=n+e.w;if(t<=end){let b=buckets.get(t)||[];b.push({a,p:e.p,v});buckets.set(t,b);}}
    for(let n=start;n<=end;n++){
     let arrivals=new Map();
     function push(a,tokens){let v=arrivals.get(a)||[];v.push(...tokens);arrivals.set(a,v)}
     for(let e of buckets.get(n)||[]){
      if(active.get(e.a)!==e.v)continue;
      active.delete(e.a);let inc=weight(e.p,e.a),list=[];
      for(let token of e.v){let t={A:token.A,cost:token.cost+inc};if(t.cost>c.H){ck(!death.has(t.A),"unique budget death");death.set(t.A,n);c.cross++;}else list.push(t);}
      if(list.length)push(e.a-e.p+1,list);c.events++;
     }
     let A=2*(3-n);if(A>=l&&A<=maxA&&A%6===0)push(A,[{A,cost:0}]);
     for(let [a,list] of arrivals){
      let v=active.get(a);if(v)list.push(...v);list.sort(f);
      for(let t of list.slice(c.M)){ck(!death.has(t.A),"unique merger death");death.set(t.A,n);c.merge++;}
      let live=list.slice(0,c.M);active.set(a,live);schedule(a,n,live);c.checks++;
     }
    }
    for(let [A,t] of traces)if(t.cost<=c.H){let v=expected.get(t.y)||[];v.push({A,cost:t.cost});expected.set(t.y,v)}
    ck(active.size===expected.size,"endpoint support");
    let ret=0;
    for(let [y,list] of expected){let v=active.get(y),w=list.sort(f).slice(0,c.M);ck(v.length===w.length&&v.every((t,i)=>t.A===w[i].A&&t.cost===w[i].cost),"exact greedy endpoint");ret+=v.length;if(q(y)>S)c.retwin+=v.length;}
    c.ret+=ret;
    ck(ret+death.size===traces.size,"live/dead partition");
    let time=0;
    for(let [A,t] of traces){
     let stop=death.get(A)??end;
     let aliveEnd=Math.max(n0,Math.min(stop,end)),life=aliveEnd-n0;
     diff[0]++;diff[life]--;time+=life;c.liveTicks+=life;
     c.early+=+(life>0);c.quarter+=+(life>=T/4);c.half+=+(life>=T/2);c.threeQuarter+=+(life>=3*T/4);
     let observed=0,band=0,low=0,tiny=0,nHigh=0,partial=0,roughCost=0,fastMedium=0,otherMedium=0,spent=0,maxInc=0,mediumGain=0;
     let highs=t.trace.map((e,i)=>!e.last&&e.p>=Y?i:-1).filter(i=>i>=0);
     for(let e of t.trace){
      if(!e.last&&e.fire<=stop){let w=weight(e.p,e.a);spent+=w;maxInc=Math.max(maxInc,w);if(e.p>z&&e.p<Y)band++;if(e.p<=z)tiny+=e.p-1;if(e.p>=Y)nHigh++;if(e.p>=Y&&e.p<P){mediumGain+=e.p-1;if(w)roughCost+=w;}}
      let dt=Math.max(0,Math.min(e.fire,end,stop)-Math.max(e.n,n0));if(!dt)continue;
      observed+=dt;
      let key=e.a+":"+(e.last?"T":e.fire),v=phase.get(key)||{m:0,a:e.a,p:e.p,last:e.last,fire:e.last?end:e.fire};v.m+=dt;phase.set(key,v);
      if(e.last){if(q(e.a)<=S)c.termBad+=dt;else c.termTwin+=dt;}
      else if(e.p<P){low+=dt;if(e.fire>stop)partial+=dt;else if(e.p>=Y){if(weight(e.p,e.a)){otherMedium+=dt;ck(dt<=2*q(e.a),'rough medium dwell cap');}else{fastMedium+=dt;ck(dt<Math.sqrt(e.p),'fast medium dwell');}}}
     }
     ck(observed===life&&spent<=c.H+maxInc&&spent===8*band+roughCost,"live time and weighted budget");c.band+=band;c.low+=low;c.roughCost+=roughCost;c.fastMedium+=fastMedium;c.otherMedium+=otherMedium;
     ck(tiny<=Q*(1+nHigh+band)&&otherMedium<=roughCost&&fastMedium<=2*mediumGain/Math.sqrt(Y)+1e-8&&low<=3*(Q*(1+nHigh+band)+Y*band)+roughCost+fastMedium+2*P,"weighted prefix low gain");
     let charged=0;
     for(let i=0;i<highs.length;i++){
      let s=t.trace[highs[i]];if(s.p<P)continue;let dt=Math.max(0,Math.min(s.fire,end,stop)-Math.max(s.n,n0));if(!dt)continue;
      c.high+=dt;
      if(s.p>=Pmax){c.near+=dt;continue;}
      let j=highs[i+1];if(j===undefined||t.trace[j].fire>stop){c.last+=dt;continue;}
      let b=t.trace.slice(highs[i]+1,j).filter(e=>e.p>z&&e.p<Y).length;
      if(b<=k)c.short+=dt;else{c.long+=dt;charged+=k+1;}
     }
     ck(charged<=band,"live disjoint charge");c.checks++;
    }
    let count=0,sum=0;for(let i=0;i<T;i++){count+=diff[i];sum+=count;}ck(sum===time,"integral of live survival");
    for(let v of phase.values()){
     let cap=c.M*Math.min(T,2*q(v.a));ck(v.m<=cap,"live phase time cap");
     if(!v.last)ck(v.m<=c.M*Math.min(T,2*v.p),"live label cap");
     c.phaseChecks++;
    }
   }
  }
  for(let c of cs){
   ck(c.merge+c.cross+c.ret===N,"loss ledger");
   ck(c.liveTicks===c.termBad+c.termTwin+c.low+c.high&&c.high===c.near+c.last+c.short+c.long,"time partition");
   ck(c.long<=(2*Pmax/(k+1))*c.band+1e-7,"aggregate charge");
  }
  rows.push({R,N,T,rootEvents,z,Y,P,k,controls:cs.map(c=>({M:c.M,H:c.H,ret:c.ret/N,retwin:c.retwin/N,merge:c.merge/N,cross:c.cross/N,live:c.liveTicks/(N*T),early:c.early/N,quarter:c.quarter/N,half:c.half/N,threeQuarter:c.threeQuarter/N,termBad:c.termBad/(N*T),termTwin:c.termTwin/(N*T),low:c.low/(N*T),high:c.high/(N*T),near:c.near/(N*T),last:c.last/(N*T),short:c.short/(N*T),long:c.long/(N*T),band:c.band/N,roughCost:c.roughCost/(N*T),fastMedium:c.fastMedium/(N*T),otherMedium:c.otherMedium/(N*T),events:c.events,checks:c.checks,phaseChecks:c.phaseChecks}))});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000]),null,2));
