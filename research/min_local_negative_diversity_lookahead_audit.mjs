// Per-relay distinct-prime cost and exact one-block lookahead selection.
// node research/min_local_negative_diversity_lookahead_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+10),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const q=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1),ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 const rows=[];
 for(let R of Rs){
  let S=Math.sqrt(2*R+1),T=Math.ceil(S),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
  const z=3,Y=47,P=97,divWeight=8,Pmax=T/2;
  const base=(p,x)=>p>z&&p<P?+(p<Y)+(4*q(x)**2>=p?2*q(x):0):0;
  let controls=[[1,48],[4,128],[16,256]].map(([M,H])=>({M,H,lookRet:0,naiveRet:0,offline:0,lookCost:0,naiveCost:0,lookLive:0,naiveLive:0,lookMerge:0,lookCross:0,naiveMerge:0,naiveCross:0,different:0,checks:0,lookEvents:0,naiveEvents:0,cache:0}));
  let rootEvents=0,supportChecks=0,pairs=0,smallSupport=0,distinctCharge=0,totalCount=0,totalDistinct=0,maxSmallLen=0,examples=[];
  for(let l=lo;l<=hi;l+=W){
   let maxA=Math.min(hi,l+W-6),start=3-maxA/2,n0=3-l/2,end=n0+T,traces=new Map(),futureCache=new Map();
   function future(a,n){
    let key=a+":"+n,v=futureCache.get(key);if(v)return v;
    let seen=new Set(),x=a,t=n;
    for(;;){let e=next(x,t),fire=t+e.w;if(fire>end||e.p>=Y)break;if(e.p>z)seen.add(e.p);x-=e.p-1;t=fire;}
    futureCache.set(key,seen);return seen;
   }
   for(let A=l;A<=maxA;A+=6){
    let a=A,n=3-A/2,trace=[],cost=0,seen=new Set(),count=0,distinct=0,block=[],blockLabels=new Set(),lastHigh=null,charged=0;
    function checkBlock(){
     if(blockLabels.size<=3){ck(block.length<=[0,2,6,18][blockLabels.size],"uniform support bound");supportChecks++;maxSmallLen=Math.max(maxSmallLen,block.length);}
    }
    for(;;){let e=next(a,n),fire=n+e.w;if(fire>end)break;
     trace.push({a,n,p:e.p,fire});cost+=base(e.p,a);
     if(e.p>=Y){
      checkBlock();
      if(lastHigh!==null&&lastHigh.p>=P){pairs++;if(seen.size<=2){smallSupport++;ck(block.length<=18,"few distinct relay bound");}else if(lastHigh.p<Pmax){charged+=3;distinctCharge+=3;}}
      lastHigh=e;seen=new Set();block=[];blockLabels=new Set();
     }else{
      block.push(e.p);blockLabels.add(e.p);
      if(e.p>z){count++;if(!seen.has(e.p)){seen.add(e.p);cost+=divWeight;distinct++;}}
     }
     a-=e.p-1;n=fire;rootEvents++;
    }
    checkBlock();ck(charged<=distinct&&distinct<=count,"disjoint distinct charge");totalCount+=count;totalDistinct+=distinct;traces.set(A,{y:a,cost,trace});
   }
   for(let c of controls){
    let expected=new Map();for(let [A,t] of traces)if(t.cost<=c.H){let v=expected.get(t.y)||[];v.push({A,cost:t.cost});expected.set(t.y,v)}
    for(let v of expected.values())v.sort((a,b)=>a.cost-b.cost||a.A-b.A);
    let offline=[...expected.values()].reduce((s,v)=>s+Math.min(c.M,v.length),0);c.offline+=offline;
    let outcomes=[];
    for(let mode of ["look","naive"]){
     let active=new Map(),buckets=new Map(),death=new Map(),merge=0,cross=0,events=0;
     function sched(a,n,v){let e=next(a,n),t=n+e.w;if(t<=end){let b=buckets.get(t)||[];b.push({a,p:e.p,v});buckets.set(t,b)}}
     for(let n=start;n<=end;n++){
      let arrivals=new Map();function push(a,ls){let v=arrivals.get(a)||[];v.push(...ls);arrivals.set(a,v)}
      for(let e of buckets.get(n)||[]){
       if(active.get(e.a)!==e.v)continue;
       active.delete(e.a);let out=[];
       for(let token of e.v){
        let seen=new Set(token.seen),cost=token.cost+base(e.p,e.a);
        if(e.p>=Y)seen.clear();else if(e.p>z&&!seen.has(e.p)){seen.add(e.p);cost+=divWeight;}
        if(cost>c.H){ck(!death.has(token.A),"budget death");death.set(token.A,n);cross++;}else out.push({A:token.A,cost,seen});
       }
       if(out.length)push(e.a-e.p+1,out);events++;
      }
      let A=2*(3-n);if(A>=l&&A<=maxA&&A%6===0)push(A,[{A,cost:0,seen:new Set()}]);
      for(let [a,ls] of arrivals){
       let v=active.get(a);if(v)ls.push(...v);
       let F=mode==="look"?future(a,n):new Set();
       const score=t=>t.cost+divWeight*[...F].filter(p=>!t.seen.has(p)).length;
       ls.sort((a,b)=>score(a)-score(b)||a.A-b.A);
       if(mode==="look"&&ls.length>1){
        // The full suffix beyond the next high is common; projected ordering
        // must therefore equal actual complete cost ordering for every pair.
        for(let i=1;i<ls.length;i++){
         let a=ls[i-1],b=ls[i],da=traces.get(a.A).cost,db=traces.get(b.A).cost;
         ck(da<db||da===db&&a.A<b.A,"lookahead order equals full cost order");c.checks++;
        }
       }
       for(let token of ls.slice(c.M)){ck(!death.has(token.A),"merge death");death.set(token.A,n);merge++;}
       let kept=ls.slice(0,c.M);active.set(a,kept);sched(a,n,kept);
      }
     }
     let ret=0,cost=0,ids=new Map();
     for(let [y,v] of active){
      v.sort((a,b)=>a.cost-b.cost||a.A-b.A);ret+=v.length;cost+=v.reduce((s,t)=>s+t.cost,0);ids.set(y,v.map(t=>t.A));
      for(let t of v)ck(t.cost===traces.get(t.A).cost&&y===traces.get(t.A).y&&t.cost<=c.H,"actual final cost");
     }
     if(mode==="look"){
      ck(ret===offline&&active.size===expected.size,"exact lookahead retention");
      for(let [y,v] of expected){let a=ids.get(y),b=v.slice(0,c.M).map(t=>t.A);ck(a&&a.length===b.length&&a.every((x,i)=>x===b[i]),"exact lookahead IDs");c.checks++;}
     }else ck(ret<=offline,"naive upper by offline");
     let live=0;for(let A of traces.keys())live+=Math.max(0,(death.get(A)??end)-n0);
     ck(ret+merge+cross===traces.size,"loss ledger");
     outcomes.push({ret,cost,live,merge,cross,ids,events});
    }
    let [a,b]=outcomes;c.lookRet+=a.ret;c.naiveRet+=b.ret;c.lookCost+=a.cost;c.naiveCost+=b.cost;c.lookLive+=a.live;c.naiveLive+=b.live;c.lookMerge+=a.merge;c.lookCross+=a.cross;c.naiveMerge+=b.merge;c.naiveCross+=b.cross;c.lookEvents+=a.events;c.naiveEvents+=b.events;
    if(a.ret>b.ret){c.different++;if(examples.length<5)examples.push({R,l,M:c.M,H:c.H,look:a.ret,naive:b.ret});}
    c.cache+=futureCache.size;
   }
  }
  rows.push({R,N,T,rootEvents,supportChecks,pairs,smallSupport,distinctCharge,totalCount,totalDistinct,maxSmallLen,examples,controls:controls.map(c=>({...c,lookRet:c.lookRet/N,naiveRet:c.naiveRet/N,offline:c.offline/N,lookLive:c.lookLive/(N*T),naiveLive:c.naiveLive/(N*T),lookCost:c.lookCost/N,naiveCost:c.naiveCost/N,lookMerge:c.lookMerge/N,lookCross:c.lookCross/N,naiveMerge:c.naiveMerge/N,naiveCross:c.naiveCross/N}))});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000]),null,2));
