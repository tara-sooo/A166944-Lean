// Negative MIN: exact compressed dual optimizer, merger-price diagnostics.
// Run: node research/lean/negative_min_merge_dual_audit.mjs
// No third-party packages. Finite proxy scales; no asymptotic inference.
function audit(){
 let assertions=0,cycles=0,windows=0,roots=0,ticks=0,comparisons=0,smallFiringHeavy=null;
 function ck(ok,msg){assertions++;if(!ok)throw Error(msg)}
 function gcd(a,b){a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a}
 function lpf(n){if(n<2)return 0;for(let p=2;p*p<=n;p++)if(n%p===0)return p;return n}
 function win(x,n){return lpf(gcd(n%2===0?x+1:x-1,n%2===0?n:n-2))}
 function literal(x,n){for(let p=3;p<=x+1;p+=2)if(lpf(p)===p&&(n%2===0?((x+1)%p===0&&n%(2*p)===0):((x-1)%p===0&&((n%(2*p)+2*p)%(2*p)===p+2))))return p;return 0}
 function trace(A,start,T,D,W,checkLiteral){
  let x=A,n=3-A/2,seen=new Set(),sat=0,low=0,states=[],cost=[0],labels=[],b=n;
  while(n<start+T){
   states.push(x);let p=win(x,n+1);if(checkLiteral)ck(p===literal(x,n+1),"literal eligibility");
   labels.push(p);ticks++;
   if(p>=17)seen.clear();if(p>3&&p<17){if(!seen.size)low++;seen.add(p);if(seen.size===2){sat++;seen.clear()}}
   cost.push(W*(2*sat+low));if(p)x-=p-1;n++;
  }
  let a=start-b;
  return {A,fullx:states,fullp:labels,age:a,x:states.slice(a),p:labels.slice(a),g:Array.from({length:T+1},(_,k)=>k===0?0:D*k-cost[a+k]),start};
 }
 function group(rs,T){
  let nodes=[],keyed=new Map(),at=rs.map(()=>Array(T));
  for(let u=0;u<T;u++){
   let m=new Map();
   for(let i=0;i<rs.length;i++){let x=rs[i].x[u];if(!m.has(x))m.set(x,[]);m.get(x).push(i)}
   for(let [x,ids] of m){
    let key=ids.join(","),id=keyed.get(key);
    if(id===undefined){id=nodes.length;keyed.set(key,id);nodes.push({ids,u,last:u,x,parent:-1,labels:[],reset:false})}
    let a=nodes[id];
    ck(a.last===u||a.last===u-1,"same fiber is contiguous");a.last=u;
    for(let i of ids)at[i][u]=id;
    if(u>0&&a.u===u){
     let prev=new Set(ids.map(i=>at[i][u-1]));ck(prev.size>=2,"new fiber formed by merge");
     a.labels=[...new Set(ids.map(i=>rs[i].p[u-1]).filter(p=>p))];
     ck(a.labels.length>0,"merge has moving branch");
     const n=rs[0].start+u,h2=2*n+x,c=n%2===0?0:6;
     a.reset=h2===c;
     for(let p of a.labels){
      ck((h2-c)%p===0,"common height pin");ck((x-(c===0?0:2))%p===0,"common center pin");
     }
     if(!a.reset&&a.labels.length>=2){for(let i=0;i<a.labels.length;i++)for(let j=0;j<i;j++)ck(Math.abs(h2-c)>=a.labels[i]*a.labels[j],"nonreset product bound")}
    }
   }
  }
  for(let i=0;i<rs.length;i++)for(let u=1;u<T;u++)if(at[i][u]!==at[i][u-1]){
   let g=nodes[at[i][u-1]],parent=at[i][u];ck(g.parent===-1||g.parent===parent,"unique group parent");g.parent=parent;
  }
  ck(nodes.length<=2*rs.length-1,"laminar group count");
  return {nodes,at};
 }
 function optimize(rs,T,M,groups,compressed){
  let n=rs.length,edges=[],nodes=0,sink=nodes++,rootIds=rs.map(()=>nodes++),stateIds=[];
  function add(u,v,cap,g,tag){let id=edges.length;edges.push({u,v,cap,g,tag,f:0});return id}
  let priceIds=[],rootEdges=[],groupIds,fullAt;
  if(compressed){
   groupIds=groups.nodes.map(()=>nodes++);
   for(let i=0;i<n;i++)rootEdges[i]=add(rootIds[i],groupIds[groups.at[i][0]],1,0,{type:"root",i});
   for(let j=0;j<groups.nodes.length;j++){
    let a=groups.nodes[j],v=a.parent<0?sink:groupIds[a.parent];
    priceIds[j]=add(groupIds[j],v,M,0,{type:"group",j});
   }
   for(let i=0;i<n;i++){
    let best=new Map();
    for(let k=1;k<=T;k++){let j=groups.at[i][k-1],g=rs[i].g[k],old=best.get(j);if(!old||g>old.g)best.set(j,{k,g})}
    for(let [j,{k,g}] of best)if(g>0){let a=groups.nodes[j];add(a.parent<0?sink:groupIds[a.parent],rootIds[i],n+1,g,{type:"option",i,k})}
   }
  }else{
   let keys=new Map();fullAt=rs.map(()=>Array(T));
   for(let i=0;i<n;i++)for(let u=0;u<T;u++){let key=u+":"+rs[i].x[u];if(!keys.has(key))keys.set(key,nodes++);fullAt[i][u]=keys.get(key)}
   let byNode=new Map();
   for(let i=0;i<n;i++){
    rootEdges[i]=add(rootIds[i],fullAt[i][0],1,0,{type:"root",i});
    for(let u=0;u<T;u++){let a=fullAt[i][u],b=u+1===T?sink:fullAt[i][u+1];
     if(!byNode.has(a)){byNode.set(a,add(a,b,M,0,{type:"state",u,j:groups.at[i][u]}))}
     else ck(edges[byNode.get(a)].v===b,"deterministic successor");
     if(rs[i].g[u+1]>0)add(b,rootIds[i],n+1,rs[i].g[u+1],{type:"option",i,k:u+1});
    }
   }
   priceIds=[...byNode.values()];
  }
  // Positive-cycle cancellation. Integer objective increases each time.
  function residual(){
   let r=[];for(let i=0;i<edges.length;i++){let e=edges[i];if(e.f<e.cap)r.push({u:e.u,v:e.v,g:e.g,cap:e.cap-e.f,i,s:1});if(e.f>0)r.push({u:e.v,v:e.u,g:-e.g,cap:e.f,i,s:-1})}return r;
  }
  let potential=null;
  while(true){
   let r=residual(),dist=Array(nodes).fill(0),prev=Array(nodes).fill(null),last=-1;
   for(let k=0;k<nodes;k++){
    last=-1;for(let a of r)if(dist[a.v]<dist[a.u]+a.g){dist[a.v]=dist[a.u]+a.g;prev[a.v]=a;last=a.v}
    if(last===-1)break;
   }
   if(last===-1){potential=dist;break}
   let v=last;for(let k=0;k<nodes;k++){ck(prev[v]!==null,"cycle predecessor");v=prev[v].u}
   let start=v,cy=[];do{let a=prev[v];cy.push(a);v=a.u;ck(cy.length<=nodes,"cycle length")}while(v!==start);
   let delta=Math.min(...cy.map(a=>a.cap)),slope=cy.reduce((s,a)=>s+a.g,0);
   ck(delta>0&&slope>0,"strictly positive residual cycle");
   for(let a of cy)edges[a.i].f+=a.s*delta;cycles++;
  }
  let balance=Array(nodes).fill(0),primal=0,dual=0,ds=Array(n).fill(0),slack=Array(n).fill(0),prices=groups.nodes.map(()=>0);
  for(let e of edges){
   ck(e.f>=0&&e.f<=e.cap,"capacity");balance[e.u]-=e.f;balance[e.v]+=e.f;
   primal+=e.g*e.f;
   let price=Math.max(0,e.g+potential[e.u]-potential[e.v]);
   ck(e.f===e.cap||price===0,"complementary capacity slack");
   if(e.f>0)ck(e.g+potential[e.u]-potential[e.v]>=0,"reverse residual");
   dual+=e.cap*price;
   if(e.tag.type==="option"){
    ck(price===0,"redundant return arc");if(e.f){ck(e.f===1&&ds[e.tag.i]===0,"integral root choice");ds[e.tag.i]=e.tag.k}
   }else if(e.tag.type==="root")slack[e.tag.i]=price;else prices[e.tag.j]+=price;
  }
  ck(balance.every(x=>x===0),"circulation conservation");ck(primal===dual,"exact primal-dual equality");
  ck(ds.reduce((s,k,i)=>s+rs[i].g[k],0)===primal,"profit reconstruction");
  for(let u=0;u<T;u++){let m=new Map();for(let i=0;i<n;i++)if(ds[i]>u){let x=rs[i].x[u];m.set(x,(m.get(x)||0)+1)}for(let x of m.values())ck(x<=M,"selected cap")}
  // All full state prices have now been pushed to their first identical
  // ancestry set. Remove underfull prices by adding them to root slacks.
  for(let j=0;j<prices.length;j++)if(prices[j]&&groups.nodes[j].ids.length<=M){
   for(let i of groups.nodes[j].ids)slack[i]+=prices[j];prices[j]=0;
  }
  let objective=M*prices.reduce((s,x)=>s+x,0)+slack.reduce((s,x)=>s+x,0);
  ck(objective===primal,"compressed heavy-only dual remains optimal");
  for(let i=0;i<n;i++){
   let tax=0;
   for(let k=1;k<=T;k++){let j=groups.at[i][k-1];if(k-1===groups.nodes[j].u)tax+=prices[j];
    ck(tax+slack[i]>=rs[i].g[k],"all prefix inequalities")}
  }
  return {primal,slack,prices};
 }


 function transportPriceToEntries(rs,T,M,groups,sol){
  let Q=6;for(let q of [30,210,2310])if(q<=6*M)Q=q;
  let newSlack=sol.slack.slice(),prices=new Map(),foreign=0,native=0,maxInflation=0;
  function add(u,x,p){let key=u+":"+x;prices.set(key,(prices.get(key)||0)+p)}
  for(let j=0;j<groups.nodes.length;j++){
   let p=sol.prices[j];if(!p)continue;let a=groups.nodes[j],u=a.u;
   if(!u){add(0,a.x,p);continue}
   let cell=Math.floor(a.x/Q),entries=new Map(),natives=[];
   for(let i of a.ids){
    let r=rs[i];
    if(Math.floor(r.A/Q)===cell){natives.push(i);native++;continue}
    foreign++;
    let k=0;while(Math.floor(r.fullx[k]/Q)!==cell){k++;ck(k<=r.age+u,"entry exists")}
    ck(k>0&&r.fullp[k-1]>0&&Q%r.fullp[k-1]!==0,"non-divisor boundary entry");
    let e=Math.max(0,k-r.age),x=r.x[e],key=e+":"+x;ck(e<=u,"entry before price");
    if(!entries.has(key))entries.set(key,{u:e,x,ids:[]});entries.get(key).ids.push(i);
   }
   ck(natives.length<=Q/6,"native root cap");ck(entries.size>0,"heavy merge contains foreign root");
   for(let i of natives)newSlack[i]+=p;
   let units=natives.length;
   for(let e of entries.values()){
    units+=Math.min(M,e.ids.length);
    if(e.ids.length<M)for(let i of e.ids)newSlack[i]+=p;
    else add(e.u,e.x,p);
   }
   maxInflation=Math.max(maxInflation,units/M);
  }
  let objective=M*[...prices.values()].reduce((s,x)=>s+x,0)+newSlack.reduce((s,x)=>s+x,0);
  ck(objective>=sol.primal,"entry-restricted dual cannot improve optimum");
  for(let i=0;i<rs.length;i++){
   let tax=0;for(let k=1;k<=T;k++){
    tax+=prices.get((k-1)+":"+rs[i].x[k-1])||0;
    ck(tax+newSlack[i]>=rs[i].g[k],"transported dual still feasible");
   }
  }
  return {objective,foreign,native,maxInflation};
 }

 function endpointRank(rs,T,M,groups){
  let n=rs.length,H=1n;
  const gcdB=(a,b)=>{while(b){[a,b]=[b,a%b]}return a};
  for(let j=1;j<=n;j++){let q=BigInt(j);H=H/gcdB(H,q)*q}
  // Individually maximize exact rational gain times min(1,M/m).
  const opts=rs.map((r,i)=>{
   let best={k:0,g:0,ids:[],weighted:0n};
   for(let k=1;k<=T;k++){
    if(r.g[k]<=0)continue;
    let ids=groups.nodes[groups.at[i][k-1]].ids,m=ids.length;
    let w=BigInt(r.g[k])*BigInt(Math.min(M,m))*(H/BigInt(m));
    if(w>best.weighted)best={k,g:r.g[k],ids,weighted:w};
   }return best;
  });
  let expected=opts.reduce((s,x)=>s+x.weighted,0n);
  // Conditional expectation of the exact uniform random ordering.
  // A root already in the order has deterministic rank; a remaining
  // root has uniform remaining rank among its group.
  let rank=Array(n).fill(-1),selected=[],changes=0;
  function value(){
   let v=0n;
   for(let i=0;i<n;i++){
    let o=opts[i];if(!o.k)continue;
    if(rank[i]>=0){
     let before=o.ids.filter(j=>rank[j]>=0&&rank[j]<rank[i]).length;
     if(before<M)v+=BigInt(o.g)*H;
    }else{
     let seen=o.ids.filter(j=>rank[j]>=0).length,remaining=o.ids.length-seen;
     if(seen<M)v+=BigInt(o.g)*BigInt(Math.min(M-seen,remaining))*(H/BigInt(remaining));
    }
   }return v;
  }
  ck(value()===expected,"initial exact expected value");
  for(let k=0;k<n;k++){
   let before=value(),best=-1,bestVal=-1n,sum=0n;
   for(let i=0;i<n;i++)if(rank[i]<0){rank[i]=k;let v=value();rank[i]=-1;sum+=v;if(v>bestVal){bestVal=v;best=i}}
   ck(sum===BigInt(n-k)*before,"conditional expectation identity");ck(bestVal>=before,"derandomization");rank[best]=k;changes++;
  }
  let net=0;
  for(let i=0;i<n;i++){
   let o=opts[i],good=o.k>0&&o.ids.filter(j=>rank[j]<rank[i]).length<M;
   selected[i]=good?o.k:0;if(good)net+=o.g;
  }
  ck(BigInt(net)*H===value(),"integer priority net");ck(BigInt(net)*H>=expected,"exact endpoint lower");
  for(let u=0;u<T;u++){
   let m=new Map();for(let i=0;i<n;i++)if(selected[i]>u){let x=rs[i].x[u];m.set(x,(m.get(x)||0)+1)}
   for(let x of m.values())ck(x<=M,"priority cap");
  }
  return {expected:Number(expected)/Number(H),net,changes};
 }

 function cutoff(rs,T,M,groups,K){
  // Maximize each root's own net profit before its full cohort exceeds K.
  let stops=rs.map((r,i)=>{let best=0,kbest=0;for(let k=1;k<=T;k++){if(groups.nodes[groups.at[i][k-1]].ids.length>K)break;if(r.g[k]>best){best=r.g[k];kbest=k}}return kbest});
  // Descending deadlines: all earlier conflicting selected paths share
  // this path's last live state, hence form a clique. Greedy K-coloring.
  let colors=rs.map(()=>-1),values=Array(K).fill(0);
  for(let i of stops.map((_,i)=>i).sort((i,j)=>stops[j]-stops[i]||i-j)){
   if(!stops[i])continue;let u=stops[i]-1,forbidden=new Set();
   for(let j=0;j<rs.length;j++)if(colors[j]>=0&&rs[j].x[u]===rs[i].x[u])forbidden.add(colors[j]);
   let c=0;while(forbidden.has(c))c++;
   ck(c<K,"deadline clique coloring");colors[i]=c;values[c]+=rs[i].g[stops[i]];
  }
  let best=values.slice().sort((a,b)=>b-a).slice(0,M).reduce((s,x)=>s+x,0);
  let total=values.reduce((s,x)=>s+x,0);ck(K*best>=M*total,"top colors lower bound");
  for(let u=0;u<T;u++){let m=new Map();for(let i=0;i<rs.length;i++)if(stops[i]>u){let k=rs[i].x[u]+":"+colors[i];ck(!m.has(k),"same color conflict");m.set(k,1)}}
  return {total,best};
 }
 let results=[];
 for(let config of [{R:600,T:18,M:1,count:34},{R:2400,T:36,M:2,count:60},{R:12000,T:72,M:4,count:100},{R:48000,T:144,M:8,count:100},{R:192000,T:288,M:16,count:100}]){
  let {R,T,M,count}=config,W=T,D=1,priceScale=Math.max(1,Math.floor(T/18));
  let row={...config,rootCount:0,rawProfit:0,opt:0,cutM:0,cut2M:0,cut4M:0,price0:0,priceSmall:0,priceOther:0,priceReset:0,slack:0,groups:0,heavyGroups:0,positivePriceGroups:0,endpointBound:0,endpointNet:0,prioritySteps:0,entryDual:0,entryNative:0,entryForeign:0,maxEntryInflation:0};
  let totalWindows=Math.ceil((Math.floor(R/6)+1)/(W/6)),chosen=new Set();
  for(let j=0;j<Math.min(count,totalWindows);j++)chosen.add(Math.floor(j*totalWindows/Math.min(count,totalWindows)));
  for(let j of chosen){
   let base=R+j*W,start=3-base/2,rs=[];for(let A=base;A<base+W&&A<=2*R;A+=6)rs.push(trace(A,start,T,D,priceScale,R===600));
   if(!rs.length)continue;windows++;roots+=rs.length;row.rootCount+=rs.length;
   let gr=group(rs,T),sol=optimize(rs,T,M,gr,true);
   if(R<=2400||j===0){let raw=optimize(rs,T,M,gr,false);ck(raw.primal===sol.primal,"uncontracted optimizer matches");comparisons++}
   let ed=transportPriceToEntries(rs,T,M,gr,sol);row.entryDual+=ed.objective;row.entryNative+=ed.native;row.entryForeign+=ed.foreign;row.maxEntryInflation=Math.max(row.maxEntryInflation,ed.maxInflation);
   let ep=endpointRank(rs,T,M,gr);ck(ep.net<=sol.primal,"endpoint net vs exact optimum");row.endpointBound+=ep.expected;row.endpointNet+=ep.net;row.prioritySteps+=ep.changes;
   row.rawProfit+=rs.reduce((s,r)=>s+Math.max(...r.g),0);row.opt+=sol.primal;row.slack+=sol.slack.reduce((s,x)=>s+x,0);
   for(let K of [M,2*M,4*M]){let q=cutoff(rs,T,M,gr,K);ck(q.best<=sol.primal,"cutoff lower vs exact optimum");row[K===M?"cutM":K===2*M?"cut2M":"cut4M"]+=q.best}
   row.groups+=gr.nodes.length;
   for(let i=0;i<gr.nodes.length;i++){let a=gr.nodes[i],p=sol.prices[i];if(a.ids.length>M)row.heavyGroups++;
    if(a.u>0&&a.ids.length>M&&a.labels.every(p=>p<=5)&&!smallFiringHeavy)smallFiringHeavy={R,T,M,base,u:a.u,x:a.x,roots:a.ids.map(i=>rs[i].A),labels:a.labels,price:p};
    if(p>0){row.positivePriceGroups++;if(a.u===0)row.price0+=M*p;else if(a.labels.every(p=>p<=5))row.priceSmall+=M*p;else row.priceOther+=M*p;if(a.reset)row.priceReset+=M*p}
   }
  }
  ck(row.opt===row.slack+row.price0+row.priceSmall+row.priceOther,"dual aggregate");
  row.entryDualRatio=row.entryDual/row.opt;row.normalizedEndpointBound=row.endpointBound/(row.rootCount*T);row.normalizedEndpointNet=row.endpointNet/(row.rootCount*T);row.normalizedOpt=row.opt/(row.rootCount*T);row.normalizedCutM=row.cutM/(row.rootCount*T);row.normalizedCut2M=row.cut2M/(row.rootCount*T);row.normalizedCut4M=row.cut4M/(row.rootCount*T);
  results.push(row);
 }
 return {assertions,cycles,windows,roots,ticks,comparisons,smallFiringHeavy,results};
}
console.log(JSON.stringify(audit()));
