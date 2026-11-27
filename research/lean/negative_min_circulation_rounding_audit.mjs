// Exact fractional path packing and constructive circulation rounding audit.
// Run: node research/lean/negative_min_circulation_rounding_audit.mjs
function run() {
 let checks=0,roots=0,tickChecks=0,assignments=0,windows=0,packingChecks=0,roundingSteps=0,roundedWindows=0;
 const ck=(x,msg)=>{checks++;if(!x)throw Error(msg)};
 function gcd(a,b){a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a}
 function least(n){if(n<2)return 0;for(let p=2;p*p<=n;p++)if(n%p===0)return p;return n}
 function mod(a,b){return ((a%b)+b)%b}
 function label(x,n){return least(gcd(n%2===0?x+1:x-1,n%2===0?n:n-2))}
 function literal(x,n){for(let p=3;p<=x+1;p+=2)if(least(p)===p&&(n%2===0?((x+1)%p===0&&mod(n,2*p)===0):((x-1)%p===0&&mod(n,2*p)===p+2)))return p;return 0}
 function trace(A,start,T){
  let birth=3-A/2,end=start+T,states=[],cost=[0],x=A,n=birth,seen=new Set(),sat=0,low=0;
  while(n<end){states.push(x);let p=label(x,n+1);ck(p===literal(x,n+1),"literal tick");tickChecks++;
   if(p>=17)seen.clear();if(p>3&&p<17){if(!seen.size)low++;seen.add(p);if(seen.size===2){sat++;seen.clear()}}
   cost.push(2*sat+low);if(p)x-=p-1;n++}
  return {A,birth,states,cost};
 }
 function deadline(r,b){let i=0;while(i<r.states.length&&r.cost[i+1]<=b)i++;return i}
 function masses(rs,ds,start,T){
  let f=new Map();for(let t=start;t<start+T;t++)for(let i=0;i<rs.length;i++){let k=t-rs[i].birth;if(k>=0&&k<ds[i]){let key=t+":"+rs[i].states[k];f.set(key,(f.get(key)||0)+1)}}return f;
 }
 function bins(rs,ds,start,T,M){let V=0;for(let m of masses(rs,ds,start,T).values())V+=Math.min(M,m);return V}
 function clip(rs,ds,start,T,M){
  let live=new Set(),dead=Array(rs.length).fill(0),V=0,first=Math.min(...rs.map(r=>r.birth));
  for(let t=first;t<start+T;t++){
   for(let i=0;i<rs.length;i++)if(rs[i].birth===t&&ds[i]>0)live.add(i);
   let f=new Map();for(let i of live){let r=rs[i],k=t-r.birth;if(k>=ds[i]){live.delete(i);continue}
    let a=r.states[k];if(!f.has(a))f.set(a,[]);f.get(a).push(i)}
   for(let arr of f.values()){arr.sort((i,j)=>(rs[j].birth+ds[j])-(rs[i].birth+ds[i])||i-j);for(let i of arr.slice(M))live.delete(i)}
   for(let i of live)dead[i]=t-rs[i].birth+1;if(t>=start)V+=live.size;
  }return {V,dead};
 }
 function each(n,k,cb,a=[]){if(a.length===n){cb(a.slice());return}for(let j=0;j<k;j++){a.push(j);each(n,k,cb,a);a.pop()}}
 function brute(rs,start,T,M,D){
  let best=0,ds=[],first=Math.min(...rs.map(r=>r.birth));
  function rec(i){
   if(i===rs.length){if(bins(rs,ds,first,start+T-first,M)!==bins(rs,ds,first,start+T-first,1e9))return;
    let C=rs.reduce((a,r,i)=>a+r.cost[ds[i]],0);best=Math.max(best,D*bins(rs,ds,start,T,M)-C);return}
   for(let k=0;k<=rs[i].states.length;k++){ds.push(k);rec(i+1);ds.pop()}
  }rec(0);return best;
 }

 // Tree edges point towards retirement, return arcs encode prefix options.
 // Flows are integer numerators with denominator H. Fractional-cycle
 // rounding only moves to adjacent multiples of H and never lowers value.
 function roundFlow(rs,cd,z,start,T,M,H,D){
  const edges=[],byKey=new Map(),nodes=new Map();let changes=0;
  function node(k){if(!nodes.has(k))nodes.set(k,nodes.size);return nodes.get(k)}
  function edge(key,u,v,cap,profit,A=-1,d=0){
   if(!byKey.has(key)){byKey.set(key,edges.length);edges.push({u,v,cap,profit,A,d,f:0})}
   let e=edges[byKey.get(key)];ck(e.u===u&&e.v===v&&e.cap===cap&&e.profit===profit,"consistent arc");return e;
  }
  const end=start+T,sink=node("retirement");
  function phys(r,k){return r.birth+k===end?sink:node((r.birth+k)+":"+r.states[k])}
  for(let j=0;j<cd.length;j++){
   let i=Math.floor(j/H),r=rs[i],d=z.dead[j];if(!d)continue;
   let leaf=node("root:"+i);edge("birth:"+i,leaf,phys(r,0),H,0).f++;
   for(let k=0;k<d;k++)edge("state:"+phys(r,k),phys(r,k),phys(r,k+1),M*H,0).f++;
   let life=Math.max(0,r.birth+d-start),value=D*life-r.cost[d];
   edge("return:"+i+":"+d,phys(r,d),leaf,H,value,i,d).f++;
  }
  function verify(){
   let balance=Array(nodes.size).fill(0),value=0;
   for(let e of edges){ck(0<=e.f&&e.f<=e.cap,"capacity");balance[e.u]-=e.f;balance[e.v]+=e.f;value+=e.f*e.profit}
   ck(balance.every(x=>x===0),"circulation");return value;
  }
  const original=verify();
  while(edges.some(e=>e.f%H!==0)){
   let adj=Array.from({length:nodes.size},()=>[]);
   for(let i=0;i<edges.length;i++){let e=edges[i];if(e.f%H){adj[e.u].push(i);adj[e.v].push(i)}}
   ck(adj.every(a=>a.length===0||a.length>=2),"fractional degree");
   let u=adj.findIndex(a=>a.length>0),prev=-1,seen=new Map(),walk=[];
   while(!seen.has(u)){
    seen.set(u,walk.length);let idx=adj[u].find(i=>i!==prev),e=edges[idx],v=e.u===u?e.v:e.u;
    walk.push({idx,sign:e.u===u?1:-1});prev=idx;u=v;
   }
   let cycle=walk.slice(seen.get(u));
   let slope=cycle.reduce((s,x)=>s+x.sign*edges[x.idx].profit,0);
   if(slope<0)for(let x of cycle)x.sign=-x.sign;
   let delta=Math.min(...cycle.map(x=>x.sign===1?H-edges[x.idx].f%H:edges[x.idx].f%H));
   ck(delta>0&&delta<H,"positive rounding step");
   let before=verify(),fractional=edges.filter(e=>e.f%H).length;
   for(let x of cycle)edges[x.idx].f+=x.sign*delta;
   ck(verify()>=before,"objective nondecrease");
   ck(edges.filter(e=>e.f%H).length<fractional,"strict progress");
   changes++;
  }
  let ds=Array(rs.length).fill(0);
  for(let e of edges)if(e.A>=0&&e.f){ck(e.f===H&&ds[e.A]===0,"at most one prefix per root");ds[e.A]=e.d}
  let first=Math.min(...rs.map(r=>r.birth));
  ck(bins(rs,ds,first,start+T-first,M)===bins(rs,ds,first,start+T-first,1e9),"rounded physical cap");
  let C=rs.reduce((a,r,i)=>a+r.cost[ds[i]],0),V=bins(rs,ds,start,T,M);
  ck(H*(D*V-C)===verify(),"rounded objective reconstruction");
  ck(H*(D*V-C)>=original,"rounded dominance");
  return {V,C,changes};
 }

 let results=[];
 for(let R of [600,1200,2400]){
  let T=18,W=18,lo=Math.ceil(R/6)*6,bs=[0,1,4],H=bs.length,M=1;
  let sv=0,sb=0,sm=0,obs=0,local=0;
  for(let base=lo;base<=2*R;base+=W){
   let start=3-base/2,rs=[];for(let a=base;a<base+W&&a<=2*R;a+=6)rs.push(trace(a,start,T));
   windows++;roots+=rs.length;obs+=rs.length*T;
   let perBin=new Map(),mus=new Map(),squares=new Map(),D=3,bd=rs.map(r=>bs.map(b=>deadline(r,b))),av=0;
   each(rs.length,H,idx=>{
    assignments++;let ds=idx.map((j,i)=>bd[i][j]),z=clip(rs,ds,start,T,M);
    ck(z.V===bins(rs,ds,start,T,M),"exact clipped life");
    for(let i=0;i<rs.length;i++){ck(z.dead[i]<=ds[i],"deadline");ck(rs[i].cost[z.dead[i]]<=bs[idx[i]],"cost")}
    av+=z.V;
    for(let [key,m] of masses(rs,ds,start,T)){let v=perBin.get(key)||[0,0,0];v[0]+=m;v[1]+=m*m;v[2]+=Math.min(M,m);perBin.set(key,v)}
   });
   let K=H**rs.length;
   for(let t=start;t<start+T;t++)for(let i=0;i<rs.length;i++){
    let k=t-rs[i].birth,key=t+":"+rs[i].states[k],w=bd[i].filter(d=>k<d).length;
    mus.set(key,(mus.get(key)||0)+w);squares.set(key,(squares.get(key)||0)+w*w);
   }
   let exact=0,loc=0,frac=0;
   for(let [key,w] of mus){let [s,q,v]=perBin.get(key)||[0,0,0];
    ck(s*H===K*w,"first moment");
    ck(q*H*H===K*(w*H+w*w-squares.get(key)),"second moment");
    ck(M*s*s<=v*((M-1)*s+q),"local moment");
    ck(2*v*H>=K*Math.min(M*H,w),"half soft cap");
    ck(v*(M*H+w)>=K*M*w,"rational soft cap");
    exact+=v;loc+=((M-1)*s+q>0?Math.floor(M*s*s/((M-1)*s+q)):0);frac+=Math.min(M*H,w)
   }
   ck(exact===av,"Fubini mass");ck(loc<=av,"local certificate");
   let cr=[],cd=[];for(let i=0;i<rs.length;i++)for(let j=0;j<H;j++){cr.push(rs[i]);cd.push(bd[i][j])}
   let z=clip(cr,cd,start,T,M*H),C=cr.reduce((a,r,i)=>a+r.cost[z.dead[i]],0);
   ck(z.V===frac,"fractional clip");ck(C<=rs.length*bs.reduce((a,b)=>a+b,0),"fractional budget");
   let rounded=roundFlow(rs,cd,z,start,T,M,H,D);ck(H*(D*rounded.V-rounded.C)>=D*z.V-C,"rounded dominates exact fractional clip");roundingSteps+=rounded.changes;roundedWindows++;
   if(base<lo+3*W){let b=brute(rs,start,T,M,D);ck(H*b>=D*z.V-C,"integral optimum");packingChecks++}
   sv+=av/K;sb+=rs.length*bs.reduce((a,b)=>a+b,0)/H;sm+=frac/H;local+=loc/K;
  }
  results.push({R,observed:obs,ensembleLife:sv/obs,fractionalLife:sm/obs,localMomentLower:local/obs,meanBudget:sb/(Math.floor((2*R-lo)/6)+1)});
 }
 return {checks,roots,tickChecks,assignments,windows,packingChecks,roundingSteps,roundedWindows,results};
}
console.log(JSON.stringify(run()));
