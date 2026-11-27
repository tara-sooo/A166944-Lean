// Spatial packing of fixed-alphabet prefixes with arbitrary clock phases and high-jump separation.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,pr=[3,5,7,11,13,17],out={states:0,prefixChecks:0,packingChecks:0,phaseChecks:0,rows:[]};
 for(let K of [3,5,7,11]){
  const P=pr.filter(p=>p<=K),Q=P.reduce((a,b)=>a*b,1),L=2*Q,nextP=pr.find(p=>p>K),s=(nextP-1)/2;
  // For each half-distance x and each small target cutoff z, store
  // maximum descent reward for every possible prefix displacement.
  let opts=Array.from({length:Q},()=>[new Map([[0,0]]),new Map([[0,0]])]),mx=[0,0],maxG=0;
  // Each full run starts at x in [0,Q-1]; walls prevent x<0.
  // Event list replay is small for these finite alphabets.
  const eligible=Array.from({length:Q},(_,x)=>P.flatMap(p=>[-1,1].filter(e=>mod(2*x-e,p)===0).map(e=>[p,e===-1?0:p+2])));
  for(let x=0;x<Q;x++)for(let n0=0;n0<L;n0++){
   let a=x,n=n0,reward=[0,0];
   while(true){let p0=0,w=Infinity;for(let [p,c] of eligible[a]){let t=mod(c-n,2*p)||2*p;if(t<w||t===w&&p<p0){p0=p;w=t}}
    if(!p0)break;a-=(p0-1)/2;n+=w;ck(a>=0,"wall");
    for(let i=0;i<2;i++){let z=i?7:5;if(p0<=z)reward[i]+=(p0-3)/2;let d=x-a,m=opts[x][i];m.set(d,Math.max(m.get(d)||0,reward[i]));mx[i]=Math.max(mx[i],reward[i])}
    maxG=Math.max(maxG,2*(x-a));out.prefixChecks++;
   }out.states++;
  }
  for(let i=0;i<2;i++){
   let z=i?7:5,spatial=opts.map(v=>Math.max(...v[i].values())),mean=spatial.reduce((a,b)=>a+b,0)/Q;
   // Maximal total reward per complete Q-period cell if starts
   // spaced by at least s; independent of outside cells.
   let dp=new Float64Array(Q+1),dpExact=new Float64Array(Q+1),bestPrefix=0;
   // x ascending: choose start at x, its prefix descends d and
   // the next start below is <=x-d-s. Boundary relaxations allowed.
   for(let x=0;x<Q;x++){
    dp[x+1]=Math.max(dp[x],spatial[x]+dp[Math.max(0,x-s+1)]);
    dpExact[x+1]=dpExact[x];
    for(let [d,c] of opts[x][i]){ck(d<=x,"prefix in wall cell");dpExact[x+1]=Math.max(dpExact[x+1],c+dpExact[Math.max(0,x-d-s+1)]);out.packingChecks++}
   }
   ck(dpExact[Q]<=dp[Q]+1e-9,"packing comparison");
   let positiveTail=[];for(let e of [.25,.5,1])positiveTail.push({threshold:e*K,meanTail:spatial.reduce((a,b)=>a+Math.max(0,b-e*K),0)/Q});
   let blockMax=0;for(let x=0;x<Q;x++){let v=0;for(let j=0;j<s;j++)v=Math.max(v,spatial[mod(x+j,Q)]);blockMax+=v}blockMax/=Q;
   // Verify the DP with exhaustive independent set enumeration for Q<=15.
   if(Q<=15){let best=0;function rec(x,c){if(x<0){best=Math.max(best,c);return}rec(x-1,c);for(let [d,v] of opts[x][i])rec(x-d-s,c+v)}rec(Q-1,0);ck(best===dpExact[Q],"direct packing");out.phaseChecks++}
   out.rows.push({K,z,Q,s,maxG,max:mx[i],meanSpatialMax:mean,blockMax,naiveRate:mx[i]/s,blockRate:blockMax/s,cellRate:dp[Q]/Q,exactPrefixCellRate:dpExact[Q]/Q,cellReward:dpExact[Q],positiveTail})
  }
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
