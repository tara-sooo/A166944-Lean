// First-profitable-passage packing and bounded-defect suffix potential audit.
// Run: node research/lean/negative_min_passage_potential_audit.mjs
function run(){
 let checks=0,words=0,splits=0,roots=0,windows=0,ticks=0,thresholds=0,bruteChecks=0,potentialChecks=0,greedyExchangeChecks=0;
 const ck=(ok,msg)=>{checks++;if(!ok)throw Error(msg)};
 function counts(xs,z,Y,reset,d){
  let seen=new Set(),sat=0,low=0;
  for(let p of xs){if(p>=reset){seen.clear();continue}
   if(z<p&&p<Y){if(!seen.size)low++;seen.add(p);if(seen.size>d){seen.clear();sat++}}}
  return [sat,low];
 }
 function joint(xs,z,Y,Yb,reset,d,k){
  let seen=new Set(),broad=0,j=0,paid=false;
  for(let p of xs){
   if(p>=reset){seen.clear();broad=0;paid=false;continue}
   if(z<p&&p<Yb)broad++;if(z<p&&p<Y)seen.add(p);
   if(!paid&&broad>k&&seen.size>d){paid=true;j++}
  }return j;
 }
 function checkWord(xs){
  words++;
  for(let d=0;d<=2;d++){
   let [s,n]=counts(xs,3,13,17,d),j=joint(xs,3,13,17,19,d,2);
   for(let i=0;i<=xs.length;i++){
    let a=xs.slice(0,i),b=xs.slice(i),[sa,na]=counts(a,3,13,17,d),[sb,nb]=counts(b,3,13,17,d),ja=joint(a,3,13,17,19,d,2),jb=joint(b,3,13,17,19,d,2);
    ck(sa+sb<=s&&s<=sa+sb+1,"sat append");
    ck(na+nb-1<=n&&n<=na+nb,"nonempty append");
    ck(Math.abs(j-ja-jb)<=1,"joint append");
    ck(s>=sb&&n>=nb&&j>=jb,"suffix monotonicity");
    if(i===1){ck(s-sb<=1&&n-nb<=1&&j-jb<=1,"unit decrement");
     if(!(xs[0]>3&&xs[0]<17))ck(s===sb&&n===nb&&j===jb,"decrement needs relevant label")}
    splits++;
   }
   ck(counts(xs.slice().reverse(),3,13,17,d)[0]===s,"reverse saturated count");
   ck(joint(xs.slice().reverse(),3,13,17,19,d,2)===j,"reverse joint count");
  }
 }
 function all(xs,depth){checkWord(xs);if(depth)for(let p of [0,5,7,11,19])all(xs.concat(p),depth-1)}
 all([],6);
 function gcd(a,b){a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a}
 function lpf(n){if(n<2)return 0;for(let p=2;p*p<=n;p++)if(n%p===0)return p;return n}
 function win(x,n){return lpf(gcd(n%2===0?x+1:x-1,n%2===0?n:n-2))}
 function literal(x,n){for(let p=3;p<=x+1;p+=2)if(lpf(p)===p&&(n%2===0?((x+1)%p===0&&n%(2*p)===0):((x-1)%p===0&&((n%(2*p)+2*p)%(2*p)===p+2))))return p;return 0}
 function trace(A,start,T,end,scale,lit){
  let x=A,n=3-A/2,states=[],ps=[],birth=n;
  while(n<end){states.push(x);let p=win(x,n+1);if(lit)ck(p===literal(x,n+1),"literal tick");ps.push(p);if(p)x-=p-1;n++;ticks++}
  let age=start-birth;
  const C=xs=>scale*(2*joint(xs,3,13,17,19,1,2)+counts(xs,3,13,13,1)[1]);
  let lim=age+T,full=C(ps),g=[0],gp=[0],F0=full;
  for(let k=0;k<=lim;k++){
   let c=C(ps.slice(0,k)),F=C(ps.slice(k)),cp=full-F;
   ck(cp>=0&&Math.abs(cp-c)<=3*scale,"actual common-suffix approximation");
   if(k){let prev=C(ps.slice(k-1));ck(prev>=F&&prev-F<=3*scale,"actual nonnegative additive increment")}
   if(k>age){g.push(k-age-c);gp.push(k-age-cp)}
   potentialChecks++;
  }
  return {A,age,x:states.slice(age,age+T),g,gp};
 }
 function feasible(rs,ends,selected,M,T){
  let loads=Array.from({length:T},()=>new Map());
  for(let i of selected)for(let u=0;u<ends[i];u++){let x=rs[i].x[u],v=(loads[u].get(x)||0)+1;if(v>M)return false;loads[u].set(x,v)}
  return true;
 }
 function greedy(rs,ends,M,T){
  let cand=ends.map((k,i)=>i).filter(i=>ends[i]>0).sort((i,j)=>ends[i]-ends[j]||i-j),accepted=[];
  let loads=Array.from({length:T},()=>new Map()),rejected=[];
  for(let i of cand){let b=-1;
   for(let u=0;u<ends[i];u++)if((loads[u].get(rs[i].x[u])||0)>=M){b=u;break}
   if(b>=0){rejected.push([i,b]);continue}
   accepted.push(i);
   for(let u=0;u<ends[i];u++){let x=rs[i].x[u];loads[u].set(x,(loads[u].get(x)||0)+1)}
  }
  ck(feasible(rs,ends,accepted,M,T),"greedy feasible");
  return {accepted,rejected,cand};
 }
 function brute(rs,ends,M,T,cand){
  let best=[];for(let mask=0;mask<(1<<cand.length);mask++){
   let sel=cand.filter((_,j)=>(mask>>j)&1);
   if(sel.length>best.length&&feasible(rs,ends,sel,M,T))best=sel;
  }return best;
 }
 function testExchange(rs,ends,M,T,cand,opt,greed){
  let selected=new Set(opt),forced=new Set();
  for(let i of cand){
   if(!greed.includes(i)){ck(!selected.has(i),"reject incompatible with forced");continue}
   if(!selected.has(i)){
    // Earliest saturated bin in an optimum extending prior choices.
    let u0=-1;
    for(let u=0;u<ends[i];u++){let count=[...selected].filter(j=>ends[j]>u&&rs[j].x[u]===rs[i].x[u]).length;if(count>=M){u0=u;break}}
    ck(u0>=0,"maximal optimum must block new root");
    let swap=[...selected].find(j=>!forced.has(j)&&ends[j]>u0&&rs[j].x[u0]===rs[i].x[u0]);
    ck(swap!==undefined&&ends[swap]>=ends[i],"later exchange witness");
    selected.delete(swap);selected.add(i);
    ck(feasible(rs,ends,[...selected],M,T),"exchange maintains every cap");greedyExchangeChecks++;
   }
   forced.add(i);
  }
  ck(selected.size===greed.length&&greed.every(i=>selected.has(i)),"exact greedy via exchange");
 }
 function oneThreshold(rs,T,M,q){
  let ends=rs.map(r=>{let k=r.g.findIndex((g,k)=>k>0&&g>=q);return k<0?0:k});
  let {accepted,rejected,cand}=greedy(rs,ends,M,T);
  let degree=[],later=[],rankBound=0,fullBound=0,pairCount=0;
  for(let i of cand){
   let k=ends[i];ck(rs[i].g[k]>=q&&rs[i].g[k]<q+1,"first passage exact reward");
   for(let t=0;t<k;t++)ck(rs[i].g[t]<q,"earliest");
   let nb=cand.filter(j=>rs[i].x[Math.min(k,ends[j])-1]===rs[j].x[Math.min(k,ends[j])-1]);
   for(let j of cand){
    let any=false;for(let u=0;u<Math.min(k,ends[j]);u++)if(rs[i].x[u]===rs[j].x[u]){any=true;break}
    ck(any===nb.includes(j),"endpoint overlap equivalence");
   }
   degree[i]=nb.length;pairCount+=nb.length-1;
   let m=rs.filter(r=>r.x[k-1]===rs[i].x[k-1]).length;
   fullBound+=Math.min(1,M/m);
   rankBound+=Math.min(1,M/nb.length);
  }
  ck(rankBound<=accepted.length+1e-8,"closed-neighborhood rank lower");
  ck(fullBound<=accepted.length+1e-8,"full cohort rank lower");
  let n=cand.length;
  if(n)ck(M*n*n/(M*n+pairCount)<=accepted.length+1e-8,"pair moment lower");
  if(cand.length<=12){let opt=brute(rs,ends,M,T,cand);ck(opt.length===accepted.length,"exact greedy vs exhaustive");bruteChecks++;testExchange(rs,ends,M,T,cand,opt,accepted)}
  // Check cap + arithmetic entry certificate on every rejected root.
  let entryWitnesses=0,Q=6;for(let [i,u] of rejected){let x=rs[i].x[u],a=rs[i].A;
   let all=cand.filter(j=>ends[j]>u&&rs[j].x[u]===x);
   let native=all.filter(j=>Math.floor(rs[j].A/Q)===Math.floor(x/Q)).length;
   ck(native<=Q/6,"native count in live success cohort");
   if(all.length>M&&M>=Q/6)entryWitnesses++;
  }
  thresholds++;return {n,accepted:accepted.length,fullBound,rankBound,pairCount,entryWitnesses};
 }
 let results=[];
 for(let cfg of [{R:600,T:18,M:1,W:18,sample:34},{R:2400,T:36,M:2,W:36,sample:50},{R:12000,T:72,M:4,W:72,sample:40},{R:48000,T:144,M:8,W:144,sample:20}]){
  let {R,T,M,W,sample}=cfg,sc=Math.max(1,T/18),nW=Math.ceil((R/6+1)/(W/6)),row={...cfg,N:0,thresholds:[],layerSum:0,maxProduct:0};
  let qs=[...new Set([1,Math.floor(T/8),Math.floor(T/4),Math.floor(T/2),Math.floor(3*T/4),T])];
  let total=Array.from({length:T+1},()=>0),th=new Map(qs.map(q=>[q,{q,n:0,accepted:0,fullBound:0,rankBound:0,pairCount:0,entryWitnesses:0}]));
  for(let j=0;j<Math.min(sample,nW);j++){
   let base=R+Math.floor(j*nW/Math.min(sample,nW))*W,start=3-base/2,rs=[];
   // Use a common end across the window, and across all windows for R=600.
   let end=R===600?3-R/2+T:start+T;
   for(let A=base;A<base+W&&A<=2*R;A+=6)rs.push(trace(A,start,T,end,sc,R===600));
   if(!rs.length)continue;roots+=rs.length;row.N+=rs.length;windows++;
   for(let q=1;q<=T;q++){
    let e=rs.map(r=>{let k=r.g.findIndex((g,k)=>k>0&&g>=q);return k<0?0:k});
    let a=greedy(rs,e,M,T).accepted.length;total[q]+=a;
    if(qs.includes(q)){let z=oneThreshold(rs,T,M,q),o=th.get(q);ck(z.accepted===a,"threshold replay");for(let key of Object.keys(z))o[key]+=z[key]}
   }
  }
  for(let q=1;q<=T;q++){row.layerSum+=total[q];row.maxProduct=Math.max(row.maxProduct,q*total[q]);if(q>1)ck(total[q]<=total[q-1],"threshold optimum monotone")}
  row.layerSum/=row.N*T;row.maxProduct/=row.N*T;row.thresholds=[...th.values()];results.push(row);
 }
 return {checks,words,splits,roots,windows,ticks,thresholds,bruteChecks,potentialChecks,greedyExchangeChecks,results}
}
console.log(JSON.stringify(run()));
