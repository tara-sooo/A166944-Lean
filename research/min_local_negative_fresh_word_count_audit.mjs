// Fresh-prime CRT word laws, finite interval union counts, and actual prefix controls.
function audit(){
 const ck=(b,m)=>{if(!b)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,up=(x,r,p)=>x+mod(r-x,p);
 const primes=[5,7,11,13,17,19,23,29,31,37],sign=(j,mask)=>(mask>>j)&1?1:-1;
 const choose=(n,k)=>{let x=1;for(let i=1;i<=k;i++)x=x*(n-k+i)/i;return Math.round(x)};
 let stats={words:0,periodStates:0,freshChecks:0,conditionalCells:0,vectorChecks:0,clockPermutationChecks:0,clockRelationChecks:0,weightedChecks:0,intervalChecks:0,subsetChecks:0,unionControls:0,unionWords:0,unionRootWordChecks:0,unionAdmissible:0,unionDistinctRoots:0,unionBoundChecks:0,unionRows:[],examples:[]};
 function word(p,e,w,x){
  let H=0,V=0,S=0,U=0,seen=new Set(),d=[],t=[],records=[];
  for(let i=0;i<p.length;i++){
   let q=p[i],a=mod(x-H-e[i]*(q+1)/2,q);V+=w[i];
   let b=mod(x-3-V+(e[i]===-1?0:q+2),2*q);
   let ds=mod(a-S,q),du=mod(b-U,2*q),fresh=!seen.has(q);
   if(fresh){let eta=mod(x-3-V+(e[i]===-1?0:q+2)-U,2),delta=mod(H+e[i]*(q+1)/2-3-V+(e[i]===-1?0:q+2)+S-U,q);
    ck(du%2===eta&&mod(du-ds-delta,q)===0,"joint residue");
    records.push({q,old:[...seen].reduce((a,b)=>a*b,1),ds,du,eta,delta});d.push(ds);t.push(du);seen.add(q)}
   S+=ds;U+=du;H+=(q-1)/2;
  }return {S,U,d,t,records}
 }
 let cases=[[5,7,11],[7,5,7,11,5,13],[11,11,5,13,7],[17,5,17,7],[5,7,11,13,5],[13,7,11,7,13,5],[5,5,5,7],[19,7,5,11]];
 for(let p of cases)for(let mask of [0,5,23])for(let parity of [0,1]){
  let e=p.map((_,i)=>sign(i,mask)),w=p.map((q,i)=>1+(3*i+mask)%Math.min(q,11)),fresh=[...new Set(p)],Q=fresh.reduce((a,b)=>a*b,1),cells=new Map(),vectors=new Set(),counts=new Map(),lap=0,lap2=0;
  for(let j=0;j<Q;j++){
   let x=6*j+3*parity,o=word(p,e,w,x),key=o.d.join(":");
   ck(!vectors.has(key),"fresh vector bijection");vectors.add(key);stats.vectorChecks++;
   let sum=o.d.reduce((a,b)=>a+b,0);counts.set(sum,(counts.get(sum)||0)+1);
   let lam=.13,mu=.07;lap+=Math.exp(-lam*sum);lap2+=Math.exp(-lam*sum-mu*o.t.reduce((a,b)=>a+b,0));
   for(let r of o.records){let k=r.q+":"+mod(x,r.old),c=cells.get(k);if(!c){c={p:r.q,d:new Map(),t:new Set(),eta:r.eta,delta:r.delta};cells.set(k,c)}
    ck(r.eta===c.eta&&r.delta===c.delta,"conditional fixed shift");c.d.set(r.ds,(c.d.get(r.ds)||0)+1);c.t.add(r.du);stats.freshChecks++;stats.clockRelationChecks++}
   stats.periodStates++;
  }
  ck(vectors.size===Q,"complete fresh vectors");
  for(let c of cells.values()){ck(c.d.size===c.p&&new Set(c.d.values()).size===1,"conditional uniform");ck(c.t.size===c.p&&[...c.t].every(v=>v%2===c.eta),"clock permutation");stats.conditionalCells++;stats.clockPermutationChecks++}
  let dist=[1];for(let q of fresh){let b=Array(dist.length+q-1).fill(0);for(let i=0;i<dist.length;i++)for(let j=0;j<q;j++)b[i+j]+=dist[i];dist=b}
  ck(dist.every((n,i)=>n===(counts.get(i)||0)),"distribution");
  let mgf=(l)=>fresh.reduce((a,p)=>a*Array.from({length:p},(_,d)=>Math.exp(-l*d)).reduce((a,b)=>a+b,0)/p,1);
  ck(Math.abs(lap/Q-mgf(.13))<1e-10&&lap2/Q<=mgf(.13+2*.07)+1e-10,"Laplace");stats.weightedChecks++;
  for(let B of [0,2,5,10,20]){
   let g=dist.slice(0,B+1).reduce((a,b)=>a+b,0);ck(g<=choose(B+fresh.length,fresh.length),"stars bars");
   // Roots A=12*j+6*parity, j in arbitrary nonperiod interval.
   for(let [start,N] of [[13,37],[Q-7,23],[Q+17,2*Q+1]]){
    let good=0;for(let j=start;j<start+N;j++){let o=word(p,e,w,6*j+3*parity);if(o.S<=B)good++}
    ck(good<=Math.ceil(N/Q)*g,"short interval");stats.intervalChecks++;
   }
   // Arbitrary subset of first indices: nondecreasing s choices.
   let keep=fresh.filter((_,i)=>i%2===0),P=keep.reduce((a,b)=>a*b,1),ok=new Set();
   for(let j=0;j<Q;j++){let o=word(p,e,w,6*j+3*parity);if(o.S<=B)ok.add(j%P)}
   ck(ok.size<=Math.min(P,choose(B+keep.length,keep.length)),"subset CRT");stats.subsetChecks++;
  }
  stats.words++;
 }
 // Explicit distinct-word union over fixed small bands, both signs.
 // Enumerate prefix word families separately, only scalar spatial test.
 function runUnion(P,k,B,N,start){
  let rows=[],words=0,roots=new Set(),admissible=0,bound=0,weighted=0;
  function walk(p){if(p.length<k){for(let q of P)if(!p.includes(q))walk([...p,q]);return}
   let Q=p.reduce((a,b)=>a*b,1);for(let mask=0;mask<2**k;mask++){
    let e=p.map((_,i)=>sign(i,mask)),w=p.map(()=>1),num=0;
    for(let j=start;j<start+N;j++){let o=word(p,e,w,3*j);if(o.S<=B){num++;roots.add(j)}stats.unionRootWordChecks++}
    let ub=Math.ceil(N/Q)*choose(B+k,k);ck(num<=ub,"union word bound");admissible+=num;bound+=ub;weighted+=1/Q;words++;
   }
  }walk([]);
  let Qmax=P.slice().sort((a,b)=>b-a).slice(0,k).reduce((a,b)=>a*b,1),simple=(N+Qmax)*choose(B+k,k)*(2*P.reduce((a,p)=>a+1/p,0))**k;
  ck(roots.size<=admissible&&admissible<=bound&&bound<=simple+1e-7,"union bound");stats.unionControls++;stats.unionWords+=words;stats.unionAdmissible+=admissible;stats.unionDistinctRoots+=roots.size;stats.unionBoundChecks++;stats.unionRows.push({P,k,B,N,start,words,roots:roots.size,admissible,bound,simple:Math.round(simple),exactHarmonic:weighted})
 }
 for(let k of [2,3])for(let B of [0,1,3,6])runUnion([11,13,17,19],k,B,2500,101);
 // Verify actual canonical high words as fixed-word candidates, and count 
 // how many roots meet a very small cumulative relay budget up to k fresh marks.
 const N=120000,spf=new Uint32Array(N+3);for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)spf[n]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
 let actual={roots:0,events:0,words:0,greedyChecks:0,distinctWords:0,smallGainDistinct:0,thresholdRows:[]};
 for(let T of [11,23,53,101]){
  let row={T,roots:0,words:0,distinct:0,smallGainDistinct:0,meanLowGain:0};
  for(let A=12;A<=N;A+=6){let a=A,v=3-A/2,S=0,U=0,p=[],e=[],w=[],seen=new Set(),firstRepeat=false;
   while(a>A/2&&p.length<3){let r=Infinity,t=Infinity,sg=0;for(let [b,f] of [[a+1,-1],[a-1,1]])for(let q of fs(b)){let z=mod((f===-1?0:q+2)-v,2*q)||2*q;if(z<t||z===t&&q<r){r=q;t=z;sg=f}}
    if(v+t>-1||a-r+1<=A/2)break;
    if(r>=T){if(seen.has(r))firstRepeat=true;seen.add(r);p.push(r);e.push(sg);w.push(t);let o=word(p,e,w,A/2);ck(o.S<=S&&o.U<=U,"actual greedy");actual.greedyChecks++}
    else{S+=(r-1)/2;U+=t}a-=r-1;v+=t;actual.events++;
   }
   actual.roots++;row.roots++;if(p.length===3){actual.words++;row.words++;if(!firstRepeat){actual.distinctWords++;row.distinct++;row.meanLowGain+=S;if(S<=3){row.smallGainDistinct++;actual.smallGainDistinct++}}}
  }if(row.distinct)row.meanLowGain/=row.distinct;actual.thresholdRows.push(row)
 }
 stats.actual=actual;return stats
}
console.log(JSON.stringify(audit(),null,2));
