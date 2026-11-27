// Actual reverse ancestry, shallow occupation and constructive simultaneous reset fans.
// Reproduce: node research/lean/negative_min_reverse_arrival_audit.mjs
function run(){
 let checks=0,ticks=0,roots=0,windows=0,reverseTests=0,shallowTicks=0,longPhaseTests=0,fanTicks=0,degreePathTests=0,maxWitnessTests=0;
 const ck=(b,s)=>{checks++;if(!b)throw Error(s)};
 const gcd=(a,b)=>{a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a};
 function sieve(n){let a=new Uint32Array(n+1);for(let p=2;p<=n;p++)if(!a[p]){a[p]=p;if(p*p<=n)for(let k=p*p;k<=n;k+=p)if(!a[k])a[k]=p}return a}
 let rows=[];
 for(let cfg of [{R:12000,T:72,M:4,sample:40},{R:48000,T:144,M:8,sample:40},{R:192000,T:288,M:16,sample:40},{R:768000,T:576,M:24,sample:40}]){
  let {R,T,M,sample}=cfg,sp=sieve(2*R+8),H=Math.max(1,Math.floor(T/8)),W=T;
  function factors(n){let a=[];while(n>1){let p=sp[n];a.push(p);while(n%p===0)n/=p}return a}
  let parentCache=new Map(),reachCache=new Map();
  function par(x){if(!parentCache.has(x)){let p=[...new Set([...factors(x),...factors(x-2)])].filter(p=>p>2&&x+p-1<=2*R);parentCache.set(x,p.map(p=>x+p-1))}return parentCache.get(x)}
  function reach(x,d){let key=x+":"+d;if(!reachCache.has(key)){let a=new Set([x]);if(d)for(let y of par(x))for(let A of reach(y,d-1))a.add(A);reachCache.set(key,a)}return reachCache.get(key)}
  let B=0;for(let x=Math.max(4,R-3*T-6+(R-3*T-6)%2);x<=2*R;x+=2)B=Math.max(B,par(x).length);
  let nW=Math.ceil((R/6+1)/(W/6)),row={...cfg,H,B,N:0,shallow:[0,0,0],shallowCapped:[0,0,0],allCap:0,deepOverflowRoots:0,overflowBins:0,largestShallow:[0,0,0],long:[0,0,0],longSites:[0,0,0],longRootCounts:[0,0,0],bound:[0,0,0],fanIn:0,firstArrivalLabels:0};
  let longMaps=Array.from({length:3},()=>new Map());
  for(let j=0;j<Math.min(sample,nW);j++){
   let base=R+Math.floor(j*nW/Math.min(sample,nW))*W,start=3-base/2,rs=[];
   for(let A=base;A<base+W&&A<=2*R;A+=6){
    let x=A,n=3-A/2,age=start-n,depth=0,obs=[],prev=0;
    while(n<start+T){
     if(n>=start)obs.push({x,depth});
     let t=n+1,p=sp[gcd(t%2===0?x+1:x-1,t%2===0?t:t-2)]||0;
     if(p){
      let y=x-p+1;
      ck(p>=3&&p%2===1&&y>2,"actual positive arrival");
      ck((t%2===0?y:y-2)%p===0,"arrival spatial pin");
      ck((t%2===0?t:t-2)%(2*p)===(t%2===0?0:p)||t%2!==0,"even clock pin");
      ck(t%2===0?t%(2*p)===0:((t%(2*p)+2*p)%(2*p)===p+2),"arrival clock");
      ck(par(y).includes(x),"reverse parent contains actual source");
      let h=t+y/2;ck((h-(t%2===0?0:3))%p===0,"arrival height pin");
      depth++;x=y;
     }
     n=t;ticks++;
    }
    for(let z of obs)if(z.depth<=2){ck(reach(z.x,z.depth).has(A),"actual shallow ancestor");reverseTests++}
    rs.push({A,obs});roots++;row.N++;
    for(let u=0;u<T;){let z=obs[u],v=u+1;while(v<T&&obs[v].x===z.x)v++;
     let len=v-u;
     if(z.depth<=2)for(let d=z.depth;d<=2;d++){
      row.shallow[d]+=len;shallowTicks+=len;
      if(len>H){
       let q=Math.min(sp[z.x-1],sp[z.x+1]);ck(2*q>len-1,"long stationary phase implies roughness");
       row.long[d]+=len;
       if(!longMaps[d].has(z.x))longMaps[d].set(z.x,new Set());
       longMaps[d].get(z.x).add(A);longPhaseTests++;
      }
     }
     u=v;
    }
   }
   if(!rs.length)continue;windows++;
   for(let u=0;u<T;u++){
    let g=new Map();for(let r of rs){let z=r.obs[u];if(!g.has(z.x))g.set(z.x,[]);g.get(z.x).push(r)}
    for(let [x,rr] of g){row.allCap+=Math.min(M,rr.length);row.fanIn=Math.max(row.fanIn,rr.length);
     for(let d=0;d<=2;d++){let ss=rr.filter(r=>r.obs[u].depth<=d);ck(ss.length<=reach(x,d).size&&ss.length<=(B+1)**d,"shallow depth bound");row.largestShallow[d]=Math.max(row.largestShallow[d],ss.length);row.shallowCapped[d]+=Math.min(M,ss.length)}
     if(rr.length>M){row.overflowBins++;let n=rr.filter(r=>r.obs[u].depth>2).length;row.deepOverflowRoots+=n;ck(n>=rr.length-(B+1)**2,"overflow deep lower")}
    }
   }
  }
  for(let d=0;d<=2;d++){
   let lm=longMaps[d],n=0;for(let [x,a] of lm){ck(a.size<=reach(x,d).size,"long phase distinct ancestor bound");n+=a.size}
   row.longSites[d]=lm.size;row.longRootCounts[d]=n;row.bound[d]=row.N*(d+1)*H+T*n;
   ck(row.shallow[d]<=row.bound[d],"shallow occupation split");
  }
  row.normalized={shallow:row.shallow.map(x=>x/(row.N*T)),shallowCapped:row.shallowCapped.map(x=>x/(row.N*T)),long:row.long.map(x=>x/(row.N*T)),allCap:row.allCap/(row.N*T)};
  rows.push(row)
 }
 // Construct a compatible set of direct first-fire prime relays and
 // exact CRT witnesses of arbitrary-size integers, not a random model.
 const sp=sieve(12000),primes=[];for(let p=3;p<sp.length;p++)if(sp[p]===p)primes.push(p);
 const mod=(a,b)=>((a%b)+b)%b;
 function residues(ps,q,Z){
  if(ps.includes(q))return ps.every(p=>p<=q||(p%q!==0&&(p-2)%q!==0))?[0]:[];
  let a=[];for(let r=0;r<q;r++)if((r+1)%q!==0&&mod(r-1,q)!==0&&ps.every(p=>p<=q||((r+p)%q!==0&&mod(r+p-2,q)!==0)))a.push(r);
  return a;
 }
 let ps=[];
 for(let p of primes){if(p<13||p%6!==1)continue;
  let a=ps.concat(p);if(primes.filter(q=>q>=5&&q<=p).every(q=>residues(a,q,p).length)){ps=a;if(ps.length>=8)break}
 }
 function bigmod(a,b){return ((a%b)+b)%b}
 function bgcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b)[a,b]=[b,a%b];return a}
 function bgcdWinner(x,n){
  let a=bgcd(n%2n===0n?x+1n:x-1n,n%2n===0n?n:n-2n);if(a<2n)return 0;
  for(let p of primes)if(a%BigInt(p)===0n)return p;
  throw Error("unexpected large gcd");
 }
 function literal(x,n,h){for(let p of primes){if(p>2*h+1)break;let q=BigInt(p);if(n%2n===0n?(x+1n)%q===0n&&bigmod(n,2n*q)===0n:(x-1n)%q===0n&&bigmod(n,2n*q)===q+2n)return p}return 0}
 let fans=[];
 for(let r of [1,2,3,4,6,8].filter(r=>r<=ps.length)){
  let a=ps.slice(0,r),Z=4*a.at(-1)+100,T=Math.floor((Z-8)/3),W=6*Math.floor(T/6),x=0n,Q=12n,localChoices=[];
  for(let q of primes){if(q<5)continue;if(q>Z)break;
   let rr=residues(a,q,Z);ck(rr.length>0,"local CRT admissibility");localChoices.push(rr.length);
   let b=BigInt(q),target=BigInt(rr[0]),j=0n;while(bigmod(x+Q*j,b)!==target)j++;x+=Q*j;Q*=b;
  }
  x+=Q;ck(x%12n===0n&&a.at(-1)-1<W,"same observation window");
  let Aset=[x,...a.map(p=>x+BigInt(p-1))],obs=new Map();
  for(let A of Aset){
   let y=A,n=3n-A/2n,end=3n-x/2n+BigInt(T),labels=[],arrival=null;
   while(n<end){
    let nn=n+1n,h=Number(nn+y/2n),p=bgcdWinner(y,nn);ck(p===literal(y,nn,h),"BigInt literal eligibility equals gcd");
    if(p){labels.push(p);y-=BigInt(p-1);arrival={x:y,n:nn,h:nn+y/2n};}
    n=nn;fanTicks++;
    if(n>=3n-x/2n)ck(y===x,"fan coalesces by target birth and remains stationary");
   }
   if(A===x)ck(labels.length===0,"target birth stationary");
   else {let p=Number(A-x+1n);ck(labels.length===1&&labels[0]===p&&arrival.x===x&&arrival.h===0n&&arrival.n===-x/2n,"single exact direct reset");}
  }
  fans.push({r,primes:a,Z,T,W,roots:r+1,digits:x.toString().length,center:r<=2?x.toString():undefined,modulusDigits:Q.toString().length,minAllowed:Math.min(...localChoices)});
 }
 // Independent relaxed spatial graph. Self-loops pad paths of length <=d.
 let degreeRows=[];
 for(let R of [300,1200,6000]){
  let sp=sieve(2*R+2),V=[];for(let x=4;x<=2*R;x+=2)V.push(x);
  function fs(n){let a=[];while(n>1){let p=sp[n];a.push(p);while(n%p===0)n/=p}return a}
  let next=new Map(),prev=new Map(),deg=new Map();
  for(let x of V){next.set(x,[x]);prev.set(x,[x])}
  for(let x of V)for(let p of new Set([...fs(x-1),...fs(x+1)])){
   let y=x-p+1;if(p>2&&y>=4&&y<x){next.get(x).push(y);prev.get(y).push(x)}
  }
  for(let x of V){
   let rr=[x,...[...new Set([...fs(x),...fs(x-2)])].filter(p=>p>2&&x+p-1<=2*R).map(p=>x+p-1)];
   ck(rr.length===prev.get(x).length&&rr.every(y=>prev.get(x).includes(y)),"exact spatial reverse adjacency");
   deg.set(x,Math.max(next.get(x).length,prev.get(x).length));
  }
  let S=V.filter(x=>Math.min(sp[x-1],sp[x+1])>Math.floor(Math.sqrt(R)/2)),maxDeg=Math.max(...deg.values()),row={R,sites:S.length,maxDeg,tests:0};
  function paths(start,d,K,adj){
   let m=new Map([[start,1]]);if(deg.get(start)>K)return 0;
   for(let j=0;j<d;j++){let n=new Map();for(let [v,k] of m)for(let w of adj.get(v))if(deg.get(w)<=K)n.set(w,(n.get(w)||0)+k);m=n}
   return [...m.values()].reduce((s,x)=>s+x,0)
  }
  for(let d=0;d<=5;d++)for(let K=1;K<=maxDeg;K++){
   let all=S.reduce((s,x)=>s+paths(x,d,maxDeg,prev),0),good=S.reduce((s,x)=>s+paths(x,d,K,prev),0);
   let badBound=(d+1)*V.filter(v=>deg.get(v)>K).reduce((s,v)=>s+deg.get(v)**d,0);
   ck(good<=S.length*K**d&&all-good<=badBound&&all<=S.length*K**d+badBound,"max degree witness bound");degreePathTests++;row.tests++;
  }
  for(let v of V.filter((_,i)=>i%19===0))for(let d=0;d<=4;d++)for(let i=0;i<=d;i++){
   let k=deg.get(v),a=paths(v,i,k,prev),b=paths(v,d-i,k,next);
   ck(a*b<=k**d,"path through specified maximum-degree vertex");maxWitnessTests++;
  }
  degreeRows.push(row)
 }
 return {checks,ticks,roots,windows,reverseTests,shallowTicks,longPhaseTests,fanTicks,degreePathTests,maxWitnessTests,rows,fans,degreeRows};
}
console.log(JSON.stringify(run()));
