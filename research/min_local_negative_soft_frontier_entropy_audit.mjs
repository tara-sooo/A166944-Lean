// Soft roughness weighted frontier, adaptive trajectory positions, and mixed Kraft certificates.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=4000005,spf=new Int32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let x=p*p;x<=N;x+=p)if(!spf[x])spf[x]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 function rough(a){return Math.min(spf[a-1]||a-1,spf[a+1]||a+1)}
 function twin(a){return !spf[a-1]&&!spf[a+1]}
 let z={roots:0,events:0,centerChecks:0,scoreChecks:0,kraftChecks:0,adaptiveChecks:0,rows:[]};
 for(let R of [12000,48000,192000,480000,1000000,2000000]){
  const S=Math.sqrt(2*R+1),K=Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),T=4*K,U=Math.ceil(8*S),J=Math.floor(T/5),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nr=(hi-lo)/6+1;
  function penalty(a){let q=Math.min(rough(a),S),d=Math.log(S/q);return 2*Math.log(Math.log(S)/Math.log(q))+Math.log1p(d)+2*Math.log1p(Math.log1p(d))}
  const maps=Array.from({length:5},()=>new Map()),paths=[],add=(m,a)=>m.set(a,(m.get(a)||0)+1);
  let badWeight=0,goodWeight=0,smallWeight=0,largeWeight=0,bad=0,good=0;
  for(let a=2*Math.ceil((lo-2*U-6)/2);a<=hi;a+=2){let c=penalty(a),w=Math.exp(-c);ck(c>=-1e-12&&w<=1+1e-12,"weight");if(twin(a)){ck(c===0,"twin weight");good++;goodWeight+=w}else{bad++;badWeight+=w;if(rough(a)<R**.4)smallWeight+=w;else largeWeight+=w}z.centerChecks++}
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,t=0,best=A,early=null,earlyBest=null;
   for(;;){let e=next(a,n);
    if(early===null&&t+e.w>T){early=a;earlyBest=best}
    if(t+e.w>U)break;
    a-=e.p-1;n+=e.w;t+=e.w;z.events++;
    ck(a>=lo-2*U-6&&a<=A,"domain");
    if(rough(a)>rough(best))best=a;
   }
   ck(early!==null&&rough(earlyBest)>=rough(early)&&rough(best)>=rough(a)&&rough(best)>=rough(earlyBest),"best");
   let list=[A,early,earlyBest,a,best],sel=A-early<=J;
   for(let i=0;i<5;i++)add(maps[i],list[i]);paths.push({list,sel});z.roots++;
  }
  let selected=new Map();for(let p of paths)if(p.sel)add(selected,p.list[1]);
  function stats(m,name){
   let ns=0,L=0,P=0,W=0,B=0,Tw=0,twMass=0;for(let [a,n] of m){let c=penalty(a),w=Math.exp(-c);ns+=n;L+=n*Math.log(n);P+=n*c;W+=w;if(twin(a)){Tw++;twMass+=n}else B+=w}
   L/=ns;P/=ns;const score=L+P-Math.log(ns/nr),jensen=ns*Math.exp(-L-P);
   ck(jensen<=W+1e-7&&B<=badWeight+1e-7,"Jensen/capacity");ck(Math.abs(W-Tw-B)<1e-7,"weights");z.scoreChecks++;
   return {name,ns,distinct:m.size,twins:Tw,twinMass:twMass/ns,L,penalty:P,score,scoreRatio:score/Math.log(Math.log(R)),weightedSupport:W,weightedBad:B,jensen,margin:Math.log(jensen/badWeight),exactMargin:Math.log(W/badWeight)}
  }
  let rows=maps.map((m,i)=>stats(m,["seed","shortEndpoint","shortBest","longEndpoint","longBest"][i]));rows.push(stats(selected,"selectedShort"));
  // Fixed mixture of codes on all four nonseed maps; adaptively choose the
  // largest weighted code. Conditional code mass per endpoint stays <= 1.
  let chosen=new Map(),weights=new Map(),cert=0,choiceCount=[0,0,0,0,0],cost=0;
  for(let {list} of paths){let idx=1,best=-Infinity;for(let i=1;i<5;i++){let a=list[i],x=-Math.log(maps[i].get(a))-penalty(a);if(x>best){idx=i;best=x}}
   let a=list[idx],v=1/(4*maps[idx].get(a));add(chosen,a);weights.set(a,(weights.get(a)||0)+v);cert+=v*Math.exp(-penalty(a));cost+=-Math.log(v);choiceCount[idx]++;z.adaptiveChecks++;
  }
  for(let v of weights.values()){ck(v<=1+1e-8,"Kraft");z.kraftChecks++}
  let adap=stats(chosen,"adaptiveCode");ck(cert<=adap.weightedSupport+1e-7&&adap.L<=cost/nr+1e-8,"adaptive support");
  z.rows.push({R,S,K,T,U,J,nr,bad,good,badWeight,goodWeight,smallWeight,largeWeight,scaledBad:badWeight*Math.log(R)**3/R,rows,adaptive:{...adap,certificate:cert,codeCost:cost/nr,choiceCount}})
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
