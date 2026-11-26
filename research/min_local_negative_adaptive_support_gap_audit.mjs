// Adaptive support thresholds, robust sparse-core time bound and large-prime wall insertion.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=1200000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let x=p*p;x<=N+2;x+=p)spf[x]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
 function ev(a,v){let p=Infinity,w=Infinity,e=0,q=Infinity;for(let [d,s] of [[a+1,-1],[a-1,1]])for(let r of fs(d)){q=Math.min(q,r);let t=mod((s===-1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e,q}}
 let z={canonicalRoots:0,canonicalEvents:0,canonicalWitnesses:0,canonicalNonTwin:0,canonicalNonTwinChecks:0,otherRoots:0,otherEvents:0,blocks:0,coreControls:0,shortControls:0,wallRunChecks:0,crtKeyChecks:0,exceptionChecks:0,quantitativeChecks:0,largeCutChecks:0,refinementChecks:0,strictWallRefinements:0,syntheticSupports:0,largePrimeAdditionChecks:0,largePrimeStrict:0,rows:[]};
 const cache=new Map();
 function walls(P,cap=1000000){let key=P.join(",");if(cache.has(key))return cache.get(key);let Q=1,W=[0];for(let p of P){if(Q*p>cap)return null;let v=[];for(let x of W)for(let j=0;j<p;j++)if(mod(-(x+Q*j),p)<=(p-3)/2)v.push(x+Q*j);Q*=p;v.sort((a,b)=>a-b);W=v}let M=1;for(let i=0;i<W.length;i++)M=Math.max(M,(i+1===W.length?Q:W[i+1])-W[i]);let t={Q,W,M};if(Q<100000&&cache.size<1000)cache.set(key,t);return t}
 function prev(x,t){let r=mod(x,t.Q),a=0,b=t.W.length;while(a+1<b){let m=(a+b)>>1;if(t.W[m]<=r)a=m;else b=m}return x-r+t.W[a]}
 function choose(P,U){let r=Math.exp(Math.log(U)/2**P.length),Q=1;for(let p of P){if(p>=U)break;if(p>=r*Q)return {T:p,Q,r};Q*=p}ck(Q<=U/r+1e-6,"gap choice");return {T:U,Q,r}}
 function check(arr,A,P,row){
  let S=new Set(P),U=Math.sqrt(A),k=P.length,d=choose(P,U),E=arr.filter(x=>!S.has(x.p)).length,W=arr.reduce((a,x)=>a+x.w,0),G=arr.reduce((a,x)=>a+x.p-1,0);
  ck(G<=A/2&&d.Q<=d.T/d.r+1e-6,"budget");ck(W<=100*(k+1)**2*A/d.r+10*Math.sqrt(A+1)*(E+1),"quantitative");z.quantitativeChecks++;z.coreControls++;
  let best=null;for(let t of [...P.filter(p=>p<U),U]){let tab=walls(P.filter(p=>p<t));if(!tab)continue;let ratio=t/tab.M;if(!best||ratio>best.ratio)best={T:t,tab,ratio}}
  if(d.Q<=1000000){ck(best&&best.ratio+1e-7>=d.r,"wall improves ratio");z.refinementChecks++;if(best.ratio>d.r+1e-6)z.strictWallRefinements++}
  if(!best||best.ratio<4)return;
  let {T,tab}=best,M=tab.M,L=P.filter(p=>p>=T).length,high=0,low=0,lowW=0,excW=0,lastW=0,pairW=0,runGain=0,runStart=null,prevMark=null,groups=new Map(),nRuns=0;
  function flushRun(){if(runStart!==null){ck(runGain<2*M,"run gain");z.wallRunChecks++;nRuns++;runStart=null;runGain=0}}
  function flushMark(){if(prevMark){lastW+=prevMark.w;prevMark=null}}
  for(let x of arr){if(!S.has(x.p)){flushRun();flushMark();excW+=x.w;continue}if(x.p<T){if(runStart===null)runStart=x.a/2;ck((x.a-x.p+1)/2>=prev(runStart,tab),"wall");runGain+=x.p-1;low+=x.p-1;lowW+=x.w;continue}
   flushRun();high++;
   if(prevMark){let a=prevMark,p=a.p,r=x.p,relay=a.a-p+1-x.a;ck(relay>=0&&relay%2===0&&relay<2*M&&p!==r,"short distinct relay");let key=[p,r,a.e,x.e,relay].join(":"),g=groups.get(key)||{p,r,n:0,W:0,first:a.a,last:a.a};g.n++;g.W+=a.w;g.last=a.a;groups.set(key,g);pairW+=a.w}prevMark=x
  }flushRun();flushMark();
  ck(nRuns<=high+E+1&&low<=2*M*(high+E+1)&&lowW<=3*low&&high<=G/(T-1)+1e-9,"low capacity");
  let S0=Math.sqrt(A+1),D=A/2+1,cap=0;
  for(let g of groups.values()){let c=Math.floor((g.first-g.last)/(2*g.p*g.r))+1;ck(g.n<=c&&g.W<=2*Math.min(g.p,S0)*c+1e-9,"pair capacity");cap+=2*Math.min(g.p,S0)*c;z.crtKeyChecks++}
  ck(pairW<=cap+1e-9&&cap<=4*M*L*Math.max(0,L-1)*(D/T+2*S0)+1e-7,"pair sum");
  ck(lastW<=2*S0*(E+1)+1e-7&&excW<=2*S0*E+1e-7&&W===lowW+excW+lastW+pairW,"exception waits");z.exceptionChecks++;
  ck(W<=6*M*(G/(T-1)+E+1)+4*M*L*Math.max(0,L-1)*(D/T+2*S0)+2*S0*(2*E+1)+1e-6,"exact bound");
  z.shortControls++;row.short++
 }
 let rng=123456;function random(){rng=(Math.imul(rng,1664525)+1013904223)>>>0;return rng/4294967296}
 let ps=[];for(let p=3;p<=199;p+=2)if(!spf[p])ps.push(p);
 for(let i=0;i<2500;i++){let P=ps.filter(()=>random()<.08),U=10**(1+6*random());choose(P,U);z.syntheticSupports++}
 for(let i=0;i<300;i++){let P=ps.slice(0,7).filter(()=>random()<.25),t=walls(P,100000);if(!t)continue;let p=ps.find(p=>!P.includes(p)&&p>=2*t.M+1&&p*t.Q<=500000);if(!p)continue;let u=walls([...P,p].sort((a,b)=>a-b));ck(u&&u.M<=(p+1)/2+2*t.M-1,"large prime insertion");z.largePrimeAdditionChecks++;if(u.M<u.Q)z.largePrimeStrict++}
 function core(arr,A,row){if(!arr.length)return;let cnt=new Map();for(let x of arr)cnt.set(x.p,(cnt.get(x.p)||0)+1);let all=[...cnt.keys()].sort((a,b)=>a-b),freq=[...all].sort((a,b)=>cnt.get(b)-cnt.get(a)||a-b),sets=new Map();
  for(let P of [[],all,all.filter(p=>p<=Math.sqrt(A)*2),all.filter(p=>p<=Math.sqrt(A)*4),freq.slice(0,1),freq.slice(0,2),freq.slice(0,3),freq.slice(0,4),all.slice(0,3)]){P=[...P].sort((a,b)=>a-b);sets.set(P.join(","),P)}
  for(let P of sets.values())check(arr,A,P,row);
  for(let F of [2,4,8]){let E=arr.filter(x=>x.p>F*Math.sqrt(A)).length,W=arr.filter(x=>x.p>F*Math.sqrt(A)).reduce((a,x)=>a+x.w,0);ck(E<=A/2/(F*Math.sqrt(A)-1)+1e-8&&W<=2*Math.sqrt(A+1)*E+1e-8,"very high");z.largeCutChecks++}
 }
 for(let A=12;A<=120000;A+=6){let a=A,v=3-A/2,arr=[],seen=false,reason;while(true){if(a<=A/2){reason="half";break}let x=ev(a,v);if(x.q>Math.sqrt(a+1))seen=true;if(v+x.w>-1){reason="time";break}z.canonicalEvents++;arr.push({a,...x});a-=x.p-1;v+=x.w}z.canonicalRoots++;let W=arr.reduce((s,x)=>s+x.w,0),bound=Math.min(A/4-3,A/2-4-2*Math.sqrt(A+1));if(W<bound){ck(seen,"witness");z.canonicalWitnesses++}if(!seen){z.canonicalNonTwin++;ck(W>=bound,"lower");if(reason==="half")arr.pop();core(arr,A,{short:0});z.canonicalNonTwinChecks++}}
 for(let R of [10000,40000,120000,250000,500000]){let row={R,blocks:0,events:0,short:0};for(let phase of [0,17,Math.floor(R/3)])for(let A=2*R-300+(6-(2*R-300)%6)%6;A<2*R;A+=6){let a=A,v=phase,arr=[];function flush(){if(!arr.length)return;core(arr,arr[0].a,row);row.blocks++;z.blocks++;arr=[]}while(a>A/2){let x=ev(a,v);if(a-x.p+1<=A/2||x.q>Math.sqrt(a+1)){flush();if(a-x.p+1<=A/2)break}else{arr.push({a,...x});z.otherEvents++;row.events++}a-=x.p-1;v+=x.w}flush();z.otherRoots++}z.rows.push(row)}
 return z
}
console.log(JSON.stringify(audit(),null,2));
