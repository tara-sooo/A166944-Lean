// Clock-gap CRT and individual-baseline weighted relay packing.
function audit(){
const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(x,p)=>(x%p+p)%p,N=600000,spf=new Uint32Array(N+3);
for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)spf[n]=p;
function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
function event(a,v){let p=Infinity,w=Infinity,e=0,q=Infinity;for(let [d,s] of [[a+1,-1],[a-1,1]])for(let r of fs(d)){q=Math.min(q,r);let t=mod((s===-1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e,q}}
function pack(bounds,c,par,min){let b=bounds.map(x=>Math.max(min,x)+mod(par-Math.max(min,x),2)).sort((a,b)=>a-b),t=[];for(let i=0;i<b.length;i++)t.push(Math.max(b[i],i>=c?t[i-c]+2:0));return t.reduce((a,x)=>a+x,0)-bounds.reduce((a,x)=>a+x,0)}
function weighted(list,c,par,min,base){let w=[...new Set(list.map(x=>x.weight).filter(x=>x>0))].sort((a,b)=>a-b),last=0,s=0;for(let v of w){s+=(v-last)*pack(list.filter(x=>x.weight>=v).map(base),c,par,min);last=v}return s}
let s={roots:0,events:0,blocks:0,controls:0,pairs:0,groups:0,repeatGroups:0,clockCRT:0,spatialCRT:0,capacity:0,clockPositive:0,spacePositive:0,clockImprovement:0,spaceImprovement:0,strictCombined:0,weightedChecks:0,globalChecks:0,maxClock:0,maxCombined:0,examples:[],synthetic:0,syntheticStrict:0,syntheticBrute:0,roundedChecks:0,roundedImprovement:0,maxRounded:0,repeatClockPositive:0,repeatClockImprovement:0,clockBeyondParity:0,repeatClockBeyondParity:0};
function check(arr,t){
 if(!arr.length)return;let n=arr.length,lev=arr.map(x=>x.p<t?-1:Math.floor(Math.log2(x.p/t))),max=Math.max(...lev),I=[],groups=new Map();
 for(let j=0;j<=max;j++){let last=-1;for(let i=0;i<n;i++){
  if(lev[i]>j){last=-1;continue}if(lev[i]!==j)continue;
  if(last>=0){let a=arr[last],b=arr[i],E=0,H=0,V=0,K=0;for(let k=last+1;k<i;k++){let x=arr[k];E+=x.p-1;V+=x.w;if(lev[k]>=0){H+=x.p-1;K+=x.w}}
   let tau=b.fire-a.fire,par=Number(a.e!==b.e);ck(tau===V+b.w&&mod(tau,2)===par,"clock gap");ck(b.a===a.a-a.p+1-E,"space gap");
   let x={l:last+1,r:i,a:a.a,n:a.fire,p:a.p,rp:b.p,e:a.e,f:b.e,E,H,V,K,tau,base:b.w+K,g:E-H,u:V-K,par,weight:0};
   ck(mod(a.fire-(a.e===-1?0:a.p+2),2*a.p)===0&&mod(b.fire-(b.e===-1?0:b.p+2),2*b.p)===0,"clock CRT");s.clockCRT++;s.pairs++;
   if(a.p!==b.p){ck(mod(a.a-a.e,a.p)===0&&mod(a.a-(a.p-1+E+b.e),b.p)===0,"space CRT");s.spatialCRT++;let key=[j,a.p,b.p,a.e,b.e].join(":"),g=groups.get(key)||[];g.push(x);groups.set(key,g)}
   else{ck(E>=a.p-1,"same space");let d=mod((b.e===-1?0:b.p+2)-(a.e===-1?0:a.p+2),2*a.p)||2*a.p;ck(tau>=d&&mod(tau-d,2*a.p)===0,"same clock");x.d=d}
   I.push(x)
  }last=i
 }}
 let depth=Array(n).fill(0);for(let x of I)for(let i=x.l;i<x.r;i++)if(lev[i]<0)depth[i]++;
 for(let x of I){let d=0;for(let i=x.l;i<x.r;i++)d=Math.max(d,depth[i]);x.weight=d?1/d:0}
 let lowG=arr.reduce((g,x,i)=>g+(lev[i]<0?x.p-1:0),0),total=0,spaceTotal=0,clockTotal=0,rounded=0;
 for(let g of groups.values()){
  let x=g[0],p=x.p,r=x.rp,span=Math.max(...g.map(x=>x.a))-Math.min(...g.map(x=>x.a)),ts=Math.max(...g.map(x=>x.n))-Math.min(...g.map(x=>x.n)),c=Math.floor(span/(2*p*r))+1,d=Math.floor(ts/(2*p*r))+1;
  for(let [key,cap,pos] of [["E",c,"a"],["tau",d,"n"]]){let m=new Map();for(let y of g){let a=m.get(y[key])||[];for(let z of a)ck(mod(z-y[pos],2*p*r)===0,"CRT capacity");a.push(y[pos]);m.set(y[key],a)}ck([...m.values()].every(a=>a.length<=cap),"count");s.capacity++}
  let es=pack(g.map(y=>y.H),c,0,0),et=pack(g.map(y=>y.base),d,x.par,x.par?1:2),actualG=g.reduce((a,y)=>a+y.g,0),actualV=g.reduce((a,y)=>a+y.u,0);
  ck(es<=actualG&&et<=actualV,"unweighted");ck(actualV<=3*actualG,"relay wait");
  let oldS=Math.max(0,pack(g.map(()=>0),c,0,0)-g.reduce((a,y)=>a+y.H,0)),oldT=Math.max(0,pack(g.map(()=>0),d,x.par,x.par?1:2)-g.reduce((a,y)=>a+y.base,0));
  let parityCost=g.reduce((a,y)=>a+mod(x.par-y.base,2),0);if(et>parityCost){s.clockBeyondParity++;if(g.length>1)s.repeatClockBeyondParity++;}if(g.length>1&&et>0)s.repeatClockPositive++;if(g.length>1&&et>oldT)s.repeatClockImprovement++;
  if(es>0)s.spacePositive++;if(et>0)s.clockPositive++;if(es>oldS)s.spaceImprovement++;if(et>oldT)s.clockImprovement++;
  if(et/3>es){s.strictCombined++;if(s.examples.length<6)s.examples.push({p,r,n:g.length,c,d,es,et,actualG,actualV,base:g.map(y=>y.base),tau:g.map(y=>y.tau)})}
  s.maxClock=Math.max(s.maxClock,et);if(g.length>1)s.repeatGroups++;s.groups++;
  let ws=weighted(g,c,0,0,y=>y.H),wt=weighted(g,d,x.par,x.par?1:2,y=>y.base);
  let wg=g.reduce((a,y)=>a+y.weight*y.g,0),wv=g.reduce((a,y)=>a+y.weight*y.u,0);
  ck(ws<=wg+1e-8&&wt<=wv+1e-8&&wv<=3*wg+1e-8,"weighted");
  total+=Math.max(ws,wt/3);spaceTotal+=ws;clockTotal+=wt/3;s.weightedChecks++;
  let weights=[...new Set(g.map(y=>y.weight).filter(x=>x>0))].sort((a,b)=>a-b),last=0,rc=0;
  for(let v of weights){let sub=g.filter(y=>y.weight>=v),a=pack(sub.map(y=>y.H),c,0,0),b=pack(sub.map(y=>y.base),d,x.par,x.par?1:2);
   let lb=Math.max(a,2*Math.ceil(b/6));ck(lb<=sub.reduce((a,y)=>a+y.g,0),"rounded subset");
   rc+=(v-last)*lb;last=v;s.roundedChecks++;
  }
  ck(rc<=wg+1e-8&&rc>=Math.max(ws,wt/3)-1e-8,"rounded group");rounded+=rc;
 }
 for(let x of I)if(x.p===x.rp){
  let es=Math.max(0,x.p-1-x.H),first=x.base+mod(x.d-x.base,2*x.p);if(first<x.d)first=x.d;let et=first-x.base;
  ck(et>=0&&et<=x.u&&es<=x.g,"same residual");
  total+=x.weight*Math.max(es,et/3);spaceTotal+=x.weight*es;clockTotal+=x.weight*et/3;rounded+=x.weight*Math.max(es,2*Math.ceil(et/6));
 }
 for(let i=0;i<n;i++)if(lev[i]<0)ck(I.reduce((a,x)=>a+(x.l<=i&&i<x.r?x.weight:0),0)<=1+1e-9,"laminar capacity");
 ck(total<=lowG+1e-7&&total>=Math.max(spaceTotal,clockTotal)-1e-7,"global");ck(rounded<=lowG+1e-7&&rounded>=total-1e-7,"rounded global");if(rounded>total+1e-7)s.roundedImprovement++;s.maxRounded=Math.max(s.maxRounded,rounded);s.globalChecks++;s.maxCombined=Math.max(s.maxCombined,total);s.controls++;
}
// Exact brute force on small slots with individual lower bounds.
for(let c of [1,2,3])for(let n=1;n<=5;n++)for(let par of [0,1])for(let mode=0;mode<4;mode++){
 let b=Array.from({length:n},(_,i)=>(i*7+mode*3)%9),min=par?1:0,lo=pack(b,c,par,min),best=Infinity,occ=new Map();
 function walk(i,sum){if(sum>=best)return;if(i===n){best=sum;return}let start=Math.max(min,b[i]);start+=mod(par-start,2);for(let x=start;x<=20;x+=2){let o=occ.get(x)||0;if(o>=c)continue;occ.set(x,o+1);walk(i+1,sum+x-b[i]);occ.set(x,o)}}
 walk(0,0);ck(lo===best,"brute");s.synthetic++;s.syntheticBrute++;if(lo>Math.max(0,pack(b.map(()=>0),c,par,min)-b.reduce((a,x)=>a+x,0)))s.syntheticStrict++;
}
for(let R of [10000,40000,120000,250000])for(let mode of [0,1,2,3])for(let A=2*R-300+(6-(2*R-300)%6)%6;A<2*R;A+=6){
 let a=A,v=mode===0?-A/2+3:mode===1?0:mode===2?17:Math.floor(A/5),arr=[];
 function flush(){if(!arr.length)return;for(let t of [5,7,11,17,23])check(arr,t);s.blocks++;arr=[]}
 while(a>=R){let x=event(a,v);if(mode===0&&v+x.w>-1)break;if(x.q>Math.sqrt(a+1))flush();else arr.push({a,...x,fire:v+x.w});v+=x.w;a-=x.p-1;s.events++}flush();s.roots++;
}
return s
}
console.log(JSON.stringify(audit(),null,2));
