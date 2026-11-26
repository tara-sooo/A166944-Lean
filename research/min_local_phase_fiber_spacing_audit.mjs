// Exact phase-fiber and compressed high-arrival spacing controls.
function audit(){
 const lim=4000300,spf=new Uint32Array(lim+1);
 for(let p=2;p*p<=lim;p++)if(!spf[p])for(let n=p*p;n<=lim;n+=p)if(!spf[n])spf[n]=p;
 const ck=(a,m)=>{if(!a)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function fs(n){ck(n>=1&&n<=lim,"factor range");let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function cand(x,low=false){return [[x-1,1],[x+1,-1]].flatMap(([n,e])=>(low?[3,5,7,11].filter(p=>n%p===0):fs(n)).map(p=>({p,e,c:e===1?0:p+2})))}
 function next(A,v){let p=Infinity,w=Infinity,e=0;for(let a of A){let t=mod(a.c-v,2*a.p)||2*a.p;if(t<w||t===w&&a.p<p){w=t;p=a.p;e=a.e}}return {p,w,e}}
 function prev(A,n){let last=-Infinity;for(let a of A)last=Math.max(last,n-1-mod(n-1-a.c,2*a.p));return last}
 function gcd(a,b){while(b){let z=a%b;a=b;b=z}return Math.abs(a)}
 let rows=[];
 for(let [R,T,K,S] of [[100000,251,6,24],[100000,503,6,48],[1000000,503,6,64],[1000000,997,6,100],[100000,503,60,64]]){
  ck(S+135<T,"phase spacing hypothesis");
  const byX=new Map(),s={R,T,K,S,arrivals:0,relayEndpoints:0,sourceOffsets:0,badOffsets:0,closePairs:0,distinctPhaseClosePairs:0,samePhaseClosePairs:0,phaseFibers:0,multipleFibers:0,goodMultipleFibers:0,goodShortFiberChecks:0,maxGoodFiber:0,maxGap:0,maxGoodWaitSum:0,largeGapMultipleOffsets:0,roughIncomingOffsets:0,allMultipleOffsets:0,roughnessChecks:0,spacingChecks:0,literalClockTicks:0,actualRoots:0,actualEvents:0,actualCovered:0,actualMergeGroups:0,actualDifferentPriorGroups:0,actualGoodMultiple:0,example:null,actualExample:null};
  for(let u=R;u<2*R;u+=2)for(let e of [1,-1]){
   let s0=e===1?0:6;for(let p of fs(u+(e===1?0:2))){
    if(p<T||p>2*T)continue;
    for(let a=1;a<=K;a++){
     let d=2*a*p+s0,v=(u+d)/2;if(v>u+1||mod(v,2*p)!==(e===1?0:p+2))continue;
     let z={u,v,p,e,a};s.arrivals++;let x=u,t=v;
     for(let j=0;;j++){
      let dd=2*t-x;
      if(dd>198&&dd<=2*K*T){
       ck(x-u<=104&&t-v<=133&&dd-d>=-16&&dd-d<=192,"relay bounds");
       if(!byX.has(x))byX.set(x,[]);byX.get(x).push({v:t,z});s.relayEndpoints++;
      }
      let q=next(cand(x,true),t);if(!isFinite(q.p))break;x+=q.p-1;t+=q.w;ck(j<25,"relay count");
     }
    }
   }
  }
  s.sourceOffsets=byX.size;const bad=new Set(),multi=new Set();
  for(let [x,list] of byX){
   list.sort((a,b)=>a.v-b.v);let close=false;const A=cand(x),q=Math.min(...A.map(a=>a.p)),groups=new Map();
   if(2*q>=S+2)s.roughIncomingOffsets++;
   for(let i=0;i<list.length;i++){
    let a=list[i];
    for(let j=i+1;j<list.length&&list[j].v-a.v<=S;j++){
     let b=list[j];ck(a.z.p!==b.z.p,"same-label near phases");let c=a.z.a*a.z.p-b.z.a*b.z.p;ck(c!==0&&Math.abs(c)<=S+107,"linear bound");s.closePairs++;if(a.v===b.v)s.samePhaseClosePairs++;else s.distinctPhaseClosePairs++;close=true;
    }
    const z=next(A,a.v),n=a.v+z.w,l=n-prev(A,n);
    ck(l>=z.w&&l<=2*q,"clock fiber");s.maxGap=Math.max(s.maxGap,l);
    if(x<R+80){
     for(let t=n-l;t<=n;t++){
      let g=gcd(t%2?t-2:t,t%2?x+1:x-1);ck(t===n||t===n-l?g>1:g===1,"literal gap");
      if(t===n)ck((spf[g]||g)===z.p,"tie");s.literalClockTicks++;
     }
    }
    if(!groups.has(n))groups.set(n,{l,p:z.p,items:[]});let g=groups.get(n);ck(g.l===l&&g.p===z.p,"fiber identity");g.items.push(a);
   }
   if(close){bad.add(x);s.badOffsets++}
   let anyMulti=false,farMulti=false;
   for(let [n,g] of groups){
    s.phaseFibers++;let N=g.items.length;if(N<=1)continue;
    s.multipleFibers++;anyMulti=true;
    if(!close){
     farMulti=true;s.goodMultipleFibers++;s.maxGoodFiber=Math.max(s.maxGoodFiber,N);
     let waits=g.items.map(a=>n-a.v).sort((a,b)=>a-b);
     for(let i=1;i<N;i++){ck(waits[i]-waits[i-1]>=S+1,"separation");s.spacingChecks++}
     ck(N<=1+Math.floor((g.l-1)/(S+1)),"fiber degree");
     let sum=waits.reduce((a,b)=>a+b,0);ck(sum>=N+(S+1)*N*(N-1)/2,"wait charge");
     ck(waits.filter(w=>w<=S+1).length<=1,"short inverse");
     ck(2*q>=S+2,"large gap roughness");s.roughnessChecks++;s.maxGoodWaitSum=Math.max(s.maxGoodWaitSum,sum);
     if(!s.example)s.example={x,n,p:g.p,q,l:g.l,waits,prior:g.items.map(a=>a.z)};
    }
   }
   if(anyMulti){multi.add(x);s.allMultipleOffsets++}
   if(farMulti)s.largeGapMultipleOffsets++;
   if(!close){for(let [n,g] of groups){ck(g.items.filter(a=>n-a.v<=S+1).length<=1,"short unique");s.goodShortFiberChecks++}}
  }
  // Actual MIN paths with a recorded previous high arrival and <=11 relay.
  // Count genuinely different prior states at the SAME outgoing event.
  let actual=new Map();
  for(let X=Math.ceil(R/6)*6;X<Math.min(R+60000,2*R);X+=6){
   s.actualRoots++;let x=X,v=X/2+3,last=null;
   while(x<X+4*T){
    let A=cand(x),z=next(A,v),n=v+z.w;let twin=fs(x-1)[0]===x-1&&fs(x+1)[0]===x+1;if(twin)break;
    let d=2*v-x;
    if(last&&d>198&&d<=2*K*T){
     let list=byX.get(x)||[];ck(list.some(a=>a.v===v&&a.z.u===last.u&&a.z.v===last.v&&a.z.p===last.p&&a.z.e===last.e),"actual prefix covered");s.actualCovered++;
     let key=x+":"+n+":"+z.p;if(!actual.has(key))actual.set(key,new Map());let g=actual.get(key);let k=last.u+":"+last.v+":"+last.p;if(!g.has(k))g.set(k,{last,v,X});
    }
    let U=x+z.p-1,V=n,dd=2*V-U,s0=z.e===1?0:6,a=(dd-s0)/(2*z.p);
    if(z.p>=T&&z.p<=2*T&&U>=R&&U<2*R&&a>=1&&a<=K)last={u:U,v:V,p:z.p,e:z.e,a};else if(z.p>11)last=null;
    x=U;v=V;s.actualEvents++;
   }
  }
  for(let [key,g] of actual){s.actualMergeGroups++;if(g.size>1){s.actualDifferentPriorGroups++;let [x,n,p]=key.split(":").map(Number);if(!bad.has(x)){s.actualGoodMultiple++;let w=[...g.values()].map(a=>n-a.v).sort((a,b)=>a-b);for(let i=1;i<w.length;i++)ck(w[i]-w[i-1]>S,"actual spacing")}if(!s.actualExample)s.actualExample={key,prior:[...g.values()]}}}
  rows.push(s);
 }
 return rows;
}
console.log(JSON.stringify(audit(),null,2));
