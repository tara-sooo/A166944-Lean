// Arbitrary gain-bounded medium relay inverse collision audit.
function audit(){
 const lim=4000300,spf=new Uint32Array(lim+1);
 for(let p=2;p*p<=lim;p++)if(!spf[p])for(let n=p*p;n<=lim;n+=p)if(!spf[n])spf[n]=p;
 const ck=(x,m)=>{if(!x)throw Error(m)},mod=(x,m)=>(x%m+m)%m;
 function fs(n){ck(n>=1&&n<=lim,"factor domain");let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function cand(x){return [[x-1,1],[x+1,-1]].flatMap(([n,e])=>fs(n).map(p=>({p,e,c:e===1?0:p+2})))}
 function ev(A,v){let p=Infinity,w=Infinity,e=0;for(let a of A){let t=mod(a.c-v,2*a.p)||2*a.p;if(t<w||t===w&&a.p<p){w=t;p=a.p;e=a.e}}return {p,w,e}}
 function gcd(a,b){while(b){let z=a%b;a=b;b=z}return Math.abs(a)}
 let rows=[];
 for(let [R,T,K,B,S] of [[100000,251,6,32,24],[100000,503,6,64,48],[1000000,503,6,64,48],[1000000,997,6,128,100]]){
  ck(3*B+S<T-2,"arrival separation");const byX=new Map(),cache=new Map();
  function A(x){let a=cache.get(x);if(!a){a=cand(x);cache.set(x,a)}return a}
  let s={R,T,K,B,S,arrivals:0,tailEvents:0,mediumTailEvents:0,maxTailEvents:0,maxMediumTailEvents:0,endpointIncidences:0,distinctEndpoints:0,offsets:0,ambiguousEndpoints:0,badOffsets:0,closePairs:0,samePhasePairs:0,differentPhasePairs:0,allMultipleOffsets:0,farMultipleOffsets:0,shortFibers:0,farMultipleFibers:0,maxFarFiber:0,roughChecks:0,linearChecks:0,exactArrivalLabelChecks:0,literalTicks:0,actualRoots:0,actualEvents:0,actualCovered:0,actualMediumCovered:0,actualDifferentPriorGroups:0,actualGoodGroups:0,example:null,farExample:null};
  for(let u=R;u<2*R;u+=2)for(let e of [1,-1]){
   for(let p of fs(u+(e===1?0:2))){
    if(p<T||p>2*T)continue;
    for(let a=1;a<=K;a++){
     let d=2*a*p+(e===1?0:6),v=(u+d)/2;if(d>2*K*T||v>u+1||mod(v,2*p)!==(e===1?0:p+2))continue;
     let z={u,v,p,e,a};s.arrivals++;
     let x=u,t=v,h=0,m=0;
     for(;;){
      let g=x-u,w=t-v,D=2*t-x;
      ck(g<=B&&w<=3*g&&D-d>=-g&&D-d<=5*g,"tail budget");ck(D>=0&&t<=x+1,"envelope");
      if(!byX.has(x))byX.set(x,[]);byX.get(x).push({v:t,z,h,m});s.endpointIncidences++;
      let r=ev(A(x),t);if(g+r.p-1>B)break;
      if(u<R+40){for(let i=1;i<=r.w;i++){let n=t+i,f=gcd(n%2?n-2:n,n%2?x+1:x-1);ck(i===r.w?(spf[f]||f)===r.p:f===1,"literal");s.literalTicks++}}
      s.tailEvents++;h++;if(r.p>11){s.mediumTailEvents++;m++}
      x+=r.p-1;t+=r.w;ck(h<=B/2,"tail depth");
     }
     s.maxTailEvents=Math.max(s.maxTailEvents,h);s.maxMediumTailEvents=Math.max(s.maxMediumTailEvents,m);
    }
   }
  }
  const bad=new Set();s.offsets=byX.size;
  for(let [x,list] of byX){
   list.sort((a,b)=>a.v-b.v);let close=false,groups=new Map(),numStates=0;
   let primes=A(x),q=Math.min(...primes.map(a=>a.p));
   for(let i=0;i<list.length;i++){
    let a=list[i];if(i===0||a.v!==list[i-1].v){numStates++;if(i+1<list.length&&a.v===list[i+1].v)s.ambiguousEndpoints++;}
    for(let j=i+1;j<list.length&&list[j].v-a.v<=S;j++){
     let b=list[j];ck(a.z.p!==b.z.p,"same label close");let c=a.z.a*a.z.p-b.z.a*b.z.p;
     ck(c!==0&&Math.abs(c)<=S+3*B+3,"close relation");
     ck((x-(x-a.z.u)+(a.z.e===1?0:2))%a.z.p===0,"offset residue");s.closePairs++;s.linearChecks++;close=true;
     if(a.v===b.v){s.samePhasePairs++;ck(Math.abs(c)<=3*B+3,"exact relation")}else s.differentPhasePairs++;
     if(!s.example&&a.v===b.v&&(a.m||b.m))s.example={x,v:a.v,a,b,c};
    }
    const r=ev(primes,a.v),n=a.v+r.w,L=n-Math.max(...primes.map(p=>n-1-mod(n-1-p.c,2*p.p)));
    ck(r.w<=L&&L<=2*q,"fiber");if(!groups.has(n))groups.set(n,{L,p:r.p,e:r.e,list:[]});groups.get(n).list.push(a);
   }
   s.distinctEndpoints+=numStates;if(close){bad.add(x);s.badOffsets++}
   let multiple=false,far=false;
   for(let [n,g] of groups){
    if(g.list.length>1)multiple=true;
    let U=x+g.p-1,D=2*n-U,s0=g.e===1?0:6;
    if(g.p>=T&&D>6&&D<=2*K*T){
     let d=(D-s0)/2;ck(d>0&&d%g.p===0&&fs(d).filter(p=>p>=T).length===1,"exact arrival label unique");s.exactArrivalLabelChecks++;
    }
    if(!close){
     let w=g.list.map(a=>n-a.v).sort((a,b)=>a-b);
     ck(w.filter(a=>a<=S+1).length<=1,"short fiber");s.shortFibers++;
     if(w.length>1){
      far=true;s.farMultipleFibers++;s.maxFarFiber=Math.max(s.maxFarFiber,w.length);
      ck(2*q>=S+2&&w.length<=1+Math.floor((g.L-1)/(S+1)),"far roughness");s.roughChecks++;
      for(let i=1;i<w.length;i++)ck(w[i]-w[i-1]>S,"phase spacing");
      if(!s.farExample&&q<Math.sqrt(x+1))s.farExample={x,n,p:g.p,q,L:g.L,waits:w};
     }
    }
   }
   if(multiple)s.allMultipleOffsets++;if(far)s.farMultipleOffsets++;
  }
  // Actual ordinary canonical roots; track every last high arrival until
  // physical tail gain exceeds B, without limiting number of medium events.
  let groups=new Map();
  for(let X=Math.ceil(R/6)*6;X<Math.min(R+60000,2*R);X+=6){
   let x=X,v=X/2+3,last=null,m=0;s.actualRoots++;
   while(x<X+4*T){
    let aa=A(x),r=ev(aa,v),n=v+r.w;if(fs(x-1)[0]===x-1&&fs(x+1)[0]===x+1)break;
    if(last&&x-last.u<=B){
     let list=byX.get(x)||[];ck(list.some(a=>a.v===v&&a.z.u===last.u&&a.z.v===last.v&&a.z.p===last.p&&a.z.e===last.e),"actual coverage");
     s.actualCovered++;if(m)s.actualMediumCovered++;
     let key=x+":"+n+":"+r.p;if(!groups.has(key))groups.set(key,new Set());groups.get(key).add(last.u+":"+last.v+":"+last.p);
    }
    let U=x+r.p-1,D=2*n-U,s0=r.e===1?0:6,a=(D-s0)/(2*r.p);
    if(r.p>=T){last=r.p<=2*T&&U>=R&&U<2*R&&a>=1&&a<=K&&D<=2*K*T?{u:U,v:n,p:r.p,e:r.e,a}:null;m=0}else if(r.p>11)m++;
    x=U;v=n;s.actualEvents++;
   }
  }
  for(let [key,g] of groups)if(g.size>1){s.actualDifferentPriorGroups++;if(!bad.has(Number(key.split(":")[0])))s.actualGoodGroups++}
  rows.push(s);
 }
 return rows;
}
console.log(JSON.stringify(audit(),null,2));
