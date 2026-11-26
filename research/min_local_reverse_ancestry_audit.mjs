// Offset-only reverse ancestry, actual MIN prefix traffic, and compressed relay diagnostics.
function audit(maxR=1000000){
 const limit=4*maxR+Math.ceil(8*Math.sqrt(maxR))+20,spf=new Uint32Array(limit+1);
 for(let p=2;p*p<=limit;p++)if(!spf[p])for(let n=p*p;n<=limit;n+=p)if(!spf[n])spf[n]=p;
 function fs(n){if(n>limit)throw Error("factor domain "+n);let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p;}return a}
 function gcd(x,y){while(y){let z=x%y;x=y;y=z}return Math.abs(x)}
 function check(x,m){if(!x)throw Error(m)}
 const mod=(x,m)=>(x%m+m)%m;
 function event(u,v){let A=fs(u-1),B=fs(u+1),p=Infinity,w=Infinity,e=0;for(let [f,s] of [[A,1],[B,-1]])for(let q of f){let z=mod((s===1?0:q+2)-v,2*q)||2*q;if(z<w||z===w&&q<p){p=q;w=z;e=s}}return {p,w,e,twin:A[0]===u-1&&B[0]===u+1}}
 function pred(U){let a=[];for(let [n,e] of [[U,1],[U+2,-1]])for(let p of fs(n))if(p>=3&&U-p+1>=2)a.push({x:U-p+1,p,e});return a}
 function rootsFor(y,R,D,T,m,H){
  let lo=Math.max(R,y-D+1),hi=Math.min(2*R-1,y),found=new Set(),seen=new Set(),stack=[[y,0,0]];
  while(stack.length){
   let [u,h,j]=stack.pop(),key=u+":"+h+":"+j;if(seen.has(key))continue;seen.add(key);
   for(let x=u;x>=Math.max(lo,u-104);x-=2){
    if(x<=hi&&x%6===0)found.add(x);
    for(let a of pred(x)){
     if(a.x<lo||a.p<=11)continue;
     if(a.p>=T&&h<H)stack.push([a.x,h+1,j]);
     else if(a.p<T&&j<m)stack.push([a.x,h,j+1]);
    }
   }
  }
  return {found,states:seen.size}
 }
 let result=[];
 for(let R of [10000,100000,1000000].filter(x=>x<=maxR)){
  let D=Math.ceil(4*Math.sqrt(R)),T=Math.ceil(Math.sqrt(R)/2),m=4,H=Math.ceil(D/(T-1)),q0=(T-1)/16;
  let stats={R,D,T,m,H,roots:0,events:0,twinStarts:0,twinStops:0,nonTwinExits:0,lowMediumExits:0,lowMediumExitsWithSignificantHigh:0,earlySignificantRoots:0,allSignificantRoots:0,earlySignificantVisits:0,earlyHighWait:0,earlyAllWait:0,allHighWait:0,lateHighWait:0,mediumCounts:{},maxEarlyMultiplicity:0,roughOffsets:0,maxOffsetDegree:0,actualReverseChecks:0,literalTicks:0,lowRelayChecks:0,reverseControls:[]};
  let carriers=new Map();
  for(let u=R+(R%2);u<2*R+D;u+=2){
   let f=fs(u-1),g=fs(u+1);if(Math.min(f[0],g[0])>=q0)stats.roughOffsets++;
   stats.maxOffsetDegree=Math.max(stats.maxOffsetDegree,pred(u).length);
  }
  for(let X=Math.ceil(R/6)*6;X<2*R;X+=6){
   stats.roots++;let u=X,v=X/2+3,j=0,h=0,lowGain=0,lowWait=0,early=false,any=false,twin=false;
   while(u<X+D){
    let {p,w,e,twin:t}=event(u,v);
    if(t){twin=true;stats.twinStops++;if(u===X)stats.twinStarts++;break}
    stats.events++;let U=u+p-1;
    check(pred(U).some(a=>a.x===u&&a.p===p&&a.e===e),"reverse identity "+JSON.stringify({X,u,v,U,p,w,e,pred:pred(U)}));stats.actualReverseChecks++;
    if(X<R+60&&w<1000){for(let k=1;k<=w;k++){let n=v+k,g=gcd(n%2?n-2:n,n%2?u+1:u-1);check(k===w?(spf[g]||g)===p:g===1,"literal");stats.literalTicks++}}
    if(p<=11){lowGain+=p-1;lowWait+=w;check(lowGain<=104&&lowWait<=133,"relay bound");stats.lowRelayChecks++}else{lowGain=lowWait=0}
    if(p>11&&p<T)j++;
    if(j<=m)stats.earlyAllWait+=w;
    if(p>=T){
     stats.allHighWait+=w;
     if(j<=m){
      stats.earlyHighWait+=w;check(h<=H,"high count before source");
      if(8*w>=p-1){
       early=true;stats.earlySignificantVisits++;check(Math.min(fs(u-1)[0],fs(u+1)[0])>=q0,"roughness");
       if(!carriers.has(u))carriers.set(u,new Set());carriers.get(u).add(X);
      }
     }else stats.lateHighWait+=w;
     if(8*w>=p-1)any=true;h++;
    }
    u=U;v+=w;check(2*v>=u&&v<=u+1,"envelope");
   }
   if(early)stats.earlySignificantRoots++;if(any)stats.allSignificantRoots++;
   if(!twin){stats.nonTwinExits++;if(j<=m){stats.lowMediumExits++;if(early)stats.lowMediumExitsWithSignificantHigh++}}
   let key=j>20?">20":String(j);stats.mediumCounts[key]=(stats.mediumCounts[key]||0)+1;
  }
  stats.earlySignificantOffsets=carriers.size;stats.maxEarlyMultiplicity=0;for(let s of carriers.values())stats.maxEarlyMultiplicity=Math.max(stats.maxEarlyMultiplicity,s.size);
  let top=[...carriers.entries()].sort((a,b)=>b[1].size-a[1].size).slice(0,2);
  for(let [u,actual] of top){let reverse=rootsFor(u,R,D,T,m,H);for(let X of actual)check(reverse.found.has(X),"actual root missing");stats.reverseControls.push({u,actual:actual.size,relaxed:reverse.found.size,states:reverse.states})}
  result.push(stats)
 }
 return {maxR,result};
}
console.log(JSON.stringify(audit(Number(process.argv[2]||1000000)),null,2));
