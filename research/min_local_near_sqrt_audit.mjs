// Near-square-root local crossing diagnostic. No asymptotic inference.
function shortAudit(limit=1000000) {
 const spf=new Uint32Array(2*limit+3);
 for(let p=3;p*p<spf.length;p+=2)if(!spf[p])for(let n=p*p;n<spf.length;n+=2*p)if(!spf[n])spf[n]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 const mod=(a,b)=>(a%b+b)%b;
 function event(u,v){let f=fs(u-1),g=fs(u+1),w=Infinity,p=Infinity;for(let [ar,s] of [[f,0],[g,1]])for(let q of ar){let k=mod((s?q+2:0)-v,2*q)||2*q;if(k<w||k===w&&q<p){w=k;p=q}}return {w,p,twin:f[0]===u-1&&g[0]===u+1,q:Math.min(f[0],g[0])}}
 const gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return Math.abs(a)};
 function check(c,m){if(!c)throw Error(m)}
 const widths={power:x=>Math.ceil(x**.75),near:x=>Math.ceil(Math.sqrt(x)*Math.exp(Math.log(Math.log(x))**.75)),log:x=>Math.ceil(Math.sqrt(x)*Math.log(x)),sqrt:x=>Math.ceil(Math.sqrt(x))};
 let results=[],literalChecks=0,ambientChecks=0,capacityMax=[];
 for(let [lo,hi] of [[10000,20000],[100000,200000],[500000,1000000]]){
  if(hi>limit)continue;
  for(let [mode,Dfn] of Object.entries(widths)){
   let stats={mode,lo,hi,seeds:0,twinStart:0,twinLater:0,noTwin:0,old:0,relaxed:0,events:0,meanD:0,minFreeK:null,maxFreeWOverD:0};
   for(let X=Math.ceil(lo/6)*6;X<=hi;X+=6){
    let D=Dfn(X),u=X,v=X/2+3,first=-1,k=0,freq=new Map(),high=new Set(),Wnon=0;
    check(D<X,"width");
    while(u<X+D){
     const {p,w,twin,q}=event(u,v);
     check(w<=2*Math.min(p,q),"clock bound");
     if(!twin){check(w*w<=4*(u+1),"non-twin bound");Wnon+=w}
     if(twin&&first<0)first=k;
     if(X<lo+60&&k<10&&w<=5000){
      for(let j=1;j<=w;j++){let n=v+j,d=gcd(n%2?n-2:n,n%2?u+1:u-1);check(j===w?(spf[d]||d)===p:d===1,"literal");literalChecks++}
     }
     freq.set(p,(freq.get(p)||0)+1);if(p**8>=X&&4*w>=p-1)high.add(p);
     u+=p-1;v+=w;k++;check(2*v>=u&&v<=u+1,"envelope");
    }
    stats.seeds++;stats.events+=k;stats.meanD+=D;
    let K=Math.floor(.9*Math.log2(Math.log(X))),L=0;
    for(let [p,n] of freq)if(p**8<X&&n**8>X)L++;
    if(first===0)stats.twinStart++;else if(first>0)stats.twinLater++;else{stats.noTwin++;check(2*Wnon>=D-6,"lower");stats.minFreeK=stats.minFreeK===null?freq.size:Math.min(stats.minFreeK,freq.size);stats.maxFreeWOverD=Math.max(stats.maxFreeWOverD,Wnon/D)}
    if(first!==0){if(freq.size<=K)stats.old++;if(L<=K&&high.size<=3)stats.relaxed++}
   }
   stats.meanD=Math.round(stats.meanD/stats.seeds);results.push(stats);
  }
  // Ambient capacity at fixed intervals; all even non-twin offsets, no reachability weighting.
  let R=lo,D=widths.near(R),L=D/Math.sqrt(R),cap=new Map();
  for(let u=Math.ceil(R/2)*2;u<R+D;u+=2){
   let f=fs(u-1),g=fs(u+1);if(f[0]===u-1&&g[0]===u+1)continue;
   let q=Math.min(f[0],g[0]);
   for(let p of [...f,...g])cap.set(p,(cap.get(p)||0)+2*Math.min(p,q));
  }
  let maxLow=0,maxHigh=0,maxTail=0,low=0,high=0,tail=0;
  for(let [p,c] of cap){
   if(p<=Math.sqrt(R)*Math.sqrt(L)){
    let z=Math.min(p,D/p),ratio=c*Math.log(2+z)**2/D;
    if(p<Math.log(R)){low++;maxLow=Math.max(maxLow,ratio)}else{high++;maxHigh=Math.max(maxHigh,ratio)}
   }else{tail++;maxTail=Math.max(maxTail,c*Math.sqrt(L)/D)}
   ambientChecks++;
  }
  capacityMax.push({R,D,L,low,high,tail,maxLow,maxHigh,maxTail});
 }
 return {limit,results,literalChecks,ambientChecks,capacityMax};
}
console.log(JSON.stringify(shortAudit(Number(process.argv[2]||1000000)),null,2));
