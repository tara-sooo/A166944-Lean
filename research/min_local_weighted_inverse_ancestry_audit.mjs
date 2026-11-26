// Weighted inverse ancestry: actual local traffic and independently enumerated relaxed inverse kernels.
function audit(){
 const maxR=1000000,lim=4*maxR+100,spf=new Uint32Array(lim+1);
 for(let p=2;p*p<=lim;p++)if(!spf[p])for(let n=p*p;n<=lim;n+=p)if(!spf[n])spf[n]=p;
 const ck=(a,m)=>{if(!a)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function fs(n){ck(n>0&&n<=lim,"factor domain");let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function gcd(a,b){while(b){let z=a%b;a=b;b=z}return Math.abs(a)}
 function ev(x,v){let f=fs(x-1),g=fs(x+1),p=Infinity,w=Infinity,e=0;for(let [A,s] of [[f,1],[g,-1]])for(let r of A){let z=mod((s===1?0:r+2)-v,2*r)||2*r;if(z<w||z===w&&r<p){w=z;p=r;e=s}}return {p,w,e,q:Math.min(f[0],g[0]),twin:f[0]===x-1&&g[0]===x+1}}
 let out=[];
 for(let [R,T,D,M] of [[10000,53,200,16],[100000,157,633,48],[100000,251,633,64],[1000000,503,2000,64],[1000000,997,2000,128]]){
   const H=Math.floor((D-1)/(T-1)),B=Math.max(1,Math.ceil(M/(H+1))),J=2*Math.ceil(Math.log(3*R+2)/Math.log(T)),C=4*J*(B+2)/3;
   const bound=2*(B+2)*Math.pow(C,H)*Math.pow(2,(3.5*D+1)/T+M/B);
   const stats={R,T,D,M,H,B,J,C,log2Bound:Math.log2(bound),roots:0,events:0,highEvents:0,lowEvents:0,budgetStops:0,twinStops:0,exitStops:0,totalWait:0,maxRootWait:0,maxRootLowGain:0,maxPriorHigh:0,maxExecutedHigh:0,maxMass:0,maxFirstHighMass:0,maxHighEntranceDiversity:0,distinctOffsets:0,markedArrivalStates:0,weightedOffsetCells:0,weightedArrivalCells:0,costChecks:0,branchChecks:0,entryChecks:0,literalTicks:0,maxBranchRatio:0,ambientQ:0,weightedQ:0,example:null};
   const offsets=new Map(),arrivals=new Map(),firstMass=new Map();
   function add(map,key,h,weight){let a=map.get(key);if(!a){a={count:0,weights:new Map(),first:new Set()};map.set(key,a)}a.count++;a.weights.set(h,(a.weights.get(h)||0)+weight);return a}
   for(let x=R+R%2;x<2*R+D;x+=2){let a=fs(x-1),b=fs(x+1);if(a[0]!==x-1||b[0]!==x+1)stats.ambientQ+=Math.min(a[0],b[0])}
   for(let X=Math.ceil(R/6)*6;X<2*R;X+=6){
    stats.roots++;let x=X,v=X/2+3,v0=v,low=0,h=0,cost=0,lastU=X,lastV=v,first=null,wait=0;
    while(x<X+D){
     let z=ev(x,v);if(z.twin){stats.twinStops++;break}
     if(z.p<T&&low+z.p-1>M){stats.budgetStops++;break}
     ck(h<=H&&low<=M&&x-X<D,"prefix budget");stats.maxPriorHigh=Math.max(stats.maxPriorHigh,h);
     let nstar=x/2+3*D+4,tail=x-lastU;
     ck(nstar>v&&v>=lastV&&tail>=0,"dummy clock");
     let c=cost+Math.floor((nstar-lastV)/T)+Math.floor(tail/B);
     ck(c<=(nstar-v0)/T+low/B+1e-10,"offset cost");stats.costChecks++;
     let a=add(offsets,x,h,Math.pow(2,-c));if(first!==null)a.first.add(first);
     stats.maxMass=Math.max(stats.maxMass,a.count);stats.maxHighEntranceDiversity=Math.max(stats.maxHighEntranceDiversity,a.first.size);
     if(a.count>=(stats.example?.count||0))stats.example={x,count:a.count,q:z.q,h,low,firstDiversity:a.first.size};
     ck(z.w<=2*z.q,"clock cap");stats.totalWait+=z.w;stats.weightedQ+=z.q;wait+=z.w;
     if(X<R+36&&z.w<=1000){for(let i=1;i<=z.w;i++){let n=v+i,d=gcd(n%2?n-2:n,n%2?x+1:x-1);ck(i===z.w?(spf[d]||d)===z.p:d===1,"literal");stats.literalTicks++}}
     let U=x+z.p-1,V=v+z.w;
     if(z.p>=T){
      let E=x-lastU;cost+=Math.floor((V-lastV)/T)+Math.floor(E/B);
      ck(cost<=(V-v0)/T+low/B+1e-10,"marked cost");stats.costChecks++;
      ck((U+(z.e===1?0:2))%z.p===0&&mod(V,2*z.p)===(z.e===1?0:z.p+2),"marked residue");
      h++;stats.highEvents++;stats.maxExecutedHigh=Math.max(stats.maxExecutedHigh,h);
      let key=U+":"+V+":"+z.p+":"+z.e;
      add(arrivals,key,h,Math.pow(2,-cost));
      if(first===null){first=key;firstMass.set(key,(firstMass.get(key)||0)+1);stats.maxFirstHighMass=Math.max(stats.maxFirstHighMass,firstMass.get(key))}
      lastU=U;lastV=V;
     }else{low+=z.p-1;stats.lowEvents++}
     x=U;v=V;stats.events++;
    }
    if(x>=X+D)stats.exitStops++;
    stats.maxRootWait=Math.max(stats.maxRootWait,wait);stats.maxRootLowGain=Math.max(stats.maxRootLowGain,low);
   }
   for(let [x,a] of offsets){ck(a.count<=bound,"mass bound");for(let [h,w] of a.weights){ck(w<=(B+2)*Math.pow(C,h)+1e-8,"offset partition");stats.weightedOffsetCells++}}
   for(let a of arrivals.values())for(let [h,w] of a.weights){ck(w<=(B+2)*Math.pow(C,h-1)+1e-8,"marked partition");stats.weightedArrivalCells++}
   stats.distinctOffsets=offsets.size;stats.markedArrivalStates=arrivals.size;
   // Independent relaxation of a single inverse step: enumerate every
   // high-marked predecessor in the entire tested physical window and
   // every envelope-admissible earlier phase in its exact clock class.
   const targets=[...offsets.entries()].sort((a,b)=>b[1].count-a[1].count).slice(0,20).map(a=>a[0]);
   for(let x of targets){
    let n=x/2+3*D+4,weight=0,entry=0;
    for(let u=Math.max(R+R%2,x-D+(D%2));u<=x;u+=2){
     let E=x-u,eg=Math.floor(E/B);
     if(u%6===0){let v=u/2+3;entry+=Math.pow(2,-eg-Math.floor((n-v)/T))}
     let a=0;
     for(let [N,e] of [[u,1],[u+2,-1]])for(let p of fs(N))if(p>=T){
      a++;let c=e===1?0:p+2,L=u/2,U=Math.min(u+1,n-1),v=L+mod(c-L,2*p),s=0;
      for(;v<=U;v+=2*p)s+=Math.pow(2,-Math.floor((n-v)/T));
      ck(s<=4/3+1e-12,"per-label geometric");weight+=Math.pow(2,-eg)*s;
     }
     ck(a<=J,"factor-count bound");
    }
    ck(weight<=C+1e-10,"relaxed inverse partition");ck(entry<=B+2+1e-10,"root entry partition");
    stats.maxBranchRatio=Math.max(stats.maxBranchRatio,weight/C);stats.branchChecks++;stats.entryChecks++;
   }
   ck(stats.budgetStops+stats.twinStops+stats.exitStops===stats.roots,"stop partition");
   ck(stats.totalWait<=2*stats.weightedQ&&stats.weightedQ<=stats.maxMass*stats.ambientQ,"ambient traffic");
   out.push(stats);
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
