// Phase-release DP vs literal full-root record profits. Run with node. Finite proxy scales only.
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},mod=(a,b)=>((a%b)+b)%b;
 const Nmax=192002,sp=new Int32Array(Nmax+1);for(let p=2;p<=Nmax;p++)if(!sp[p]){sp[p]=p;if(p*p<=Nmax)for(let j=p*p;j<=Nmax;j+=p)if(!sp[j])sp[j]=p}
 const cache=new Map();
 function factors(n){const out=[];while(n>1){let p=sp[n];ok(p>0,"factor bound");out.push(p);while(n%p===0)n/=p}return out}
 function info(x){let a=cache.get(x);if(a)return a;let c=[...factors(x+1).map(p=>[p,0]),...factors(x-1).map(p=>[p,p+2])];a={c,q:Math.min(...c.map(z=>z[0])),twin:sp[x-1]===x-1&&sp[x+1]===x+1};cache.set(x,a);return a}
 function next(x,n){let f=Infinity,p0=0;for(const [p,c] of info(x).c){let w=mod(c-n,2*p)||2*p;if(w<f||(w===f&&p<p0)){f=w;p0=p}}return {f:n+f,p:p0}}
 function gap(x,f){let g=Infinity;for(const [p,c] of info(x).c)g=Math.min(g,mod(f-c,2*p)||2*p);return g}
 const D=48;
 function cost(x,f,p,K,Y,mode){if(mode==="old")return p<Y?102*(p-1):0;if(info(x).q>=K)return 0;let g=gap(x,f);return mode==="calendar"?D*g:Math.min(102*(p-1),D*g+1580)}
 function reward(n,obs,mode){return mode==="old"?D*Math.max(0,n-obs):D*n}
 let result=[];
 for(const [R,T,K,Y] of [[12000,96,5,24],[48000,192,9,48],[96000,384,13,96]]){
  let W=6*Math.floor(T/6),lo=Math.ceil(R/6)*6,windows=Math.floor((2*R-lo)/W)+1,rootCount=0,rows=[];
  for(const mode of ["old","calendar","hybrid","arrival","hybridArrival"]){
   let exact=0,sparse=0,bins=0,phaseCount=0,transitions=0,recordBins=0,sparseBins=0,rootChecks=0,ticks=0,roughMass=0,nonTwinMass=0,raw=0,lower=0,capUpper=0,phaseArrivalChecks=0,costChecks=0;
   for(let J=0;J<windows;J++){
    let a0=lo+J*W,a1=Math.min(2*R,a0+W-6),obs=3-a0/2,end=obs+T,first=3-a1/2;
    const full=new Map(),arrivalGap=new Map();
    // Full reachability preprocessing, independent of debts: earliest arrival at each completed physical phase.
    if(mode==='arrival'||mode==='hybridArrival')for(let A=a0;A<=a1;A+=6){let x=A,n=3-A/2;while(n<end){const e=next(x,n);if(e.f>end)break;const key=x+','+e.f;arrivalGap.set(key,Math.max(arrivalGap.get(key)||0,e.f-n));n=e.f;x-=e.p-1}}
    function charge(x,f,p){if(mode!=='arrival'&&mode!=='hybridArrival')return cost(x,f,p,K,Y,mode);if(info(x).q>=K)return 0;const g=arrivalGap.get(x+','+f);ok(g>0&&g<=gap(x,f),'actual phase gap');return mode==='arrival'?D*g:Math.min(102*(p-1),D*g+1580)}
    // Independent root-by-root computation of maximum record profit at each physical bin.
    for(let A=a0;A<=a1;A+=6){
     if(mode==="old")rootCount++;let x=A,b=3-A/2,last=b,debt=0,net=0,peak=0,oldCost=0,newCost=0,high=0,ep=next(x,b);
     for(let n=b;n<end;n++){
      const fired=ep.f===n+1,inc=fired?charge(x,n+1,ep.p):0,rew=reward(n+1,obs,mode)-reward(n,obs,mode);
      const profit=Math.max(0,rew-inc-debt);debt=Math.max(0,debt+inc-rew);net+=rew-inc;const peak1=Math.max(peak,net);ok(profit===peak1-peak&&debt===peak1-net,"reflected debt");peak=peak1;ticks++;
      if(profit){let k=x+","+n;full.set(k,Math.max(full.get(k)||0,profit))}
      if(fired){
       let g=gap(x,n+1);ok(n+1-last<=g&&g<=2*info(x).q,"calendar full wait bound");costChecks++;if(mode==='arrival'||mode==='hybridArrival')ok(n+1-last<=arrivalGap.get(x+','+(n+1)),'actual gap dominates every wait');
       if(mode==="hybrid"||mode==="hybridArrival"){const c0=cost(x,n+1,ep.p,K,Y,"old");oldCost+=c0;newCost+=inc;if(ep.p>=Y)high++;ok(ep.p>=Y||inc<=c0,"low cost dominance")}
       x-=ep.p-1;last=n+1;ep=next(x,last);
      }
     }
     if(mode==="hybrid"||mode==="hybridArrival")ok(newCost<=oldCost+high*(96*K+1580),"global cost comparison");
     raw+=peak;rootChecks++;
     let ini=next(A,b),j=Math.min(end,b+ini.f-b-1);if(mode!=="old"&&j>b)lower+=D*(j-b);
    }
    // Phase solver: calendar buckets contain only actual reached phase endings.
    const active=new Map(),bucket=Array.from({length:end-first+1},()=>[]),born=new Map();
    for(let A=a0;A<=a1;A+=6)born.set(3-A/2,A);
    function insert(x,n,lambda){
     ok(lambda>=reward(n,obs,mode),"arrival debt");let a=active.get(x);phaseArrivalChecks++;
     if(a){ok(n<a.end,"arrival before phase end");a.lambda=Math.min(a.lambda,lambda);return}
     let {f,p}=next(x,n),e=Math.min(f,end);a={x,f,p,end:e,lambda};active.set(x,a);bucket[e-first].push(a);
    }
    const record=new Map();
    for(let n=first;n<=end;n++){
     let arrivals=[];
     for(const a of bucket[n-first]){
      ok(active.get(a.x)===a,"phase uniqueness");active.delete(a.x);phaseCount++;
      let fires=a.f===n,lastIdle=fires?n-1:n,r=reward(lastIdle,obs,mode),lambda=a.lambda;
      const idle=Math.max(0,r-lambda);sparse+=idle;
      // Expand only positive-profit bins for exact independent matching.
      let start=mode==="old"?Math.max(obs,obs+Math.floor(lambda/D)):Math.floor(lambda/D);
      for(let t=start;t<lastIdle;t++){
       let r1=reward(t+1,obs,mode),r0=reward(t,obs,mode),p=Math.max(0,r1-Math.max(r0,lambda));
       if(p){record.set(a.x+","+t,p);sparseBins++}
      }
      if(fires){
       let c=charge(a.x,n,a.p),r1=reward(n,obs,mode),profit=Math.max(0,r1-r-c-Math.max(0,lambda-r));
       sparse+=profit;if(profit){record.set(a.x+","+(n-1),profit);sparseBins++}
       let out=Math.max(r1,r+c,lambda+c);
       ok(out===r1+Math.max(0,Math.max(0,lambda-r)+c-(r1-r)),"max-plus phase map");
       if(n<end)arrivals.push([a.x-a.p+1,out]);transitions++;
      }
     }
     if(n<end){for(const [x,lambda] of arrivals)insert(x,n,lambda);if(born.has(n))insert(born.get(n),n,reward(n,obs,mode))}
    }
    ok(active.size===0&&full.size===record.size,"all bins match");
    for(const [k,p] of full){ok(record.get(k)===p,"phase/full record exact");exact+=p;bins++;recordBins++;let x=Number(k.split(",")[0]);if(info(x).q>=K)roughMass+=p;if(!info(x).twin)nonTwinMass+=p}
    // Uniform finite rough upper by counting possible centers for this window.
    let possible=0;for(let x=a0-3*T-6;x<=a1;x+=2)if(info(x).q>=K)possible++;
    const N=(a1-a0)/6+1;
    capUpper+=D*(end-first)*possible+D*(2*K+1)*N;
   }
   ok(exact===sparse&&recordBins===sparseBins,"objective equality");
   if(mode==="calendar"||mode==="arrival"){ok(exact<=capUpper,"calendar rough upper");ok(exact>=lower,"disjoint birth idle lower")}
   rows.push({mode,exact,raw,normalized:exact/(D*rootCount*T),bins,phaseCount,transitions,rootChecks,ticks,roughMass,nonTwinMass,birthIdleLower:lower,capUpper,phaseArrivalChecks,costChecks});
  }
  const o=rows[0],h=rows[2];ok(h.exact+ D*rootCount*(3*T+6)/(Y-1)*(2*K+1580/D)>=o.exact,"hybrid optimum comparison");
  ok(rows[3].exact>=rows[1].exact&&rows[4].exact>=rows[2].exact,"arrival-gap objective dominance");result.push({R,T,K,Y,roots:rootCount,windows,rows});
 }
 return result
}
console.log(JSON.stringify(audit(),null,2));
