// Root-biased exact absorption/preemption identity: finite conditional sampling.
function audit(){
 const ck=(b,m)=>{if(!b)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p;
 const MAX=98304,Z=2*Math.floor(9*MAX/4+8)+7,spf=new Uint32Array(Z+1),pr=[];
 for(let p=2;p*p<=Z;p++)if(!spf[p])for(let x=p*p;x<=Z;x+=p)if(!spf[x])spf[x]=p;
 for(let p=3;p<=Z;p+=2)if(!spf[p])pr.push(p);
 let seed=0xf3918e27;function u32(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0}
 function unif(n){let M=Math.floor(4294967296/n)*n,x;do{x=u32()}while(x>=M);return x%n}
 function roughRes(p){let n=unif(p-2);return n===0?0:n+1}
 const cap=g=>Math.floor(9*g/4+8);
 let out={samples:0,absorbed:0,overBudget:0,events:0,hazardTicks:0,hazardFactorChecks:0,hazardUniqueChecks:0,hazardBoundChecks:0,exactPreemptionChecks:0,jointHazardChecks:0,restrictedGainChecks:0,rows:[]};
 function factors(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 for(let [L,samples] of [[96,4096],[384,3072],[1536,2048],[6144,1024],[24576,512],[98304,256]]){
  let z=L+1,limit=2*cap(L)+7,P=pr.filter(p=>p<=z),V=P.filter(p=>p>=5).reduce((s,p)=>s*(1-2/p),1),row={L,z,samples,absorb:0,gainSum:0,timeSum:0,maxHeightSum:0,highSurvivalSum:0,minSurvival:1,meanHazardSum:0,maxHazard:0,actualNoPreempt:0,fullSuccess:0,shortGain:0,highHeight:0,cap:[]};
  let buckets=[1/16,1/8,1/4,1/2,1].map(f=>({f,n:0,w:0}));
  for(let s=0;s<samples;s++){
   let parity=unif(2),res=new Int32Array(limit+1),clock=new Int32Array(z+1),heads=new Int32Array(L/2+1).fill(-1),ep=[],ec=[],en=[];
   function add(i,p,c){en.push(heads[i]);ep.push(p);ec.push(c);heads[i]=ep.length-1}
   for(let p of P){let r=p===3?0:unif(p);res[p]=r;let x=mod(r*((p+1)/2),p);if(mod(x,2)!==parity)x+=p;clock[p]=x;
    for(let e of [-1,1]){let i0=mod((r-e)*((p+1)/2),p);for(let i=i0;i<heads.length;i+=p)add(i,p,e===-1?0:p+2)}
   }
   let G=0,t=0,h=3,maxH=3,path=[],success=false;
   while(true){let p0=0,w0=Infinity,i=G/2;
    for(let k=heads[i];k>=0;k=en[k]){let p=ep[k],w=mod(clock[p]+ec[k]-(3+t),2*p)||2*p;if(w<w0||w===w0&&p<p0){p0=p;w0=w}}
    if(!p0){success=true;break}if(G+p0-1>L)break;
    path.push({G,t,h,p:p0,w:w0});t+=w0;G+=p0-1;maxH=Math.max(maxH,h+w0);h+=w0-(p0-1)/2;out.events++;
    ck(h===3+t-G/2&&h>=0&&t<=cap(G),"restricted gain invariant");out.restrictedGainChecks++;
   }
   out.samples++;if(!success){out.overBudget++;continue}
   ck(G%6===0&&h>=0,"canonical absorber");row.absorb++;out.absorbed++;row.gainSum+=G;row.timeSum+=t;row.maxHeightSum+=maxH;if(G<=L/4)row.shortGain++;if(maxH>(z-1)/2)row.highHeight++;
   let B=new Map(),tests=0;
   for(let e of path){let d=G-e.G;for(let u=1;u<e.w;u++){
     let b=e.h+u,np=mod(3+e.t+u-parity,2),f=Math.abs(np?2*b-5:2*b+1);out.hazardTicks++;
     let count=0;for(let p of factors(f))if(p>z){
      count++;let r=mod(-d+(np?1:-1),p);
      if(r===1||r===p-1)continue;let S=B.get(p)||new Set();S.add(r);B.set(p,S);tests++;
     }
     ck(count<=1,"one omitted factor");out.hazardFactorChecks++;
   }}
   let prob=1,lambda=0;
   for(let [p,S] of B){ck(S.size<=G/2+1&&S.size/(p-2)<=2/3+1e-9,"offset denominator");out.hazardUniqueChecks++;lambda+=S.size/(p-2);prob*=1-S.size/(p-2)}
   ck(lambda<=cap(G)/L+1e-9&&prob>=Math.exp(-3*lambda)-1e-12&&prob>=Math.exp(-11)-1e-12,"uniform preemption lower");out.hazardBoundChecks++;
   row.highSurvivalSum+=prob;row.minSurvival=Math.min(row.minSurvival,prob);row.meanHazardSum+=lambda;row.maxHazard=Math.max(row.maxHazard,lambda);
   for(let b of buckets)if(G<=b.f*L){b.n++;b.w+=prob}
   // Independent high-coordinate completion conditioned on the
   // restricted endpoint being rough, with an exact tick replay.
   let sampled=new Map();for(let p of pr){if(p>limit)break;if(p>z){let r=roughRes(p);sampled.set(p,r);res[p]=mod(r+G,p)}}
   let no=true;for(let [p,S] of B)if(S.has(sampled.get(p)))no=false;
   if(no)row.actualNoPreempt++;
   let gg=0,hh=3;
   for(let tt=0;tt<cap(G)&&gg<G;tt++){
    let b=hh+1,np=mod(3+tt+1-parity,2),f=Math.abs(np?2*b-5:2*b+1),p=1;
    for(let q of factors(f))if(mod(res[q]-gg+(np?-1:1),q)===0){p=q;break}
    gg+=p-1;hh=b-(p-1)/2;
   }
   let hit=gg===G;ck(hit===no,{L,G,hit,no});out.exactPreemptionChecks++;if(hit)row.fullSuccess++;
  }
  row.restrictedFraction=row.absorb/samples;row.mu1Estimate=row.highSurvivalSum/(samples*V);row.invV=1/V;row.survivalConditional=row.highSurvivalSum/row.absorb;row.meanGainConditional=row.gainSum/row.absorb;row.meanMaxHeightConditional=row.maxHeightSum/row.absorb;row.meanHazardConditional=row.meanHazardSum/row.absorb;row.cap=buckets.map(b=>({...b,fraction:b.n/samples,weightedFraction:b.w/samples}));out.rows.push(row);
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
