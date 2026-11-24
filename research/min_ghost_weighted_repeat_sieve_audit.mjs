// Gain-capped weighted repeat candidates and first-selection stride ledger.
function audit(U,N=256){
 const V=4*U,root=Math.ceil(Math.sqrt(2*U)),z=Math.max(root,Math.ceil(U/Math.log(U)**2.5)),K=Math.max(2,Math.floor(Math.log(U)**.8)),q0=Math.max(11,Math.floor(Math.sqrt(U)/4)),sieve=new Uint8Array(V+1),ps=[];
 for(let p=2;p<=V;p++)if(!sieve[p]){if(p>2)ps.push(p);if(p*p<=V)for(let q=p*p;q<=V;q+=p)sieve[q]=1}
 const mod=(x,p)=>(x%p+p)%p,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x143b0e4d^U)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let a=4294967296-4294967296%p,x;do{x=u32()}while(x>=a);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),first=new Int32Array(ps.length),ranges=[q0,root,z],out={U,V,N,root,z,K,q0,events:0,checks:0,blocks:0,peakSum:0,freshWaitSum:0};
 out.ranges=ranges.map(q=>({q,firsts:0,candidates:0,candidateWeight:0,localCandidates:0,localCandidateWeight:0,longReturns:0,longWeight:0,longWait:0,localLong:0,localWeight:0,localWait:0,distantLong:0,blockPositive:0,localBlockPositive:0,shortBlockChecks:0,pathsWithLong:0}));
 function rough(p,g){for(let i=0;i<ps.length&&ps[i]<=47&&8*ps[i]<=p;i++)if([1,ps[i]-1].includes(mod(c[i]+g,ps[i])))return false;return true}
 for(let k=0;k<N;k++){
  let parity=uni(2);first.fill(-1);let lists=new Map();
  for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let x=uni(p);t[i]=x%2===parity?x:x+p;}
  const path=ranges.map(q=>({q,cand:0,localCand:0,long:0,local:0,weight:0,localWeight:0,wait:0,localWait:0,bpos:0,localBpos:0}));let e=0,g=0,peak=0,fw=0,block=null;
  function close(){if(!block||!block.repeat||block.p<q0||block.g>2*U||block.p<62)return;let b=Math.max(0,block.delta+block.lowMax);out.blocks++;ck(b<=2*block.w,"block wait bound");if(!block.long)ck(b===0,"short block");for(let j=0;j<ranges.length;j++)if(block.p>=ranges[j]){path[j].bpos+=b;if(block.m<=K)path[j].localBpos+=b;if(!block.long)out.ranges[j].shortBlockChecks++;}}
  for(;;){
   let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[j]+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i])){w=f;i=j}}
   if(e+w>U)break;
   let p=ps[i],rep=first[i]>=0,delta=2*w-p+1,m=0,long=4*w>p;
   ck(w<=2*p,"wait");out.checks++;
   if(!rep){
    first[i]=g;fw+=w;
    if(p>=q0&&p<=2*U+1&&g<=2*U){
     const map=new Map();let lc=0;
     for(let a of [-2,0,2])for(let j=1;j*p+a<=2*U-g;j++){let x=g+j*p+a;if(x<g+p-1||x%2||!rough(p,x))continue;ck(!map.has(x),"candidate unique");map.set(x,j);if(j<=K)lc++}
     lists.set(i,map);
     for(let j=0;j<ranges.length;j++)if(p>=ranges[j]){out.ranges[j].firsts++;out.ranges[j].candidates+=map.size;out.ranges[j].localCandidates+=lc;path[j].cand+=p*map.size;path[j].localCand+=p*lc;}
    }
   }else if(p>=q0&&g<=2*U){
    let a=[-2,0,2].filter(a=>(g-first[i]-a)%p===0);ck(a.length===1,"unique stride offset");m=(g-first[i]-a[0])/p;ck(m>=1&&g-first[i]>=p-1,"stride");
    if(long){let map=lists.get(i);ck(rough(p,g)&&map&&map.get(g)===m,"candidate coverage");map.delete(g);for(let j=0;j<ranges.length;j++)if(p>=ranges[j]){let x=path[j];x.long++;x.weight+=p;x.wait+=w;if(m<=K){x.local++;x.localWeight+=p;x.localWait+=w;}}}
   }
   if(p>=5){close();block={p,g,repeat:rep,delta,w,m,long,low:0,lowMax:0};}
   else if(block){block.low+=delta;block.lowMax=Math.max(block.lowMax,block.low);ck(block.lowMax<=30,"low peak");}
   e+=w;g+=p-1;peak=Math.max(peak,2*e-g);out.events++;
  }
  close();
  for(let j=0;j<ranges.length;j++){let x=path[j],a=out.ranges[j];ck(x.weight<=x.cand&&x.localWeight<=x.localCand&&x.wait<=2*x.weight&&x.localWait<=2*x.localWeight&&x.weight<=4*U,"weighted injection");ck(x.bpos<=2*x.wait&&x.localBpos<=2*x.localWait,"block budgets");a.candidateWeight+=x.cand;a.localCandidateWeight+=x.localCand;a.longReturns+=x.long;a.longWeight+=x.weight;a.longWait+=x.wait;a.localLong+=x.local;a.localWeight+=x.localWeight;a.localWait+=x.localWait;a.distantLong+=x.long-x.local;a.blockPositive+=x.bpos;a.localBlockPositive+=x.localBpos;a.pathsWithLong+=+(x.long>0);}
  out.peakSum+=peak;out.freshWaitSum+=fw;
 }
 return out;
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?128:256)));
