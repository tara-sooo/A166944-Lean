// Fixed-small-alphabet landing localization and mean-profile rather than pathwise L2 diagnostics.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=131100,spf=new Uint32Array(N+1),pr=[];
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)spf[a]=p;
 for(let p=3;p<=N;p+=2)if(!spf[p])pr.push(p);
 function fs(n){let a=[];n=Math.abs(n);while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 const factors=Array.from({length:N+1},(_,i)=>i%2?fs(i):[]);
 // For the fixed small alphabet, compute exact maximum prefix
 // gain, duration and local descent occupation over every phase.
 const P=[3,5,7],Q=P.reduce((a,b)=>a*b,1),L=2*Q,period=4*Q;
 let wall=2*(Q-1),D=0,W=0,C=0,phase=0;
 for(let a0=0;a0<period;a0+=2)for(let n0=0;n0<L;n0++){
  let a=a0,n=n0,g=0,w=0,m=new Map();
  for(;;){let p=0,t=Infinity;for(let q of P)for(let s of [-1,1])if(mod(a-s,q)===0){let v=mod((s===-1?0:q+2)-n,2*q)||2*q;if(v<t||v===t&&q<p){t=v;p=q}}
   if(!p)break;
   let b=n+t+(a-a0)/2-n0,k=(p-1)/2;
   for(let x=b+1-k;x<b;x++)m.set(x,(m.get(x)||0)+1);
   a-=p-1;n+=t;g+=p-1;w+=t;ck(g<=wall,"wall")
  }
  D=Math.max(D,g);W=Math.max(W,w);for(let x of m.values())C=Math.max(C,x);phase++
 }
 let seed=0x08b5cafe;function u32(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0}function rnd(n){let m=Math.floor(4294967296/n)*n,x;do{x=u32()}while(x>=m);return x%n}
 let out={phase,D,W,C,paths:0,ticks:0,localChecks:0,runChecks:0,localizedChecks:0,rows:[]};
 for(let T of [1024,4096,16384,65536]){
  const Y=Math.ceil(T/4),ns=T<=4096?384:T<=16384?192:96,H=T+3;
  const beta=new Float64Array(H+1),rare=new Uint8Array(H+1),near=new Uint8Array(H+1),pref=new Int32Array(H+2),smallSum=new Float64Array(H+1),smallSq=new Float64Array(H+1),landSum=new Float64Array(H+1),stats={T,Y,ns,meanGain:0,meanZsmall:0,meanZ:0,meanToll:0,meanSmallToll:0,meanSmallRare:0,meanSmallTotal:0,meanRareLandings:0,meanRareLandingsMedium:0,meanRareLandingsLarge:0,meanSmallRunGain:0,maxLocal:0};
  for(let h=1;h<=H;h++){for(let q of [...factors[2*h+1],...factors[Math.abs(2*h-5)]])if(q>Y)beta[h]+=1/q;rare[h]=+(beta[h]>0);pref[h+1]=pref[h]+rare[h]}
  for(let h=0;h<=H;h++)near[h]=+(pref[Math.min(H,h+W)+1]-pref[Math.max(0,h-D/2)]>0);
  for(let i=0;i<ns;i++){
   let parity=rnd(2),res=new Int32Array(N+1).fill(-1);res[3]=0;function aMod(p){if(res[p]<0)res[p]=rnd(p);return res[p]}
   let small=new Int32Array(H+2),all=new Int32Array(H+2),land=new Int32Array(H+1),gain=0,h=3,startH=3,startT=0,runG=0,runL=new Map(),rareCount=0,rareMid=0,rareBig=0;
   function endRun(t){ck(runG<=D,"run gain");for(let [b,m] of runL){ck(m<=C&&b>=startH-D/2&&b<=startH+W,"run local bounds");out.runChecks++}runL.clear();runG=0;startT=t}
   for(let t=1;t<=T;t++){
    let b=h+1,par=mod(3-parity+t,2),s=par?1:-1,p=1;
    for(let q of factors[Math.abs(par?2*b-5:2*b+1)])if(q<=Y&&mod(aMod(q)-gain-s,q)===0){p=q;break}
    let k=(p-1)/2,l=b+1-k,r=b-1;
    if(p>1&&l<=r){all[l]++;all[r+1]--;if(p<=7){small[l]++;small[r+1]--;for(let x=l;x<=r;x++)runL.set(x,(runL.get(x)||0)+1)}}
    if(p>7){endRun(t);startH=b-k;land[startH]++;if(near[startH]){rareCount++;if(p<=127)rareMid++;else rareBig++}}
    else if(p>1)runG+=p-1;
    h=b-k;gain+=p-1;out.ticks++;
   }
   endRun(T);
   let ds=0,da=0,rareSmall=0,smallTotal=0,st=0,tt=0,zs=0,za=0;
   const lp=new Int32Array(H+2);for(let b=0;b<=H;b++)lp[b+1]=lp[b]+land[b];
   for(let b=1;b<=H;b++){ds+=small[b];da+=all[b];let incoming=lp[Math.min(H,b+D/2)+1]-lp[Math.max(0,b-W)];let init=+(b>=3-D/2&&b<=3+W);
    ck(ds<=C*(incoming+init),"landing convolution");out.localChecks++;smallSum[b]+=ds;smallSq[b]+=ds*ds;landSum[b]+=land[b];rareSmall+=ds*rare[b];smallTotal+=ds;st+=ds*beta[b];tt+=da*beta[b];zs+=ds*ds;za+=da*da;stats.maxLocal=Math.max(stats.maxLocal,ds)
   }
   let initRare=near[3]?1:0;ck(rareSmall<=Math.floor(D/2)*(rareCount+initRare),"localized landing bound");out.localizedChecks++;
   stats.meanGain+=gain;stats.meanZsmall+=zs;stats.meanZ+=za;stats.meanToll+=tt;stats.meanSmallToll+=st;stats.meanSmallRare+=rareSmall;stats.meanSmallTotal+=smallTotal;stats.meanRareLandings+=rareCount;stats.meanRareLandingsMedium+=rareMid;stats.meanRareLandingsLarge+=rareBig;out.paths++;
  }
  for(let k of Object.keys(stats))if(k.startsWith("mean"))stats[k]/=ns;
  let meanProfileSq=0,unbiased=0,maxMean=0,tv=0,periodStep=2*Q;
  for(let b=1;b<=H;b++){let u=smallSum[b]/ns;meanProfileSq+=u*u;unbiased+=(smallSum[b]*smallSum[b]-smallSq[b])/(ns*(ns-1));maxMean=Math.max(maxMean,u);if(b+periodStep<=H)tv+=Math.abs(u-smallSum[b+periodStep]/ns)}
  stats.meanProfileSq=meanProfileSq;stats.crossSampleProfileSq=unbiased;stats.maxMeanLocal=maxMean;stats.stepVariation=tv;stats.rareHeights=pref[H+1];stats.nearHeights=near.reduce((a,b)=>a+b,0);out.rows.push(stats)
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
