// Finite-time averaged clipped potential: exact phase audit and finite-cutoff time-window sample.
function exact(Y,S,K){
 const ps=[];for(let p=3;p<Y;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const L=2*ps.reduce((a,b)=>a*b,1),n=L/2,N=n*L,mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)};
 if(N>30000)throw Error("exact cap");
 let delta=new Int16Array(N),wait=new Uint16Array(N),label=new Uint16Array(N),succ=new Uint32Array(N),r0=new Uint16Array(N);
 for(let i=0;i<n;i++)for(let t=0;t<L;t++){
  let p0=0,w=L+1,C=2*i,r=0;
  for(let p of ps){let cc=mod(C,p);if(cc!==1&&cc!==p-1)continue;if(!r)r=p;
   let f=2*p-mod(t-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<p0)){w=f;p0=p}}
  let j=i*L+t;if(!p0)continue;
  wait[j]=w;delta[j]=2*w-(p0-1);label[j]=p0;r0[j]=r;succ[j]=((i+(p0-1)/2)%n)*L+mod(t+w,L);
 }
 const D=Array.from({length:2*S+1},()=>new Uint16Array(N)),sum=new Uint32Array(N);
 for(let T=1;T<=2*S;T++)for(let j=0;j<N;j++){
  let w=wait[j];if(w&&w<=T)D[T][j]=Math.max(0,delta[j]+D[T-w][succ[j]]);
  ck(D[T][j]>=D[T-1][j]&&D[T][j]<=2*T,"time monotonicity");
  if(T>=S)sum[j]+=Math.min(K,D[T][j]);
 }
 let checks=0,short=0,long=0,positive=0,tail=0,sumPeak=0,sumClip=0,maxPeak=0,maxLeak=0,clipLeak=0,boundarySum=0,deltaTail=0,maxBoundary=0;
 for(let j=0;j<N;j++){
  tail+=D[2*S][j]>K;sumPeak+=D[2*S][j];sumClip+=sum[j]/(S+1);maxPeak=Math.max(maxPeak,D[2*S][j]);
  let w=wait[j],p=label[j];if(!p)continue;
  let x=succ[j],inc=(S+1)*delta[j]+sum[x]-sum[j],leak=Math.max(0,inc);
  if(leak)positive++;clipLeak+=leak/(S+1);maxLeak=Math.max(maxLeak,leak/(S+1));
  if(w<=S){
   short++;let shifted=0,local=0;
   for(let T=S;T<=2*S;T++){let a=D[T][j],b=D[T-w][x],z=Math.max(0,delta[j]+Math.min(K,b)-Math.min(K,a));ck(z===Math.min(Math.max(0,delta[j]),Math.max(0,a-K)),"finite clipped identity");shifted+=Math.min(K,b);local+=z;checks++}
   let b=sum[x]-shifted;ck(b>=0&&b<=w*K,"averaged boundary");ck(leak<=local+b,"averaged leakage");ck(leak<=(S+1)*Math.max(0,delta[j])*(D[2*S][j]>K?1:0)+w*K,"tail bound");
   boundarySum+=b/(S+1);deltaTail+=Math.max(0,delta[j])*(D[2*S][j]>K?1:0);maxBoundary=Math.max(maxBoundary,b/(S+1));
  }else{long++;ck(inc<=(S+1)*6*r0[j],"long wait")}
  ck(inc<=(S+1)*6*r0[j],"all low cost");
 }
 return {Y,L,N,S,K,checks,short,long,positive,tail:tail/N,meanPeak:sumPeak/N,maxPeak,meanCorrection:sumClip/N,meanPositiveLeak:clipLeak/N,meanBoundary:boundarySum/N,meanDeltaTail:deltaTail/N,maxBoundary,maxLeak};
}
function sample(S,N=512){
 const V=4*S,ps=[];const sieve=new Uint8Array(V);for(let p=2;p<V;p++)if(!sieve[p]){if(p>2)ps.push(p);if(p*p<V)for(let q=p*p;q<V;q+=p)sieve[q]=1}
 let rng=(0x4acb9213^S)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let l=4294967296-4294967296%p,x;do{x=u32()}while(x>=l);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),mod=(a,b)=>(a%b+b)%b;
 let peaks=[],endHeights=[],eventCounts=[],lastTimes=[],gains=[],ks=[Math.floor(S/8),Math.floor(S/4),Math.floor(S/2),Math.floor(S/Math.sqrt(Math.log(S)))],tail=ks.map(()=>0),peakAtS=0,peakAfterS=0,events=0,negativeAtEnd=0,zero=0,earlyFrozen=0,maxEventTime=0;
 for(let j=0;j<N;j++){
  let parity=uni(2);for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let b=uni(p);t[i]=b%2===parity?b:b+p}
  let e=0,g=0,D=0,DS=0,n=0;
  for(;;){let w=Infinity,b=-1;for(let i=0;i<ps.length;i++){let p=ps[i],cc=(c[i]+g)%p;if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[i]+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[b])){w=f;b=i}}
   if(e+w>2*S){if(b<0)earlyFrozen++;break}
   e+=w;g+=ps[b]-1;n++;D=Math.max(D,2*e-g);if(e<=S)DS=Math.max(DS,2*e-g);
  }
  peaks.push(D);lastTimes.push(e);endHeights.push(2*e-g);gains.push(g);eventCounts.push(n);events+=n;maxEventTime=Math.max(maxEventTime,e);peakAtS+=DS;peakAfterS+=D>DS;negativeAtEnd+=2*e-g<0;zero+=D===0;for(let i=0;i<ks.length;i++)tail[i]+=D>ks[i];
 }
 function stat(a){let s=a.reduce((a,b)=>a+b,0);a.sort((a,b)=>a-b);return {mean:s/N,median:a[Math.ceil(N*.5)-1],q90:a[Math.ceil(N*.9)-1],q99:a[Math.ceil(N*.99)-1],max:a.at(-1)}}
 let p=stat(peaks);return {S,V,N,primes:ps.length,peak:p,peakRatio:p.mean/S,meanPeakAtS:peakAtS/N,peakInSecondHalf:peakAfterS,tail:ks.map((K,i)=>({K,n:tail[i],fraction:tail[i]/N})),lastTime:stat(lastTimes),endHeight:stat(endHeights),gain:stat(gains),eventCount:stat(eventCounts),negativeAtEnd,zero,earlyFrozen,maxEventTime};
}
for(const Y of [5,7,11])for(const S of [8,16,32])for(const K of [Math.floor(S/4),Math.floor(S/2),S])console.log(JSON.stringify(exact(Y,S,K)));
for(const S of process.argv.slice(2).map(Number))console.log(JSON.stringify(sample(S)));
