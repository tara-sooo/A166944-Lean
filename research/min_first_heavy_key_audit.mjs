// Node.js: horizon-ordered absorbing selected-key process with original source cutoffs.
function audit(X) {
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,L=210,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const check=b=>{if(!b)throw Error("assertion failed")},gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return a};
 function hit(t,C,K){let u=K+1,q=0;for(let s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let m=2*p,r=s===-1?0:p+2,h=t+1+((r-t-1)%m+m)%m;if(h<u||(h===u&&p<q)){u=h;q=p}while(v%p===0)v/=p}}return [u,q]}
 const caps=[{name:"B/8",t:Math.max(2,Math.floor(B/8))},{name:"B/4",t:Math.max(2,Math.floor(B/4))},{name:"B/2",t:Math.max(2,Math.floor(B/2))},{name:"B",t:B},{name:"B log^2 B",t:Math.ceil(B*Math.log(B)**2)}];
 const primes=[];for(let p=11;p<=B;p++)if(spf[p]===p)primes.push(p);
 let S0=0,Skey=0,Sblock=0,keyCount=0;
 for(let C=2*X;C<7*X;C+=2){let r=Math.min(spf[C-1],spf[C+1]);if(r<=B)S0+=r}
 for(let p of primes)for(let s of [-1,1]){let C=2*X+((-s-2*X)%p+p)%p;if(C%2)C+=p;for(;C<7*X;C+=2*p){let r=Math.min(spf[C-1],spf[C+1]);check(r<=p);Skey+=r;Sblock+=r+1.5*((L-(C+p-1)%L)%L);keyCount++}}
 let runs=[];
 for(let cap of caps){
  const head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N).fill(-1),t=new Int32Array(N),K=new Int32Array(N),high=new Int32Array(N),cost=new Int32Array(N),lowGain=new Int32Array(N),stopC=new Int32Array(N),stopP=new Int32Array(N),root=i=>2*X+4*i;
  function push(i,C){next[i]=head[C/2];head[C/2]=i}
  for(let i=0;i<N;i++){let M=X+2*i+1;t[i]=M+2;K[i]=Math.floor((7*M-1)/4);push(i,root(i))}
  let st={...cap,R:0,elapsed:0,highR:0,lowR:0,events:0,stopped:0,sinks:0,maxMass:0,maxPassed:0,twin:0,bad:0,stopGain:0,stopElapsed:0,stopCost:0,stopPairs:0,stopMaxGain:0,stopMaxHigh:0,shortDepth:[0,0,0,0,0,0,0,0,0,0,0],shortTime:[0,0,0,0],overshoot:0,distinctIncomingOne:0,literal:0,sampleSinks:[]};
  const sample=[];
  for(let C=2*X;C<7*X;C+=2){
   let i=head[C/2];if(i<0)continue;let groups=new Map(),r=Math.min(spf[C-1],spf[C+1]);
   while(i>=0){let j=next[i],[u,p]=hit(t[i],C,K[i]);if(X<=1024){let a=K[i]+1,b=0;for(let k=t[i]+1;k<=K[i];k++){let g=gcd(k%2?k-2:k,C+(k%2?1:-1));if(g>1&&spf[g]<=B){a=k;b=spf[g];break}}check(u===a&&p===b);st.literal++}
    if(!p){check(lowGain[i]<L);if(spf[C-1]===C-1&&spf[C+1]===C+1)st.twin++;else{st.bad++;check(K[i]-t[i]<2*B);check(2*cost[i]+2*B>=K[i]-(X+2*i+3))}}
    else if(p>7){if(!groups.has(p))groups.set(p,[]);groups.get(p).push([i,u])}
    else{check(r<=p&&u-t[i]<=2*r);lowGain[i]+=p-1;check(lowGain[i]<L);st.R+=r;st.lowR+=r;st.elapsed+=u-t[i];st.events++;cost[i]+=r;t[i]=u;check(C+p-1<=2*u);push(i,C+p-1)}
    i=j
   }
   for(let [p,a] of groups){if(a.length>=cap.t){st.sinks++;st.stopped+=a.length;st.maxMass=Math.max(st.maxMass,a.length);st.stopPairs+=a.length*(a.length-1);st.overshoot+=a.length-cap.t;
     let local={p,C,m:a.length,minHigh:Infinity,maxHigh:0,minRoot:Infinity,maxRoot:0,short:[0,0,0,0,0]};let inc=new Set();
     for(let [i,u] of a){let g=C-root(i),dt=t[i]-(X+2*i+3);check(g>=0&&g<=2*dt+6&&dt<=2*cost[i]);st.stopGain+=g;st.stopElapsed+=dt;st.stopCost+=cost[i];st.stopMaxGain=Math.max(st.stopMaxGain,g);st.stopMaxHigh=Math.max(st.stopMaxHigh,high[i]);for(let k=high[i];k<st.shortDepth.length;k++)st.shortDepth[k]++;for(let k=0;k<4;k++)if(dt<=B*2**k)st.shortTime[k]++;local.minHigh=Math.min(local.minHigh,high[i]);local.maxHigh=Math.max(local.maxHigh,high[i]);local.minRoot=Math.min(local.minRoot,root(i));local.maxRoot=Math.max(local.maxRoot,root(i));for(let k=high[i];k<5;k++)local.short[k]++;stopC[i]=C;stopP[i]=p}
     check(local.maxRoot-local.minRoot>=4*(a.length-1));if(sample.length<5)sample.push(local);else{let m=0;for(let k=1;k<5;k++)if(sample[k].m<sample[m].m)m=k;if(local.m>sample[m].m)sample[m]=local}
    }else{st.maxPassed=Math.max(st.maxPassed,a.length);for(let [i,u] of a){check(r<=p&&u-t[i]<=2*r&&lowGain[i]<L);lowGain[i]=0;high[i]++;st.R+=r;st.highR+=r;st.elapsed+=u-t[i];st.events++;cost[i]+=r;t[i]=u;check(C+p-1<=2*u);push(i,C+p-1)}}
   }
  }
  check(st.stopped+st.twin+st.bad===N);check(st.maxPassed<cap.t);check(st.sinks*cap.t<=st.stopped);check(st.stopPairs<=st.stopGain/2);check(st.stopGain<=4*st.stopCost+6*st.stopped);check(st.stopCost<=st.R);check(st.highR<= (cap.t-1)*Skey);check(st.R<=1.5*L*N+(cap.t-1)*Sblock);check(st.elapsed<=2*st.R);
  // Independent source-wise replay using final stop keys, including every cutoff.
  let stopKeys=new Set();for(let i=0;i<N;i++)if(stopP[i])stopKeys.add(stopC[i]*B+stopP[i]);
  check(stopKeys.size===st.sinks);
  if(X<=16384){let rr=0,ns=0;for(let i=0;i<N;i++){let M=X+2*i+1,tt=M+2,C=root(i),k=0;for(;;){let [u,p]=hit(tt,C,K[i]);if(!p){check(!stopP[i]);break}if(p>7&&stopKeys.has(C*B+p)){check(stopP[i]===p&&stopC[i]===C&&k===high[i]);ns++;break}if(p>7)k++;rr+=Math.min(spf[C-1],spf[C+1]);C+=p-1;tt=u}}check(rr===st.R&&ns===st.stopped)}
  st.sampleSinks=sample;runs.push(st)
 }
 return {X,B,N,S0,Skey,Sblock,keyCount,runs};
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
