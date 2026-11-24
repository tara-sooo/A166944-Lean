// Low-transparent cap and last-large-gateway source moment audit.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,L=210,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=(x,m="assertion")=>{if(!x)throw Error(m)},mod=(x,m)=>(x%m+m)%m,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c}return a};
 function hit(t,C,K){let n=K+1,p=0;for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(q>B)break;let u=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(u<n||(u===n&&q<p)){n=u;p=q}while(v%q===0)v/=q}}return [n,p]}
 const out=[];
 for(let mode of ["uniform","transparent","truncatedInverse"]){
  const T=Math.max(2,Math.floor(B/4)),Y=13,Z=Math.max(Y,Math.ceil(Math.sqrt(B))),A=T*B,low=mode==="uniform"?11:Y,cap=p=>mode==="truncatedInverse"?Math.ceil(A/Math.max(p,Z)):T;let Llow=2;for(let p=3;p<low;p++)if(spf[p]===p)Llow*=p;
  const head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N),t=new Int32Array(N),K=new Int32Array(N),masses=new Map(),stops=new Map(),cohorts=[];
  const put=(i,C)=>{next[i]=head[C/2];head[C/2]=i};
  for(let i=0;i<N;i++){let M=X+2*i+1;t[i]=M+2;K[i]=Math.floor((7*M-1)/4);put(i,2*M-2)}
  let R=0,S=0,twin=0,bad=0,events=0,literal=0,Rlo=0,Rhi=0,hi=0,maxGain=0,maxLowCost=0;const lowGain=new Int32Array(N),lowCost=new Int32Array(N);
  for(let C=2*X;C<7*X;C+=2){let i=head[C/2];if(i<0)continue;let groups=new Map(),r=Math.min(spf[C-1],spf[C+1]);
   while(i>=0){let j=next[i],[n,p]=hit(t[i],C,K[i]);if(X<=1024){let nn=K[i]+1,pp=0;for(let k=t[i]+1;k<=K[i];k++){let g=gcd(k%2?k-2:k,C+(k%2?1:-1));if(g>1&&spf[g]<=B){nn=k;pp=spf[g];break}}ck(nn===n&&pp===p,"literal");literal++}
    if(!p){if(spf[C-1]===C-1&&spf[C+1]===C+1)twin++;else bad++}
    else if(p<low){R+=r;Rlo+=r;events++;lowGain[i]+=p-1;lowCost[i]+=r;ck(lowGain[i]<Llow&&lowCost[i]<=1.5*lowGain[i]);maxGain=Math.max(maxGain,lowGain[i]);maxLowCost=Math.max(maxLowCost,lowCost[i]);t[i]=n;put(i,C+p-1)}
    else{if(!groups.has(p))groups.set(p,[]);groups.get(p).push([i,n])}i=j}
   for(let [p,a] of groups){let key=C*B+p;ck(!masses.has(key));masses.set(key,a.length);
    if(a.length>=cap(p)){S+=a.length;stops.set(key,a.length);cohorts.push({C,p,ids:a.map(x=>x[0]).sort((a,b)=>a-b)})}
    else for(let [i,n] of a){R+=r;Rhi+=r;hi++;events++;lowGain[i]=0;lowCost[i]=0;t[i]=n;put(i,C+p-1)}
   }
  }
  ck(S+twin+bad===N);
  // Replay exactly the stopped tags. Pair in increasing horizon, but never change their trajectories.
  const hist=new Map(),arrivals=new Map(),finalKey=new Map();
  for(const {C:Cs,p:ps,ids} of cohorts)for(const i of ids){
   let M=X+2*i+1,C=2*M-2,t=M+2,prior=null,hs=[],guard=0,cost=0;
   for(;;){let [n,p]=hit(t,C,K[i]);ck(p>0,"replay ended");let r=Math.min(spf[C-1],spf[C+1]);ck(n-t<=2*r);
    if(p>=low){let key=C*B+p,b=n%2?6:0,h=2*n-(C+p-1),k=(h-b)/(2*p);ck(k>=0&&Number.isInteger(k));
     let e={i,key,C,p,n,t,b,h,k,r,prior,cost};
     if(prior){let g=C-prior.postC,dt=n-prior.n,err=b-prior.b-2*dt+g-1;ck(g>=0&&g<Llow&&dt>0&&dt<=3*Llow+2*r);ck(2*prior.k*prior.p===(2*k+1)*p+err&&Math.abs(err)<=7*Llow+4*r+7&&err%2!==0);e.err=err;}
     hs.push(e);if(!arrivals.has(key))arrivals.set(key,[]);arrivals.get(key).push(i);
     if(stops.has(key)){ck(C===Cs&&p===ps);finalKey.set(i,key);break}
     prior={key,p,C,n,b,h,k,postC:C+p-1};
    }
    cost+=r;t=n;C+=p-1;ck(++guard<7*X)
   }
   hist.set(i,hs)
  }
  ck(hist.size===S&&finalKey.size===S);
  ck(R===Rlo+Rhi&&Rlo<=1.5*Llow*(N+hi));
  let highMass=0,lowMass=0,first=0,rootOnly=0,gateMass=0,gateKeys=0,gatePhys=0,maxSuffix=0,gateTopMass=0,gateTopKeys=0,maxGateClasses=0,topI=0,topH=0,topU=0,topKeys=0,topMass=0,gateTopH=0,gateTopI=0,gateTopU=0,gateTopPhysical=0;
  const gates=new Map(),top=new Map(),stopSummary=[];
  for(let [i,hs] of hist){let e=hs.at(-1),M=X+2*i+1;ck(e.p>=low&&e.h<=6+4*e.cost+4*e.r);
   if(e.p>=Y)highMass++;else lowMass++;
   if(hs.length===1){first++;ck(e.C-(2*M-2)<Llow);}
   if(e.p>=Z){topMass++;let v=top.get(e.key)||{p:e.p,m:0,H:0,cl:new Map()};v.m++;v.H+=e.h;v.cl.set(e.n,(v.cl.get(e.n)||0)+1);top.set(e.key,v)}
   if(e.p>=Y)continue;
   let a=hs.slice(0,-1).findLast(h=>h.p>=Y);
   if(!a){rootOnly++;ck(e.C-(2*M-2)<2310);continue;}
   let g=e.C-(a.C+a.p-1);ck(g>=0&&g<2310&&e.n-a.n<=3*2310+2*e.r);maxSuffix=Math.max(maxSuffix,g);
   let key=e.key+":"+a.key,v=gates.get(key)||{p:a.p,m:0,H:0,cl:new Map()};v.m++;v.H+=a.h;v.cl.set(a.n,(v.cl.get(a.n)||0)+1);gates.set(key,v);gateMass++;
  }
  ck(first<=stops.size*(Math.floor(Llow/4)+1)&&lowMass===rootOnly+gateMass&&highMass+lowMass===S);
  function sum(v,a){let U=0,J=0,n0=Math.min(...v.cl.keys());for(let [n,m] of v.cl){let j=(n-n0)/(2*v.p);ck(Number.isInteger(j)&&j>=0);U+=Math.min(a,m);J+=j*Math.min(a,m)}ck(v.H>=4*v.p*J&&2*a*J>=U*U-a*U);return U}
  for(let v of top.values()){topKeys++;topI+=1/v.p;topH+=v.H;topU+=sum(v,8);if(mode==="truncatedInverse")ck(v.m*v.p>=A)}
  if(mode==="truncatedInverse")ck(topI<=topMass/A+1e-9);
  for(let v of gates.values()){gateKeys++;gatePhys+=v.cl.size;maxGateClasses=Math.max(maxGateClasses,v.cl.size);if(v.p>=Math.ceil(B/2)){gateTopMass+=v.m;gateTopKeys++;gateTopH+=v.H;gateTopI+=1/v.p;gateTopU+=sum(v,8);for(let m of v.cl.values())if(m>8)gateTopPhysical+=m;}}
  ck(gateTopU<=8*gateTopKeys+Math.sqrt(4*gateTopH*gateTopI)+1e-6&&topU<=8*topKeys+Math.sqrt(4*topH*topI)+1e-6);
  for(let [key,m] of stops)stopSummary.push({p:key%B||B,m});
  out.push({mode,T,Y,Z,A,low,Llow,S,R,Rlo,Rhi,hi,maxGain,maxLowCost,twin,bad,literal,stopKeys:stops.size,first,highMass,lowMass,rootOnly,gateMass,gateKeys,gatePhys,maxGateClasses,maxSuffix,gateTopMass,gateTopKeys,gateTopH,gateTopI,gateTopU,gateTopPhysical,topMass,topKeys,topH,topI,topU,stopSummary});
 }
 return {X,B,N,runs:out}
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
