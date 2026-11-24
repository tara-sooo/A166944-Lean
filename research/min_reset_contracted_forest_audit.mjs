// Common-cutoff reset graph and LOW-y contracted forest, independent canonical replay.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),K=Math.floor((7*X-1)/4),N=X/8,Ls=[{y:7,L:210},{y:11,L:2310},{y:13,L:30030}],spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=(b,m="assertion")=>{if(!b)throw Error(m)},gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return a},Creset=t=>2*t-(t%2?6:0);
 function hit(t,C){let u=K+1,q=0;for(let s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let h=t+1+(((s===-1?0:p+2)-t-1)%(2*p)+2*p)%(2*p);if(h<u||(h===u&&p<q)){u=h;q=p}while(v%p===0)v/=p}}return [u,q]}
 function exc(t){let start=t,C=Creset(t),rCost=0,events=0,high=0,maxP=0,maxH=0,firstHigh=0,firstHighR=0,firstHighGain=0;
  for(;;){let [u,p]=hit(t,C);if(!p){let twin=spf[C-1]===C-1&&spf[C+1]===C+1;return {from:start,to:0,last:t,C,rCost,events,high,maxP,maxH,firstHigh,firstHighR,firstHighGain,twin}}
   let r=Math.min(spf[C-1],spf[C+1]);ck(u-t<=2*r&&r<=p);
   if(p>7){high++;if(!firstHigh){firstHigh=p;firstHighR=r;firstHighGain=C-Creset(start);ck(firstHighGain<210)}}
   events++;maxP=Math.max(maxP,p);rCost+=r;C+=p-1;t=u;let h=2*t-C;ck(h>=0);maxH=Math.max(maxH,h);
   if(h===(t%2?6:0)){ck(C===Creset(t));let gain=C-Creset(start);ck(gain>0&&gain===2*(t-start)+(start%2?6:0)-(t%2?6:0));ck(maxP-1<=gain&&rCost<=1.5*gain&&t-start<=2*rCost);return {from:start,to:t,last:t,C,rCost,events,high,maxP,maxH,firstHigh,firstHighR,firstHighGain,twin:false}}
  }
 }
 // construct every reset-time vertex (not only reached) on common cutoff.
 let edge=new Array(K+1),mass=new Int32Array(K+1),inj=new Uint8Array(K+1),sink=new Int32Array(K+1),gainSum=0,lit=0,rootT=0;
 for(let M=X+1;M<X+X/4;M+=2){let t=M+2;inj[t]=1;mass[t]=1;rootT++}ck(rootT===N);
 for(let t=X+3;t<=K;t++){edge[t]=exc(t);let e=edge[t];if(e.to)ck(e.to>t&&e.to<=K)}
 let R=0,weightedReset=0,weightedExc=0,reached=0,edges=0,terminal=0,twin=0,bad=0,maxMass=0,maxEdge=0,maxEvents=0,allEdges=0,allLong=0,allHigh=0,allOneHigh=0,allMultiHigh=0,oneHigh=0,multiHigh=0,noHigh=0,weightedOne=0,weightedMulti=0,weightedNone=0,allMax=0,allCost=0,terminalMax=0;
 const tail=[1,2,4,8,16,32,64,128,256,512,1024,2048].map(k=>({k,all:0,reached:0,weighted:0}));
 for(let t=X+3;t<=K;t++){let e=edge[t];allCost+=e.rCost;if(e.to){allEdges++;allMax=Math.max(allMax,e.to-t);if(e.high){allHigh++;if(e.high===1)allOneHigh++;else allMultiHigh++}for(let a of tail)if(e.to-t>=a.k)a.all++}
  let m=mass[t];if(!m)continue;reached++;maxMass=Math.max(maxMass,m);R+=m*e.rCost;weightedExc+=m;maxEvents=Math.max(maxEvents,e.events);
  if(e.to){edges++;weightedReset+=m;mass[e.to]+=m;maxEdge=Math.max(maxEdge,e.to-t);if(!e.high){noHigh++;weightedNone+=m}else if(e.high===1){oneHigh++;weightedOne+=m}else{multiHigh++;weightedMulti+=m}
   for(let a of tail)if(e.to-t>=a.k){a.reached++;a.weighted+=m}
  }else{terminal+=m;terminalMax=Math.max(terminalMax,m);if(e.twin)twin+=m;else bad+=m}
 }
 ck(terminal===N&&twin+bad===N);
 // independent root-wise replay against the graph and original literal clocks for small X.
 let r2=0,tw2=0,bad2=0,nr2=0,ex2=0;
 for(let M=X+1;M<X+X/4;M+=2){let t=M+2,C=2*M-2;for(;;){let [u,p]=hit(t,C);if(X<=1024){let a=K+1,b=0;for(let j=t+1;j<=K;j++){let g=gcd(j%2?j-2:j,C+(j%2?1:-1));if(g>1&&spf[g]<=B){a=j;b=spf[g];break}}ck(a===u&&b===p);lit++}
   if(!p){ex2++;if(spf[C-1]===C-1&&spf[C+1]===C+1)tw2++;else bad2++;break}r2+=Math.min(spf[C-1],spf[C+1]);C+=p-1;t=u;if(C===Creset(t)){nr2++;ex2++}
  }}
 ck(r2===R&&tw2===twin&&bad2===bad&&nr2===weightedReset&&ex2===weightedExc);
 const modes=[];
 for(let {y,L} of Ls){
  const comp=new Int32Array(K+1),rootCount=new Int32Array(K+1),vertexCount=new Int32Array(K+1),minC=new Int32Array(K+1).fill(2147483647),maxC=new Int32Array(K+1),longAncestor=new Int32Array(K+1),rootComponents=new Int32Array(K+1);
  // every reset vertex reaches exactly one short-edge sink; short means all labels <=y.
  for(let t=K;t>=X+3;t--){let e=edge[t];comp[t]=e.to&&e.maxP<=y?comp[e.to]:t;ck(comp[t]>=t);let c=comp[t];vertexCount[c]++;rootCount[c]+=inj[t];minC[c]=Math.min(minC[c],Creset(t));maxC[c]=Math.max(maxC[c],Creset(t));ck(Creset(c)-Creset(t)>=0&&Creset(c)-Creset(t)<L)}
  let components=0,rootComps=0,largestRootComp=0,largestVertexComp=0,largestSpan=0,reachableLong=0,allLong=0,allSingleHigh=0,allMultiHigh=0,usedRootComp=0,terminalCompMass=0,maxRootCompsInBasin=0,maxLongInBasin=0,maxBound=0,compEdges=0;
  const cmass=new Int32Array(K+1),ancRoots=new Int32Array(K+1);
  for(let t=X+3;t<=K;t++)if(comp[t]===t){
   components++;largestRootComp=Math.max(largestRootComp,rootCount[t]);largestVertexComp=Math.max(largestVertexComp,vertexCount[t]);largestSpan=Math.max(largestSpan,maxC[t]-minC[t]);ck(rootCount[t]<=Math.floor(L/4)+1);if(rootCount[t]){rootComps++;rootComponents[t]++}
   cmass[t]+=rootCount[t];ancRoots[t]+=rootCount[t];ck(cmass[t]===mass[t]);ck(cmass[t]<=(Math.floor(L/4)+1)*(longAncestor[t]+1));ck(rootComponents[t]<=longAncestor[t]+1);
   let e=edge[t];if(e.to){ck(e.maxP>y);let c=comp[e.to];ck(c>t);compEdges++;allLong++;if(e.high===1)allSingleHigh++;if(e.high>=2)allMultiHigh++;if(cmass[t])reachableLong++;cmass[c]+=cmass[t];ancRoots[c]+=ancRoots[t];longAncestor[c]+=longAncestor[t]+1;rootComponents[c]+=rootComponents[t]}
   else{terminalCompMass+=cmass[t];maxRootCompsInBasin=Math.max(maxRootCompsInBasin,rootComponents[t]);maxLongInBasin=Math.max(maxLongInBasin,longAncestor[t]);maxBound=Math.max(maxBound,cmass[t]);}
  }
  ck(terminalCompMass===N&&compEdges<=components);modes.push({y,L,components,rootComps,largestRootComp,largestVertexComp,largestSpan,reachableLong,allLong,allSingleHigh,allMultiHigh,maxRootCompsInBasin,maxLongInBasin,maxBound})
 }
 return {X,B,K,N,R,reached,edges,weightedReset,weightedExc,twin,bad,maxMass,maxEdge,maxEvents,allEdges,allHigh,allOneHigh,allMultiHigh,oneHigh,multiHigh,noHigh,weightedOne,weightedMulti,weightedNone,allMax,allCost,terminalMax,lit,tail,modes}
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
