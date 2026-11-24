// Exact once-only far projected contact audit (original sources, uniform first-heavy absorption).
function audit(X,which){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,L=210,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=(b,msg="assertion")=>{if(!b)throw Error(msg)},mod=(x,m)=>(x%m+m)%m,gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return a};
 function hit(t,C,K){let u=K+1,q=0;for(let s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let h=t+1+mod((s===-1?0:p+2)-t-1,2*p);if(h<u||(h===u&&p<q)){u=h;q=p}while(v%p===0)v/=p}}return [u,q]}
 const caps=which==="wide"?[Math.max(2,Math.floor(B/2)),Math.ceil(B*Math.log(B)**2)]:[Math.max(2,Math.floor(B/4)),Math.max(2,Math.floor(B/2)),Math.ceil(B*Math.log(B)**2)];
 const runs=[];
 for(let T of caps){
  const d=Math.floor(T/2),Z=Math.ceil(Math.sqrt(B)),A=Math.ceil(Math.sqrt(T)),a0=Math.ceil(Math.log(B)**.25);
  const head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N),t=new Int32Array(N),K=new Int32Array(N),pp=new Int32Array(N),pd=new Int32Array(N),pr=new Int32Array(N),pm=new Int32Array(N),h=new Int32Array(N),root=i=>2*X+4*i;
  const push=(i,C)=>{next[i]=head[C/2];head[C/2]=i};
  for(let i=0;i<N;i++){let M=X+2*i+1;t[i]=M+2;K[i]=Math.floor((7*M-1)/4);push(i,root(i))}
  let seen=new Set(),allSeen=X<=1024?new Set():null,bins=new Map(),J=0,P=0,R=0,events=0,stopped=0,sinks=0,twin=0,bad=0,literal=0,stopFar=0,maxMass=0,maxRootDist=0,stopMax=0,firstAtStop=0,firstEarlierThanStop=0,sameQ=0,sameQFar=0,sameQFirst=0,distinctNearQ=0,largeLarge=0,largeLargeJ=0,largeLargeRough=0,largeLargeBothRough=0,largeLargeBothCheap=0,largeLargeNearQ=0,largeLargeSameQ=0,productSmall=0,productMedium=0,productRough=0,firstRoot=0,rootJ=0,largeLargeStop=0,largeLargeLargest=0,largeExamples=[],witnessFar=0,witnessVeryFar=0,witnessPairs=0,stops=[];
  const levels=[0,1,2,4,8,16,32,64,128,256,512,1024,2048,4096],roughCounts=[0,0,0],roughJ=[0,0,0],llprod=[0,0,0,0],massbin=m=>Math.floor(Math.log2(m));
  for(let C=2*X;C<7*X;C+=2){
   let i=head[C/2];if(i<0)continue;let groups=new Map(),r=Math.min(spf[C-1],spf[C+1]);
   while(i>=0){let j=next[i],[n,p]=hit(t[i],C,K[i]);if(X<=1024){let nn=K[i]+1,qq=0;for(let k=t[i]+1;k<=K[i];k++){let g=gcd(k%2?k-2:k,C+(k%2?1:-1));if(g>1&&spf[g]<=B){nn=k;qq=spf[g];break}}ck(nn===n&&qq===p,"literal");literal++}
    if(!p){if(spf[C-1]===C-1&&spf[C+1]===C+1)twin++;else bad++}
    else if(p<=7){ck(n-t[i]<=2*r);R+=r;events++;t[i]=n;ck(C+p-1<=2*n);push(i,C+p-1)}
    else {if(!groups.has(p))groups.set(p,[]);groups.get(p).push([i,n])}i=j
   }
   for(let [p,a] of groups){
    const stop=a.length>=T;maxMass=Math.max(maxMass,a.length);
    let classes=new Map(),ids=a.map(x=>x[0]).sort((a,b)=>a-b);maxRootDist=Math.max(maxRootDist,2*(ids[ids.length-1]-ids[0]));
    for(let [i,n] of a){let q=pp[i],D=pd[i],g=q?C-D-q+1:0;if(q){ck(g>=0&&g<L&&g%2===0);ck((D-1)%q===0||(D+1)%q===0);ck((C-g)%q===0||(C-g+2)%q===0);ck(pm[i]<T)}
      else ck(C-root(i)<L);
      let k=q?D*B+q:-(i+1);
      if(!classes.has(k))classes.set(k,{q,D,g,r:q?pr[i]:0,m:q?pm[i]:1,ids:[]});
      let cl=classes.get(k);ck(cl.m===(q?pm[i]:1));cl.ids.push(i);
    }
    let c=[...classes.values()];for(let a of c){a.ids.sort((a,b)=>a-b);ck(a.ids.length<=a.m)}
    if(allSeen){for(let j=0;j<ids.length;j++)for(let k=j+1;k<ids.length;k++)if(2*(ids[k]-ids[j])>d)allSeen.add(ids[j]*N+ids[k])}
    for(let j=0;j<c.length;j++)for(let k=j+1;k<c.length;k++){
      let u=c[j],v=c[k],rr=+(u.r>=Z)+ +(v.r>=Z),small=Math.min(u.m,v.m),big=Math.max(u.m,v.m),prod=u.m*v.m,isLL=u.q&&v.q&&small>=A,isRoot=!u.q||!v.q,isSame=u.q&&u.q===v.q,near=u.q&&v.q&&u.q!==v.q&&Math.abs(u.q-v.q)<=L+2;
      if(isSame){sameQ++;if(u.q>L+2){ck(Math.abs(u.D-v.D)===2);ck(Math.min(u.r,v.r)===3)}}
      if(2*Math.max(u.ids[u.ids.length-1]-v.ids[0],v.ids[v.ids.length-1]-u.ids[0])<=d)continue;
      let far=0,fresh=0;
      for(let x of u.ids)for(let y of v.ids){
        if(2*Math.abs(x-y)<=d)continue;
        far+=2;let l=Math.min(x,y),h=Math.max(x,y),key=l*N+h;if(!seen.has(key)){seen.add(key);fresh+=2}
      }
      if(!far)continue;J+=far;P+=fresh;
      let key=massbin(small)+","+massbin(big)+","+rr;
      if(!bins.has(key))bins.set(key,{smallBand:massbin(small),largeBand:massbin(big),rough:rr,J:0,P:0,groups:0});let b=bins.get(key);b.J+=far;b.P+=fresh;b.groups++;
      roughJ[rr]+=far;roughCounts[rr]+=fresh;
      if(isRoot){rootJ+=far;firstRoot+=fresh}
      if(isSame){sameQFar+=far;sameQFirst+=fresh}
      if(near)distinctNearQ+=fresh;
      if(prod<=T/Math.max(1,Math.log(Math.log(B)))**3)productSmall+=fresh;
      if(prod<=T)productMedium+=fresh;
      if(rr&&prod<=T*Math.log(B)**1.5)productRough+=fresh;
      if(isLL){largeLarge+=fresh;largeLargeJ+=far;if(rr)largeLargeRough+=fresh;if(rr===2)largeLargeBothRough+=fresh;if(!rr)largeLargeBothCheap+=fresh;if(near)largeLargeNearQ+=fresh;if(isSame)largeLargeSameQ+=fresh;if(stop)largeLargeStop+=fresh;
        let f=prod/(T*T);llprod[f>=.25?3:f>=.0625?2:f>=.015625?1:0]+=fresh;
        if(small>=T/4)largeLargeLargest+=fresh;
        if(fresh){let e={p,C,stop,q:u.q,q2:v.q,D:u.D,D2:v.D,m:u.m,m2:v.m,sub:u.ids.length,sub2:v.ids.length,r:u.r,r2:v.r,far,fresh};if(largeExamples.length<5)largeExamples.push(e);else{let j=0;for(let k=1;k<5;k++)if(largeExamples[k].fresh<largeExamples[j].fresh)j=k;if(e.fresh>largeExamples[j].fresh)largeExamples[j]=e}}
      }
      if(stop)firstAtStop+=fresh;
    }
    if(stop){
     stopped+=a.length;sinks++;stopMax=Math.max(stopMax,a.length);let far=0,very=0;const Dfar=Math.floor(X/Math.sqrt(Math.log(B)));
     for(let j=0;j<ids.length;j++)for(let k=j+1;k<ids.length;k++)if(2*(ids[k]-ids[j])>d){far+=2;ck(seen.has(ids[j]*N+ids[k]),"stop pair missing")}
     stopFar+=far;ck(far>=a.length*Math.max(0,a.length-1-d));
     // Partition whole stopping fibre into blocks of T, discard final partial, retaining >= half the tags.
     for(let s=0;s+T<=ids.length;s+=T)for(let j=s;j<s+T;j++)for(let k=j+1;k<s+T;k++){witnessPairs+=2;if(2*(ids[k]-ids[j])>d)witnessFar+=2;if(2*(ids[k]-ids[j])>Dfar)witnessVeryFar+=2}
     stops.push({p,C,m:a.length,far,span:2*(ids[ids.length-1]-ids[0]),parents:c.length});
    }else{
     for(let [i,n] of a){ck(r<=p&&n-t[i]<=2*r);R+=r;events++;pp[i]=p;pd[i]=C;pr[i]=r;pm[i]=a.length;t[i]=n;h[i]++;ck(C+p-1<=2*n);push(i,C+p-1)}
    }
   }
  }
  if(allSeen){ck(allSeen.size===seen.size,"independent all-pair oracle");for(let k of allSeen)ck(seen.has(k))}
  ck(P===2*seen.size&&P<=J&&P>=stopFar&&stopFar>=Math.max(0,T-1-d)*stopped);
  ck(stopped+twin+bad===N&&roughCounts.reduce((a,b)=>a+b,0)===P&&roughJ.reduce((a,b)=>a+b,0)===J);
  ck(largeLarge===largeLargeRough+largeLargeBothCheap&&llprod.reduce((a,b)=>a+b,0)===largeLarge);
  ck(witnessFar>=Math.floor(stopped/2)*Math.max(0,T-1-d)||stopped===0,"witness lower");
  firstEarlierThanStop=P-firstAtStop;
  runs.push({T,d,Z,A,a0,R,events,stopped,sinks,twin,bad,literal,maxMass,maxRootDist,stopMax,P,J,stopFar,firstAtStop,firstEarlierThanStop,ratio:P/(N*T),rootJ,firstRoot,sameQ,sameQFar,sameQFirst,distinctNearQ,roughCounts,roughJ,largeLarge,largeLargeJ,largeLargeRough,largeLargeBothRough,largeLargeBothCheap,largeLargeNearQ,largeLargeSameQ,largeLargeStop,largeLargeLargest,llprod,productSmall,productMedium,productRough,witnessFar,witnessVeryFar,witnessPairs,largeExamples,bins:[...bins.values()].sort((a,b)=>a.smallBand-b.smallBand||a.largeBand-b.largeBand||a.rough-b.rough),stops})
 }
 return {X,B,N,runs}
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a),Number(a)>=262144?'wide':'all')));
