// Independent two-pass stopped-cohort witness first-contact audit, balanced blocks.
function stopWitnessAudit(X){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,L=210,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=(b,msg="assertion")=>{if(!b)throw Error(msg)},mod=(x,m)=>(x%m+m)%m;
 function hit(t,C,K){let n=K+1,q=0;for(let s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let h=t+1+mod((s===-1?0:p+2)-t-1,2*p);if(h<n||(h===n&&p<q)){n=h;q=p}while(v%p===0)v/=p}}return [n,q]}
 const caps=[Math.max(2,Math.floor(B/4)),Math.max(2,Math.floor(B/2))],runs=[];
 for(let T of caps){
  const d=Math.floor(T/2),A=Math.ceil(Math.sqrt(T)),Z=Math.ceil(Math.sqrt(B)),Dfar=Math.floor(X/Math.sqrt(Math.log(B)));
  const head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N),t=new Int32Array(N),K=new Int32Array(N);
  const root=i=>2*X+4*i,put=(i,C)=>{next[i]=head[C/2];head[C/2]=i};
  for(let i=0;i<N;i++){let M=X+2*i+1;t[i]=M+2;K[i]=Math.floor((7*M-1)/4);put(i,root(i))}
  let masses=new Map(),cohorts=[],stopKeys=new Set(),R=0,stopped=0,twin=0,bad=0;
  for(let C=2*X;C<7*X;C+=2){let i=head[C/2];if(i<0)continue;let g=new Map(),r=Math.min(spf[C-1],spf[C+1]);
   while(i>=0){let j=next[i],[n,p]=hit(t[i],C,K[i]);if(!p){if(spf[C-1]===C-1&&spf[C+1]===C+1)twin++;else bad++}else if(p<=7){R+=r;t[i]=n;put(i,C+p-1)}else{if(!g.has(p))g.set(p,[]);g.get(p).push([i,n])}i=j}
   for(let [p,a] of g){let k=C*B+p;masses.set(k,a.length);if(a.length>=T){stopped+=a.length;stopKeys.add(k);cohorts.push({p,C,ids:a.map(e=>e[0]).sort((a,b)=>a-b)})}
    else for(let [i,n] of a){R+=r;t[i]=n;put(i,C+p-1)}}
  }
  ck(stopped+twin+bad===N);
  let totals={allFar:0,witnessFar:0,witnessVeryFar:0,allFirst:0,witnessFirst:0,allJ:0,witnessJ:0,allLL:0,witnessLL:0,allLLCheap:0,witnessLLCheap:0,allLLBothRough:0,witnessLLBothRough:0,allLLSameQ:0,witnessLLSameQ:0,allLLNearQ:0,witnessLLNearQ:0,allLLFull:0,witnessLLFull:0,allFirstAtStop:0,witnessFirstAtStop:0,witnessBlockCount:0,witnessMaxDegree:0,veryFarEarlier:new Set(),totalLongRoots:0,longRootsCost:0,stopCost:0,allParentProductBins:[0,0,0,0],witnessParentProductBins:[0,0,0,0],witnessMinParentBins:{},top:[]};
  for(let {p,C,ids} of cohorts){
   // Balanced disjoint blocks of size in [T,2T-1]; every stopped root retained.
   let m=ids.length,k=Math.floor(m/T),bsize=Math.floor(m/k),extra=m%k,block=new Int32Array(m),s=0;
   for(let b=0;b<k;b++){let size=bsize+(b<extra?1:0);ck(size>=T&&size<2*T);for(let j=s;j<s+size;j++)block[j]=b;s+=size;totals.witnessBlockCount++;totals.witnessMaxDegree=Math.max(totals.witnessMaxDegree,size-1)}
   ck(s===m);
   let bucket=new Map(),seen=new Uint8Array(m*m),allFar=0,witFar=0,localLL=0,localLLCheap=0,localLLSameQ=0,localFresh=0,localWitFresh=0;
   for(let j=0;j<m;j++){let i=ids[j],tt=X+2*i+3,D=root(i),q=0,E=0,cost=0;
    for(;;){let [n,a]=hit(tt,D,K[i]);ck(a>0,"source ended before its stop");let r=Math.min(spf[D-1],spf[D+1]);
     if(a>7){let key=D*B+a,prior=q?E*B+q:0,pm=q?masses.get(prior):1;ck(pm!==undefined&&pm<T,"prior mass");
      if(!bucket.has(key))bucket.set(key,{p:a,C:D,entries:[]});bucket.get(key).entries.push({j,q,E,pm,r:q?Math.min(spf[E-1],spf[E+1]):0,prior});
      if(stopKeys.has(key)){ck(D===C&&a===p,"wrong stop");break}q=a;E=D}
     cost+=r;D+=a-1;tt=n
    }
    ck(D-root(i)<=4*cost+6);totals.stopCost+=cost;
    if(D-root(i)>2*Dfar){totals.totalLongRoots++;totals.longRootsCost+=cost}
   }
   for(let a of [...bucket.values()].sort((a,b)=>a.C-b.C||a.p-b.p)){
    let es=a.entries,stop=a.p===p&&a.C===C;
    for(let j=0;j<es.length;j++)for(let l=j+1;l<es.length;l++){
     let u=es[j],v=es[l],i=Math.min(u.j,v.j),h=Math.max(u.j,v.j),dist=2*(ids[h]-ids[i]);
     if(dist<=d)continue;
     let wit=block[i]===block[h],key=i*m+h,sameParent=u.q&&v.q&&u.prior===v.prior;
     if(!sameParent){totals.allJ+=2;if(wit)totals.witnessJ+=2}
     if(seen[key])continue;
     ck(!sameParent,"first pair same parent");seen[key]=1;totals.allFirst+=2;localFresh+=2;
     if(wit){totals.witnessFirst+=2;localWitFresh+=2}
     if(stop){totals.allFirstAtStop+=2;if(wit)totals.witnessFirstAtStop+=2}
     const sm=Math.min(u.pm,v.pm),prod=u.pm*v.pm,rr=+(u.r>=Z)+ +(v.r>=Z);
     let pi=prod>=T*T/4?3:prod>=T*T/16?2:prod>=T?1:0;
     totals.allParentProductBins[pi]+=2;if(wit)totals.witnessParentProductBins[pi]+=2;
     if(wit){let bin=Math.floor(Math.log2(sm));totals.witnessMinParentBins[bin]=(totals.witnessMinParentBins[bin]||0)+2}
     if(u.q&&v.q&&sm>=A){
      totals.allLL+=2;if(wit){totals.witnessLL+=2;localLL+=2}
      if(!rr){totals.allLLCheap+=2;if(wit){totals.witnessLLCheap+=2;localLLCheap+=2}}
      if(rr===2){totals.allLLBothRough+=2;if(wit)totals.witnessLLBothRough+=2}
      if(u.q===v.q){totals.allLLSameQ+=2;if(wit){totals.witnessLLSameQ+=2;localLLSameQ+=2}}
      else if(Math.abs(u.q-v.q)<=L+2){totals.allLLNearQ+=2;if(wit)totals.witnessLLNearQ+=2}
      if(sm>=T/4){totals.allLLFull+=2;if(wit)totals.witnessLLFull+=2}
     }
    }
   }
   for(let j=0;j<m;j++)for(let l=j+1;l<m;l++){
    let dist=2*(ids[l]-ids[j]);if(dist<=d)continue;allFar+=2;ck(seen[j*m+l],"missing pair");
    if(block[j]===block[l]){witFar+=2;if(dist>Dfar){totals.witnessVeryFar+=2;totals.veryFarEarlier.add(ids[j])}}
   }
   ck(allFar===localFresh&&witFar===localWitFresh&&witFar>=m*Math.max(0,T-1-d));
   totals.allFar+=allFar;totals.witnessFar+=witFar;
   let rec={p,C,m,allFar,witFar,witLL:localLL,witLLCheap:localLLCheap,witLLSameQ:localLLSameQ};
   if(totals.top.length<5)totals.top.push(rec);else{let j=0;for(let k=1;k<5;k++)if(totals.top[k].witLL<totals.top[j].witLL)j=k;if(rec.witLL>totals.top[j].witLL)totals.top[j]=rec}
  }
  ck(totals.allFar===totals.allFirst&&totals.witnessFar===totals.witnessFirst);
  ck(totals.allJ>=totals.allFirst&&totals.witnessJ>=totals.witnessFirst);
  ck(totals.witnessFar>=stopped*Math.max(0,T-1-d));
  ck(totals.witnessVeryFar<=2*totals.witnessMaxDegree*totals.veryFarEarlier.size);
  ck(totals.stopCost<=R&&totals.longRootsCost<=R&&totals.veryFarEarlier.size<=totals.totalLongRoots);
  totals.veryFarEarlier=totals.veryFarEarlier.size;
  runs.push({T,d,A,Z,Dfar,R,stopped,twin,bad,sinks:cohorts.length,...totals});
 }
 return {X,B,N,runs};
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(stopWitnessAudit(Number(a))));
