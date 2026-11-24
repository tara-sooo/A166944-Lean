// Greedy residual matching: prefix-cost and first-large-label crossing audit.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,L=210,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=(x,m="assertion")=>{if(!x)throw Error(m)},mod=(x,m)=>(x%m+m)%m,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c}return a};
 function hit(t,C,K){let n=K+1,p=0;for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(q>B)break;let u=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(u<n||(u===n&&q<p)){n=u;p=q}while(v%q===0)v/=q}}return [n,p]}
 const out=[];
 for(let mode of ["uniform","hybrid"]){
  const T=Math.max(2,Math.floor(B/4)),floor=Math.ceil(Math.sqrt(B)),W=4,cap=p=>mode==="uniform"?T:W*Math.max(floor,p);
  const head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N),t=new Int32Array(N),K=new Int32Array(N),masses=new Map(),stops=new Map(),cohorts=[];
  const put=(i,C)=>{next[i]=head[C/2];head[C/2]=i};
  for(let i=0;i<N;i++){let M=X+2*i+1;t[i]=M+2;K[i]=Math.floor((7*M-1)/4);put(i,2*M-2)}
  let R=0,S=0,twin=0,bad=0,events=0,literal=0;
  for(let C=2*X;C<7*X;C+=2){let i=head[C/2];if(i<0)continue;let groups=new Map(),r=Math.min(spf[C-1],spf[C+1]);
   while(i>=0){let j=next[i],[n,p]=hit(t[i],C,K[i]);if(X<=1024){let nn=K[i]+1,pp=0;for(let k=t[i]+1;k<=K[i];k++){let g=gcd(k%2?k-2:k,C+(k%2?1:-1));if(g>1&&spf[g]<=B){nn=k;pp=spf[g];break}}ck(nn===n&&pp===p,"literal");literal++}
    if(!p){if(spf[C-1]===C-1&&spf[C+1]===C+1)twin++;else bad++}
    else if(p<=7){R+=r;events++;t[i]=n;put(i,C+p-1)}
    else{if(!groups.has(p))groups.set(p,[]);groups.get(p).push([i,n])}i=j}
   for(let [p,a] of groups){let key=C*B+p;ck(!masses.has(key));masses.set(key,a.length);
    if(a.length>=cap(p)){S+=a.length;stops.set(key,a.length);cohorts.push({C,p,ids:a.map(x=>x[0]).sort((a,b)=>a-b)})}
    else for(let [i,n] of a){R+=r;events++;t[i]=n;put(i,C+p-1)}
   }
  }
  ck(S+twin+bad===N);
  // Replay exactly the stopped tags. Pair in increasing horizon, but never change their trajectories.
  const hist=new Map(),arrivals=new Map(),finalKey=new Map();
  for(const {C:Cs,p:ps,ids} of cohorts)for(const i of ids){
   let M=X+2*i+1,C=2*M-2,t=M+2,prior=null,hs=[],guard=0,cost=0;
   for(;;){let [n,p]=hit(t,C,K[i]);ck(p>0,"replay ended");let r=Math.min(spf[C-1],spf[C+1]);ck(n-t<=2*r);
    if(p>7){let key=C*B+p,b=n%2?6:0,h=2*n-(C+p-1),k=(h-b)/(2*p);ck(k>=0&&Number.isInteger(k));
     let e={i,key,C,p,n,t,b,h,k,r,prior,cost};
     if(prior){let g=C-prior.postC,dt=n-prior.n,err=b-prior.b-2*dt+g-1;ck(g>=0&&g<L&&dt>0&&dt<=3*L+2*r);ck(2*prior.k*prior.p===(2*k+1)*p+err&&Math.abs(err)<=7*L+4*r+7&&err%2!==0);e.err=err;}
     hs.push(e);if(!arrivals.has(key))arrivals.set(key,[]);arrivals.get(key).push(i);
     if(stops.has(key)){ck(C===Cs&&p===ps);finalKey.set(i,key);break}
     prior={key,p,C,n,b,h,k,postC:C+p-1};
    }
    cost+=r;t=n;C+=p-1;ck(++guard<7*X)
   }
   hist.set(i,hs)
  }
  ck(hist.size===S&&finalKey.size===S);
  let runs=[];
  const keys=[...arrivals.keys()].sort((a,b)=>a-b);
  for(let s of [4,8,16,32]){
   let paired=new Set(),pool=new Map(),residual=new Map(),witness=[],endKey=new Map();
   let st={s,pairs:0,unmatched:0,pairedAtStop:0,pairedBeforeStop:0,differentFinalStops:0,earlierFirstContact:0,firstAtPairing:0,firstAtStop:0,maxPool:0,maxResidual:0,maxParentResidual:0,maxActualAtFirst:0,actualOverS:0,actualOver4p:0,firstP11:0,firstP31:0,root:0,bothReset:0,mixed:0,positive:0,sameQ:0,sameP:0,distinct:0,sameLargeQ:0,sameLargeParity:0,excludedHypothesis:0,firstContactChecks:0,armChecks:0,modes:[[11,4,31],[31,4,31],[11,8,7],[Math.ceil(Math.sqrt(Math.log(B))),4,31]].map(([P,H,z])=>({P,H,z,qualifying:0,oldMassFails:0,longLag:0,atStop:0,earlier:0,distinct:0,sameQ:0,sameP:0,root:0,reset:0,examples:[]}))};
   for(let key of keys){let a=arrivals.get(key).filter(i=>!paired.has(i)).sort((a,b)=>a-b),m=a.length;pool.set(key,m);st.maxPool=Math.max(st.maxPool,m);let k=m>=s?Math.floor(m/2):0;
    for(let j=0;j<k;j++){let i=a[j],v=a[m-k+j];ck(!paired.has(i)&&!paired.has(v)&&2*(v-i)>=m&&m>=s,"far pairing");paired.add(i);paired.add(v);endKey.set(i,key);endKey.set(v,key);witness.push([i,v,key]);if(stops.has(key))st.pairedAtStop++;else st.pairedBeforeStop++;if(finalKey.get(i)!==finalKey.get(v))st.differentFinalStops++}
    residual.set(key,m-2*k);ck(m-2*k<s);st.maxResidual=Math.max(st.maxResidual,m-2*k)
   }
   st.pairs=witness.length;st.unmatched=S-2*st.pairs;ck(st.unmatched>=0&&st.unmatched<=(s-1)*stops.size);
   let useParent=new Map(),useCurrent=new Map();
   for(let [i,v,pairKey] of witness){let a=hist.get(i),b=hist.get(v),ii=0,jj=0;
    while(a[ii].key!==b[jj].key){if(a[ii].key<b[jj].key)ii++;else jj++;ck(ii<a.length&&jj<b.length,"no shared key")}
    let x=a[ii],y=b[jj],key=x.key,p=x.p;ck(key<=pairKey&&pool.get(key)>=2);
    if(key<pairKey){ck(pool.get(key)<s,"earlier contact would already pair");st.earlierFirstContact++}else st.firstAtPairing++;
    if(stops.has(key))st.firstAtStop++;
    useCurrent.set(key,(useCurrent.get(key)||0)+1);ck(2*useCurrent.get(key)<=pool.get(key));
    let lag=(x.n-y.n)/(2*p);ck(Number.isInteger(lag));st.firstContactChecks++;
    let m=masses.get(key);st.maxActualAtFirst=Math.max(st.maxActualAtFirst,m);if(m>s)st.actualOverS++;if(m>4*p)st.actualOver4p++;if(p<=11)st.firstP11++;if(p<=31)st.firstP31++;
    for(let e of [x,y])if(e.prior){let pk=e.prior.key;ck(pk<key&&residual.get(pk)<s);useParent.set(pk,(useParent.get(pk)||0)+1);ck(useParent.get(pk)<=residual.get(pk),"residual source cap");st.maxParentResidual=Math.max(st.maxParentResidual,residual.get(pk))}
    let q=x.prior?.p,qq=y.prior?.p,kind;
    if(!q||!qq){st.root++;kind="root"}
    else {ck(x.prior.key!==y.prior.key);st.armChecks++;ck(x.k-y.k===2*lag);
     let k=x.prior.k,k2=y.prior.k;
     if(!k&&!k2)st.bothReset++;else if(!k||!k2)st.mixed++;else st.positive++;
     if(q===qq){st.sameQ++;kind="sameQ";if(q>L+2){st.sameLargeQ++;let A=x.prior,B2=y.prior;ck(Math.abs(A.C-B2.C)===2&&A.b!==B2.b&&Math.abs(k-k2)%2===1,"opposite parent parity");st.sameLargeParity++;
       if(p>Math.max(2*k,2*k2,Math.abs(k2*x.err-k*y.err),Math.abs(x.err),Math.abs(y.err)))throw Error("same q excluded");
     }}else if(q===p||qq===p){st.sameP++;kind="sameP"}else{st.distinct++;kind="distinct"}
     let H0=Math.max(k,k2),E0=Math.max(Math.abs(x.err),Math.abs(y.err));if(p>Math.max(4*H0*(L+3),2*H0*E0,E0+1)){ck(k>0&&k2>0&&kind==="distinct");st.excludedHypothesis++}
    }
    for(let w of st.modes)if(p>=w.P&&x.r<=w.z&&(!x.prior||x.prior.k<=w.H)&&(!y.prior||y.prior.k<=w.H)){
     w.qualifying++;if(m>4*p)w.oldMassFails++;if(Math.abs(lag)>4)w.longLag++;if(stops.has(key))w.atStop++;if(key<pairKey)w.earlier++;
     if(kind==="root")w.root++;else if(!x.prior.k||!y.prior.k)w.reset++;else w[kind]++;
     if(w.examples.length<2)w.examples.push({p,C:x.C,q,qq,lag,m,pool:pool.get(key),priorResidual:x.prior?residual.get(x.prior.key):null,otherResidual:y.prior?residual.get(y.prior.key):null});
    }
   }
   ck(st.pairs===st.earlierFirstContact+st.firstAtPairing&&st.pairs===st.pairedAtStop+st.pairedBeforeStop&&st.root+st.bothReset+st.mixed+st.positive===st.pairs&&st.root+st.sameQ+st.sameP+st.distinct===st.pairs);
   let budgets={total:0,highCost:0,lowCost:0,maxCost:0,maxLabel:0,maxGain:0,allPrefixChecks:0,crossings:[]};
   let byKey=new Map();
   for(let [i,hs] of hist){let target=endKey.get(i)||finalKey.get(i),end=hs.find(e=>e.key===target);ck(!!end,"matching endpoint");budgets.total+=end.cost;budgets.maxCost=Math.max(budgets.maxCost,end.cost);budgets.maxGain=Math.max(budgets.maxGain,end.C-(2*(X+2*i+1)-2));
    ck(end.C-(2*(X+2*i+1)-2)<=4*end.cost+6,"gain budget");
    let hc=0,previous=null;
    for(let e of hs){if(e.key>target)break;budgets.maxLabel=Math.max(budgets.maxLabel,e.p);
     if(previous)ck(e.cost-previous.cost-previous.r>=0&&e.cost-previous.cost-previous.r<=1.5*L,"low cost");else ck(e.cost<=1.5*L,"initial low cost");
     if(e.key===target)break;
     hc+=e.r;byKey.set(e.key,(byKey.get(e.key)||0)+1);ck(byKey.get(e.key)<=residual.get(e.key),"executed effective cap");previous=e;
    }
    budgets.highCost+=hc;budgets.lowCost+=end.cost-hc;budgets.allPrefixChecks++;
   }
   ck(budgets.total===budgets.highCost+budgets.lowCost&&budgets.lowCost<=1.5*L*(S+[...byKey.values()].reduce((a,b)=>a+b,0))&&budgets.total<=R);
   for(let Y of [17,31,Math.max(11,Math.ceil(Math.sqrt(B))),Math.max(11,Math.ceil(B**.75)),Math.max(11,Math.ceil(B/2))]){
    let z={Y,crossers:0,rough:0,expensivePrefix:0,cheapPrefix:0,rootRough:0,priorRough:0,proposedAtPairing:0,proposedAtStop:0,prefixCost:0,prefixHighCost:0,prefixLowCost:0,roughKeys:0,roughTransfers:0,roughTransferMass:0,maxRoughTransfer:0,examples:[]},mk=new Map(),rk=new Set();
    for(let [i,hs] of hist){let target=endKey.get(i)||finalKey.get(i),end=hs.find(e=>e.key===target),cross=hs.find(e=>e.key<=target&&e.p>=Y);let endpoint=cross||end,high=0;
     for(let e of hs){if(e.key>=endpoint.key)break;ck(e.p<Y);high+=e.r;}
     z.prefixCost+=endpoint.cost;z.prefixHighCost+=high;z.prefixLowCost+=endpoint.cost-high;
     if(!cross)continue;z.crossers++;if(cross.key===target&&endKey.has(i))z.proposedAtPairing++;if(stops.has(cross.key))z.proposedAtStop++;
     if(cross.cost>=Y/16)z.expensivePrefix++;else{z.cheapPrefix++;if(Y>=32)ck(cross.r>=cross.p/8,"rough first crossing")}
     if(cross.r>=cross.p/8){z.rough++;rk.add(cross.key);if(cross.prior){z.priorRough++;ck(cross.prior.p<Y);let k=cross.prior.key+":"+cross.key;let a=mk.get(k)||{n:0,cap:residual.get(cross.prior.key)};a.n++;ck(a.n<=a.cap);mk.set(k,a);}else z.rootRough++;
      if(z.examples.length<2)z.examples.push({p:cross.p,C:cross.C,r:cross.r,cost:cross.cost,q:cross.prior?.p});
     }
    }
    z.roughKeys=rk.size;z.roughTransfers=mk.size;for(let a of mk.values()){z.roughTransferMass+=a.cap;z.maxRoughTransfer=Math.max(z.maxRoughTransfer,a.n)}
    ck(z.crossers===z.expensivePrefix+z.cheapPrefix&&z.rough===z.rootRough+z.priorRough&&z.priorRough<=z.roughTransferMass&&z.prefixCost<=budgets.total&&z.prefixCost===z.prefixHighCost+z.prefixLowCost);budgets.crossings.push(z)
   }
   st.budgets=budgets;runs.push(st)
  }
  out.push({mode,T,floor,W,R,S,twin,bad,stopKeys:stops.size,runs});
 }
 return {X,B,N,runs:out}
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
