// Exact source-flow DAG and bounded spatial variance merge/split ledger.
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
  // The immutable projected-path DAG on the original stopped tags.
  const nodes=new Map(),edges=new Map();
  function node(key){if(!nodes.has(key))nodes.set(key,{ids:[],in:new Map(),out:new Map(),root:[],p:key%B,C:Math.floor(key/B),qual:[]});return nodes.get(key)}
  // Decode labels using each record, not key%B (p=B is possible).
  for(let [i,hs] of hist){
   for(let j=0;j<hs.length;j++){
    let e=hs[j],v=node(e.key);v.p=e.p;v.C=e.C;v.r=e.r;v.ids.push(i);
    if(!j)v.root.push(i);
    else{let a=hs[j-1],u=node(a.key),key=a.key+":"+e.key;
     if(!edges.has(key)){let ids=[];edges.set(key,ids);u.out.set(e.key,ids);v.in.set(a.key,ids)}
     edges.get(key).push(i);
     ck(e.prior.key===a.key);
     if(a.k<=4&&a.k>0&&e.p>=31&&e.r<=31&&a.p!==e.p)v.qual.push([i,a.p]);
    }
   }
  }
  for(let [key,v] of nodes){let inc=v.root.length+[...v.in.values()].reduce((s,a)=>s+a.length,0),outc=[...v.out.values()].reduce((s,a)=>s+a.length,0);
   ck(inc===v.ids.length&&outc===(stops.has(key)?0:v.ids.length),"flow");
   if(stops.has(key))ck(v.ids.length===stops.get(key));v.ids.sort((a,b)=>a-b);
   for(let a of v.in.values())a.sort((a,b)=>a-b);
  }
  const T0=mode==="uniform"?T:W*floor;
  // Each origin M has spacing 2. For an id-sorted array the raw kernel sum is integer.
  function kernel(a,D,d=Infinity){
   let l=0,u=0,pl=0,pu=0,total=0,prefix=0;
   for(let j=0;j<a.length;j++){
    while(l<j&&2*(a[j]-a[l])>d){pl+=a[l++];}
    if(u<l){u=l;pu=pl}
    while(u<j&&2*(a[j]-a[u])>=D){pu+=a[u++];}
    total+=(u-l)*D+2*((j-u)*a[j]-(prefix-pu));prefix+=a[j];
   }
   return total;
  }
  let kernelTests=0;
  for(let a of [[0,1,2,3,12],[1,4,8,9,11,29],[],[2]])for(let D of [1,3,8,31])for(let d of [0,2,6,15,Infinity]){
   let v=0;for(let i=0;i<a.length;i++)for(let j=i+1;j<a.length;j++)if(2*(a[j]-a[i])<=d)v+=Math.min(D,2*(a[j]-a[i]));
   ck(kernel(a,D,d)===v,"kernel brute");kernelTests++;
  }
  const Ds=[...new Set([1,Math.max(1,Math.floor(T0/16)),Math.max(1,Math.floor(T0/4)),Math.max(1,Math.floor(T0/2)),T0])],runs=[];
  for(let D of Ds){let cuts=[...new Set([2,Math.max(2,Math.floor(Math.sqrt(D))),Math.max(2,Math.floor(D/4)),D])].sort((a,b)=>a-b);
   let s={D,T0,nodes:nodes.size,edges:edges.size,rootCount:0,terminal:0,merge:0,split:0,proxy:0,minority:0,mergeKeys:0,splitKeys:0,qualProxy:0,qualKeys:0,qualOvershoot:0,qualUncovered:0,near:cuts.map(d=>({d,proxy:0,far:0})),maxMass:0};
   for(let [key,v] of nodes){let m=v.ids.length,base=kernel(v.ids,D),F=base/(D*m),incoming=0,inRaw=0,outgoing=0,maxIn=v.root.length?1:0;
    for(let a of v.in.values()){let x=kernel(a,D);incoming+=x/(D*a.length);inRaw+=x;maxIn=Math.max(maxIn,a.length);}
    for(let a of v.out.values())outgoing+=kernel(a,D)/(D*a.length);
    let merge=F-incoming,proxy=(base-inRaw)/(D*m);ck(merge>=-1e-8&&merge<=proxy+1e-8,"Jensen merge");
    s.merge+=merge;s.proxy+=proxy;s.rootCount+=v.root.length;s.minority+=m-maxIn;s.maxMass=Math.max(s.maxMass,m);if(merge>1e-9)s.mergeKeys++;
    if(stops.has(key)){s.terminal+=F;ck(m>=D&&F>=m/8-.25,"terminal bound");}
    else{let split=F-outgoing;ck(split>=-1e-8,"split variance");s.split+=split;if(split>1e-9)s.splitKeys++;}
    for(let z of s.near){let w=kernel(v.ids,D,z.d);for(let a of v.in.values())w-=kernel(a,D,z.d);
     ck(w>=0&&w<=base-inRaw,"near raw");let near=w/(D*m);ck(near<=((z.d/2|0)*((z.d/2|0)+1))/D+1e-8,"spacing near bound");z.proxy+=near;z.far+=proxy-near;}
    if(v.qual.length>1){let aa=v.qual.map(x=>x[0]).sort((a,b)=>a-b),groups=new Map();for(let [i,q] of v.qual){if(!groups.has(q))groups.set(q,[]);groups.get(q).push(i)}
     let w=kernel(aa,D);for(let a of groups.values()){a.sort((a,b)=>a-b);w-=kernel(a,D)}
     let val=w/(D*m);ck(val>=0&&val<=proxy+1e-8);if(val>0){s.qualKeys++;if(m<=4*v.p)s.qualProxy+=val;else{s.qualUncovered+=val;if(stops.has(key))s.qualOvershoot+=val;}}
    }
   }
   ck(s.rootCount===S&&Math.abs(s.merge-s.split-s.terminal)<1e-6*Math.max(1,S),"telescoping");ck(s.terminal<=s.proxy+1e-6);
   for(let z of s.near)ck(Math.abs(z.proxy+z.far-s.proxy)<1e-6*Math.max(1,s.proxy)&&z.far+1e-6>=s.terminal-z.proxy);
   runs.push(s)
  }
  out.push({mode,T0,S,stopKeys:stops.size,R,twin,bad,kernelTests,runs});
 }
 return {X,B,N,runs:out}
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
