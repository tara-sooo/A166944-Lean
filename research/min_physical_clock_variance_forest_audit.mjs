// Physical-clock refinement and terminal virtual merge forest audit.
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
  // Refine the projected graph by the proposed event clock. Stop nodes are virtual unions.
  const T0=mode==="uniform"?T:W*floor,phys=new Map(),virt=new Map(),proj=new Map();
  function node(map,key){if(!map.has(key))map.set(key,{ids:[],in:new Map(),root:0,next:null});return map.get(key)}
  for(let [i,hs] of hist){
   for(let j=0;j<hs.length;j++){
    let e=hs[j],k=e.key+":"+e.n,v=node(phys,k);v.ids.push(i);v.p=e.p;v.C=e.C;v.n=e.n;v.key=e.key;
    let pv=node(proj,e.key);pv.ids.push(i);if(!pv.in.has(k))pv.in.set(k,[]);pv.in.get(k).push(i);
    if(!j)v.root++;
    else {let a=hs[j-1],ak=a.key+":"+a.n,u=phys.get(ak);ck(u.next===null||u.next===k,"physical successor uniqueness");u.next=k;if(!v.in.has(ak))v.in.set(ak,[]);v.in.get(ak).push(i)}
    if(j===hs.length-1){let vk="s:"+e.key;ck(stops.has(e.key)&& (v.next===null||v.next===vk));v.next=vk;let w=node(virt,vk);w.ids.push(i);if(!w.in.has(k))w.in.set(k,[]);w.in.get(k).push(i)}
   }
  }
  let roots=0,branch=0,virtualClasses=0,minority=0,maxClocks=0,oneClockStops=0,largestPhysical=0,physicalAtStop=0;
  for(let [k,v] of phys){let inc=v.root+[...v.in.values()].reduce((s,a)=>s+a.length,0);ck(inc===v.ids.length&&v.next!==null);let w=v.next.startsWith("s:")?virt.get(v.next):phys.get(v.next);ck(w.in.get(k).length===v.ids.length);roots+=v.root;if(v.root+v.in.size>=2)branch++;v.ids.sort((a,b)=>a-b);for(let a of v.in.values())a.sort((a,b)=>a-b);}
  for(let [k,v] of virt){let m=v.ids.length,a=[...v.in.values()];ck(a.reduce((s,x)=>s+x.length,0)===m);v.ids.sort((a,b)=>a-b);for(let x of a)x.sort((a,b)=>a-b);let mx=Math.max(...a.map(x=>x.length));minority+=m-mx;virtualClasses+=a.length;maxClocks=Math.max(maxClocks,a.length);if(a.length===1)oneClockStops++;largestPhysical=Math.max(largestPhysical,mx);physicalAtStop+=m; if(a.length>=2)branch++;}
  ck(roots===S&&physicalAtStop===S&&virt.size===stops.size&&branch<=S-virt.size,"forest leaf bound");
  // Four times D^3 times the squared distance between unit-normalized hat translates.
  function scalar(t,D){return t<=D?6*D*t*t-3*t*t*t:t<2*D?4*D**3-(2*D-t)**3:4*D**3;}
  function kernel(a,D,d=Infinity){
   let l=0,u=0,v=0,total=0,n=a.length;
   if(n<=1)return 0;
   let y=new Array(n),s1=[0],s2=[0],s3=[0];
   for(let j=0;j<n;j++){let x=2*(a[j]-a[0]);y[j]=x;s1.push(s1[j]+x);s2.push(s2[j]+x*x);s3.push(s3[j]+x*x*x);}
   function moment(j,lo,hi){let x=y[j],N=hi-lo,A=s1[hi]-s1[lo],B=s2[hi]-s2[lo],C=s3[hi]-s3[lo];return [N,N*x-A,N*x*x-2*x*A+B,N*x*x*x-3*x*x*A+3*x*B-C];}
   for(let j=0;j<n;j++){
    while(l<j&&y[j]-y[l]>d)l++;
    u=Math.max(u,l);while(u<j&&y[j]-y[u]>=2*D)u++;
    v=Math.max(v,u);while(v<j&&y[j]-y[v]>D)v++;
    total+=(u-l)*4*D**3;
    let [N,A,B,C]=moment(j,u,v);total+=-4*D**3*N+12*D*D*A-6*D*B+C;
    [N,A,B,C]=moment(j,v,j);total+=6*D*B-3*C;
   }
   ck(Number.isSafeInteger(total)&&total>=0,"integer hat numerator");
   return total;
  }
  let kernelTests=0;
  for(let a of [[0,1,2,3,12],[1,4,8,9,11,29],[],[2]])for(let D of [1,3,8,31])for(let d of [0,2,6,15,Infinity]){
   let v=0;for(let i=0;i<a.length;i++)for(let j=i+1;j<a.length;j++)if(2*(a[j]-a[i])<=d)v+=scalar(2*(a[j]-a[i]),D);
   ck(kernel(a,D,d)===v,"kernel brute");kernelTests++;
  }

  const Ds=[...new Set([Math.max(1,Math.floor(T0/4)),Math.max(1,Math.floor(T0/2)),T0])],runs=[];
  for(let D of Ds){
   let ds=[...new Set([2,Math.max(2,Math.floor(D/Math.log(B))),Math.max(2,Math.floor(D**(2/3))),D])].sort((a,b)=>a-b),unit=4*D**3;
   let s={D,terminal:0,physGain:0,virtGain:0,physProxy:0,virtProxy:0,projClockVariance:0,internalClockVariance:0,terminalClockVariance:0,near:ds.map(d=>({d,phys:0,virt:0,unweighted:0,bound:0})),pruned:[]};
   function F(a){return a.length?kernel(a,D)/(unit*a.length):0}
   for(let [map,label] of [[phys,"phys"],[virt,"virt"]])for(let [key,v] of map){
    let m=v.ids.length,g=F(v.ids),raw=kernel(v.ids,D);
    for(let a of v.in.values()){g-=F(a);raw-=kernel(a,D)}
    ck(g>=-1e-8&&g<=raw/(unit*m)+1e-8);
    s[label+"Gain"]+=g;s[label+"Proxy"]+=raw/(unit*m);
    if(label==="virt")s.terminal+=F(v.ids);
    for(let w of s.near){let z=kernel(v.ids,D,w.d),u=kernel(v.ids,1,w.d);for(let a of v.in.values()){z-=kernel(a,D,w.d);u-=kernel(a,1,w.d)}ck(z>=0&&u>=0);w[label]+=z/(unit*m);w.unweighted+=u/(4*m);}
   }
   for(let [key,v] of proj){let g=F(v.ids.sort((a,b)=>a-b));for(let a of v.in.values())g-=F(a.sort((a,b)=>a-b));ck(g>=-1e-8);s.projClockVariance+=g;if(stops.has(key))s.terminalClockVariance+=g;else s.internalClockVariance+=g;}
   ck(Math.abs(s.physGain+s.virtGain-s.terminal)<1e-6*Math.max(1,S)&&Math.abs(s.terminalClockVariance-s.virtGain)<1e-6*Math.max(1,S)&&s.virtGain<=minority+1e-6);
   for(let w of s.near){let H=0;for(let j=1;j<=w.d;j++)H+=1/j;w.bound=S/2*H;ck(w.unweighted<=w.bound+1e-6&&w.phys+w.virt<=1.5*(w.d/D)**2*w.unweighted+1e-6);}
   // Removing arbitrary original sources costs at most one unit of terminal variance each.
   for(let A of [B,Math.ceil(X/Math.log(B)**2)]){
    let del=new Set();for(let [i,hs] of hist)if(hs.some(e=>e.h>=A))del.add(i);
    let terminal=0;for(let v of virt.values())terminal+=F(v.ids.filter(i=>!del.has(i)));
    ck(s.terminal-terminal>=-1e-7&&s.terminal-terminal<=del.size+1e-7);
    s.pruned.push({A,deleted:del.size,terminal,loss:s.terminal-terminal});
   }
   runs.push(s)
  }
  out.push({mode,T0,S,R,twin,bad,stopKeys:stops.size,physicalNodes:phys.size,virtualClasses,minority,maxClocks,oneClockStops,largestPhysical,branch,kernelTests,runs});
 }
 return {X,B,N,runs:out}
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
