// Terminal clock capped-mass moment; inverse-prime projected stop diagnostic.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,L=210,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=(x,m="assertion")=>{if(!x)throw Error(m)},mod=(x,m)=>(x%m+m)%m,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c}return a};
 function hit(t,C,K){let n=K+1,p=0;for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(q>B)break;let u=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(u<n||(u===n&&q<p)){n=u;p=q}while(v%q===0)v/=q}}return [n,p]}
 const out=[];
 for(let mode of ["uniform","inverse","inverseSmall"]){
  const T=Math.max(2,Math.floor(B/(mode==="inverseSmall"?32:4))),Y=Math.max(11,Math.ceil(Math.sqrt(B))),cap=p=>mode==="uniform"||p<Y?T:Math.ceil(T*B/p);
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
  const groups=new Map();
  for(let [i,hs] of hist){let e=hs.at(-1),key=e.key;if(!groups.has(key))groups.set(key,{p:e.p,C:e.C,classes:new Map(),h:0,cost:0,ids:[]});let v=groups.get(key);if(!v.classes.has(e.n))v.classes.set(e.n,[]);v.classes.get(e.n).push(i);v.h+=e.h;v.cost+=e.cost;v.ids.push(i);ck(e.h<=6+4*e.cost+4*e.r);}
  let H=0,Rstop=0,low=0,high=0,highKeys=0;
  for(let v of groups.values()){let m=v.ids.length;ck(m>=cap(v.p));H+=v.h;Rstop+=v.cost;if(v.p>=Y){high+=m;highKeys++;}else low+=m;}
  ck(H<=6*S+4*R+4*B*S&&Rstop<=R&&low+high===S);
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


  let runs=[];
  for(let D of [...new Set([1,2,4,8,Math.max(1,Math.floor(Math.log(B))),Math.max(1,Math.floor(T/4))])]){
   let unit=4*D**3,a=2*D,stat={D,a,all:0,phys:0,virt:0,high:0,highPhys:0,highVirt:0,highU:0,highH:0,highInv:0,highBound:0,highKeys:0,low:0,maxClock:0,checks:0,perThreshold:[]};
   let byP=[];
   for(let v of groups.values()){
    v.ids.sort((a,b)=>a-b);let m=v.ids.length,F=kernel(v.ids,D)/(unit*m),phys=0,U=0,sumIndex=0,classes=[...v.classes.entries()].sort((a,b)=>a[0]-b[0]);
    let n0=classes[0][0],last=-1;
    for(let [n,ids] of classes){ids.sort((a,b)=>a-b);let j=(n-n0)/(2*v.p),c=Math.min(a,ids.length);ck(j>last&&Number.isInteger(j));last=j;sumIndex+=j*c;U+=c;let f0=kernel(ids,D)/(unit*ids.length);phys+=f0;ck(ids.length/2-f0<=c/2+1e-8);}
    let gv=F-phys;
    ck(gv>=-1e-8&&gv<=U/2+1e-8&&v.h>=4*v.p*sumIndex&&2*a*sumIndex>=U*U-a*U,"clock moment");
    ck(U<=a+Math.sqrt(a*v.h/(2*v.p))+1e-8);
    ck(F>=m/2-D-1e-8);
    stat.checks++;stat.all+=F;stat.phys+=phys;stat.virt+=gv;stat.maxClock=Math.max(stat.maxClock,classes.length);
    if(v.p>=Y){stat.high+=F;stat.highPhys+=phys;stat.highVirt+=gv;stat.highU+=U;stat.highH+=v.h;stat.highInv+=1/v.p;stat.highKeys++;}
    else stat.low+=F;
    byP.push({p:v.p,m,F,phys,gv,U,h:v.h});
   }
   for(let P of [...new Set([11,17,31,Y,Math.ceil(B/2)])].sort((a,b)=>a-b)){
    let b=byP.filter(v=>v.p>=P),s={P,m:0,keys:b.length,phys:0,virt:0,U:0,H:0,inv:0,bound:0};
    for(let v of b){s.m+=v.m;s.phys+=v.phys;s.virt+=v.gv;s.U+=v.U;s.H+=v.h;s.inv+=1/v.p;}
    s.bound=(a*s.keys+Math.sqrt(a*s.H*s.inv/2))/2;ck(s.virt<=s.U/2+1e-6&&s.U/2<=s.bound+1e-6);
    ck(s.phys>=s.m/2-D*s.keys-s.bound-1e-6);
    if(mode!=="uniform"&&P>=Y)ck(s.inv<=s.m/(T*B)+1e-10);
    stat.perThreshold.push(s);
   }
   stat.highBound=(a*stat.highKeys+Math.sqrt(a*stat.highH*stat.highInv/2))/2;
   ck(stat.highVirt<=stat.highU/2+1e-6&&stat.highU/2<=stat.highBound+1e-6&&Math.abs(stat.all-stat.phys-stat.virt)<1e-6);
   runs.push(stat);
  }
  out.push({mode,T,Y,S,R,Rstop,H,high,highKeys,low,stopKeys:stops.size,twin,bad,kernelTests,runs});
 }
 return {X,B,N,runs:out}
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
