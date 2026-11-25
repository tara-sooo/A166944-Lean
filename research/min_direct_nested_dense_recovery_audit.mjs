// Nested dense modular cuts, exact scaled potential, and ordinary recovery budget.
function audit(N=50000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 const primes=R=>{let a=[];for(let p=3;p<=R;p+=2)if(spf[p]===p)a.push(p);return a};
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 const s={roots:0,events:0,a1:0,terminal:0,capped:0,periods:[],localChecks:0,nestedChecks:0,noncrossingChecks:0,blockChecks:0,markedBlocks:0,segments:0,separators:0,marked:0,charged:0,ordinaryDecrease:0,ordinaryBudgetChecks:0,weightedBudgetChecks:0,smallCapacityChecks:0,witness:[]};
 const tabs=new Map();
 for(let S of [3,5,7,11,13,17]){
  let ps=primes(S),P=ps.reduce((a,p)=>a*p,1),A=ps.reduce((a,p)=>a*(p-1)/2,1),pre=new Uint32Array(P+1),mn=0,mx=0;
  for(let j=0;j<P;j++){pre[j+1]=pre[j]+(ps.every(p=>mod(2*j,p)%2===0&&mod(2*j,p)<=p-3)?1:0);let v=2*A*(j+1)-2*P*pre[j+1];mn=Math.min(mn,v);mx=Math.max(mx,v)}
  if(pre[P]!==A||mx-mn>2*P*A)throw Error("period");
  const pB=BigInt(P),aB=BigInt(A),mB=BigInt(mn);
  function count(H){let j=BigInt(H)/2n;return j/pB*aB+BigInt(pre[Number(j%pB)])}
  function rho(H){let j=BigInt(H)/2n%pB;return 2n*aB*j-2n*pB*BigInt(pre[Number(j)])-mB}
  tabs.set(S,{S,P,A,K:2*P,alpha:A/P,count,rho});
  s.periods.push({S,P,A,oscillationNumerator:mx-mn,denominator:A});
 }
 const cuts=[[5,3],[7,3],[11,5],[13,5],[17,7]];
 const tol=1e-8;
 function budget(ev,lo,hi,R,S,Q,witness=false){
  let tab=tabs.get(S),sub=tabs.get(Q),{P,A,K,alpha}=tab,T=R/5+K,ell=Math.log(10/(1+5*K/R)),gamma=Math.log(1.5+K/T);
  const u=(d,H)=>Number(BigInt(A)*BigInt(d+3)+tab.rho(H))/A;
  let m=0,j=0,delta=0,resetLoss=0,lossSum=0,F=0,W=0,net=0,positive=0,z=0,segments=0,band=0;
  function seg(a,b){
   if(a>=b)return;let last=-1;for(let k=a;k<b;k++)if(ev[k].a1&&ev[k].p>R)last=k;
   if(last<0)return;
   segments++;let end=b===hi?last+1:b;
   delta+=Math.log(Math.max(T,u(ev[end-1].dp,ev[end-1].Z)))-Math.log(Math.max(T,u(ev[a].d,ev[a].H)));
   for(let k=a;k<end;k++){
    let v=ev[k],c=tab.count(v.Z)-tab.count(v.H),c0=sub.count(v.Z)-sub.count(v.H),g=v.p-1;
    let U=BigInt(A)*BigInt(v.d+3)+tab.rho(v.H),V=BigInt(A)*BigInt(v.dp+3)+tab.rho(v.Z);
    if(V-U!==2n*BigInt(A)*BigInt(v.w)-2n*BigInt(P)*c||2n*BigInt(P)*c>BigInt(A)*BigInt(g+K)||c>BigInt(g/2))throw Error("local");
    s.localChecks++;
    if(c>c0||2n*BigInt(sub.P)*c0>BigInt(sub.A)*BigInt(g+sub.K))throw Error("nested");s.nestedChecks++;
    if(v.p<=S&&c!==0n||c===0n&&V<=U)throw Error("noncross");if(c===0n)s.noncrossingChecks++;
    let drop=Math.log(Math.max(T,Number(U)/A))-Math.log(Math.max(T,Number(V)/A));
    if(v.a1){if(v.p<=R||-drop+tol<ell)throw Error("marked");m++;continue}
    if(drop>tol){
     if(c===0n||v.p<=S)throw Error("loss without cross");
     if(v.D===0){z++;let bound=Math.max(0,Math.log((v.p+6+K)/T));if(drop>bound+tol)throw Error("reset");resetLoss+=bound}
     else{
      if(v.p>=47&&v.p>=5*v.d+15)throw Error("classification");
      let w=2*P*Number(c)/A,loss=w-2*v.w,ord=v.d-v.dp;
      if(drop>gamma+tol||T*drop>loss+tol||loss>ord+K+tol||w>sub.alpha/alpha*(g+sub.K)+tol)throw Error("recovery");
      j++;W+=w;F+=g;lossSum+=loss;net+=ord;positive+=Math.max(0,ord);if(ord>0)s.ordinaryDecrease++;if(v.p<=R)band++;s.smallCapacityChecks++;
     }
    }
   }
  }
  let left=lo;for(let k=lo;k<hi;k++)if(ev[k].a1&&ev[k].p<=R){if(u(ev[k].d,ev[k].H)>T+tol)throw Error("separator");seg(left,k);left=k+1;s.separators++}
  seg(left,hi);
  let target=T*(ell*m-delta-resetLoss);
  if(m!==ev.slice(lo,hi).filter(v=>v.a1&&v.p>R).length||ell*m>delta+gamma*j+resetLoss+tol)throw Error("count budget");
  if(lossSum+tol<target||W+tol<lossSum||W>F/alpha+tol||W>sub.alpha/alpha*(F+sub.K*j)+tol)throw Error("weighted budget");
  if(net+K*j+tol<target||positive+K*j+tol<target)throw Error("ordinary budget");
  s.blockChecks++;s.weightedBudgetChecks++;s.ordinaryBudgetChecks++;s.segments+=segments;s.marked+=m;s.charged+=j;if(m)s.markedBlocks++;
  if(witness)s.witness.push({R,S,Q,m,j,z,band,F,W,lossSum,net,positive,delta,ell,target});
 }
 for(let M=5;M<=N;M+=2){
  s.roots++;let H=2*M-2,t=M+2,ev=[];
  for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");let a=next(t,H);if(!a){s.terminal++;break}
   let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,D=dp-3*(1-a.e),a1=a.p>=47&&a.p>=5*d+15&&D===2*a.p;
   if(a1)s.a1++;ev.push({...a,H,Z,d,dp,D,a1});H=Z;t=n;s.events++;if(i===steps-1)s.capped++;
  }
  if(!ev.length)continue;
  for(let R of [47,101,1009])for(let [S,Q] of cuts){budget(ev,0,ev.length,R,S,Q);if(ev.length>=4)budget(ev,Math.floor(ev.length/2),ev.length,R,S,Q)}
 }
 // Literal CRT control: earlier sharp eight-event word.
 const word=[7687,5233,3541,2389,1621,1093,733,7369],sh=[0];for(let p of word)sh.push(sh.at(-1)+p-1);
 let H=0n,P=4n,ticks=0,checks=0;
 for(let l of primes(3*Math.max(...word)+6)){let j=word.indexOf(l),a=j>=0?mod(1-sh[j],l):0;
  const valid=x=>sh.slice(0,-1).every((h,i)=>{let v=mod(x+h,l);return word[i]===l?v===1:v!==1&&v!==l-1});
  if(j>=0){if(!valid(a))throw Error("selected CRT")}else{while(a<l&&!valid(a))a++;if(a===l)throw Error("empty CRT")}
  let L=BigInt(l),x=Number(P%L),y=mod(a-Number(H%L),l),u=1,v=0,b=l;while(b){let q=Math.floor(x/b);[x,b]=[b,x-q*b];[u,v]=[v,u-q*v]}if(x!==1)throw Error("inverse");H+=P*BigInt(mod(u*y,l));P*=L;checks+=word.length
 }
 if(H<100000000n)H+=P;let H0=H,t=H/2n+3n,ev=[];
 for(let p of word){let d=Number(2n*t-H),w=(3*p-d-1)/2;for(let j=1;j<=w;j++){let n=t+BigInt(j),e=n%2n?-1n:1n,x=e===1n?n:n-2n,y=H-e;while(y)[x,y]=[y,x%y];if(j<w?x!==1n:x!==BigInt(p)||e!==1n)throw Error("literal");ticks++}
 let Z=H+BigInt(p-1),dp=Number(2n*(t+BigInt(w))-Z);if(dp!==2*p||BigInt(p*p)>H+1n)throw Error("post");ev.push({p,H,Z,d,dp,D:dp,w,a1:p>=47&&p>=5*d+15});H=Z;t+=BigInt(w)}
 for(let [S,Q] of cuts)budget(ev,0,ev.length,1009,S,Q,true);
 s.witnessInfo={rootDigits:(H0/2n+1n).toString().length,ticks,checks};
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||50000),Number(process.argv[3]||180)),null,2));
