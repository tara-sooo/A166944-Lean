// Hybrid modular barriers and cut-adjusted deficit recovery.
function audit(N=50000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 const primes=R=>{let a=[];for(let p=3;p<=R;p+=2)if(spf[p]===p)a.push(p);return a};
 const cuts=[5,7,11,13,47].map(S=>({S,K:2n*primes(S).reduce((a,p)=>a*BigInt(p),1n)}));
 const hybrid=[];for(let [S,R] of [[3,5],[5,7],[5,11],[7,13],[11,17]]){let ps=primes(R),P=ps.reduce((a,p)=>a*p,1),K=2*primes(S).reduce((a,p)=>a*p,1),A=ps.filter(p=>p>S).reduce((a,p)=>a*(p-1)/2,1),pre=new Uint32Array(P+1);for(let j=0;j<P;j++)pre[j+1]=pre[j]+(ps.every(p=>p<=S?2*j%p===0:2*j%p%2===0&&2*j%p<=p-3)?1:0);if(pre[P]!==A)throw Error("period");let C=j=>Math.floor(j/P)*A+pre[j%P];hybrid.push({S,R,P,K,A,count:(h,z)=>C(z/2)-C(h/2)})}
 const s={roots:0,events:0,terminal:0,capped:0,a1:0,blocks:0,markedBlocks:0,segments:0,localChecks:0,noncrossingChecks:0,separatorChecks:0,logChecks:0,weightedChecks:0,hybridChecks:0,hybridEventChecks:0,crossingRecovery:0,marks:0,hybridPeriods:hybrid.map(({S,R,P,A})=>({S,R,P,A})),witness:null};
 const tol=1e-8;
 function budget(ev,lo,hi,K,R,S,big=false){
  if(lo>=hi)return;
  const T=R/5+Number(K),ell=Math.log(2/(.2+Number(K)/R)),L=Math.log(1.5+Number(K)/T);
  function u(d,H){let a=BigInt(H),r=(a-1n)%K+1n;return Number(BigInt(d+3)+r)}
  let delta=0,marked=0,J=0,z=0,loss=0,weighted=0,segments=0,marks=0,otherGain=0,ordinaryDown=0;
  function segment(a,b){if(a>=b)return;let last=-1;for(let j=a;j<b;j++)if(ev[j].a1&&ev[j].p>R)last=j;
   if(last<0)return;segments++;let trim=b===hi?last+1:b;
   let start=Math.log(Math.max(T,u(ev[a].d,ev[a].H))),end=Math.log(Math.max(T,u(ev[trim-1].dp,ev[trim-1].Z)));delta+=end-start;
   for(let j=a;j<trim;j++){let v=ev[j],c=(BigInt(v.Z)-1n)/K-(BigInt(v.H)-1n)/K,g=v.p-1;
    const x=BigInt(v.d+3)+(BigInt(v.H)-1n)%K+1n,y=BigInt(v.dp+3)+(BigInt(v.Z)-1n)%K+1n;
    if(y-x!==2n*BigInt(v.w)-K*c||K*c>BigInt(g)+K||v.p<=S&&c!==0n)throw Error("local");
    s.localChecks++;if(c===0n){if(y<x)throw Error("noncrossing");s.noncrossingChecks++}
    let a=Math.max(T,Number(x)),b=Math.max(T,Number(y)),drop=Math.log(a)-Math.log(b);
    if(v.a1){if(v.p<=R||-drop+tol<ell)throw Error("mark");marked++;marks+=g;continue}
    if(drop>tol){if(c===0n||v.p<=S)throw Error("loss without crossing");
     if(v.D===0){z++;let max=Math.max(0,Math.log((v.p+6+Number(K))/T));if(drop>max+tol)throw Error("reset");loss+=max}
     else{if(v.p>=47&&v.p>=5*v.d+15)throw Error("B");if(drop>L+tol||drop>Number(K*c)/T+tol)throw Error("loss");J++;weighted+=Number(K*c);otherGain+=g;if(v.dp<v.d)ordinaryDown++}
    }
   }
  }
  let left=lo;for(let j=lo;j<hi;j++)if(ev[j].a1&&ev[j].p<=R){if(u(ev[j].d,ev[j].H)>T+tol)throw Error("separator");segment(left,j);left=j+1;s.separatorChecks++}segment(left,hi);
  if(marked!==ev.slice(lo,hi).filter(v=>v.a1&&v.p>R).length)throw Error("marked count");
  if(marked*ell>delta+J*L+loss+tol||marked*ell>delta+weighted/T+loss+tol)throw Error("budget");
  if(weighted>otherGain+Number(K)*J+tol)throw Error("weighted");
  s.blocks++;s.logChecks++;s.weightedChecks++;s.segments+=segments;s.marks+=marked;s.crossingRecovery+=J;if(marked)s.markedBlocks++;
  if(big&&R===1009&&S===5)s.witness={R,S,marked,J,z,weighted,otherGain,ordinaryDown,marks,delta,ell,L};
 }
 for(let M=5;M<=N;M+=2){s.roots++;let H=2*M-2,t=M+2,ev=[];
  for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");let a=next(t,H);if(!a){s.terminal++;break}let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,D=dp-3*(1-a.e),a1=a.p>=47&&a.p>=5*d+15&&D===2*a.p;if(a1)s.a1++;ev.push({...a,H,Z,d,dp,D,a1});H=Z;t=n;s.events++;if(i===steps-1)s.capped++}
  if(!ev.length)continue;
  for(let R of [47,101,1009])for(let {S,K} of cuts)if(S<R){budget(ev,0,ev.length,K,R,S);if(ev.length>=4)budget(ev,Math.floor(ev.length/2),ev.length,K,R,S)}
  for(let {S,R,P,K,A,count} of hybrid){let total=count(ev[0].H,H),sum=0;
   for(let v of ev){let b=count(v.H,v.Z),c=Math.floor((v.Z-1)/K)-Math.floor((v.H-1)/K);if(b>c||v.p<=R&&b||2*P*b>A*(v.p-1+2*P))throw Error("hybrid");sum+=b;s.hybridEventChecks++}if(sum!==total)throw Error("partition");s.hybridChecks++}
 }
 // Reconstruct previous exact canonical witness.
 const word=[7687,5233,3541,2389,1621,1093,733,7369],sh=[0];for(let p of word)sh.push(sh.at(-1)+p-1);
 let H=0n,P=4n,ticks=0,checks=0;
 for(let l of primes(3*Math.max(...word)+6)){let j=word.indexOf(l),a=j>=0?mod(1-sh[j],l):0;
  const valid=x=>sh.slice(0,-1).every((h,i)=>{let v=mod(x+h,l);return word[i]===l?v===1:v!==1&&v!==l-1});
  if(j>=0){if(!valid(a))throw Error("selected CRT")}else{while(a<l&&!valid(a))a++;if(a===l)throw Error("empty CRT")}
  let L=BigInt(l),x=Number(P%L),y=mod(a-Number(H%L),l),u=1,v=0,b=l;while(b){let q=Math.floor(x/b);[x,b]=[b,x-q*b];[u,v]=[v,u-q*v]}if(x!==1)throw Error("inverse");H+=P*BigInt(mod(u*y,l));P*=L;checks+=word.length}
 if(H<100000000n)H+=P;let H0=H,t=H/2n+3n,ev=[];
 for(let p of word){let d=Number(2n*t-H),w=(3*p-d-1)/2;for(let j=1;j<=w;j++){let n=t+BigInt(j),e=n%2n?-1:1,x=e===1?n:n-2n,y=H-BigInt(e);while(y)[x,y]=[y,x%y];if(j<w?x!==1n:x!==BigInt(p)||e!==1)throw Error("literal");ticks++}
 let Z=H+BigInt(p-1),dp=Number(2n*(t+BigInt(w))-Z);if(dp!==2*p||BigInt(p*p)>H+1n)throw Error("post");ev.push({p,H,Z,d,dp,D:dp,w,a1:p>=47&&p>=5*d+15});H=Z;t+=BigInt(w)}
 for(let {S,K} of cuts)budget(ev,0,ev.length,K,1009,S,true);
 s.witness={...s.witness,rootDigits:(H0/2n+1n).toString().length,ticks,checks};
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||50000),Number(process.argv[3]||180)),null,2));
