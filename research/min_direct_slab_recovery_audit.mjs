// Exact rational geometric slabs for label-weighted ordinary recovery.
function audit(N=50000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 let s={roots:0,events:0,a1:0,terminal:0,capped:0,blocks:0,nonempty:0,marks:0,goodMarks:0,badMarks:0,slabs:0,completeSlabs:0,unfinishedSlabs:0,resetHits:0,highHits:0,intersectionChecks:0,allocationChecks:0,weightedChecks:0,tailChecks:0,rootChecks:0,witness:[]};
 function inspect(ev,roots,lo,hi,R,A,B,witness=false){
  let marks=[];for(let i=lo;i<hi;i++)if(ev[i].a1&&ev[i].p>R)marks.push(i);
  s.blocks++;if(!marks.length)return;s.nonempty++;
  let C=Math.max(...marks.map(i=>ev[i].p)),a=BigInt(R),b=5n,L=0;
  while(a<=2n*BigInt(C)*b){L++;a*=BigInt(A);b*=BigInt(B)}
  const den=5n*BigInt(B)**BigInt(L-1),ys=[];
  for(let j=0;j<L;j++)ys.push(BigInt(R)*BigInt(A)**BigInt(j)*BigInt(B)**BigInt(L-1-j));
  let active=Array(L-1).fill(null),rec=new Map(),alloc=[],resetHits=0,highHits=0,unfinished=0,Hcount=0,Zcount=0;
  // Safe ceiling of log_b(1.5) plus 2, computed by integer arithmetic.
  let m=0,aa=1n,bb=1n;while(2n*aa<3n*bb){m++;aa*=BigInt(A);bb*=BigInt(B)}const kappa=m+2;
  let min=(x,y)=>x<y?x:y,max=(x,y)=>x>y?x:y;
  for(let i=lo;i<hi;i++){
   let v=ev[i],x=BigInt(v.d+3)*den,y=BigInt(v.dp+3)*den;
   if(v.a1&&v.p>R){
    let p=BigInt(v.p),r={i,p,bad:false,slabs:[],allocation:0n};rec.set(i,r);
    for(let k=0;k<L-1;k++)if(5n*ys[k]>p*den&&ys[k+1]<=2n*p*den){
     if(active[k]||x>=ys[k]||y<ys[k+1])throw Error("slab start");
     let o={r,k,total:0n,low:0n,done:false};r.slabs.push(o);active[k]=o;s.slabs++;
    }
    if(!r.slabs.length)throw Error("no slabs");
    let width=ys[r.slabs.at(-1).k+1]-ys[r.slabs[0].k];
    if(5n*BigInt(A*B)*width < (10n*BigInt(B*B)-BigInt(A*A))*p*den)throw Error("minimum width");
    r.width=width;
   }
   if(y>=x)continue;
   let isReset=v.D===0,high=v.p>R;
   if(isReset){if(v.p<7)throw Error("reset");Zcount++}
   else{if(v.p<5||2n*x>=3n*y)throw Error("ratio");if(high)Hcount++}
   let intersections=0,allocated=0n;
   for(let k=0;k<L-1;k++){
    let len=max(0n,min(x,ys[k+1])-max(y,ys[k]));
    if(len>0n)intersections++;
    let o=active[k];if(!o)continue;
    if(len>0n){
     o.total+=len;s.intersectionChecks++;
     if(isReset||high){o.r.bad=true;if(isReset)resetHits++;else highHits++}
     else{
      o.low+=len;allocated+=len;alloc.push({o,v,len});
      if(15n*BigInt(v.D)+135n<=2n*o.r.p)throw Error("high h");
      if(BigInt(v.p)>BigInt(R)||v.dp>=v.d||y>=ys[k+1])throw Error("low charge");
     }
    }
    if(y<=ys[k]){if(o.total<ys[k+1]-ys[k])throw Error("full slab");o.done=true;active[k]=null;s.completeSlabs++}
   }
   if(!isReset&&intersections>kappa||allocated>x-y)throw Error("disjoint allocation");
   s.allocationChecks++;
  }
  for(let o of active)if(o){o.r.bad=true;unfinished++}
  let Nroot=roots.filter(t=>t>ev[lo].t&&t<=ev[hi-1].n).length;
  if(Zcount>Nroot+1||resetHits>Zcount*(L-1)||highHits>kappa*Hcount||unfinished>L-1)throw Error("exception bound");
  let good=[...rec.values()].filter(r=>!r.bad),bad=marks.length-good.length,weight=0n,need=0n,have=0n;
  if(bad>resetHits+highHits+unfinished)throw Error("bad marks");
  for(let r of good){weight+=r.p;need+=r.width;for(let o of r.slabs){if(!o.done||o.low<ys[o.k+1]-ys[o.k])throw Error("good complete");have+=o.low}}
  let total=ev.slice(lo,hi).filter(v=>v.D!==0&&v.p<=R&&v.dp<v.d).reduce((t,v)=>t+BigInt(v.d-v.dp)*den,0n);
  if(need>have||have>total||5n*BigInt(A*B)*need < (10n*BigInt(B*B)-BigInt(A*A))*weight*den)throw Error("weighted");
  for(let U of [R+1,Math.ceil((R+C)/2),C]){
   let sel=good.filter(r=>r.p>=BigInt(U)),w=sel.reduce((a,r)=>a+r.p,0n),req=sel.reduce((a,r)=>a+r.width,0n);
   let got=alloc.filter(o=>!o.o.r.bad&&o.o.r.p>=BigInt(U)).reduce((a,o)=>a+o.len,0n);
   let cap=ev.slice(lo,hi).filter(v=>v.D!==0&&v.p<=R&&v.dp<v.d&&15n*BigInt(v.D)+135n>2n*BigInt(U)).reduce((a,v)=>a+BigInt(v.d-v.dp)*den,0n);
   if(req>got||got>cap||5n*BigInt(A*B)*req<(10n*BigInt(B*B)-BigInt(A*A))*w*den)throw Error("tail");
   s.tailChecks++;
  }
  s.marks+=marks.length;s.goodMarks+=good.length;s.badMarks+=bad;s.unfinishedSlabs+=unfinished;s.resetHits+=resetHits;s.highHits+=highHits;s.weightedChecks++;s.rootChecks++;
  if(witness)s.witness.push({R,beta:`${A}/${B}`,marks:marks.map(i=>ev[i].p),good:good.map(r=>Number(r.p)),bad,slabs:[...rec.values()].map(r=>r.slabs.length),weightedRequired:Number(need*1000000n/den)/1e6,assignedActual:Number(have*1000000n/den)/1e6,availableLow:Number(total*1000000n/den)/1e6,resetHits,highHits,unfinished});
 }
 for(let M=5;M<=N;M+=2){s.roots++;let H=2*M-2,t=M+2,ev=[],roots=[];
  for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");let a=next(t,H);if(!a){s.terminal++;break}
   let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,I=(1-a.e)/2,D=dp-6*I,a1=a.p>=47&&a.p>=5*d+15&&D===2*a.p;
   if(a1)s.a1++;let rt=H/2+3;if(H%4===0&&rt>t&&rt<n)roots.push(rt);if(Z%4===0&&dp===6)roots.push(n);
   ev.push({...a,H,Z,t,n,d,dp,I,D,a1});H=Z;t=n;s.events++;if(i===steps-1)s.capped++;
  }
  if(ev.length)for(let R of [47,71,101])for(let [A,B] of [[3,2],[5,4],[11,10]]){inspect(ev,roots,0,ev.length,R,A,B);if(ev.length>=4)inspect(ev,roots,Math.floor(ev.length/2),ev.length,R,A,B)}
 }
 // Reconstruct earlier exact eight-event witness.
 const word=[7687,5233,3541,2389,1621,1093,733,7369],sh=[0];for(let p of word)sh.push(sh.at(-1)+p-1);
 let H=0n,P=4n,ticks=0,checks=0;
 for(let l=3;l<=3*Math.max(...word)+6;l+=2){if(spf[l]!==l)continue;let j=word.indexOf(l),a=j>=0?mod(1-sh[j],l):0;
  const valid=x=>sh.slice(0,-1).every((h,i)=>{let v=mod(x+h,l);return word[i]===l?v===1:v!==1&&v!==l-1});
  if(j>=0){if(!valid(a))throw Error("selected CRT")}else{while(a<l&&!valid(a))a++;if(a===l)throw Error("empty CRT")}
  let L=BigInt(l),x=Number(P%L),y=mod(a-Number(H%L),l),u=1,v=0,b=l;while(b){let q=Math.floor(x/b);[x,b]=[b,x-q*b];[u,v]=[v,u-q*v]}if(x!==1)throw Error("inverse");H+=P*BigInt(mod(u*y,l));P*=L;checks+=word.length
 }
 if(H<100000000n)H+=P;let H0=H,t=H/2n+3n,rel=0,ev=[];
 for(let p of word){let d=Number(2n*t-H),w=(3*p-d-1)/2;for(let j=1;j<=w;j++){let n=t+BigInt(j),e=n%2n?-1:1,x=e===1?n:n-2n,y=H-BigInt(e);while(y)[x,y]=[y,x%y];if(j<w?x!==1n:x!==BigInt(p)||e!==1)throw Error("literal");ticks++}
  let Z=H+BigInt(p-1),dp=Number(2n*(t+BigInt(w))-Z);if(dp!==2*p||BigInt(p*p)>H+1n)throw Error("post");ev.push({p,w,d,dp,D:dp,I:0,t:rel,n:rel+w,a1:p>=47&&p>=5*d+15});H=Z;t+=BigInt(w);rel+=w;
 }
 for(let [A,B] of [[3,2],[5,4],[11,10],[101,100]])inspect(ev,[],0,ev.length,7500,A,B,true);
 s.witnessInfo={rootDigits:(H0/2n+1n).toString().length,ticks,checks};
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||50000),Number(process.argv[3]||180)),null,2));
