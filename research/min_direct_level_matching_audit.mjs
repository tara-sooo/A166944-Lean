// Exact geometric-level matching of A1 marks to smaller ordinary-decrease events.
function audit(N=100000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 let s={roots:0,events:0,a1:0,terminal:0,capped:0,blocks:0,nonempty:0,marks:0,slots:0,sixMarks:0,matched:0,resetSlots:0,endSlots:0,completeMarks:0,dropChecks:0,levelChecks:0,scaleChecks:0,cumulativeChecks:0,rootBounds:0,witness:[]};
 function check(ev,roots,lo,hi,R,phaseA,phaseB,witness=false){
  let marks=[];for(let i=lo;i<hi;i++)if(ev[i].a1&&ev[i].p>R)marks.push(i);
  s.blocks++;if(!marks.length)return;s.nonempty++;
  let C=Math.max(...marks.map(i=>ev[i].p)),levels=[];
  let a=BigInt(R*phaseA),b=BigInt(5*phaseB);
  while(a<=BigInt(2*C)*b){levels.push({a,b,pending:null});a*=3n;b*=2n}
  let slotMap=new Map(),used=new Set(),assigned=[],lostReset=0,lostEnd=0,six=0;
  for(let i=lo;i<hi;i++){
   let v=ev[i],x=BigInt(v.d+3),y=BigInt(v.dp+3),sel=v.a1&&v.p>R;
   if(sel){
    let slots=levels.filter(l=>5n*l.a>BigInt(v.p)*l.b&&l.a<=2n*BigInt(v.p)*l.b);
    if(slots.length<5||slots.length>6)throw Error("slots");
    if(slots.length===6)six++;
    let ar=slots.map((l,j)=>({mark:i,rank:j+1,level:l,match:null,reason:null}));
    slotMap.set(i,ar);
    for(let o of ar){
     let l=o.level;
     if(l.pending||x*l.b>=l.a||y*l.b<l.a||10n*2n**BigInt(o.rank)*l.a>2n*3n**BigInt(o.rank)*BigInt(v.p)*l.b)throw Error("up");
     l.pending=o;s.levelChecks++;
    }
   }
   if(y>=x)continue;
   let crossed=levels.filter(l=>y*l.b<l.a&&l.a<=x*l.b);
   let reset=v.D===0;
   if(!reset){if(v.p<5||3n*y<=2n*x||crossed.length>1)throw Error("nonreset ratio");s.dropChecks++}
   else if(v.p<7)throw Error("reset label");
   for(let l of crossed){
    let o=l.pending;if(!o)continue;
    l.pending=null;
    if(reset){lostReset++;o.reason="reset";continue}
    if(used.has(i)||i<=o.mark)throw Error("matching");
    let p=BigInt(ev[o.mark].p),k=BigInt(o.rank),q=BigInt(v.p);
    if(10n*2n**k*q>=3n**k*p||2n*x>=3n*y||y*l.b>=l.a||3n*y*l.b<=2n*l.a||v.dp<2*v.p)throw Error("scale");
    if(10n*3n*BigInt(v.dp+3)<=2n*BigInt(ev[o.mark].p))throw Error("lower deficit");
    // hq = (d' - 6I)/2, and hq > y_level/3 - 9/2.
    let hq=BigInt(v.D)/2n;
    if(6n*hq*l.b<=2n*l.a-27n*l.b)throw Error("h scale");
    o.match=i;assigned.push({mark:o.mark,rank:o.rank,index:i,q:v.p,post:v.dp});used.add(i);s.scaleChecks++;
   }
  }
  for(let l of levels)if(l.pending){l.pending.reason="end";lostEnd++}
  let total=0,complete=0;
  for(let [i,ar] of slotMap){total+=ar.length;if(ar.every(o=>o.match!==null))complete++}
  let Nroot=roots.filter(t=>t>ev[lo].t&&t<=ev[hi-1].n).length;
  let resets=ev.slice(lo,hi).filter(v=>v.dp<v.d&&v.D===0).length;
  if(resets>Nroot+1||lostReset>resets*levels.length||lostEnd>levels.length||assigned.length+lostReset+lostEnd!==total||complete<marks.length-lostReset-lostEnd)throw Error("account");
  s.rootBounds++;
  for(let U of [R+10,Math.ceil((R+C)/2),C])for(let k=1;k<=5;k++){
   let count=marks.filter(i=>ev[i].p<=U).length;
   let bnd=assigned.filter(o=>ev[o.mark].p<=U&&o.rank<=k).length;
   let down=ev.slice(lo,hi).filter(v=>v.D!==0&&v.dp<v.d&&10n*2n**BigInt(k)*BigInt(v.p)<3n**BigInt(k)*BigInt(U)).length;
   if(bnd<k*count-lostReset-lostEnd||down<bnd)throw Error("cumulative");
   s.cumulativeChecks++;
  }
  s.marks+=marks.length;s.slots+=total;s.sixMarks+=six;s.matched+=assigned.length;s.resetSlots+=lostReset;s.endSlots+=lostEnd;s.completeMarks+=complete;
  if(witness)s.witness.push({R,phase:`${phaseA}/${phaseB}`,marks:marks.map(i=>ev[i].p),slots:total,assigned:assigned.map(o=>({rank:o.rank,q:o.q,post:o.post})).sort((a,b)=>a.rank-b.rank),lostReset,lostEnd});
 }
 for(let M=5;M<=N;M+=2){s.roots++;let H=2*M-2,t=M+2,ev=[],roots=[];
  for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");let a=next(t,H);if(!a){s.terminal++;break}
   let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,I=(1-a.e)/2,D=dp-6*I,a1=a.p>=47&&a.p>=5*d+15&&D===2*a.p;
   if(a1)s.a1++;let rt=H/2+3;if(H%4===0&&rt>t&&rt<n)roots.push(rt);if(Z%4===0&&dp===6)roots.push(n);
   ev.push({...a,H,Z,t,n,d,dp,I,D,a1});H=Z;t=n;s.events++;if(i===steps-1)s.capped++;
  }
  if(ev.length)for(let R of [47,71,101,151])for(let [a,b] of [[1,1],[5,4],[7,5]]){check(ev,roots,0,ev.length,R,a,b);if(ev.length>=4)check(ev,roots,Math.floor(ev.length/2),ev.length,R,a,b)}
 }
 // Reconstruct the previous exact eight-event canonical witness.
 const word=[7687,5233,3541,2389,1621,1093,733,7369],sh=[0];for(let p of word)sh.push(sh.at(-1)+p-1);
 let H=0n,P=4n,ticks=0,checks=0;
 for(let l=3;l<=3*Math.max(...word)+6;l+=2){if(spf[l]!==l)continue;let j=word.indexOf(l),a=j>=0?mod(1-sh[j],l):0;
  const valid=x=>sh.slice(0,-1).every((h,i)=>{let v=mod(x+h,l);return word[i]===l?v===1:v!==1&&v!==l-1});
  if(j>=0){if(!valid(a))throw Error("selected CRT")}else{while(a<l&&!valid(a))a++;if(a===l)throw Error("empty CRT")}
  let L=BigInt(l),x=Number(P%L),y=mod(a-Number(H%L),l),u=1,v=0,b=l;while(b){let q=Math.floor(x/b);[x,b]=[b,x-q*b];[u,v]=[v,u-q*v]}if(x!==1)throw Error("inverse");H+=P*BigInt(mod(u*y,l));P*=L;checks+=word.length;
 }
 if(H<100000000n)H+=P;let H0=H,t=H/2n+3n,rel=0,ev=[];
 for(let p of word){let d=Number(2n*t-H),w=(3*p-d-1)/2;for(let j=1;j<=w;j++){let n=t+BigInt(j),e=n%2n?-1:1,x=e===1?n:n-2n,y=H-BigInt(e);while(y)[x,y]=[y,x%y];if(j<w?x!==1n:x!==BigInt(p)||e!==1)throw Error("literal");ticks++}
  let Z=H+BigInt(p-1),dp=Number(2n*(t+BigInt(w))-Z);if(dp!==2*p||BigInt(p*p)>H+1n)throw Error("post");ev.push({p,w,d,dp,D:dp,I:0,t:rel,n:rel+w,a1:p>=47&&p>=5*d+15});H=Z;t+=BigInt(w);rel+=w;
 }
 for(let [a,b] of [[1,1],[5,4],[7,5]])check(ev,[],0,ev.length,7500,a,b,true);
 s.witnessInfo={rootDigits:(H0/2n+1n).toString().length,ticks,checks};
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||100000),Number(process.argv[3]||180)),null,2));
