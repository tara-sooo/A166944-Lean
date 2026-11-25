// Deficit-side modular barriers, fixed-level multiplicity and rounded level matching.
function audit(N=60000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 const primes=S=>{let a=[];for(let p=3;p<=S;p+=2)if(spf[p]===p)a.push(p);return a};
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 function allowed(y,p){if(p===3)return true;return [0,1].every(I=>{let r=mod(y-6*I,2*p);return !(r>=2&&r<=p-3)})}
 const tabs=[];for(let S of [5,7,11,13]){
  let ps=primes(S),P=ps.reduce((a,p)=>a*p,1),A=ps.reduce((a,p)=>a*Array.from({length:p},(_,j)=>2*j).filter(y=>allowed(y,p)).length,1),pre=new Uint32Array(P+1);
  for(let j=0;j<P;j++)pre[j+1]=pre[j]+(ps.every(p=>allowed(2*j,p))?1:0);
  if(pre[P]!==A)throw Error("CRT count");
  const count=d=>{let n=Math.floor(d/2)+1;return Math.floor(n/P)*A+pre[n%P]-1};
  tabs.push({S,P,K:2*P,A,count});
 }
 let s={roots:0,events:0,a1:0,terminal:0,capped:0,decreases:0,nonresets:0,resets:0,localChecks:0,barrierChecks:0,levelChecks:0,crossingPairs:0,repeatChecks:0,capacityChecks:0,roundedBlocks:0,roundedSlots:0,roundedMatches:0,roundedHighMatches:0,roundedLoss:0,weightedBlocks:0,weightedMarks:0,weightedPaid:0,periods:tabs.map(({S,P,A})=>({S,P,A})),witness:[]};
 function inspect(ev,lo,hi,R,S,phaseA=1,phaseB=1){
  const {K,P,A,count}=tabs.find(t=>t.S===S);
  let marks=[];for(let i=lo;i<hi;i++)if(ev[i].a1&&ev[i].p>R)marks.push(i);
  if(!marks.length)return;
  let C=Math.max(...marks.map(i=>ev[i].p)),pending=new Map(),paid=0,slots=0,reset=0,high=0,low=0;
  let levels=[];for(let b=2;b<=2*C;b+=2)if(count(b)>count(b-2))levels.push(b);
  for(let i=lo;i<hi;i++){
   let v=ev[i];
   if(v.a1&&v.p>R){
    let r=levels.filter(b=>5*(b+3)>v.p&&b+3<=2*v.p);
    if(2*P*r.length+2*P*A< A*(1.8*v.p-4)-1e-7)throw Error("mark density");
    slots+=r.length;
    for(let b of r){if(pending.has(b)||!(v.d<b&&b<=v.dp))throw Error("up");pending.set(b,v.p)}
   }
   if(v.dp>=v.d)continue;
   let n=0;
   for(let [b,p] of pending)if(v.dp<b&&b<=v.d){pending.delete(b);n++;if(v.D===0)reset++;else{
    if(v.p<=S||v.p>=p)throw Error("assigned label");
    if(v.p>R)high++;else low++;
    paid++;s.crossingPairs++;
   }}
   if(n>count(v.d)-count(v.dp)||n>(v.d-v.dp)/2)throw Error("capacity");s.capacityChecks++;
  }
  if(slots!==paid+reset+pending.size||paid!==high+low)throw Error("account");
  let F=ev.slice(lo,hi).filter(v=>v.dp<v.d&&v.D!==0&&v.p>S&&v.p<=R).reduce((z,v)=>z+v.d-v.dp,0);
  if(2*low>F)throw Error("ordinary total");
  s.weightedBlocks++;s.weightedMarks+=marks.length;s.weightedPaid+=low;
  if(K*200>R)return;
  let a=BigInt(R*phaseA),b=BigInt(5*phaseB),num=3n*BigInt(R)+20n*BigInt(K),den=2n*BigInt(R),L=[];
  if(a*den>=BigInt(R)*b*5n*num/5n){/* phase checked by caller */}
  while(a<=BigInt(2*C)*b){
   let z=3n+BigInt(K)*((a-3n*b+BigInt(K)*b-1n)/(BigInt(K)*b));
   if(z*b<a||z*b>=a+BigInt(K)*b||z%BigInt(K)!==3n%BigInt(K))throw Error("round");
   if(L.length&&2n*z<3n*L.at(-1).z)throw Error("separation");
   L.push({a,b,z,pending:null});a*=num;b*=den;
  }
  let usedEvents=new Set(),nslot=0,nmatch=0,nloss=0,nhigh=0,labels=[];
  for(let i=lo;i<hi;i++){
   let v=ev[i],x=BigInt(v.d+3),y=BigInt(v.dp+3);
   if(v.a1&&v.p>R){
    let r=L.filter(l=>5n*l.a>BigInt(v.p)*l.b&&l.a<=BigInt(2*v.p-K)*l.b);
    if(r.length<5||r.length>6)throw Error("slot count");
    for(let l of r){if(l.pending!==null||x>=l.z||y<l.z)throw Error("rounded up");l.pending=v.p;nslot++}
   }
   if(y>=x)continue;
   for(let l of L)if(l.pending!==null&&y<l.z&&l.z<=x){
    if(v.D===0)nloss++;else{
     if(v.p<=S||v.p>=l.pending||usedEvents.has(i))throw Error("rounded match");
     usedEvents.add(i);nmatch++;labels.push(v.p);if(v.p>R)nhigh++;
    }l.pending=null;
   }
  }
  nloss+=L.filter(l=>l.pending!==null).length;if(nslot!==nmatch+nloss)throw Error("rounded count");
  s.roundedBlocks++;s.roundedSlots+=nslot;s.roundedMatches+=nmatch;s.roundedHighMatches+=nhigh;s.roundedLoss+=nloss;
  return {S,R,phase:[phaseA,phaseB],denseMatchedLow:low,roundedSlots:nslot,roundedMatches:nmatch,labels};
 }
 for(let M=5;M<=N;M+=2){
  s.roots++;let H=2*M-2,t=M+2,ev=[],last=new Map();
  for(let i=0;i<steps;i++){
   if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");let a=next(t,H);if(!a){s.terminal++;break}
   let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,I=(1-a.e)/2,D=dp-6*I,a1=a.p>=47&&a.p>=5*d+15&&D===2*a.p;
   if(a1)s.a1++;
   ev.push({...a,H,Z,t,n,d,dp,I,D,a1});s.events++;
   if(dp<d){s.decreases++;
    for(let {S,K,P,A,count} of tabs){let c=count(d)-count(dp);
     if(c<0||2*P*c>A*(d-dp+K)||2*c>d-dp)throw Error("cut bound");
     if(a.p<=S&&D!==0&&c)throw Error("barrier");
     if(a.p<=S&&D===0&&d>a.p+3)throw Error("reset pre");
     s.barrierChecks++;
    }
    if(D!==0){s.nonresets++;let h=D/(2*a.p);
     if(a.p<5||!Number.isInteger(h)||h<1||d-dp>a.p-3)throw Error("nonreset");
     let q=(H-a.e)/a.p;
     if(mod(H-(a.e+a.p*(2*I-2*h-1)),4*a.p)!==0||mod(h+(q+1)/2-I,2)!==0)throw Error("H class");
     for(let b=dp+2;b<=d;b+=2){
      if(allowed(b,a.p))throw Error("allowed down");
      let hh=Math.floor((b-6*I-1)/(2*a.p)),r=b-6*I-2*a.p*hh;
      if(hh!==h||r<2||r>a.p-3)throw Error("unique h");
      let key=`${b}/${a.p}/${I}`,old=last.get(key);
      if(old!==undefined&&(H-old<4*a.p||(H-old)%(4*a.p)))throw Error("spacing");
      if(old!==undefined)s.repeatChecks++;
      last.set(key,H);s.levelChecks++;
     }
     s.localChecks++;
    }else s.resets++;
   }
   H=Z;t=n;if(i===steps-1)s.capped++;
  }
  for(let R of [47,71,101])for(let S of [5,7,11]){inspect(ev,0,ev.length,R,S);if(ev.length>=4)inspect(ev,Math.floor(ev.length/2),ev.length,R,S)}
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

 for(let S of [5,7,11,13])for(let [a,b] of [[1,1],[5,4],[7,5]]){
  let v=inspect(ev,0,ev.length,7500,S,a,b);if(v)s.witness.push(v);
 }
 s.witnessInfo={rootDigits:(H0/2n+1n).toString().length,ticks,checks};

 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000),Number(process.argv[3]||180)),null,2));
