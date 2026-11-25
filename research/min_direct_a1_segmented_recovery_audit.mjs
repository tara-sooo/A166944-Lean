// Segmented logarithmic recovery budget with B-only high nonresets.
function audit(N=100000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 const cuts=[5,7,11,47,53].map(S=>{let K=2;for(let p=3;p<=S;p+=2)if(spf[p]===p)K*=p;return {S,K}});
 const s={roots:0,events:0,a1:0,terminal:0,capped:0,blocks:0,nonemptyMarked:0,segments:0,separatorChecks:0,lowRuns:0,highNonresetChecks:0,rootBoundChecks:0,budgetChecks:0,selectedMarks:0,selectedB:0,selectedJ:0,selectedResets:0,nearBChecks:0,smallThresholdExamples:[],witness:null};
 const tol=1e-8;
 function inspect(ev,roots,lo,hi,all=true){
  if(lo>=hi)return;
  let C=Math.floor(Math.sqrt(ev[hi-1].Z+1)),Nroot=roots.filter(x=>x>ev[lo].t&&x<=ev[hi-1].n).length;
  for(let R of [47,71,101,151,1009])for(let {S,K} of cuts){if(S>=R)continue;
   let T=R/5,phi=d=>Math.log(Math.max(T,d+3)),eps=Math.log1p(K/T),marked=0,n=0,J=0,z=0,loss=0,blocks=0,delta=0,lowRuns=0,nearB=0,farB=0,globalB=0,globalZ=0,globalNearB=0;
   let left=lo;
   function segment(a,b,separator){
    if(a>=b)return;
    let m=0;for(let k=a;k<b;k++)if(ev[k].a1&&ev[k].p>R)m++;
    if(!m)return;
    blocks++;marked+=m;delta+=phi(ev[b-1].dp)-phi(ev[a].d);
    if(separator&&Math.abs(phi(ev[b-1].dp)-Math.log(T))>tol)throw Error("end baseline");
    let gain=0,start=0,end=0;
    function close(){if(gain){if(gain>K+tol||phi(start)-phi(end)>eps+tol)throw Error("low run");lowRuns++;gain=0}}
    for(let k=a;k<b;k++){
     let v=ev[k];if(v.p<=S){if(!gain)start=v.d;gain+=v.p-1;end=v.dp;continue}
     close();
     if(v.a1){if(v.p<=R||phi(v.dp)-phi(v.d)<Math.log(10)-tol)throw Error("mark");}
     else if(v.D===0){z++;loss+=Math.max(0,Math.log((v.p+6)/T))}
     else{n++;if(v.dp<v.d)J++;if(v.p>=47&&v.p>=5*v.d+15)throw Error("B classification");if(v.near)nearB++;else farB++}
    }
    close();
   }
   for(let k=lo;k<hi;k++){
    let v=ev[k];
    if(v.p>S&&v.D===0)globalZ++;
    if(v.p>S&&v.D!==0&&!v.a1){globalB++;if(v.near)globalNearB++}
    if(v.a1&&v.p<=R){if(Math.abs(phi(v.d)-Math.log(T))>tol)throw Error("separator");segment(left,k,true);left=k+1;s.separatorChecks++}
   }
   segment(left,hi,false);
   if(marked!==ev.slice(lo,hi).filter(v=>v.a1&&v.p>R).length)throw Error("mark count");
   if(blocks>marked||lowRuns>marked+n+z+blocks||delta>phi(ev[hi-1].dp)-Math.log(T)+tol||n>globalB||z>globalZ||globalZ>Nroot+1)throw Error("bounds");
   if(marked*Math.log(10)>delta+J*Math.log(1.5)+loss+eps*lowRuns+tol)throw Error("exact budget");
   if((Math.log(10)-2*eps)*marked>(Math.log(1.5)+eps)*globalB+(Nroot+1)*(Math.max(0,Math.log((C+6)/T))+eps)+phi(ev[hi-1].dp)-Math.log(T)+tol)throw Error("global budget");
   if(nearB+farB!==n||nearB>globalNearB)throw Error("nearB");
   s.blocks++;s.budgetChecks+=2;s.rootBoundChecks++;s.segments+=blocks;s.lowRuns+=lowRuns;s.highNonresetChecks+=n;s.selectedMarks+=marked;s.selectedB+=n;s.selectedJ+=J;s.selectedResets+=z;s.nearBChecks++;
   if(marked)s.nonemptyMarked++;
   if(!all&&marked&&S===47&&R===1009)s.witness={R,S,marked,n,J,z,blocks,delta,eps,globalB,farB};
  }
 }
 for(let M=5;M<=N;M+=2){
  s.roots++;let H=2*M-2,t=M+2,ev=[],roots=[];
  for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");let a=next(t,H);if(!a){s.terminal++;break}
   let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,D=dp-3*(1-a.e),a1=a.p>=47&&a.p>=5*d+15&&D===2*a.p,q=(H-a.e)/a.p,x=(q+a.p)/2,k=(q-a.p)/2;
   if(a1)s.a1++;let rt=H/2+3;if(H%4===0&&rt>t&&rt<n)roots.push(rt);if(Z%4===0&&dp===6)roots.push(n);
   ev.push({...a,H,t,n,Z,d,dp,D,a1,near:x>=64&&2*k*k<=x});H=Z;t=n;s.events++;if(i===steps-1)s.capped++;
  }
  if(ev.length){inspect(ev,roots,0,ev.length);if(ev.length>=4)inspect(ev,roots,Math.floor(ev.length/2),ev.length)}
 }
 // Exact previous sharp word, expressed in relative coordinates. Reconstruct
 // the CRT root and check literal GCDs, then apply the new block inequality
 // with absolute horizons represented only through a safe upper label bound.
 const word=[7687,5233,3541,2389,1621,1093,733,7369],sh=[0];for(let p of word)sh.push(sh.at(-1)+p-1);
 let H=0n,P=4n,checks=0,ticks=0;
 for(let l=3;l<=3*Math.max(...word)+6;l+=2){if(spf[l]!==l)continue;let j=word.indexOf(l),a=j>=0?mod(1-sh[j],l):0;
  const valid=x=>sh.slice(0,-1).every((h,i)=>{let v=mod(x+h,l);return word[i]===l?v===1:v!==1&&v!==l-1});
  if(j>=0){if(!valid(a))throw Error("selected CRT")}else{while(a<l&&!valid(a))a++;if(a===l)throw Error("empty CRT")}
  let L=BigInt(l),x=Number(P%L),y=mod(a-Number(H%L),l),u=1,v=0,b=l;
  while(b){let q=Math.floor(x/b);[x,b]=[b,x-q*b];[u,v]=[v,u-q*v]}
  if(x!==1)throw Error("inverse");H+=P*BigInt(mod(u*y,l));P*=L;checks+=word.length;
 }
 if(H<100000000n)H+=P;let H0=H,t=H/2n+3n,ev=[],rel=0;
 for(let p of word){let d=Number(2n*t-H),w=(3*p-d-1)/2;
  for(let j=1;j<=w;j++){let n=t+BigInt(j),e=n%2n?-1:1,x=e===1?n:n-2n,y=H-BigInt(e);while(y)[x,y]=[y,x%y];if(j<w?x!==1n:x!==BigInt(p)||e!==1)throw Error("literal witness");ticks++}
  let Z=H+BigInt(p-1),dp=Number(2n*(t+BigInt(w))-Z);
  if(dp!==2*p||BigInt(p*p)>H+1n)throw Error("witness post");
  // Relative ticks plus a conservative finite C for this finite word
  // (C is used only as an upper bound for reset labels; there are none).
  ev.push({p,H:sh[ev.length],Z:1000000000+sh[ev.length+1],t:rel,n:rel+w,d,dp,D:dp,a1:p>=47&&p>=5*d+15,near:false});
  H=Z;t+=BigInt(w);rel+=w;
 }
 inspect(ev,[],0,ev.length,false);
 s.witness={...s.witness,rootDigits:(H0/2n+1n).toString().length,ticks,checks};
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||100000),Number(process.argv[3]||180)),null,2));
