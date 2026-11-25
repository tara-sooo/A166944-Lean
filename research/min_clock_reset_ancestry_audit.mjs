// Reset-anchor ancestry: long waits versus short waits with recent high ancestors.
// Run node research/min_clock_reset_ancestry_audit.mjs 1024 4096 16384 65536
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,G=2*H+B+6,U=7*X+4,W=16*B,u=Math.log(B),ell=Math.log(u);
 const ok=(b,m)=>{if(!b)throw Error(m);};
 ok(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(U);
 for(let p=2;p<U;p++)if(!spf[p]){spf[p]=p;if(p*p<U)for(let j=p*p;j<U;j+=p)if(!spf[j])spf[j]=p;}
 let z=2,L=2;
 if(mode==='analytic'){for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>B**(1/16))break;L*=p;z=p;}}
 else {z=3;L=6;}
 const T=mode==='analytic'?Math.max(z+1,Math.ceil(B**.25)):Math.ceil(Math.sqrt(B));
 const mH=mode==='analytic'?Math.max(1,Math.floor(u**2.75)):mode==='diagnostic'||mode==='stress'?8:16;
 const mM=mode==='analytic'?Math.max(1,Math.floor(B**.625)):mode==='diagnostic'||mode==='stress'?12:24;
 const D0=mode==='analytic'?Math.ceil(40*ell)+1:4;
 const lo=X,hi=7*X/2-1,len=hi+1,r=new Int32Array(len),degrees=new Uint8Array(len);
 function fac(n,cb){while(n>1){const p=spf[n];if(p>B)break;if(p>2)cb(p);while(n%p===0)n/=p;}}
 let rare=0,maxDegree=0;
 for(let j=lo;j<=hi;j++){const q=Math.min(spf[2*j-1],spf[2*j+1]);if(q<=B)r[j]=q;for(const C of [2*j,2*j+2])fac(C,()=>degrees[j]++);maxDegree=Math.max(maxDegree,degrees[j]+1);rare+=+(degrees[j]+1>D0);}
 function hit(t,C,K){let v=K+1,p=0;for(const side of [-1,1])fac(C+side,q=>{const m=2*q,res=side===-1?0:q+2,w=t+1+(res-(t+1)%m+m)%m;if(w<v||(w===v&&w<=K&&q<p)){v=w;p=q;}});return [v,p];}
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a;};
 const paths=[],at=new Map(),W0=new Float64Array(len),WM=new Float64Array(len),WH=new Float64Array(len);
 let R=0,RM=0,RH=0,events=0,literal=0,twins=0;
 for(let i=0;i<N;i++){const M=X+1+2*i,s=M+2,K=Math.floor((7*M-1)/4),path=[];let t=s,C=2*M-2,inc=0,rr=0;
  for(;;){const e={i,M,C,t,inc,p:0,w:0};path.push(e);let row=at.get(C);if(!row){row=[];at.set(C,row);}row.push(e);
   ok(C<=2*t&&C-(2*M-2)<=G,'prefix gain');
   if(t>=s+H)break;
   const [v,p]=hit(t,C,K);
   if(X===1024){let vv=K+1,pp=0;for(let j=t+1;j<=K;j++){const n=gcd(j%2?j-2:j,j%2?C+1:C-1);if(n>1&&spf[n]<=B){vv=j;pp=spf[n];break;}}ok(v===vv&&p===pp,'literal');literal++;}
   if(!p){ok(!r[C/2]&&spf[C-1]===C-1&&spf[C+1]===C+1,'twin');twins++;break;}
   const q=r[C/2],cost=Math.max(0,Math.min(v,s+H)-Math.max(t,s+a))/2;
   ok(v-t<=2*q&&q<=p,'wait');e.p=p;e.w=cost/q;rr+=cost;R+=cost;W0[C/2]+=e.w;
   if(p>z&&p<=T){RM+=cost;WM[C/2]+=e.w;}if(p>T){RH+=cost;WH[C/2]+=e.w;}
   t=v;C+=p-1;inc=p;events++;
  }
  ok(rr<=B,'root cost');paths.push(path);
 }



 const Q=mode==='analytic'?Math.max(7,Math.ceil(B**.75)):Math.max(19,Math.ceil(B/(mode==='stress'?32:8)));
 const P=Math.max(Q,Math.ceil(B/(mode==='analytic'?u**.125:mode==='stress'?8:4)));
 const A=Math.min(mode==='analytic'?2*Math.floor(u**.125):12,2*Math.floor((Q-4)/8)),Z=3*A;
 const V=mode==='analytic'?Math.max(1,Math.floor(B**.0625)):Math.max(1,Math.min(8,Math.floor((P-9)/10)));
 const Dmax=mode==='analytic'?2*Math.floor(V/2):2*Math.floor(Math.min(12,(P-2*V-9)/6)/2);
 ok(P>2*V+5*Dmax+7,'positive ancestor deficit');
 const mod=(a,m)=>(a%m+m)%m,key=(J,s,p)=>J+':'+s+':'+p;
 const long=new Set(),short=new Set(),direct=new Set(),all=new Map();
 let divisorTests=0,crtTests=0,maxFactors=0,formChecks=0,actualReset=0,actualLong=0,actualRecent=0,actualOld=0,excursionChecks=0,minExcursionRatio=Infinity;
 function inv(a,m){let b=m,x=1,y=0;while(b){let k=Math.floor(a/b);[a,b]=[b,a-k*b];[x,y]=[y,x-k*y];}ok(a===1,'inverse');return mod(x,m);}
 for(let p=P;p<=B;p++)if(spf[p]===p)for(let s=0;s<2;s++)for(let e=0;e<=Dmax;e+=2)for(let s0=0;s0<2;s0++){
  const mn=Math.ceil((p-1+6*s-2*V-5*e-6*s0)/2),mx=Math.floor((p-1+6*s-2+e-6*s0)/2);
  for(let n=mn;n<=mx;n++){
   ok(n>0&&n<p,'nonzero divisor below p');divisorTests++;let nf=0;
   fac(n,q=>{if(q<Q)return;nf++;ok(q!==p,'different labels');
    const k=n/q,off=p-1+e,rr=mod(-2*s,p),r2=mod(off-2*s0,q);
    const c=rr+p*mod((r2-rr)*inv(p,q),q),m=p*q;
    if(mod(-off-2*k,4))return;
    const j0=c+m*mod(-c*(m%4),4),step=4*m,lo2=2*X+off;
    for(let J=j0+Math.ceil((lo2-j0)/step)*step;J<7*X;J+=step){short.add(key(J,s,p));crtTests++;}
   });maxFactors=Math.max(maxFactors,nf);
  }
 }
 for(let J=2*X;J<7*X;J+=4)for(let s=0;s<2;s++)fac(J+2*s,p=>{
  if(p<Q)return;const t=J/2+3*s,k0=key(J,s,p);let arr=all.get(J);if(!arr){arr=[];all.set(J,arr);}arr.push({J,s,p,t,key:k0});
  if(p<P||J-p+1<2*X)return;
  const D=J-p+1,eta=2-4*s,m=(J+2*s)/p;
  ok(p*(m-1)===D+(s?1:-1)&&p*(m-1)+eta===D+(s?-1:1),'reset quotient forms');formChecks++;
  if(r[D/2]>V/2)long.add(k0);
  if(X<=4096)for(let e=0;e<=Dmax;e+=2){const E=D-e;if(E<2*X)continue;
   for(let s0=0;s0<2;s0++)fac(E+2*s0,q=>{if(q<Q)return;
    const low=p-1+6*s-2*V-5*e,high=p-1+6*s-2+e;
    for(let k=Math.max(1,Math.ceil((low-6*s0)/(2*q)));6*s0+2*q*k<=high;k++){
     const t0=(E+6*s0)/2+q*k;if(t0%2===s0)direct.add(k0);
    }
   });
  }
 });
 if(X<=4096)ok(short.size===direct.size&&[...short].every(x=>direct.has(x)),'independent ancestor envelopes');
 const neighbors=new Map();
 function near(e){if(neighbors.has(e.key))return neighbors.get(e.key);let n=0;
  for(let a=-4*Math.floor(A/4);a<=A;a+=4)for(const f of all.get(e.J+a)||[])if(f.J!==e.J||f.t!==e.t){if(Math.abs(f.t-e.t)<=Z){ok(f.p!==e.p,'distinct close labels');n++;}}
  neighbors.set(e.key,n);return n;
 }
 let totalPairs=0,longPairs=0,shortPairs=0,maxNeighbors=0;
 for(const arr of all.values())for(const e of arr)if(e.p>=P&&e.J-e.p+1>=2*X){const n=near(e);totalPairs+=n;maxNeighbors=Math.max(maxNeighbors,n);if(long.has(e.key))longPairs+=n;if(short.has(e.key))shortPairs+=n;}
 for(const path of paths){let prev=-1,lastReset=0;
  for(let j=0;j<path.length;j++){
   const v=path[j],s=v.t%2,delta=2*v.t-v.C-6*s;
   if(v.inc>=Q){ok(delta>=0&&delta%(2*v.inc)===0,'high deficit');
    if(v.inc>=P&&delta===0){
     actualReset++;const p=v.inc,D=path[j-1],wait=v.t-D.t,k0=key(v.C,s,p);
     if(wait>V){v.cls=0;actualLong++;ok(long.has(k0),'long reset envelope');}
     else {
      const eR=D.C-path[lastReset].C,dt=D.t-path[lastReset].t;
      ok(dt<=3*eR&&5*eR>=p-1+6*s-2*wait-6,'short reset excursion');
      excursionChecks++;minExcursionRatio=Math.min(minExcursionRatio,eR/p);
      if(prev>=0&&D.C-path[prev].C<=Dmax){
       v.cls=1;actualRecent++;const E=path[prev],e=D.C-E.C,l=D.t-E.t,n=(2*E.t-E.C-6*(E.t%2))/2;
       ok(n>0&&n<p&&n%E.inc===0&&l<=3*e,'actual ancestor divisor');
       ok(2*E.t-E.C===p-1+6*s-2*wait+e-2*l,'deficit drift');
       ok(short.has(k0),'short reset envelope');
      }else{v.cls=2;actualOld++;}
     }
    }
    prev=j;
   }
   v.latest=prev;if(delta===0)lastReset=j;
  }
 }
 const results=[];
 for(const sector of [0,1]){
  const accept=e=>sector===0?e.p>z&&e.p<=T:e.p>T;
  const cap=mode==='analytic'?[u**5/(1+A),Q*u**2/((1+A)*(1+Dmax)*(1+V+Dmax))].map(v=>v*(sector===0?B**.625:1)):mode==='stress'?[8,16]:[16,64];
  const stats=[0,1,2].map(c=>({raw:0,paid:0,rest:0,inc:0,keys:new Map(),maxProduct:0}));
  let E=0,diag=0,sync=0,asynch=0,same=0,eligible=0,checks=0,immediate=0;
  for(const [C,row] of at){
   const r0=r[C/2],tags=row.filter(e=>e.w>0&&accept(e));if(!tags.length)continue;
   const sum=tags.reduce((s,v)=>s+v.w,0);E+=r0*sum*sum;diag+=r0*tags.reduce((s,v)=>s+v.w*v.w,0);
   const batch=new Map();
   for(let i=0;i<tags.length;i++)for(let j=0;j<i;j++){
    const x=tags[i],y=tags[j],ee=2*r0*x.w*y.w;
    if(x.t!==y.t){asynch+=ee;continue;}sync+=ee;
    const a=paths[x.i],b=paths[y.i];let k=0,l=0;
    while(k<a.length&&l<b.length){checks++;if(a[k].C<b[l].C){k++;continue;}if(b[l].C<a[k].C){l++;continue;}if(a[k].t===b[l].t)break;k++;l++;}
    ok(k<a.length&&l<b.length&&a[k].C<=C&&a[k].C===b[l].C&&a[k].t===b[l].t,'first physical');
    if(!k||!l||a[k].inc!==b[l].inc)continue;same+=ee;
    const ai=a[k-1].latest,bi=b[l-1].latest;if(ai<0||bi<0)continue;
    const f=a[ai],g=b[bi];if(Math.max(f.inc,g.inc)<P||Math.abs(f.C-g.C)>A||Math.abs(f.t-g.t)>Z)continue;
    if(2*f.t-f.C!==6*(f.t%2)||2*g.t-g.C!==6*(g.t%2))continue;
    const [v,w]=f.inc>=P?[f,g]:[g,f],cl=v.cls;ok(cl>=0&&cl<=2,'actual reset class');
    const vkey=key(v.C,v.t%2,v.inc),wkey=key(w.C,w.t%2,w.inc),id=vkey+'/'+wkey,s=stats[cl],mt=a[k].C+':'+a[k].t;
    ok(vkey!==wkey&&near({J:v.C,t:v.t,p:v.inc,key:vkey})>0,'actual pair envelope');
    if(cl===0)ok(long.has(vkey),'long pair');if(cl===1)ok(short.has(vkey),'recent pair');
    let v0=s.keys.get(id)||{mt,last:-1,tail:0};ok(v0.mt===mt,'unique meeting');if(v0.last!==C){v0.last=C;v0.tail+=r0;}s.keys.set(id,v0);
    s.raw+=ee;s.inc++;eligible+=ee;if(ai===k-1&&bi===l-1)immediate+=ee;
    const bk=cl+':'+id,b0=batch.get(bk)||{cl,mass:0};b0.mass+=ee/r0;batch.set(bk,b0);
   }
   for(const b of batch.values()){const s=stats[b.cl],c=cap[b.cl]||0;s.maxProduct=Math.max(s.maxProduct,b.mass);s.paid+=r0*Math.min(c,b.mass);s.rest+=r0*Math.max(0,b.mass-c);}
  }
  const eps=1e-6*Math.max(1,E);ok(Math.abs(E-diag-sync-asynch)<=eps&&Math.abs(eligible-stats.reduce((s,v)=>s+v.raw,0))<=eps,'energy ledger');
  for(let j=0;j<3;j++){const s=stats[j];let tail=0;for(const v of s.keys.values()){ok(v.tail<=1.5*G,'common suffix');tail+=v.tail;}
   ok(s.keys.size<=[longPairs,shortPairs,totalPairs][j]&&s.paid<=(cap[j]||0)*tail+eps&&Math.abs(s.raw-s.paid-s.rest)<=eps,'cap');
   s.keyCount=s.keys.size;delete s.keys;
  }
  results.push({sector,E,same,eligible,immediate,checks,cap,stats});
 }
 return {X,B,mode,P,Q,A,Z,V,Dmax,events,literal,R,actualReset,actualLong,actualRecent,actualOld,excursionChecks,minExcursionRatio:Number.isFinite(minExcursionRatio)?minExcursionRatio:null,longKeys:long.size,shortKeys:short.size,directKeys:X<=4096?direct.size:null,totalPairs,longPairs,shortPairs,maxNeighbors,divisorTests,crtTests,maxFactors,formChecks,results};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','stress'])console.log(JSON.stringify(audit(X,mode)));
