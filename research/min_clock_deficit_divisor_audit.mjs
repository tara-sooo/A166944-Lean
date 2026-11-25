// Deficit-divisor counting of close distinct physical high anchors.
// Run node research/min_clock_deficit_divisor_audit.mjs 1024 4096 16384 65536
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
 const A=mode==='analytic'?Math.min(2*Math.floor(u**.125),2*Math.floor((Q-4)/8)):Math.min(12,2*Math.floor((Q-4)/8));
 const Z=3*A,def=12*B+6;
 ok(Q>A+2&&Q>Z+A/2+3,'short anchor geometry');
 const ps=[];for(let p=3;p<=B;p+=2)if(spf[p]===p&&p>=Q)ps.push(p);
 const mod=(a,m)=>(a%m+m)%m;
 function inv(a,m){let b=m,x=1,y=0;while(b){const k=Math.floor(a/b);[a,b]=[b,a-k*b];[x,y]=[y,x-k*y];}ok(a===1,'inverse');return mod(x,m);}
 const invs=new Map();
 function countCRT(q,b,a,s1,s2,k1,k2){
  if(mod(2*k1+a-2*k2,4))return 0;
  const id=q*U+b;let qi=invs.get(id);if(qi===undefined){qi=inv(q,b);invs.set(id,qi);}
  const n0=mod(-2*s1,q),c=n0+q*mod((-a-2*s2-n0)*qi,b),m=q*b;
  const d=c+m*mod((2*k1-c)*(m%4),4),M=4*m,l=Math.max(2*X,2*X-a),h=Math.min(7*X-2,7*X-2-a);
  return Math.max(0,Math.floor((h-d)/M)-Math.ceil((l-d)/M)+1);
 }
 const env=[0,0],direct=[0,0];let divisorTests=0,crtCalls=0,factorChoices=0,maxFactors=0;
 for(const q of ps){if(q<P)continue;for(let s1=0;s1<2;s1++)for(let k=0;6*s1+2*q*k<=def;k++)for(let a=-A;a<=A;a+=2)for(let s2=0;s2<2;s2++)for(let b=-Z;b<=Z;b++){
  if((a===0&&b===0)||mod(b-(s2-s1),2))continue;
  const n=q*k+b-a/2-3*(s2-s1);if(n<0)continue;
  if(k===0&&n!==0){ok(n<Q,'one reset impossible');continue;}
  if(k>0)ok(n>0,'nonreset positive divisor target');
  const cls=k===0?0:1,qs=[];
  if(cls===0)qs.push(...ps);else{fac(n,p=>{if(p>=Q)qs.push(p);});divisorTests++;factorChoices+=qs.length;maxFactors=Math.max(maxFactors,qs.length);}
  for(const q2 of qs){
   if(q===q2){if(a+2*(s2-s1)===0&&mod(2*k+a-2*(cls?n/q2:0),4)===0&&6*s2+2*n<=def)throw Error('same label close distinct physical anchors');continue;}
   const k2=cls?n/q2:0;ok(Number.isInteger(k2),'factor quotient');
   if(6*s2+2*q2*k2>def)continue;
   env[cls]+=countCRT(q,q2,a,s1,s2,k,k2);crtCalls++;
  }
 }}
 if(X<=4096){
  const states=new Map();
  for(let D=2*X;D<7*X;D+=2){const arr=[];for(let s=0;s<2;s++)fac(D+2*s,q=>{if(q<Q)return;for(let k=0;6*s+2*q*k<=def;k++){const t=(D+6*s)/2+q*k;if(t%2===s)arr.push({q,k,t});}});if(arr.length)states.set(D,arr);}
  for(const [D,arr] of states)for(const a0 of arr){if(a0.q<P)continue;for(let e=-A;e<=A;e+=2)for(const b of states.get(D+e)||[]){
   if(Math.abs(a0.t-b.t)>Z||e===0&&a0.t===b.t)continue;
   ok(a0.q!==b.q&&(a0.k===0)===(b.k===0),'direct close anchor identities');direct[a0.k===0?0:1]++;
  }}
  ok(direct[0]===env[0]&&direct[1]===env[1],'independent arithmetic envelope '+JSON.stringify({env,direct}));
 }
 for(const path of paths){let h=-1;for(let j=0;j<path.length;j++){if(path[j].inc>=Q)h=j;path[j].anchor=h;}}
 const results=[];
 for(const sector of [0,1]){
  const accept=e=>sector===0?e.p>z&&e.p<=T:e.p>T;
  const caps=mode==='analytic'?[u**3.5,B**.75*u**2/(1+A)**2].map(v=>v*(sector===0?B**.625:1)):mode==='stress'?[8,16]:[16,64];
  let R1=0,E=0,diag=0,async=0,sync=0,same=0,other=0,checks=0,eligible=0,immediate=0,low=0,oneHigh=0;
  const ar=[0,1].map(i=>({cap:caps[i],raw:0,paid:0,rest:0,immediate:0,earlier:0,low:0,incidences:0,maxProduct:0,keys:new Map()}));
  for(const [C,row] of at){const r0=r[C/2],tags=row.filter(e=>e.w>0&&accept(e));if(!tags.length)continue;
   const sum=tags.reduce((s,v)=>s+v.w,0);R1+=r0*sum;E+=r0*sum*sum;diag+=r0*tags.reduce((s,v)=>s+v.w*v.w,0);
   const batch=new Map();
   for(let i=0;i<tags.length;i++)for(let j=0;j<i;j++){
    const x=tags[i],y=tags[j],e=2*r0*x.w*y.w;
    if(x.t!==y.t){async+=e;continue;}sync+=e;
    const a=paths[x.i],b=paths[y.i];let k=0,l=0;
    while(k<a.length&&l<b.length){checks++;if(a[k].C<b[l].C){k++;continue;}if(b[l].C<a[k].C){l++;continue;}if(a[k].t===b[l].t)break;k++;l++;}
    ok(k<a.length&&l<b.length&&a[k].C<=C&&a[k].C===b[l].C&&a[k].t===b[l].t,'first physical');
    const v=a[k];if(!k||!l||v.inc!==b[l].inc){other+=e;continue;}same+=e;
    const ai=a[k-1].anchor,bi=b[l-1].anchor;
    if(ai<0||bi<0)continue;const A1=a[ai],A2=b[bi];if(Math.max(A1.inc,A2.inc)<P)continue;oneHigh+=e;
    if(Math.abs(A1.C-A2.C)>A||Math.abs(A1.t-A2.t)>Z)continue;
    const [f,g]=A1.inc>=P?[A1,A2]:[A2,A1],q=f.inc,q2=g.inc,s1=f.t%2,s2=g.t%2,a0=g.C-f.C,b0=g.t-f.t;
    const k1=(2*f.t-f.C-6*s1)/(2*q),k2=(2*g.t-g.C-6*s2)/(2*q2);
    ok(q!==q2&&Number.isInteger(k1)&&Number.isInteger(k2)&&k1>=0&&k2>=0&&(k1===0)===(k2===0),'actual anchor arithmetic');
    ok(q2*k2===q*k1+b0-a0/2-3*(s2-s1),'deficit divisor equation');
    ok(countCRT(q,q2,a0,s1,s2,k1,k2)>0,'actual anchor counted');
    const cls=k1===0?0:1,key=[f.C,f.t,q,g.C,g.t,q2].join(':'),id=cls+':'+key,imm=ai===k-1&&bi===l-1;
    const isLow=a.slice(ai+1,k+1).every(e=>e.inc<=5)&&b.slice(bi+1,l+1).every(e=>e.inc<=5);
    const z0=ar[cls],meet=v.C+':'+v.t,prev=z0.keys.get(key)||{meet,last:-1,suffix:0};
    ok(prev.meet===meet,'one first physical meeting per anchor pair');
    if(prev.last!==C){prev.last=C;prev.suffix+=r0;}z0.keys.set(key,prev);
    let w=batch.get(id);if(!w){w={cls,mass:0};batch.set(id,w);}w.mass+=e/r0;
    eligible+=e;z0.raw+=e;z0.incidences++;if(imm){immediate+=e;z0.immediate+=e;}else z0.earlier+=e;if(isLow){low+=e;z0.low+=e;}
   }
   for(const b of batch.values()){const s=ar[b.cls];s.maxProduct=Math.max(s.maxProduct,b.mass);s.paid+=r0*Math.min(s.cap,b.mass);s.rest+=r0*Math.max(0,b.mass-s.cap);}
  }
  const eps=1e-6*Math.max(1,E);
  ok(Math.abs(E-diag-async-sync)<=eps&&Math.abs(sync-same-other)<=eps&&Math.abs(eligible-ar.reduce((s,v)=>s+v.raw,0))<=eps,'direct energy oracle');
  for(let j=0;j<2;j++){const v=ar[j];let ss=0;for(const k of v.keys.values()){ok(k.suffix<=1.5*G,'unique deterministic suffix weight');ss+=k.suffix;}ok(v.keys.size<=env[j]&&v.paid<=v.cap*ss+eps&&Math.abs(v.raw-v.paid-v.rest)<=eps,'actual pair cap and envelope');v.maxSuffix=Math.max(0,...[...v.keys.values()].map(k=>k.suffix));v.keyCount=v.keys.size;delete v.keys;}
  results.push({sector,R:R1,E,diag,sync,async,same,other,checks,oneHigh,eligible,immediate,low,ar});
 }
 return {X,B,mode,P,Q,A,Z,env,direct:X<=4096?direct:null,divisorTests,crtCalls,factorChoices,maxFactors,events,literal,R,results};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','stress'])console.log(JSON.stringify(audit(X,mode)));
