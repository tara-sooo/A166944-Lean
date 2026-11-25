// Physical post-state pair deficit flux and short-wait descent gain.
// Run node research/min_clock_descent_flux_audit.mjs 1024 4096 16384 65536
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,startAge=mode==='full'?0:mode==='early'?B:2*B,a=startAge,N=X/2,G=2*H+B+6,U=7*X+4,W=16*B,u=Math.log(B),ell=Math.log(u);
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
  ok(rr<=(H-startAge)/2,'root cost');paths.push(path);
 }









 const eps=mode==='analytic'?Math.min(.125,u**(-.125)):mode==='wide'?.25:.0625;
 const m=mode==='analytic'?Math.max(1,Math.floor(u**2.5)):mode==='wide'?16:4;
 const nodes=new Map(),posW=new Float64Array(len),posOff=new Float64Array(len);
 const d=e=>2*e.t-e.C,P=n=>n*(n-1),key=e=>e.t+':'+e.C;
 let edges=0,diagDown=0,diagCheapGain=0,cheapGain=0,cheapInc=0,fullR=0;
 for(const path of paths){let a=null;for(let j=0;j<path.length;j++){
   const e=path[j],id=key(e);let v=nodes.get(id);
   if(!v){v={id,C:e.C,t:e.t,d:d(e),n:0,out:0,children:new Map(),next:null,root:0};nodes.set(id,v);}
   v.n++;if(a){let k=v.children.get(a.id);if(!k){k={a,n:0,p:e.inc,wait:v.t-a.t,drift:v.d-a.d};v.children.set(a.id,k);edges++;}k.n++;ok(k.p===e.inc&&k.wait>0&&k.drift===2*k.wait-(k.p-1),'edge identity');
    a.out++;ok(!a.next||a.next===v,'deterministic successor');a.next=v;
    fullR+=k.wait/2;
    if(k.drift>0){const q=r[a.C/2],w=k.wait/(2*q);ok(k.drift<=24*q*w*w+1e-9,'positive drift credit');posW[a.C/2]+=w;posOff[a.C/2]+=q*w*w;}
    diagDown+=Math.max(0,-k.drift);
    if(k.wait<=eps*(k.p-1)){ok(k.drift<0,'cheap descent');cheapInc++;diagCheapGain+=k.p-1;}
   }else v.root++;
   a=v;
 }}
 let birth=0,expiry=0,birthPairs=0,expiryPairs=0,positive=0,negative=0,cheapSharedGain=0,cheapSharedDrop=0,entryDown=0,entryCheapGain=0,entryCheapDrop=0,birthCap=0,allBirthCap=0,lowBirth=0,highBirth=0,thinBirth=0,thinPairs=0,thinCharge=0,thinAll=0,diag=0,groups=0,mixedPairs=0,sameLabelBirth=0,levelOracle=0,levelFormula=0,cheapLevelOracle=0,cheapLevelFormula=0,maxMass=0;
 let allBirthByLabel=0;const out=[];
 function f(n){return n<=m?n*n:2*m*n-m*m;}
 for(const v of nodes.values()){
  maxMass=Math.max(maxMass,v.n);
  let inP=0,sumF=v.root*f(1),sumN=v.root,own=0,entry=0,entryCheap=0,entryGain=0,cap=v.d;
  const labels=new Map();const cs=[...v.children.values()];
  ok(v.root<=1&&v.out<=v.n,'mass');
  for(const e of cs){
   sumN+=e.n;sumF+=f(e.n);const pp=P(e.n);inP+=pp;
   if(e.drift>0)positive+=e.drift*pp;
   if(e.drift<0)negative-=e.drift*pp;
   if(e.wait<=eps*(e.p-1)){cheapSharedGain+=(e.p-1)*pp;cheapSharedDrop-=e.drift*pp;}
   let z=labels.get(e.p);if(!z){z=[];labels.set(e.p,z);}z.push(e);
  }
  ok(sumN===v.n,'incoming mass');
  const b=P(v.n)-inP,x=P(v.n)-P(v.out);
  birthPairs+=b;expiryPairs+=x;birth+=v.d*b;expiry+=v.d*x;
  if(v.d<=m)lowBirth+=v.d*b;else highBirth+=v.d*b;
  if(v.n<=m){thinBirth+=v.d*b;thinPairs+=b;}
  const pot=f(v.n)-sumF;ok(pot>=-1e-9,'truncated convex potential');thinCharge+=pot;
  if(v.n<=m)ok(pot===b,'small birth potential');
  for(const [p,es] of labels){
   groups++;
   let n=0,sp=0;for(const e of es){n+=e.n;sp+=P(e.n);}
   sameLabelBirth+=P(n)-sp;
   // Cross-child pairs in the same selected label: each common downward
   // crossing covers exactly min(predeficits)-postdeficit levels.
   for(let i=0;i<es.length;i++){const a=es[i],dropA=Math.max(0,-a.drift),isA=a.wait<=eps*(p-1);
    levelFormula+=dropA*a.n*a.n;
    if(isA)cheapLevelFormula+=dropA*a.n*a.n;
    for(let j=0;j<i;j++){const b=es[j],k=2*a.n*b.n,drop=Math.min(dropA,Math.max(0,-b.drift)),isB=b.wait<=eps*(p-1);
     entry+=drop*k;
     if(isA&&isB){entryCheap+=drop*k;entryGain+=(p-1)*k;}
     cap=Math.max(cap,a.a.d,b.a.d);
     levelFormula+=drop*k;if(isA&&isB)cheapLevelFormula+=drop*k;
    }
   }
   // Independent difference-array integration of actual level occupancy.
   // Restrict to observed nonzero ranges; no candidate envelope.
   const diff=new Map(),dc=new Map();
   function add(map,k,n){map.set(k,(map.get(k)||0)+n);}
   for(const e of es)if(e.drift<0){add(diff,v.d+1,e.n);add(diff,e.a.d+1,-e.n);if(e.wait<=eps*(p-1)){add(dc,v.d+1,e.n);add(dc,e.a.d+1,-e.n);}}
   for(const [map,b0] of [[diff,0],[dc,1]]){let prev=0,n=0,E=0;for(const k of [...map.keys()].sort((a,b)=>a-b)){E+=(k-prev)*n*n;n+=map.get(k);prev=k;}ok(n===0,'level integral');if(b0)cheapLevelOracle+=E;else levelOracle+=E;}
  }
  mixedPairs+=b-(Array.from(labels.values()).reduce((s,es)=>s+P(es.reduce((q,e)=>q+e.n,0))-es.reduce((q,e)=>q+P(e.n),0),0));
  entryDown+=entry;entryCheapDrop+=entryCheap;entryCheapGain+=entryGain;
  birthCap+=v.d*b+entry;allBirthCap+=cap*b;
  if(v.n<=m)thinAll+=v.d*b+entry;
 }
 let Epos=0,EposOff=0;for(let j=lo;j<=hi;j++){Epos+=r[j]*posW[j]**2;EposOff+=r[j]*posW[j]**2-posOff[j];}
 const tol=1e-6*Math.max(1,Epos,negative,birth,levelOracle);
 ok(birthPairs===expiryPairs,'pair conservation');
 ok(negative+expiry===positive+birth,'exact pair drift flux');
 ok(positive<=24*EposOff+tol,'positive common edge energy');
 ok(levelOracle===levelFormula&&cheapLevelOracle===cheapLevelFormula,'independent level integrals');
 ok(levelOracle===diagDown+negative+entryDown,'full descent moment exact');
 ok(cheapLevelOracle===cheapSharedDrop+entryCheapDrop+paths.reduce((s,path)=>s+path.slice(1).reduce((a,e,j)=>{const p=e.inc,w=e.t-path[j].t;return a+(w<=eps*(p-1)?p-1-2*w:0)},0),0),'cheap descent exact');
 ok((1-2*eps)*(cheapSharedGain+entryCheapGain)<=cheapSharedDrop+entryCheapDrop+tol,'cheap gain transfer');
 ok(birthCap<=allBirthCap&&thinAll<=(12*B+6)*thinPairs&&thinPairs<=2*m*N&&thinCharge<=2*m*N,'birth caps and potential');
 // Pair-level oracle on a bounded deterministic set of original root pairs:
 // compare exact first shared state / all subsequent drift and cheap gain.
 let pairChecks=0,pairBirthEntry=0,pairShared=0;
 for(let i=0;i<paths.length;i+=Math.max(1,Math.floor(N/128))){
  const x=paths[i],mx=new Map(x.map((e,j)=>[key(e),j]));
  for(let j=Math.max(0,i-16);j<i;j++){
   const y=paths[j];let first=null,last=null,A=0,D=0,CG=0;
   for(let k=0;k<y.length;k++){const q=mx.get(key(y[k]));if(q===undefined)continue;
    if(first===null){first=[q,k];last=[q,k];continue;}
    ok(q===last[0]+1&&k===last[1]+1,'common event suffix');const dx=d(y[k])-d(y[k-1]),p=y[k].inc,w=y[k].t-y[k-1].t;
    A+=Math.max(0,dx);D+=Math.max(0,-dx);if(w<=eps*(p-1))CG+=p-1;last=[q,k];
   }
   if(first){pairChecks++;const z=d(y[first[1]]);ok(D+d(y[last[1]])===A+z&&CG*(1-2*eps)<=D+1e-8,'individual pair flux');pairShared+=D;
    const [q,k]=first;if(q&&k&&x[q].inc===y[k].inc)pairBirthEntry+=Math.min(Math.max(0,d(x[q-1])-z),Math.max(0,d(y[k-1])-z));
   }
  }
 }
 return {X,B,mode,eps,m,N,R,events,literal,nodes:nodes.size,edges,groups,maxMass,fullR,birthPairs,expiryPairs,birth,expiry,positive,negative,diagDown,entryDown,levelOracle,cheapInc,diagCheapGain,cheapSharedGain,cheapSharedDrop,entryCheapGain,entryCheapDrop,cheapLevelOracle,Epos,EposOff,birthCap,allBirthCap,lowBirth,highBirth,thinBirth,thinPairs,thinCharge,thinAll,mixedPairs,sameLabelBirth,pairChecks,pairBirthEntry,pairShared};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','wide'])console.log(JSON.stringify(audit(X,mode)));
