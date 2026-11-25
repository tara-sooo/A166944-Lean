// Actual first-birth drawdown, matched upward drift, and mixed-label deficit-band quotas.
// Run node research/min_clock_birth_drawdown_audit.mjs 1024 4096 16384 65536
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










 const m=mode==='analytic'?u**2.5:mode==='wide'?64:8;
 const y=mode==='analytic'?Math.max(3,Math.ceil(B**.125)):3,ell0=1+Math.log(u),lim=12*B+6;
 const nodes=new Map(),key=e=>e.t+':'+e.C,def=e=>2*e.t-e.C;
 for(const path of paths){const stop=path[path.length-1].t;let a=null;
  for(const e of path){let v=nodes.get(key(e));if(!v){v={id:key(e),t:e.t,C:e.C,d:def(e),n:0,root:null,children:new Map(),next:null,stops:[]};nodes.set(v.id,v);}
   v.n++;v.stops.push({stop,child:a?a.id:'root',p:e.inc});if(a){let g=v.children.get(a.id);if(!g){g={a,p:e.inc,n:0};v.children.set(a.id,g);}g.n++;ok(g.p===e.inc&&(!a.next||a.next===v),'common successor');a.next=v;}else{ok(v.root===null,'unique root');v.root=e.i;}a=v;
  }
 }
 const P=n=>n*(n-1),band=d=>Math.floor(Math.log2(lim/d));
 function cap(d,p,q){const j=band(d),D=lim/2**j;return B*p*q*m/(D*D*(j+1)**2*(p>=y&&q>=y?1:ell0**2));}
 let birth=0,expiry=0,A=0,D=0,pairs=0,initial=0,matched=0,unused=0,unspent=0,entry=0,entryNR=0,actualNR=0,rawNR=0;
 let mixed=0,mixedDraw=0,mixedQuota=0,mixedDrawQuota=0,mixedSmall=0,mixedQuotaAfterSmall=0,mixedDrawQuotaAfterSmall=0,smallDraw=0,smallRaw=0,smallPairs=0,largeDraw=0,zeroDrawPairs=0,positiveDrawPairs=0,layerCount=0,oracle=0,maxDepth=0,nonresetMixedPairs=0,mixedKeys=0,mixedHeavyKeys=0,largeBothMixed=0;
 const keyBands=new Map(),actualKeys=new Map(),byType={same:{pairs:0,raw:0,draw:0},mixed:{pairs:0,raw:0,draw:0},root:{pairs:0,raw:0,draw:0}};
 for(const v of nodes.values()){
  const cs=[...v.children.values()],b=P(v.n)-cs.reduce((a,e)=>a+P(e.n),0);if(!b)continue;
  pairs+=b;birth+=v.d*b;
  const nr=v.d!==6*(v.t%2)&&v.d>6,small=v.n<=m||v.d<=m;
  const labelMass=new Map();for(const e of cs)labelMass.set(e.p,(labelMass.get(e.p)||0)+e.n);
  const quota=new Map();const labelDraw=new Map();
  if(nr)for(const [p,np] of labelMass)for(const [q,nq] of labelMass)if(p<q){
   ok((v.d-6*(v.t%2))%(2*p*q)===0&& (v.C+2*(v.t%2))%(p*q)===0,'mixed divisor');
   const id=p+':'+q,prod=2*np*nq,c=cap(v.d,p,q);quota.set(id,Math.min(1,c/prod));mixedKeys++;mixedHeavyKeys+=+(prod>c);nonresetMixedPairs+=prod;
   const j=band(v.d),kk=j+':'+p+':'+q;actualKeys.set(kk,(actualKeys.get(kk)||0)+1);
   mixedQuota+=v.d*Math.min(prod,c);if(!small)mixedQuotaAfterSmall+=v.d*Math.min(prod,c);
   if(p>=y&&q>=y)largeBothMixed+=v.d*prod;
  }
  // Compute all suffix minima and drift sums, indexed by actual earlier stop.
  const suffix=new Map();let cur=v,mi=v.d,up=0,down=0,depth=0;
  while(cur){suffix.set(cur.t,{mi,up,down,d:cur.d});if(!cur.next)break;const dr=cur.next.d-cur.d;up+=Math.max(0,dr);down+=Math.max(0,-dr);cur=cur.next;mi=Math.min(mi,cur.d);depth++;}
  maxDepth=Math.max(maxDepth,depth);
  // Sorted stop times: each new birth pair is counted at its earlier stop,
  // using the remaining mass in other incoming children, by label.
  const sorted=v.stops.slice().sort((a,b)=>a.stop-b.stop),rem=new Map(),remLabel=new Map();
  for(const e of sorted){rem.set(e.child,(rem.get(e.child)||0)+1);remLabel.set(e.p,(remLabel.get(e.p)||0)+1);}
  let local=0,localDraw=0;
  for(let i=0;i<sorted.length;i++){const e=sorted[i],s=suffix.get(e.stop);ok(!!s,'stop on common suffix');
   rem.set(e.child,rem.get(e.child)-1);remLabel.set(e.p,remLabel.get(e.p)-1);
   const n=2*(sorted.length-i-1-rem.get(e.child));if(!n)continue;
   const I=v.d-s.mi,U=s.d-s.mi;ok(I>=0&&U>=0&&s.down>=I&&s.up>=U&&s.down-I===s.up-U,'drawdown matching');
   local+=n;localDraw+=I*n;initial+=I*n;matched+=(s.down-I)*n;unused+=U*n;A+=s.up*n;D+=s.down*n;expiry+=s.d*n;unspent+=s.mi*n;
   if(I===0)zeroDrawPairs+=n;else positiveDrawPairs+=n;
   if(small){smallPairs+=n;smallDraw+=I*n;smallRaw+=v.d*n;}else largeDraw+=I*n;
   for(const [q,nq] of remLabel){const count=2*(nq-(q===e.p?rem.get(e.child):0));if(!count)continue;
    const type=e.p===0||q===0?'root':q===e.p?'same':'mixed';const rec=byType[type];rec.pairs+=count;rec.raw+=v.d*count;rec.draw+=I*count;
    if(type==='mixed'&&nr){const id=Math.min(e.p,q)+':'+Math.max(e.p,q),f=quota.get(id);ok(f!==undefined,'quota key');mixed+=v.d*count;mixedDraw+=I*count;mixedDrawQuota+=f*I*count;if(small)mixedSmall+=I*count;else mixedDrawQuotaAfterSmall+=f*I*count;labelDraw.set(id,(labelDraw.get(id)||0)+I*count);}
   }
  }
  ok(local===b,'ordered birth count');
  // Independent explicit pair oracle for small nodes, including true suffix minima.
  if(v.n<=16){let bb=0,dd=0;for(let i=0;i<sorted.length;i++)for(let j=0;j<i;j++){const a=sorted[i],b=sorted[j];if(a.child===b.child)continue;bb+=2;dd+=2*(v.d-suffix.get(Math.min(a.stop,b.stop)).mi);oracle++;}ok(bb===local&&dd===localDraw,'drawdown pair oracle');}
  for(let i=0;i<cs.length;i++)for(let j=0;j<i;j++){const a=cs[i],b=cs[j];if(a.p!==b.p)continue;const k=2*a.n*b.n*Math.min(Math.max(0,a.a.d-v.d),Math.max(0,b.a.d-v.d));entry+=k;if(v.d!==6*(v.t%2))entryNR+=k;}
 }
 ok(D===initial+matched&&A===matched+unused&&birth===initial+unspent&&expiry===unused+unspent,'exact four-way conservation');
 ok(byType.same.pairs+byType.mixed.pairs+byType.root.pairs===pairs&&byType.same.draw+byType.mixed.draw+byType.root.draw===initial,'birth classes');
 // Direct independent edge flow (including expiry multiplicity).
 let edgeA=0,edgeD=0,edgeExpiry=0;
 for(const v of nodes.values()){let out=0;if(v.next){const g=v.next.children.get(v.id);out=g.n;const z=v.next.d-v.d;edgeA+=Math.max(0,z)*P(out);edgeD+=Math.max(0,-z)*P(out);}edgeExpiry+=v.d*(P(v.n)-P(out));}
 ok(edgeA===A&&edgeD===D&&edgeExpiry===expiry,'independent graph flux');
 // Candidate support per deficit band and labels: exact arithmetic count
 // by CRT residue and phase; no enumeration of individual horizons.
 let envelope=0,envelopeGain=0,quotaEnvelope=0,quotaUsed=0,supportChecks=0;
 for(const [id,n] of actualKeys){const [j,p,q]=id.split(':').map(Number),D=lim/2**j;let cnt=0;
  for(const s of [0,1])for(let k=1;6*s+2*p*q*k<=D;k++){const d=6*s+2*p*q*k;if(d<=D/2)continue;
   const pq=p*q;let J=2*X+(((-2*s-2*X)%pq+pq)%pq);if(J%2)J+=pq;
   // t=(J+d)/2 must have parity s.
   if(((J+d)/2)%2!==s)J+=2*pq;
   if(J<7*X)cnt+=1+Math.floor((7*X-1-J)/(4*pq));
  }ok(n<=cnt,'CRT envelope');supportChecks++;envelope+=cnt;quotaEnvelope+=cnt*D*cap(D,p,q);quotaUsed+=n*D*cap(D,p,q);
 }
 ok(mixedQuota<=quotaUsed+1e-5&&mixedDrawQuota<=mixedQuota+1e-5&&mixedDrawQuotaAfterSmall<=mixedQuotaAfterSmall+1e-5,'mixed quota budget');
 ok(smallDraw<=smallRaw&&initial===smallDraw+largeDraw,'small drawdown union');
 return {X,B,mode,m,y,N,R,events,literal,nodes:nodes.size,pairs,birth,expiry,A,D,initial,matched,unused,unspent,entry,entryNR,rawNR:birth+entryNR,actualNR:initial+entryNR,smallDraw,smallRaw,smallPairs,largeDraw,zeroDrawPairs,positiveDrawPairs,byType,mixed,mixedDraw,mixedQuota,mixedDrawQuota,mixedSmall,mixedQuotaAfterSmall,mixedDrawQuotaAfterSmall,nonresetMixedPairs,mixedKeys,mixedHeavyKeys,largeBothMixed,oracle,maxDepth,envelope,quotaEnvelope,quotaUsed,supportChecks};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','wide'])console.log(JSON.stringify(audit(X,mode)));
