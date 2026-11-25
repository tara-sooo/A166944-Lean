// Exceptional-degree reverse set expansion and growing-depth good first meetings.
// Run: node research/min_clock_reverse_growth_audit.mjs 1024 4096 16384 65536 262144
function audit(X,mode='analytic'){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,ell=Math.log(Math.log(B));
 const check=(x,m)=>{if(!x)throw Error(m)};
 check(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(7*X+4);
 for(let p=2;p<spf.length;p++)if(!spf[p]){
   spf[p]=p;if(p*p<spf.length)for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 }
 const S=Math.max(1,Math.log(ell));
 let L=2,y=2;
 for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>6*S**.25)break;L*=p;y=p;}
 const rough=mode.startsWith('rough'),Z=mode==='roughDiagnostic'?Math.ceil(B/10):Math.ceil(B**.25);
 const Q=mode==='analytic'?Math.ceil(B/Math.exp(Math.sqrt(ell))):Math.ceil(.95*B);
 const T=mode==='analytic'?Math.ceil(20*ell):mode==='degree'?4:Math.ceil(20*ell);
 const g=Math.max(2,T*L),k=mode==='analytic'?Math.max(0,Math.floor(ell/(2*Math.log(g)))):mode==='roughAnalytic'?Math.max(0,Math.floor(1.5*ell/Math.log(g))):mode==='degree'?3:5;
 const lo=X,hi=7*X/2-1,len=hi+1;
 const d=new Uint8Array(len),exposed=new Uint8Array(len),A=new Uint8Array(len),r=new Int32Array(len);
 function factors(n,cb){while(n>1){const p=spf[n];if(p>B)break;if(p>2)cb(p);while(n%p===0)n/=p;}}
 let nA=0,nHigh=0,nExc=0,tail=0,maxDegree=0,S0=0;
 for(let j=lo;j<=hi;j++){
   const C=2*j;let n=0;
   for(const x of [C,C+2])factors(x,p=>{if(p>y)n++;if(p>=Q)exposed[j]=1;});
   for(const x of [C-1,C+1])factors(x,p=>{if(p>=Q)exposed[j]=1;});
   d[j]=n;maxDegree=Math.max(maxDegree,n);
   const q=Math.min(spf[C-1],spf[C+1]);if(q<=B){r[j]=q;S0+=q;}
   if(rough)exposed[j]=+(r[j]>=Z);
   if(n>T){tail+=n;nExc++;}
   if(exposed[j])nHigh++;
   if(exposed[j]||n>T){A[j]=1;nA++;}
 }
 let cur=A,curN=nA,relaxed=new Uint8Array(len),layers=[nA],relaxedN=0;
 for(let i=0;i<=k;i++){
   const J=new Uint8Array(len);let jN=0;
   for(let x=lo;x<=hi;x++)if(cur[x])for(let e=0;e<L/2&&x-e>=lo;e++){
     if(!J[x-e]){J[x-e]=1;jN++;}
     if(!relaxed[x-e]){relaxed[x-e]=1;relaxedN++;}
   }
   check(jN<=L/2*curN,'LOW offset bound');
   if(i===k)break;
   const next=new Uint8Array(len);let nextN=0,edges=0;
   for(let j=lo;j<=hi;j++)if(J[j]){
     let n=0;for(const v of [2*j,2*j+2])factors(v,p=>{
       if(p<=y)return;n++;const D=j-(p-1)/2;
       if(D>=lo&&!next[D]){next[D]=1;nextN++;}
     });check(n===d[j],'reverse degree identity');edges+=n;
   }
   check(nextN<=edges&&edges<=T*jN+tail&&nextN<=g*curN+tail,'reverse recurrence');
   cur=next;curN=nextN;layers.push(curN);
 }
 const layerSum=layers.reduce((s,x)=>s+x,0);
 check(relaxedN<=L/2*layerSum,'root union bound');
 let relaxedRoots=0;for(let M=X+1;M<2*X;M+=2)relaxedRoots+=relaxed[M-1];
 const U=new Float64Array(len),UK=new Float64Array(len),goodH=new Int32Array(len);
 const V=new Map(),key=(t,C)=>t*(7*X+4)+C,oracle=X<=16384;
 function vertex(rec){const id=key(rec.t,rec.C);let v=V.get(id);
   if(!v){v={n:0,g:0,e:0,edges:new Map(),good:oracle?[]:null,expire:oracle?[]:null,slab:oracle?[]:null};V.set(id,v);}
   return v;
 }
 function hit(t,C,K){
   let T=K+1,P=0;
   for(const s of [-1,1]){
     let v=C+s;while(v>1){const p=spf[v];if(p>B)break;
       const m=2*p,res=s===-1?0:p+2,u=t+1+((res-(t+1)%m+m)%m);
       if(p>2&&(u<T||(u===T&&u<=K&&p<P))){T=u;P=p;}
       while(v%p===0)v/=p;
     }
   }return [T,P];
 }
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a;};
 let marked=0,markedHigh=0,markedDegree=0,markedBoth=0,R=0,RK=0,events=0,literal=0,finished=0,keptFinished=0,gg=0,gb=0,bb=0,allPairs=0,shallowCost=0,maxShallowAge=0;
 let shallowWithHigh=0,keptRoots=0,actualMaxDepth=0,keptSlabRoots=0;
 for(let M=X+1;M<2*X;M+=2){
   const s=M+2,C0=2*M-2,K=Math.floor((7*M-1)/4),path=[];
   let t=s,C=C0,depth=0,medium=0,large=0,low=0,flagH=false,flagD=false,cost=0,twin=false,prev=null;
   for(;;){
     check(C<=2*t&&C>=C0&&C-C0<=2*H+B+6,'prefix invariant');
     const j=C/2;
     if(depth<=k){if(exposed[j])flagH=true;if(d[j]>T)flagD=true;}
     const rec={t,C,prev,depth,medium,large,w:0,ell:0};path.push(rec);
     if(t>=s+H)break;
     const [u,p]=hit(t,C,K);
     if(X<=1024){
       let aa=K+1,bb=0;for(let n=t+1;n<=K;n++){
         const q=gcd(n%2?n-2:n,n%2?C+1:C-1);
         if(q>1&&spf[q]<=B){aa=n;bb=spf[q];break;}
       }check(aa===u&&bb===p,'literal MIN');literal++;
     }
     if(!p){check(!r[j]&&spf[C-1]===C-1&&spf[C+1]===C+1,'terminal twin');twin=true;finished++;break;}
     const q=r[j],dur=Math.max(0,Math.min(u-s,H)-Math.max(t-s,a));
     check(q>0&&u-t<=2*q&&q<=p,'wait bound');
     rec.w=dur/(2*q);rec.ell=dur;
     U[j]+=rec.w;cost+=dur/2;R+=dur/2;
     if(!rough&&p>=Q&&medium<=k){check(flagH,'shallow high selection must mark');shallowWithHigh++;}
     if(p<=y){low+=p-1;check(low<L,'LOW barrier');}
     else{depth++;low=0;check((C+p-1)%p===0||(C+p+1)%p===0,'reverse congruence');if(p>=Q)large++;else medium++;}
     prev=key(t,C);t=u;C+=p-1;events++;
   }
   actualMaxDepth=Math.max(actualMaxDepth,depth);
   check(cost<=B,'per-root budget');
   if(flagH||flagD){
     check(relaxed[M-1]===1,'actual marked root contained in reverse union');
     marked++;markedHigh+=+flagH;markedDegree+=+flagD;markedBoth+=+(flagH&&flagD);continue;
   }
   keptRoots++;if(twin)keptFinished++;
   if(cost>0)keptSlabRoots++;
   let lastGood=null;
   for(const rec of path){
     const j=rec.C/2,v=vertex(rec),inc=v.edges.get(rec.prev)||[0,0],good=rough?rec.depth<=k:rec.medium<=k;
     if(good){
       check((rough||rec.large===0)&&rec.depth<=k&&!A[j],'retained shallow property');
       goodH[j]++;lastGood=v;if(oracle)v.good.push(M);
       shallowCost+=rec.ell/2;
       if(!rough)check(rec.C-C0<=k*(Q-1)+(k+1)*(L-2),'shallow gain');
       else check(r[j]<Z,'retained shallow rough gate');
       maxShallowAge=Math.max(maxShallowAge,rec.t-s);
       check(rec.t-s<=(rough?2*Z*(k+1)*L:3*(k*(Q-1)+(k+1)*(L-2))),'shallow arrival age');
     }
     const fresh=v.n-inc[0],fg=v.g-inc[1];
     check(fresh>=fg&&fg>=0,'first meet counts');
     allPairs+=fresh;
     if(good){gg+=fg;gb+=fresh-fg;v.g++;inc[1]++;}
     else{gb+=fg;bb+=fresh-fg;}
     v.n++;inc[0]++;v.edges.set(rec.prev,inc);
     if(rec.ell){RK+=rec.ell/2;UK[j]+=rec.w;if(oracle)v.slab.push([M,rec.w,r[j]]);}
   }
   if(lastGood){lastGood.e++;if(oracle)lastGood.expire.push(M);}
 }
 check(marked===markedHigh+markedDegree-markedBoth&&marked+keptRoots===N&&marked<=relaxedRoots,'marked roots union');
 check(R-RK<=B*marked,'linear cost deletion');
 const cap=(L/2)*Array.from({length:k+1},(_,i)=>(T*L/2)**i).reduce((s,x)=>s+x,0);
 let E=0,EK=0,maxGood=0;
 for(let j=lo;j<=hi;j++){
   maxGood=Math.max(maxGood,goodH[j]);check(goodH[j]<=cap,'bounded reverse branching shallow mass');
   E+=r[j]*U[j]**2;EK+=r[j]*UK[j]**2;
 }
 const ageBound=rough?2*Z*(k+1)*L:(3*k+2)*Q+3*(k+1)*L;
 if(ageBound<=a)check(shallowCost===0,'no shallow occupation');
 let expiry=0,totalExpiry=0;
 const pairs=oracle?new Set():null,pairKey=(u,v)=>(Math.min(u,v)-X)*X+Math.max(u,v)-X;
 for(const v of V.values()){
   check(v.e<=v.g&&v.g<=maxGood,'expiry subset');
   expiry+=v.e*(v.g-v.e)+v.e*(v.e-1)/2;totalExpiry+=v.e;
   if(oracle&&v.e){
     const ex=new Set(v.expire);
     for(const u of ex)for(const w of v.good)if(u!==w&&(!ex.has(w)||u<w)){
       const id=pairKey(u,w);check(!pairs.has(id),'unique expiry pair');pairs.add(id);
     }
   }
 }
 check(gg===expiry&&allPairs===gg+gb+bb&&totalExpiry===keptRoots,'expiry identity');
 check(gg<=keptRoots*Math.max(0,maxGood-1)&&gg<=keptRoots*Math.max(0,cap-1),'pair cap');
 let goodSuffix=null,shared=null;
 if(oracle){check(pairs.size===gg,'pair set count');goodSuffix=0;shared=0;
   for(const v of V.values())for(let i=0;i<v.slab.length;i++)for(let j=0;j<i;j++){
     const [u,w,r]=v.slab[i],[u2,w2]=v.slab[j],en=2*r*w*w2;shared+=en;if(pairs.has(pairKey(u,u2)))goodSuffix+=en;
   }
   check(goodSuffix<=2*B*gg+1e-7*Math.max(1,E),'whole suffix cap');
 }
 return {X,B,Q,Z,L,y,T,g,k,mode,nA,nHigh,nExc,tail,maxDegree,layers,relaxedN,relaxedRoots,marked,markedHigh,markedDegree,markedBoth,keptRoots,keptSlabRoots,events,literal,finished,keptFinished,actualMaxDepth,shallowWithHigh,shallowCost,maxShallowAge,ageBound,R,RK,E,EK,S0,cap,maxGood,allPairs,gg,gb,bb,expiry,goodSuffix,shared};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536,262144])for(const mode of ['analytic','narrow','degree','roughAnalytic','roughDiagnostic'])console.log(JSON.stringify(audit(X,mode)));
