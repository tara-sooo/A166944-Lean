// Original rough upward-birth key graph and exact source-order cut; prior checks preserved.
// Original terminal pair-level graph, directed gap and weighted core peeling, arithmetic quotas.
// Pair-specific short-reference control on the same natural rough weights; includes fixed-cell check.
// Extended common-cell reference, original unchanged rough masks, terminal level transport.
// Rough outgoing-slot weighted support, delayed class peeling, and true-tick level audit.
function audit(X,stress=false,Wmult=1,coreCap=2,birthCap=32){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,u=Math.log(B),D=Math.max(1,Math.floor(stress?B/4:B/u**2)),rough=Math.max(3,Math.ceil(D/4)),m=stress?12:u**(11/4),eta=stress?1/8:u**(-1/4),L=stress?30:2,y=stress?5:2,factor=stress?4:u**(1/4);
 const ok=(v,s)=>{if(!v)throw Error(s)},close=(x,y)=>Math.abs(x-y)<1e-7*Math.max(1,Math.abs(x),Math.abs(y));
 const sp=new Int32Array(8*X+100);for(let p=2;p<sp.length;p++)if(!sp[p])for(let j=p;j<sp.length;j+=p)if(!sp[j])sp[j]=p;
 function gcd(a,b){while(b){let c=a%b;a=b;b=c}return a}
 function r(C){let p=Math.min(sp[C-1]||Infinity,sp[C+1]||Infinity);return p<=B?p:0}
 function fac(n){let out=[];while(n>1){let p=sp[n];out.push(p);while(n%p===0)n/=p}return out}
 const allSlots=new Map(),roughSlots=new Map(),paths=[];let refR=0,roots=0,selectedGain=0;
 for(let M=X+1;M<2*X;M+=2){
   const s=M+2;ok(s+H+2*B<=Math.floor((7*M-1)/4),"cutoff");roots++;
   let t=s,C=2*M-2,anchor=null,records=[];
   const path={M,s,records,end:0,min:null};
   while(t<s+H){
     let rr=r(C);if(!rr)break;
     let lo=t,p=0;
     while(!p){t++;let k=t%2;p=sp[gcd(t-2*k,C+2*k-1)]||0;if(p>B)p=0}
     ok(t-lo<=2*rr,"wait");
     const key=`${C},${t}`,q=anchor?anchor.q:0,cl=q===0?0:q*factor>=rr?1:2;
     const rec={C,lo,v:t,p,r:rr,cl,path,i:records.length,post:2*t-(C+p-1)};
     records.push(rec);refR+=rr;selectedGain+=p-1;
     let h=allSlots.get(key);if(!h){h={C,v:t,p,r:rr,n:0};allSlots.set(key,h)}h.n++;
     if(rr>=rough&&rr>y){
       let g=roughSlots.get(key);if(!g){g={C,v:t,p,r:rr,entries:[[],[],[]]};roughSlots.set(key,g)}
       g.entries[cl].push(rec);
     }
     C+=p-1;if(p>y)anchor={q:p,J:C,t};ok(C<=2*t,"deficit");
   }
   path.end=t;path.endC=C;paths.push(path);const mins=new Int32Array(records.length);let d=2*t-C;
   for(let j=records.length-1;j>=0;j--){d=Math.min(d,records[j].post);mins[j]=d}path.min=mins;
 }

 const W=Math.max(1,Math.floor(Wmult*B)),width=10*B,shift=5*B,cell=(M,j)=>Math.floor((M-X+j*shift)/width);
 const cellData=[new Map(),new Map()],stepCache=new Map();let stepOracle=0,edgeCount=0;
 function step(t,C){
   const key=t+','+C;if(stepCache.has(key))return stepCache.get(key);
   const rr=r(C);if(!rr)return null;let v=Infinity,p=Infinity;
   for(let k=0;k<2;k++)for(const q of fac(C+2*k-1)){
     if(q>B)continue;const res=k?q+2:0,tt=res+2*q*(Math.floor((t-res)/(2*q))+1);
     if(tt<v||(tt===v&&q<p)){v=tt;p=q}
   }
   ok(v>t&&v-t<=2*rr&&p<=B,"event jump");
   if(stepOracle<256){let b=t,pp=0;while(!pp){b++;let k=b%2;pp=sp[gcd(b-2*k,C+2*k-1)]||0;if(pp>B)pp=0}ok(b===v&&pp===p,"literal future event");stepOracle++}
   const ans={lo:t,C,v,p,r:rr,post:2*v-(C+p-1),d0:2*t-C};stepCache.set(key,ans);return ans;
 }
 function addEdge(g,e){
   const key=e.C+','+e.lo+','+e.v;let z=g.edges.get(key);
   if(!z){z={e,n:0};g.edges.set(key,z);edgeCount++}z.n++;
 }
 for(let j=0;j<2;j++){
   for(const P of paths){
     let k=cell(P.M,j),g=cellData[j].get(k);if(!g){g={roots:[],T:0,edges:new Map(),future:new Map(),endpoints:new Map()};cellData[j].set(k,g)}
     g.roots.push(P);g.T=Math.max(g.T,P.s+H+2*B+W);
   }
   for(const g of cellData[j].values()){
     const start=g.T-W;
     for(const P of g.roots){
       ok(g.T<=Math.floor((7*P.M-1)/4)&&P.end<=start,"extension inside common cutoff");
       for(const e of P.records)addEdge(g,{C:e.C,lo:e.lo,v:e.v,p:e.p,r:e.r,post:e.post,d0:2*e.lo-e.C});
       let t=P.end,C=P.endC,rec=[],weights=[],clock=0,rsum=0;
       while(t<g.T&&r(C)){
         const e=step(t,C),b=Math.min(e.v,g.T),len=Math.max(0,b-Math.max(t,start));
         if(len){weights.push([e.C,len/(2*e.r)]);clock+=len;rsum+=e.r}
         if(e.v>g.T){t=g.T;break}
         rec.push(e);addEdge(g,e);C+=e.p-1;t=e.v;ok(C<=2*t,"future invariant");
       }
       const twin=!r(C);if(twin)ok(sp[C-1]===C-1&&sp[C+1]===C+1,"actual twin terminal");
       const key=t+','+C;g.endpoints.set(key,(g.endpoints.get(key)||0)+1);
       for(const [C,w] of weights)g.future.set(C,(g.future.get(C)||0)+w);
       let min=2*P.end-P.endC;for(const e of rec)min=Math.min(min,e.post);
       P.ext??=[];P.ext[j]={g,t,C,twin,key,rec,min,weights,clock,rsum};
       if(!twin)ok(t===g.T&&clock===W&&rsum<=3*W+50*B,"future full slab clock/gain bound");
     }
   }
 }
 
// Local continuation after the earlier actual recorded stop, not the fixed-cell slab.
// All queried earlier stops have both original roots still within their K gate.
const localCache=new Map();
function local(P){
 const key=P.end+','+P.endC;if(localCache.has(key))return localCache.get(key);
 let t=P.end,C=P.endC,min=2*t-C,rsum=0,clock=0,energy=0,rec=[];
 const end=t+W;
 while(t<end&&r(C)){
  let e=step(t,C),len=Math.min(end,e.v)-t;
  rsum+=e.r;clock+=len;energy+=len*len/(2*e.r);
  if(e.v>end){t=end;break}
  rec.push(e);t=e.v;C+=e.p-1;min=Math.min(min,e.post);
 }
 const twin=!r(C);
 if(!twin)ok(t===end&&clock===W&&energy+1e-8>=W*W/(2*(3*W+22*B)),"local future pair lower bound");
 const ans={t,C,min,clock,rsum,energy,twin,rec};localCache.set(key,ans);return ans;
}
let futureE=0,futureDown=0,endpointMax=0,twinRoots=[0,0];
 for(let j=0;j<2;j++)for(const g of cellData[j].values()){
   for(const [C,U] of g.future)futureE+=r(C)*U*U;
   for(const {e,n} of g.edges.values())futureDown+=Math.max(0,e.d0-e.post)*n*(n-1)/4;
   for(const n of g.endpoints.values())endpointMax=Math.max(endpointMax,n);
   for(const P of g.roots)if(P.ext[j].twin)twinRoots[j]++;
 }
 let arithmetic=0,weighted=0,horizons=0,weightedExact=0,rawDown=0;
 for(let C=2*X-2;C<=4*X+2*H+6;C+=2){
   let rr=r(C);if(rr<rough||rr<=y)continue;horizons++;
   for(let k=0;k<2;k++)for(const p of fac(C+2*k-1)){
     if(p>B)continue;
     const residue=k?p+2:0,lo=Math.ceil(C/2),hi=Math.floor(C/2+3+H+2*B);
     let n=Math.max(0,Math.floor((hi-residue)/(2*p))-Math.ceil((lo-residue)/(2*p))+1);
     arithmetic+=n;weighted+=rr*n;
   }
 }
 for(const g of roughSlots.values())weightedExact+=g.r;
 ok(roughSlots.size<=arithmetic&&weightedExact<=weighted,"weighted support");
 for(const h of allSlots.values())rawDown+=(h.p-3)*h.n*(h.n-1)/2;

 const Lmax=12*B+6,Y=Math.max(5,Math.ceil(B**.125)),Ptop=Math.ceil(B/u**2),support=[0,0,0];
 function band(C,p){return r(C)>=Y?0:p>=Ptop?1:2}
 for(let C=2*X-2;C<7*X;C+=2){
   if(!r(C))continue;
   for(let side=0;side<2;side++)for(const p of fac(C+2*side-1)){
     if(p<5||p>B)continue;
     const J=C+p-1;
     for(let d=6*side;d<Lmax;d+=2*p){
       const t=(J+d)/2;
       if(t%2!==side||!Number.isInteger(t)||(t-2*side)%p!==0)continue;
       support[band(C,p)]+=Math.min(Lmax-d,p-3);
     }
   }
 }
 const out=[];
 for(let mode=0;mode<2;mode++){
   const intervals=[];
   const pairRemain=new Map(),localPairs=new Map();let localMatched=0,localTwin=0,localRemain=0,localLow=0,localOracle=0,extMatched=0,extTwin=0,extRemain=0,extLow=0,extThin=0,extHeavy=0,extPairs=0,extOracle=0,raw=0,ratioLoss=0,delayLoss=0,thinLoss=0,R=0,E=0,diag=0,off=0,immediate=0,later=0,terminal=0,smallSame=0,smallMatched=0,smallTerminal=0,pairs=0,oracle=0,thinClasses=0,keptClasses=0,largeEnd=0,cross=0,slotHorizon=new Map();
   for(const h of roughSlots.values()){
     const {C,v,p,r:rr}=h,ell=Math.max(1,Math.floor(eta*rr)),entries=[];
     let nraw=0;
     for(const cls of h.entries){
       const sorted=cls.slice().sort((a,b)=>a.lo-b.lo);
       // threshold time: first tick at which >m actual original arrivals are present
       const T=sorted.length>m?sorted[Math.floor(m)].lo:Infinity;
       if(sorted.length&&T===Infinity)thinClasses++;
       let used=false;
       for(const rec of sorted){
         let lo=mode===0?Math.max(rec.lo,rec.path.s+a):rec.lo,hi=mode===0?Math.min(v,rec.path.s+H):v;
         if(mode===0&&p<=Math.ceil(B**.25)||mode===1&&2*(v-rec.lo)<=p-1||lo>=hi)continue;
         raw+=hi-lo;nraw+=hi-lo;
         if(p>factor*rr){ratioLoss+=hi-lo;continue}
         const b=Math.min(hi,Math.max(lo,rec.lo+ell+1));delayLoss+=b-lo;lo=b;
         const c=Math.min(hi,Math.max(lo,T+ell));thinLoss+=c-lo;lo=c;
         if(lo>=hi)continue;
         ok(lo-ell>rec.lo&&lo-ell>=T,"delayed gate");
         const w=(hi-lo)/(2*rr);entries.push({rec,lo,hi,w});used=true;
       }
       if(used)keptClasses++;
     }
     let U=entries.reduce((s,e)=>s+e.w,0);R+=rr*U;E+=rr*U*U;
     slotHorizon.set(C,(slotHorizon.get(C)||0)+U);
     let ls=0,li=0,ll=0,lt=0;
     for(let i=0;i<entries.length;i++){
       const x=entries[i];diag+=rr*x.w*x.w;
       for(let j=i+1;j<entries.length;j++){
         const z=entries[j];pairs++;
         const f=x.rec.lo>=z.rec.lo?x:z,b=f===x?z:x;
         const P=f.rec.path,Q=b.rec.path,earlier=P.end<=Q.end?f.rec:b.rec;
         const min=earlier.path.min[earlier.i],post=f.rec.post;
         ok(P.end>=v&&Q.end>=v&&min<=post,"actual common suffix minimum");
         // count two adjacent upward levels per shifted focal tick, split by future min and first post-deficit.
         // levels are 2*(lo-ell)-C-1 through 2*(hi-1-ell)-C, inclusive.
         const low=2*(f.lo-ell)-C-1,high=2*(f.hi-1-ell)-C;
         ok(low>=1&&high<=2*(v-1)-C&&high-low+1===2*(f.hi-f.lo),"true stationary levels");
         const above=d=>Math.max(0,high-Math.max(d,low-1));
         const e=(f.hi-f.lo)*b.w,imm=above(post)*b.w/2,mat=above(min)*b.w/2;
         ok(imm<=mat+1e-8&&mat<=e+1e-8,"matched level split");
         ls+=e;li+=imm;ll+=mat-imm;lt+=e-mat;
         if(e>mat+1e-12){
           const part=cell(P.M,0)===cell(Q.M,0)?0:1;
           ok(cell(P.M,part)===cell(Q.M,part),"two-cell cover");
           const F=earlier.path.ext[part],other=(earlier.path===P?Q:P).ext[part];
           ok(F.g===other.g&&F.t===other.t&&F.C===other.C&&F.twin===other.twin,"persistent shared extension");
           const extMin=Math.min(min,F.min),extra=(above(extMin)-above(min))*b.w/2;
           const remain=e-mat-extra;ok(extra>=-1e-8&&remain>=-1e-8,"monotone terminal ledger");extMatched+=extra;
           if(F.twin)extTwin+=remain;
           else{
             extRemain+=remain;
             const lowPay=Math.max(0,Math.min(high,extMin,Math.floor(u**2.5))-low+1)*b.w/2;
             ok(lowPay<=remain+1e-8,"low-level cap");extLow+=lowPay;
             if(F.g.endpoints.get(F.key)<=m)extThin+=remain-lowPay;else extHeavy+=remain-lowPay;
             ok(F.clock===W&&other.clock===W&&close(F.rsum,other.rsum),"shared future slab");
             const pk=Math.min(P.M,Q.M)+','+Math.max(P.M,Q.M);
             pairRemain.set(pk,(pairRemain.get(pk)||0)+remain);
             if(extOracle<128){
               ok(F.weights.length===other.weights.length,"future occupation length");
               let pe=0;for(let k=0;k<F.weights.length;k++){const [cc,ww]=F.weights[k],[dd,zz]=other.weights[k];ok(cc===dd&&close(ww,zz),"future occupation oracle");pe+=2*r(cc)*ww*zz}
               ok(pe+1e-8>=W*W/(2*(3*W+50*B)),"pair transport lower bound");extOracle++;
             }
           }
           extPairs++;
           ok(earlier.path.end+W<=Math.min(Math.floor((7*P.M-1)/4),Math.floor((7*Q.M-1)/4)),"local original cutoff");
           const Lc=local(earlier.path),lm=Math.min(min,Lc.min),lmPay=(above(lm)-above(min))*b.w/2,lr=e-mat-lmPay;
           ok(lr>=-1e-8&&lmPay>=-1e-8,"local terminal monotonicity");
           
           // Original terminal charge intervals, classified by first future record low.
           let cur=Math.min(high,min),prev=min;
           const i=earlier.path.M,j=earlier.path===P?Q.M:P.M,w=b.w/2,laterEnd=Math.max(P.end,Q.end),birth=C+','+v;
           ok((P.M<Q.M?P.end<=Q.end:Q.end<=P.end),"source-monotone original stop");
           ok(w<=.5+1e-9,"charge cap");
           for(const z of Lc.rec){
             if(z.post>=prev)continue;
             const lower=Math.max(low,z.post+1),upper=Math.min(cur,prev);
             if(lower<=upper){
               ok(z.d0>=upper&&z.post<lower&&z.v>earlier.path.end&&z.p>=5,"net descent");
               ok(z.post>=upper-z.p+3&&z.post<=lower-1,"arithmetic window");
               ok((z.post-6*(z.v%2))%(2*z.p)===0,"post phase");
               const cut=z.lo-H-2,isGap=z.v<=laterEnd;
               ok(isGap?(i<=cut&&j>cut):(i<=cut&&j<=cut),"exact source cut at predecessor");
               intervals.push({lo:lower,hi:upper,i,j,w,type:isGap?0:1,band:band(z.C,z.p),key:z.v+','+(z.C+z.p-1)+','+z.p,birth,cut,arrivalMax:Math.max(f.rec.lo,b.rec.lo),C,v});
             }
             prev=z.post;cur=Math.min(cur,z.post);if(cur<low)break;
           }
           if(cur>=low)intervals.push({lo:low,hi:cur,i,j,w,type:Lc.twin?3:2,band:-1,key:"",birth,arrivalMax:Math.max(f.rec.lo,b.rec.lo),C,v});
           localMatched+=lmPay;
           if(Lc.twin)localTwin+=lr;
           else {
             localRemain+=lr;
             const lp=Math.max(0,Math.min(high,lm,Math.floor(u**2.5))-low+1)*b.w/2;
             localLow+=lp;
             const pk=Math.min(P.M,Q.M)+','+Math.max(P.M,Q.M);
             let acc=localPairs.get(pk);if(!acc){acc={charge:0,energy:Lc.energy};localPairs.set(pk,acc)}
             ok(close(acc.energy,Lc.energy),"fixed local pair continuation");acc.charge+=lr;
           }
           if(localOracle<128&&Lc.rec.length){
             let n=min;for(const z of Lc.rec)n=Math.min(n,z.post);
             let count=0;for(let k=low;k<=Math.min(high,min);k++)if(k>n)count++;
             ok(close(lmPay,count*b.w/2),"literal local level scan");localOracle++;
           }
         }
         if(f.rec.cl===2&&b.rec.cl===2){smallSame+=e;smallMatched+=mat;smallTerminal+=e-mat}
         if(oracle<128){
           // direct common recorded suffix compare and literal two-level crossing count
           const A=P.records.slice(f.rec.i),Z=Q.records.slice(b.rec.i),len=Math.min(A.length,Z.length);
           let mn=Infinity;for(let k=0;k<len;k++){ok(A[k].C===Z[k].C&&A[k].v===Z[k].v&&A[k].p===Z[k].p,"actual shared future");mn=Math.min(mn,A[k].post)}
           ok(mn===min,"minimum oracle");
           let im=0,ma=0;for(let d=low;d<=high;d++){if(post<d)im++;if(A.slice(0,len).some(e=>e.post<d))ma++}
           ok(im===above(post)&&ma===above(min),"level oracle");oracle++;
         }
       }
     }
     ok(close(rr*U*U-entries.reduce((s,e)=>s+rr*e.w*e.w,0),ls)&&close(ls,li+ll+lt),"pair split");off+=ls;immediate+=li;later+=ll;terminal+=lt;
   }
   for(const [C,U] of slotHorizon)cross+=r(C)*U*U;
   ok(close(raw,ratioLoss+delayLoss+thinLoss+2*R),"linear masks");
   ok(thinLoss<=6*m*weightedExact+1e-6,"three class weighted thin budget");
   ok(delayLoss<=2*(eta+1/rough)*refR+1e-6,"delay budget");
   ok(ratioLoss<=2*selectedGain/(factor*(1-1/3))+1e-6,"ratio budget");
   ok(close(E,diag+off)&&close(off,immediate+later+terminal),"global energy ledger");
   ok(immediate+later<=rawDown/2+1e-6,"matched downward injection");
   ok(close(terminal,extMatched+extTwin+extRemain)&&close(extRemain,extLow+extThin+extHeavy),"extension split");
   ok(extMatched<=futureDown+1e-6,"extended net descent bound");
   for(const v of pairRemain.values())ok(v<=6*B+3+1e-6,"terminal pair budget");
   ok(extRemain<= (6*B+3)*2*(3*W+50*B)/(W*W)*futureE+1e-6,"future energy transport");
   ok(extThin<=2*roots*m*(6*B+3)+1e-6,"thin endpoint pair bound");
   ok(close(terminal,localMatched+localTwin+localRemain),"local terminal split");
   let localFuturePairE=0;for(const v of localPairs.values()){
     ok(v.charge<=6*B+3+1e-6,"local pair charge cap");localFuturePairE+=v.energy;
   }
   ok(localRemain<=(6*B+3)*2*(3*W+22*B)/(W*W)*localFuturePairE+1e-6,"local transport");
   
   const starts=Array.from({length:Lmax+2},()=>[]),ends=Array.from({length:Lmax+2},()=>[]);
   for(let i=0;i<intervals.length;i++){const e=intervals[i];ok(e.lo>=1&&e.hi<=Lmax&&e.lo<=e.hi,"interval bounds");starts[e.lo].push(i);ends[e.hi+1].push(i)}
   const active=new Set(),tot=[0,0,0,0],peeled=[0,0,0,0],core=[0,0,0,0],coreGroups=[0,0,0],arithPaid=[0,0,0],arithRemain=[0,0,0],realKeys=[0,0,0],maxCoreDegree=[0,0,0];
   let gapSources=0,lateVertices=0,survVertices=0,levelPairs=0,oracleLevels=0;
   const birthRaw=[0,0,0],birthPaid=[0,0,0],birthCore=[0,0,0],birthRemainder=[0,0,0],birthCapPaid=[0,0,0],birthKeyCount=[0,0,0],birthCoreCount=[0,0,0],bothSideMin=[Infinity,Infinity],maxBirthMass=[0,0,0],memberships=[0,0,0];
   let allBirthKeys=0,matchedBirthKeys=0,splitBirthKeys=0,maxDestinationFanIn=0,maxGapBirthSides=0;
   const originalClock=paths.reduce((s,p)=>s+p.end-p.s,0);
   const birthLimit=stress?birthCap:u**(23/4);
   const caps=stress?[4,3,2]:[u**4.75,u**3.75,u**2.75],threshold=stress?coreCap:u**2.75;
   function peel(es,type){
     const degree=new Map(),inc=new Map(),alive=new Set(es),queue=[];
     for(const e of es)for(const v of [e.i,e.j]){
       degree.set(v,(degree.get(v)||0)+e.w);
       if(!inc.has(v))inc.set(v,[]);inc.get(v).push(e);
     }
     for(const [v,d] of degree)if(d<=threshold+1e-10)queue.push(v);
     let removed=0;
     for(let q=0;q<queue.length;q++){
       const v=queue[q];if((degree.get(v)||0)>threshold+1e-10)continue;
       for(const e of inc.get(v)||[]){
         if(!alive.delete(e))continue;removed+=e.w;
         for(const z of [e.i,e.j]){
           let before=degree.get(z),after=before-e.w;degree.set(z,after);
           if(before>threshold+1e-10&&after<=threshold+1e-10)queue.push(z)
         }
       }
     }
     for(const e of alive)for(const v of [e.i,e.j]){
       ok(degree.get(v)>threshold-1e-9,"weighted core");maxCoreDegree[type]=Math.max(maxCoreDegree[type],degree.get(v));
     }
     ok(removed<=threshold*inc.size+1e-6,"level core budget");
     return {removed,kept:[...alive],vertices:inc.size};
   }
   for(let l=1;l<=Lmax;l++){
     for(const id of ends[l])active.delete(id);for(const id of starts[l])active.add(id);
     if(!active.size)continue;
     const seen=new Set(),gap=[],late=[],surv=[],lateKey=new Map(),gapKey=new Map(),actualKeys=new Map(),birthGroups=new Map(),birthHit=new Map(),birthTypes=new Map(),destinationBirths=new Map();
     for(const id of active){
       const e=intervals[id],pk=Math.min(e.i,e.j)+','+Math.max(e.i,e.j);
       ok(!seen.has(pk),"unique terminal level per unordered pair");seen.add(pk);tot[e.type]+=e.w;
       const z=Math.ceil((e.C+l)/2);
       ok(e.arrivalMax<z&&z<e.v,"actual shared stationary birth tick");
       let types=birthTypes.get(e.birth);if(!types){types=new Set();birthTypes.set(e.birth,types)}types.add(e.type);
       if(e.type<2){
         const h=birthHit.get(e.birth);ok(!h||(h.key===e.key&&h.cut===e.cut),"unique future first hit and cut from birth");
         birthHit.set(e.birth,{key:e.key,cut:e.cut});
         let a=destinationBirths.get(e.key);if(!a){a=new Set();destinationBirths.set(e.key,a)}a.add(e.birth)
       }
       if(e.type<3){
         const k=e.birth+'|'+e.type;if(!birthGroups.has(k))birthGroups.set(k,[]);birthGroups.get(k).push(e);
       }
       if(e.type===0||e.type===1){
         actualKeys.set(e.key,e.band);
         if(e.type===0){
           ok(!gapKey.has(e.i)||gapKey.get(e.i)===e.key,"unique gap key");gapKey.set(e.i,e.key);gap.push(e)
         }else{
           for(const v of [e.i,e.j]){ok(!lateKey.has(v)||lateKey.get(v)===e.key,"unique late key");lateKey.set(v,e.key)}
           late.push(e);
         }
       }else if(e.type===2)surv.push(e);
     }
     levelPairs+=active.size;for(const b of actualKeys.values())realKeys[b]++;
     allBirthKeys+=birthTypes.size;matchedBirthKeys+=birthHit.size;
     for(const x of birthTypes.values())if(x.size>1)splitBirthKeys++;
     for(const x of destinationBirths.values())maxDestinationFanIn=Math.max(maxDestinationFanIn,x.size);
     // Independent birth-key peeling and cap, not cumulatively added to previous ledger.
     const birthAfterPeel=new Map();
     for(const es of birthGroups.values()){
       const ty=es[0].type;const val=es.reduce((s,e)=>s+e.w,0);birthRaw[ty]+=val;birthKeyCount[ty]++;
       const pp=peel(es,ty);memberships[ty]+=pp.vertices;birthPaid[ty]+=pp.removed;
       const rest=pp.kept.reduce((s,e)=>s+e.w,0);birthCore[ty]+=rest;maxBirthMass[ty]=Math.max(maxBirthMass[ty],rest);
       if(rest>1e-12){
         birthCoreCount[ty]++;ok(rest>threshold*threshold-1e-7,"core minimum mass");
         if(ty===0){
           const A=new Set(),B2=new Set();for(const e of pp.kept){ok(e.i<=e.cut&&e.j>e.cut,"core source cut");A.add(e.i);B2.add(e.j)}
           ok(A.size>2*threshold&&B2.size>2*threshold,"bilateral partner core");
           bothSideMin[0]=Math.min(bothSideMin[0],A.size);bothSideMin[1]=Math.min(bothSideMin[1],B2.size);maxGapBirthSides=Math.max(maxGapBirthSides,A.size,B2.size);
         }
         const k=es[0].birth;
         if(!birthAfterPeel.has(k))birthAfterPeel.set(k,[]);
         birthAfterPeel.get(k).push({ty,rest});
       }
     }
     for(const gs of birthAfterPeel.values()){
       const total=gs.reduce((s,e)=>s+e.rest,0),paid=Math.min(total,birthLimit);
       for(const e of gs){const share=paid*e.rest/total;birthCapPaid[e.ty]+=share;birthRemainder[e.ty]+=e.rest-share}
     }
     const gd=new Map();for(const e of gap)gd.set(e.i,(gd.get(e.i)||0)+e.w);
     gapSources+=gd.size;let paid=0,remain=[];
     for(const e of gap){if(gd.get(e.i)<=threshold+1e-10)paid+=e.w;else remain.push(e)}
     ok(paid<=threshold*gd.size+1e-6,"directed cap");peeled[0]+=paid;core[0]+=remain.reduce((s,e)=>s+e.w,0);
     const pl=peel(late,1),ps=peel(surv,2);lateVertices+=pl.vertices;survVertices+=ps.vertices;
     peeled[1]+=pl.removed;peeled[2]+=ps.removed;core[1]+=pl.kept.reduce((s,e)=>s+e.w,0);core[2]+=ps.kept.reduce((s,e)=>s+e.w,0);
     const byKey=new Map();
     for(const e of [...remain,...pl.kept]){
       if(!byKey.has(e.key))byKey.set(e.key,{b:e.band,w:0});byKey.get(e.key).w+=e.w
     }
     for(const z of byKey.values()){coreGroups[z.b]++;const p=Math.min(z.w,caps[z.b]);arithPaid[z.b]+=p;arithRemain[z.b]+=z.w-p}
     oracleLevels++;
   }
   ok(close(tot[0]+tot[1],localMatched)&&close(tot[2],localRemain)&&close(tot[3],localTwin),"sweep partition");
   for(let i=0;i<3;i++){ok(close(tot[i],peeled[i]+core[i]),"peel ledger");ok(realKeys[i]<=support[i]&&arithPaid[i]<=caps[i]*support[i]+1e-6,"arithmetic support")}
   ok(close(core[0]+core[1],arithPaid.reduce((a,b)=>a+b,0)+arithRemain.reduce((a,b)=>a+b,0)),"arithmetic residual");
   ok(peeled[0]+peeled[1]+peeled[2]<=3*threshold*roots*Lmax+1e-6,"global core budget");
   for(let i=0;i<3;i++){
     ok(close(birthRaw[i],tot[i])&&close(birthRaw[i],birthPaid[i]+birthCapPaid[i]+birthRemainder[i]),"birth exact ledger");
     ok(memberships[i]<=2*originalClock,"original tag-level incidence");
   }
   ok(allBirthKeys<=4*weightedExact&&birthCapPaid.reduce((a,b)=>a+b,0)<=birthLimit*allBirthKeys+1e-6,"birth arithmetic cap");
   ok(birthPaid.reduce((a,b)=>a+b,0)<=6*threshold*originalClock+1e-6,"birth core absolute bound");
   out.push({birthLedger:{birthLimit,threshold,birthRaw,birthPaid,birthCore,birthCapPaid,birthRemainder,birthKeyCount,birthCoreCount,memberships,originalClock,allBirthKeys,matchedBirthKeys,splitBirthKeys,maxDestinationFanIn,maxBirthMass,bothSideMin:bothSideMin.map(x=>Number.isFinite(x)?x:null),maxGapBirthSides},levelCore:{threshold,caps,intervals:intervals.length,levelPairs,oracleLevels,tot,peeled,core,arithPaid,arithRemain,realKeys,support,coreGroups,maxCoreDegree,gapSources,lateVertices,survVertices},localMatched,localTwin,localRemain,localLow,localSurvivorPairs:localPairs.size,localFuturePairE,localOracle,extMatched,extTwin,extRemain,extLow,extThin,extHeavy,extPairs,extOracle,survivorPairs:pairRemain.size,mode:mode?"full-positive":"late-high",raw,ratioLoss,delayLoss,thinLoss,R,E,diag,off,immediate,later,terminal,smallSame,smallMatched,smallTerminal,cross:cross-E,pairs,oracle,thinClasses,keptClasses});
 }
 return {X,B,D,rough,coreCap,birthCap,Y,Ptop,m,eta,L,y,factor,stress,W,Wmult,futureE,futureDown,stepOracle,edgeCount,endpointMax,twinRoots,roots,roughSlots:roughSlots.size,horizons,arithmetic,weighted,weightedExact,refR,selectedGain,rawDown,out};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[4096,16384]))for(const [W,cap,bc] of [[1/8,2,32],[1,8,128],...(X===16384?[[1/8,.25,4]]:[])])console.log(JSON.stringify(audit(X,true,W,cap,bc)));
