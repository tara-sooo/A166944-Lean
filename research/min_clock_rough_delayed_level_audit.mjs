// Rough outgoing-slot weighted support, delayed class peeling, and true-tick level audit.
function audit(X,stress=false){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,u=Math.log(B),D=Math.max(1,Math.floor(stress?B/4:B/u**2)),rough=Math.max(3,Math.ceil(D/4)),m=stress?12:u**(11/4),eta=stress?1/8:u**(-1/4),L=stress?30:2,y=stress?5:2,factor=stress?4:u**(1/4);
 const ok=(v,s)=>{if(!v)throw Error(s)},close=(x,y)=>Math.abs(x-y)<1e-7*Math.max(1,Math.abs(x),Math.abs(y));
 const sp=new Int32Array(8*X+100);for(let p=2;p<sp.length;p++)if(!sp[p])for(let j=p;j<sp.length;j+=p)if(!sp[j])sp[j]=p;
 function gcd(a,b){while(b){let c=a%b;a=b;b=c}return a}
 function r(C){let p=Math.min(sp[C-1]||Infinity,sp[C+1]||Infinity);return p<=B?p:0}
 function fac(n){let out=[];while(n>1){let p=sp[n];out.push(p);while(n%p===0)n/=p}return out}
 const allSlots=new Map(),roughSlots=new Map();let refR=0,roots=0,selectedGain=0;
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
   path.end=t;const mins=new Int32Array(records.length);let d=2*t-C;
   for(let j=records.length-1;j>=0;j--){d=Math.min(d,records[j].post);mins[j]=d}path.min=mins;
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
 const out=[];
 for(let mode=0;mode<2;mode++){
   let raw=0,ratioLoss=0,delayLoss=0,thinLoss=0,R=0,E=0,diag=0,off=0,immediate=0,later=0,terminal=0,smallSame=0,smallMatched=0,smallTerminal=0,pairs=0,oracle=0,thinClasses=0,keptClasses=0,largeEnd=0,cross=0,slotHorizon=new Map();
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
   out.push({mode:mode?"full-positive":"late-high",raw,ratioLoss,delayLoss,thinLoss,R,E,diag,off,immediate,later,terminal,smallSame,smallMatched,smallTerminal,cross:cross-E,pairs,oracle,thinClasses,keptClasses});
 }
 return {X,B,D,rough,m,eta,L,y,factor,stress,roots,roughSlots:roughSlots.size,horizons,arithmetic,weighted,weightedExact,refR,selectedGain,rawDown,out};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[4096,16384,65536]))for(const stress of [false,true])console.log(JSON.stringify(audit(X,stress)));
