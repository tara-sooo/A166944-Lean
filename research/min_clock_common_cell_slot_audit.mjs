// All-odd true-tick common-cell and clock-slot audit; no dependencies.
function audit(X, stress=false) {
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,u=Math.log(B),D=Math.max(1,Math.floor(stress?B/4:B/u**2)),eps=stress?.12:u**(-.25),zeta=stress?.22:u**(-.125),width=10*B,shift=5*B,stride=16*X+100;
 const assert=(v,m)=>{if(!v)throw Error(m)},close=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b));
 const spf=new Int32Array(8*X+100);
 for(let p=2;p<spf.length;p++)if(!spf[p])for(let j=p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function gcd(a,b){while(b){let t=a%b;a=b;b=t}return a}
 function factors(n){const p=[];while(n>1){let q=spf[n];p.push(q);while(n%q===0)n/=q}return p}
 function r(C){let v=Math.min(spf[C-1]||Infinity,spf[C+1]||Infinity);return v<=B?v:0}
 let L=2,y=2;for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>D/12)break;L*=p;y=p}
 const scaleGate=L<=D/12, roots=[];for(let M=X+1;M<2*X;M+=2)roots.push({M,s:M+2,K:Math.floor((7*M-1)/4),refs:[]});
 function cell(M,j){return Math.floor((M-X+j*shift)/width)}
 const A=[new Map(),new Map()];let instability=0,growth=0,refTicks=0,initialHeavy=0,refBudget=[0,0],checks=0;
 for(let j=0;j<2;j++){
   const cells=new Map();
   for(const root of roots){let k=cell(root.M,j);if(!cells.has(k))cells.set(k,[]);cells.get(k).push(root)}
   for(const pop of cells.values()){
     const end=pop[pop.length-1].s+H+2*B;
     assert(end<=pop[0].K,"common original cutoff");
     const mass=new Map();
     for(const root of pop){
       const {s,M}=root;let C=2*M-2,t=s,trace=[],rec=[],latest=[],last=-1;
       while(t<end){
         const q=r(C);if(!q)break;let lo=t,p=0;
         while(t<end){
           trace.push(C);latest.push(last);
           const v=t+1,par=v%2,g=gcd(v-2*par,C+2*par-1);
           p=spf[g]||0;if(p>B)p=0;t=v;
           if(p)break;
         }
         assert(t-lo<=2*q,"wait");
         rec.push({C,r:q,lo,hi:t,p});
         A[j].set(C,1+(A[j].get(C)||0));refBudget[j]+=q;
         if(p){C+=p-1;if(p>y)last=t;assert(C<=2*t,"deficit")}
       }
       for(let i=0;i<trace.length;i++){let key=(s+i)*stride+trace[i];mass.set(key,1+(mass.get(key)||0))}
       root.refs[j]={trace,rec,latest};
     }
     for(const root of pop){
       const f=root.refs[j],n=new Int32Array(f.trace.length),stable=new Uint8Array(f.trace.length);
       for(let i=0;i<n.length;i++){
         n[i]=mass.get((root.s+i)*stride+f.trace[i]);assert(n[i]>=1&&(!i||n[i]>=n[i-1]),"cell persistence");
         const prior=i>=D?n[i-D]:1;stable[i]=Math.log(n[i]/prior)<=eps+1e-12?1:0;
       }
       const bad=n.length-stable.reduce((a,b)=>a+b,0),g=n.length?Math.log(n[n.length-1]):0;
       assert(bad<=D*g/eps+1e-6,"Fubini");instability+=bad;growth+=g;refTicks+=n.length;initialHeavy+=n[0]>1?1:0;
       f.n=n;f.stable=stable;
     }
   }
 }
 const Amax=new Map(A[0]);for(const [C,v] of A[1])Amax.set(C,Math.max(v,Amax.get(C)||0));
 let RA=0;for(const [C,v] of Amax)RA+=r(C)*v;
 const groups=[new Map(),new Map()];
 for(const root of roots){
   const [f,g]=root.refs;
   const len=Math.min(f.trace.length,g.trace.length);
   for(let i=0;i<len;i++)assert(f.trace[i]===g.trace[i],"same original trajectory");
   for(const rec of f.rec){
     if(rec.lo>=root.s+H)break;
     assert(rec.p>0&&rec.hi<=root.s+H+2*B,"completed original wait");
     for(let mode=0;mode<2;mode++){
       if(mode===0&&rec.p<=Math.ceil(B**.25))continue;
       if(mode===1&&2*(rec.hi-rec.lo)<=rec.p-1)continue;
       const lo=mode===0?Math.max(rec.lo,root.s+a):rec.lo,hi=mode===0?Math.min(rec.hi,root.s+H):rec.hi;
       if(lo>=hi)continue;
       const map=groups[mode];let h=map.get(rec.C);if(!h){h={r:rec.r,entries:[],raw:0};map.set(rec.C,h)}
       h.raw+=hi-lo;const ticks=[];
       for(let t=lo;t<hi;t++){
         const i=t-root.s;assert(i<len,"common ref contains mask");
         if(f.stable[i]&&g.stable[i]&&(!stress||(t+root.M)%7))ticks.push(t);
       }
       if(ticks.length)h.entries.push({root,lo:rec.lo,hi:rec.hi,p:rec.p,ticks,w:ticks.length/(2*rec.r)});
     }
   }
 }
 const results=[];
 const beta=4*(1-Math.exp(-eps))/zeta,m=u**2.5,himb=u**.25;
 for(let mode=0;mode<2;mode++){
   let raw=0,preGate=0,gate=0,kept=0,E=0,diag=0,recent=0,old=0,cross=0,oldStationary=0,oldRough=0,oldAnchor=0,oldThinAnchor=0,oldOther=0,thin=0,imb=0,thick=0,reoriented=0,pairs=0,oracle=0,maxSlots=0,slotBoundMax=0,commonCell1=0,R=0;
   for(const [C,group] of groups[mode]){
     const {r:q,entries}=group;raw+=group.raw;let U=entries.reduce((s,e)=>s+e.w,0);preGate+=2*q*U;
     if(U<zeta*Amax.get(C)){gate+=2*q*U;continue}
     if(!entries.length)continue;
     const slots=new Map();for(const e of entries)slots.set(e.hi,(slots.get(e.hi)||0)+e.w);
     const K=[...factors(C-1),...factors(C+1)].filter(p=>p<=B).reduce((s,p)=>s+Math.floor((6*B+6)/(2*p))+1,0);
     assert(slots.size<=K&&K>=1,"arithmetic slot support");
     maxSlots=Math.max(maxSlots,slots.size);slotBoundMax=Math.max(slotBoundMax,K);
     let energy=q*U*U;E+=energy;R+=q*U;kept+=2*q*U;
     let d=0,rec=0,o=0,c=0,tThin=0,tImb=0,tThick=0;
     for(let i=0;i<entries.length;i++){
       const x=entries[i];d+=q*x.w*x.w;
       for(let j=i+1;j<entries.length;j++){
         const z=entries[j];pairs++;
         assert(Math.abs(x.root.M-z.root.M)<=H+3,"source support");
         const part=cell(x.root.M,0)===cell(z.root.M,0)?0:1;
         assert(cell(x.root.M,part)===cell(z.root.M,part),"two cell cover");commonCell1+=part;
         const val=2*q*x.w*z.w;
         if(x.hi!==z.hi){
           assert(x.hi<=z.lo||z.hi<=x.lo,"distinct clock slots disjoint");
           c+=val;let w1=slots.get(x.hi),w2=slots.get(z.hi);
           if(Math.min(w1,w2)<=m/K)tThin+=val;
           else if(Math.min(w1,w2)<=Math.max(w1,w2)/(K*himb))tImb+=val;
           else tThick+=val;
           continue;
         }
         assert(x.p===z.p&&Math.max(x.lo,z.lo)<x.hi,"same slot");
         let f=x,b=z;if(z.lo>x.lo){f=z;b=x;reoriented+=val}
         const F=f.root.refs[part],G=b.root.refs[part],s=f.root.s,s2=b.root.s;
         const eq=t=>t>=s&&t>=s2&&t-s<F.trace.length&&t-s2<G.trace.length&&F.trace[t-s]===G.trace[t-s2];
         let left=Math.max(s,s2),right=Math.max(f.lo,b.lo);
         assert(eq(right),"true meeting by later arrival");
         while(left<right){let mid=Math.floor((left+right)/2);if(eq(mid))right=mid;else left=mid+1}
         const meet=left;
         if(oracle<128){let t=Math.max(s,s2);while(!eq(t))t++;assert(t===meet,"literal meeting oracle");oracle++}
         for(const t of f.ticks){
           assert(eq(t),"later-arrival expansion");const val=b.w;
           if(t-D<meet){rec+=val;continue}
           o+=val;assert(eq(t-D),"old common tick");
           if(F.trace[t-D-s]===C){oldStationary+=val;assert(2*q>D,"stationary rough")}
           if(q>=D/4){oldRough+=val;continue}
           if(!scaleGate){oldOther+=val;continue}
           const anchor=F.latest[t-s];
           assert(anchor>t-D&&anchor<=t,"shared nonLOW anchor");
           const k=anchor-s,k2=anchor-s2;
           assert(eq(anchor)&&k>0&&k2>=0&&F.trace[k]-F.trace[k-1]+1>y,"actual common anchor");
           oldAnchor+=val;
           if(F.n[k]<=m)oldThinAnchor+=val;
         }
       }
     }
     assert(close(energy,d+rec+o+c)&&close(c,tThin+tImb+tThick),"exact energy partition");
     assert(rec<=beta*energy+1e-6,"relative recent");
     assert(tThin<=2*m*q*U+1e-6,"thin slots");
     assert(tImb<=2*energy/himb+1e-6,"relative imbalanced slots");
     diag+=d;recent+=rec;old+=o;cross+=c;thin+=tThin;imb+=tImb;thick+=tThick;
   }
   assert(close(E,diag+recent+old+cross)&&close(old,oldRough+oldAnchor+oldOther),"global partition");
   assert(oldThinAnchor<=4*m*R+1e-6,"thin shared anchors");
   assert(gate<=2*zeta*RA+1e-6,"linear density");
   results.push({mode:mode===0?"late-high":"full-positive",raw,preGate,gate,kept,E,diag,recent,old,cross,oldStationary,oldRough,oldAnchor,oldThinAnchor,oldOther,thin,imb,thick,reoriented,pairs,oracle,maxSlots,slotBoundMax,commonCell1,R});
 }
 return {X,B,D,y,L,scaleGate,stress,eps,zeta,beta,instability,growth,refTicks,initialHeavy,RA,results};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[4096,16384]))for(const stress of [false,true])console.log(JSON.stringify(audit(X,stress)));
