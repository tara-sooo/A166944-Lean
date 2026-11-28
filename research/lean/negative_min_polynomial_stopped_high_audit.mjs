// Finite proxy audit of the shell, actual stopping, clock-refined separation and flux identities; not an asymptotic proof.
function audit(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 const mod=(x,m)=>((x%m)+m)%m;
 function spf(N){const f=new Int32Array(N+1);for(let p=2;p<=N;p++)if(!f[p]){f[p]=p;if(p*p<=N)for(let n=p*p;n<=N;n+=p)if(!f[n])f[n]=p;}return f;}
 let anchors=0, shellTests=0, pinTests=0, nonexceptional=0, stoppedTicks=0, timeStops=0,gainStops=0, recordTests=0, nearPairs=0, actualMeetings=0, cutIncidences=0, cutKeys=0, sameLabelTests=0, actualCases=[];
 for(const R of [100000,400000,1000000]){
   const f=spf(2*R+1000), fac=n=>{n=Math.abs(n);const a=[];while(n>1){const p=f[n];assert(p>0,"factor range");a.push(p);while(n%p===0)n/=p;}return a;};
   const win=(x,n)=>{const s=n%2===0?1:-1;return fac(x+s).find(p=>p>2&&mod(n,2*p)===(s===1?0:p+2))||0};
   const cohort=[];
   for(let A=6*Math.ceil(R/6);A<=2*R;A+=6){
     const pp=f[A+1],v=(A+1)/pp;
     if(v<=pp||f[v]!==v||pp<R**.28||pp>R**.46)continue;
     const r=f[A-1],u=(A-1)/r;
     if(r<=23||u<=r||u%4!==1)continue;
     if([...fac(A-1).filter(q=>q!==r),...fac(A+1)].some(q=>q<=3*r+7))continue;
     const w0=(3*r-1)/2,nb=3-A/2;
     let w=1;for(;w<=w0;w++)if(win(A,nb+w))break;
     assert(w===w0&&win(A,nb+w)===r,"anchor");
     const x0=A-r+1,n0=nb+w0;
     assert(x0===r*(u-1)+2&&x0/2+n0===r+3,"anchor pins");
     cohort.push({A,r,u,x0,n0});
   }
   anchors+=cohort.length;
   // Deliberately small, independent finite proxy budgets, not the asymptotic M=T L^6.
   for(const [T,D,M] of [[8,4,5],[24,12,6],[48,20,8]]){
     const E=(M+1)*(D+1), good=[], seen=new Map(), cuts=new Map(), labelCuts=new Map();
     let bad=0,localTime=0,localGain=0,localNear=0,localMeet=0,localTicks=0,localRecords=0,localFlux=0;
     for(const a of cohort){
       if(a.r<=D+3)continue;
       let exceptional=false;
       for(let g=0;g<D;g+=2){
         const shell=2**Math.floor(Math.log2(g+1));
         for(let w=1;w<=T;w++){
           const n=a.n0+w,s=n%2===0?1:-1,bs=s===1?0:3;
           const F=2*(a.r+3)+2*w-g+1-2*bs;
           const x=a.x0-g;
           const direct=fac(x+s).filter(q=>q>2&&mod(n,2*q)===(s===1?0:q+2));
           const pinned=fac(F).filter(q=>q>2&&(x+s)%q===0);
           assert(direct.join(",")===pinned.join(","),"pin equivalence");
           assert(!direct.includes(a.r),"anchor label cannot repeat");
           pinTests+=direct.length;
           if(direct.some(q=>q>=M*shell))exceptional=true;
           shellTests++;
         }
       }
       if(exceptional){bad++;continue;}
       nonexceptional++;
       let x=a.x0,g=0,maxp=0,k=0,t=0,largeGain=0;const path=[[x,a.n0]],events=[];
       while(t<T&&g<D){
         t++;
         const n=a.n0+t,p=win(x,n);
         if(p){
           assert(p<M*(g+1),"multiplicative shell bound");
           if(p>maxp){
             if(maxp)assert(p<=M*(T+1)*maxp,"record ratio");
             else assert(p<M,"first record");
             maxp=p;k++;localRecords++;recordTests++;
           }
           events.push({x,n,p});
           if(p-1>=D/(2*T))largeGain+=p-1;
           x-=p-1;g=a.x0-x;
         }
         path.push([x,n]);localTicks++;
         assert(g<=E,"overshoot");
         assert(x/2+n===a.r+3+t-g/2,"height ledger");
       }
       stoppedTicks+=t;
       if(t===T){timeStops++;localTime++;}
       else{
         assert(g>=D,"gain stop");
         assert(g<=T*maxp,"gain max");
         assert((M*(T+1))**k+1e-7>=D/T,"record depth");
         assert(largeGain>=D/2,"large gain charge");
         gainStops++;localGain++;
       }
       good.push({...a,path,events,g,t});
     }
     // For exact physical contacts, only one pair of nearby labels per time offset.
     // Count pairs that meet, and check the sharpened clock restriction.
     for(const a of good){
       for(const [x,n] of a.path){
         const key=x+","+n;
         const prev=seen.get(key)||[];
         for(const b of prev){
           if(a.A===b.A)continue;
           const d=b.x0-a.x0;
           assert(Math.abs(d)<=E,"offset width");
           assert(Math.abs(b.r-a.r-d/2)<=T,"clock difference");
           if(a.r===b.r&&E<a.r){assert(d===0&&a.A===b.A,"equal label");sameLabelTests++;}
           localMeet++;actualMeetings++;
         }
         prev.push(a);seen.set(key,prev);
       }
     }
     // Enumerate near pairs independently of path occupancy on a small finite sample.
     const small=good.slice(0,Math.min(300,good.length));
     for(let i=0;i<small.length;i++)for(let j=i+1;j<small.length;j++){
       const a=small[i],b=small[j],d=b.x0-a.x0;
       if(Math.abs(d)<=E&&Math.abs(b.r-a.r-d/2)<=T){localNear++;nearPairs++;}
       if(a.r===b.r&&Math.abs(d)<a.r){assert(a.A===b.A,"same label CRT");sameLabelTests++;}
     }
     // De-duplicate actual physical moving keys, then verify cut overlap via clock factors.
     const unique=new Map();
     for(const a of good)if(a.t<T)for(const e of a.events)if(e.p-1>=D/(2*T))unique.set(e.x+","+e.n+","+e.p,e);
     for(const {x,n,p} of unique.values()){
       const dest=x-p+1;
       for(let z=dest+2;z<=x;z+=2){
         const key=z+","+n, lk=key+","+p;
         assert(!labelCuts.has(lk),"same prime disjoint cuts");
         labelCuts.set(lk,true);
         const old=cuts.get(key)||new Set();old.add(p);cuts.set(key,old);localFlux++;cutIncidences++;
       }
     }
     for(const [key,ps] of cuts){
       const n=Number(key.split(",")[1]),clock=n%2===0?n:n-2;
       for(const p of ps)assert(clock%p===0,"clock prime flux");
       assert(ps.size<=fac(clock).filter(p=>p>2&&p-1>=D/(2*T)).length,"cut multiplicity");
     }
     cutKeys+=cuts.size;
     actualCases.push({R,T,D,M,anchors:cohort.length,excluded:bad,retained:good.length,timeStops:localTime,gainStops:localGain,ticks:localTicks,recordChecks:localRecords,nearPairsSample:localNear,meetingIncidences:localMeet,largeCutIncidences:localFlux,distinctCuts:cuts.size});
   }
 }
 assert(timeStops>0&&gainStops>0&&recordTests>0&&cutIncidences>0,"nonvacuous branches");
 // Exact rational exponent inequalities for the concrete examples (scale 10^4).
 const examples=[[3000,3128,400,2100],[2855,2856,400,1950],[3000,3128,500,1900]];
 for(const [a,c,t,d] of examples){assert(d+2*t<a&&2*c<10000,"power margin");}
 return {anchors,shellTests,pinTests,nonexceptional,stoppedTicks,timeStops,gainStops,recordTests,nearPairs,actualMeetings,cutIncidences,cutKeys,sameLabelTests,actualCases};
}
console.log(JSON.stringify(audit(),null,2));

// Independent synthetic geometry controls; these are not canonical trajectories.
function syntheticAudit(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 const mod=(x,m)=>((x%m)+m)%m;
 const primes=[11,13,17,19,23,29,31,37,41,43,47];
 let pairTests=0,clockTests=0,crtTests=0,collisionTests=0,cutOverlap=0,cutIncidences=0,maxMultiplicity=0;
 for(const c of [0,2]){
   const b=c===0?0:3,E=48,T=9,anchors=[];
   for(const p of primes)for(let x=1000+mod(c-1000,2*p);x<=1600;x+=2*p){
     // Force even x and x=c mod p; c is even.
     assert(x%2===0&&mod(x-c,p)===0,"anchor class");
     anchors.push({p,x,n:p+b-x/2});
   }
   for(let i=0;i<anchors.length;i++)for(let j=i+1;j<anchors.length;j++){
     const a=anchors[i],b0=anchors[j],d=b0.x-a.x;
     const near=Math.abs(d)<=E&&Math.abs(b0.n-a.n)<=T;
     assert(near===(Math.abs(d)<=E&&Math.abs(b0.p-a.p-d/2)<=T),"refined near equivalence");pairTests++;
     if(near){
       clockTests++;
       const possible=[];
       for(let q=a.p+d/2-T;q<=a.p+d/2+T;q++)possible.push(q);
       assert(possible.length===2*T+1&&possible.includes(b0.p),"clock window");
       if(a.p!==b0.p){
         const m=a.p*b0.p;
         let count=0,rep=-1;
         for(let x=0;x<m;x++)if(mod(x-c,a.p)===0&&mod(x+d-c,b0.p)===0){count++;rep=x}
         assert(count===1&&mod(a.x-rep,m)===0,"CRT class");
         crtTests++;
       }
       // Geometric envelopes intersect iff both x and clock intervals overlap.
       const lo=Math.max(a.x-E,b0.x-E),hi=Math.min(a.x,b0.x);
       const l=Math.max(a.n,b0.n),h=Math.min(a.n+T,b0.n+T);
       assert(lo<=hi&&l<=h,"envelope overlap");collisionTests++;
     }
   }
 }
 for(const n of [-2*11*13,-2*11*13*17,2-11*13,2-11*13*17]){
   const s=n%2===0?1:-1,clock=n%2===0?n:n-2;
   const labels=primes.filter(p=>clock%p===0);
   const cuts=new Map(),same=new Set();
   for(const p of labels)for(let x=1000;x<=1500;x+=2)if((x+s)%p===0){
     const dest=x-p+1;
     for(let z=dest+2;z<=x;z+=2){
       const key=z+","+p;assert(!same.has(key),"same p interval disjoint");same.add(key);
       const set=cuts.get(z)||new Set();set.add(p);cuts.set(z,set);cutIncidences++;
     }
   }
   for(const set of cuts.values()){
     assert(set.size<=labels.length,"clock multiplicity");
     if(set.size>1)cutOverlap++;
     maxMultiplicity=Math.max(maxMultiplicity,set.size);
   }
 }
 assert(clockTests>0&&crtTests>0&&collisionTests>0&&cutOverlap>0&&maxMultiplicity>=2,"nonvacuous");
 return {pairTests,clockTests,crtTests,collisionTests,cutOverlap,cutIncidences,maxMultiplicity};
}
console.log(JSON.stringify(syntheticAudit(),null,2));
