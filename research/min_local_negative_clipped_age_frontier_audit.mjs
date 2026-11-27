// Age-frontier entropy and clipped mass loss ledger for actual Negative MIN. Node >=18.
// node research/min_local_negative_clipped_age_frontier_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+5),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const f=x=>x?x*Math.log(x):0,phi=(a,b)=>f(a+b)-f(a)-f(b),add=(m,k,v)=>m.set(k,(m.get(k)||0)+v),sumF=m=>[...m.values()].reduce((s,v)=>s+f(v),0),ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 const rows=[];
 for(let R of Rs){
  const T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
  const us=[...new Set([1,Math.floor(Math.log(R)),Math.floor(Math.log(R)**1.5),Math.min(T,Math.floor(Math.log(R)**2))])].filter(u=>u<=T);
  const stat=us.map(u=>({u,M:1+Math.floor((2*u+6)/6),clip:0,clipMix:0,clipOld:0,clipMinor:0,clipEnd:0,clipEndGlobal:0,early:0,mixed:0,oldOld:0,oldExposure:0,youngMass:0,oldYoungNodes:0,oldOldNodes:0,oldOldHigh:0,oldOldLow:0,oldOldMix:0,highReset:0,lowTicks:0,minority:0,majority:0,rank:0,lowMinority:0,lowMajority:0,lowRank:0}));
  let endings=new Map(),direct=new Map(),endWindow=0,events=0,merges=0,checks=0;
  for(let l=lo;l<=hi;l+=W){
   let maxA=Math.min(hi,l+W-6),start=3-maxA/2,n0=3-l/2,end=n0+T,active=new Map(),buckets=new Map(),directW=new Map(),actualW=new Map();
   const sched=(a,n,v)=>{const e=next(a,n),t=n+e.w;if(t<=end){let b=buckets.get(t)||[];b.push({a,p:e.p,v});buckets.set(t,b)}};
   const close=(a,v,n)=>{for(let s of stat){let left=Math.max(v.s,3-v.maxA/2+s.u),right=Math.min(n,s.u+3-a/2);if(right>=left)s.lowTicks+=v.m*(right-left+1)}};
   for(let n=start;n<=end;n++){
    let arrivals=new Map();const push=(a,g)=>{let v=arrivals.get(a)||[];v.push(g);arrivals.set(a,v)};
    for(let e of buckets.get(n)||[]){
     let v=active.get(e.a);if(v!==e.v)continue;
     close(e.a,v,n-1);active.delete(e.a);let a=e.a-e.p+1,h=n+a/2;
     ck(h>=0&&((n%2===0&&mod(h,e.p)===0)||(n%2!==0&&mod(h-3,e.p)===0)),["clock height",a,n,e.p,h]);checks++;
     push(a,{m:v.m,maxA:v.maxA,p:e.p});events++;
    }
    let A=2*(3-n);if(A>=l&&A<=maxA&&A%6===0)push(A,{m:1,maxA:A,p:0,birth:true});
    for(let [a,groups] of arrivals){
     let v=active.get(a);if(v){close(a,v,n-1);groups.push({m:v.m,maxA:v.maxA,p:0,idle:true})}
     let m=groups.reduce((x,g)=>x+g.m,0),maxA=Math.max(...groups.map(g=>g.maxA)),h=n+a/2;
     ck(h>=0,"height");if(groups.length>1){
      merges++;const total=f(m)-groups.reduce((x,g)=>x+f(g.m),0);
      for(let s of stat){
       let u=s.u,young=groups.filter(g=>g.birth||n-1-3+g.maxA/2<u),old=groups.filter(g=>!g.birth&&n-1-3+g.maxA/2>=u);
       let Y=young.reduce((x,g)=>x+g.m,0),O=m-Y,ey=f(Y)-young.reduce((x,g)=>x+f(g.m),0),eo=f(O)-old.reduce((x,g)=>x+f(g.m),0),mix=phi(Y,O);
       const M=1+Math.floor((2*u+6)/6);
       ck(Y<=M&&Math.abs(ey+eo+mix-total)<1e-6,["partition",R,n,a,u,Y,M]);
       if(Y){ck(h<=u+3,["young height",h,u]);for(let g of young)if(g.p)ck(g.p-1<=2*u+6,"young gain");}
       const cap=x=>Math.min(x,M),cl=groups.reduce((t,g)=>t+cap(g.m),0)-cap(m),
        co=old.reduce((t,g)=>t+cap(g.m),0)-cap(O),cm=cap(Y)+cap(O)-cap(m);
       ck(cl===co+cm&&cm>=0&&cm<=Y&&co>=0,"clipped age partition");
       let aMinor=old.reduce((t,g)=>t+cap(g.m),0)-Math.max(0,...old.map(g=>cap(g.m)));
       ck(co<=aMinor,"clipped minority");
       s.clip+=cl;s.clipMix+=cm;s.clipOld+=co;s.clipMinor+=aMinor;
       s.early+=ey;s.oldOld+=eo;s.mixed+=mix;
       if(Y&&O){s.youngMass+=Y;s.oldExposure+=O;s.oldYoungNodes++;for(let g of old)if(g.p>u+3){ck(h===0||h===3,"large old into young reset");s.highReset+=g.m;}}
       function charge(gs,kind){if(gs.length<=1)return;let b=Math.max(...gs.map(g=>g.m)),a=gs.reduce((t,g)=>t+g.m,0)-b,r=a*Math.log(gs.length-1);
        if(kind==="low"){s.lowMinority+=a;s.lowMajority+=b;s.lowRank+=r;}else{s.minority+=a;s.majority+=b;s.rank+=r;}
        ck(f(a+b)-gs.reduce((t,g)=>t+f(g.m),0)<=phi(a,b)+r+1e-7,"minority local");}
       if(old.length>1){
        s.oldOldNodes++;charge(old,"all");
        let H=old.filter(g=>g.p>u+3),L=old.filter(g=>g.p<=u+3),hm=H.reduce((x,g)=>x+g.m,0),lm=O-hm;
        s.oldOldHigh+=f(hm)-H.reduce((x,g)=>x+f(g.m),0);s.oldOldLow+=f(lm)-L.reduce((x,g)=>x+f(g.m),0);s.oldOldMix+=phi(hm,lm);charge(L,"low");
       }
       checks++;
      }
     }
     let z={m,maxA,s:n};active.set(a,z);sched(a,n,z);
    }
   }
   for(let [a,v] of active){close(a,v,end);add(endings,a,v.m);actualW.set(a,v.m)}
   for(let A=l;A<=maxA;A+=6){let a=A,n=3-A/2;for(;;){let e=next(a,n);if(n+e.w>end)break;a-=e.p-1;n+=e.w;}add(direct,a,1);add(directW,a,1)}
   ck(actualW.size===directW.size&&[...actualW].every(([a,m])=>directW.get(a)===m),"independent endpoint replay");endWindow+=sumF(actualW);for(let s of stat)s.clipEnd+=[...actualW.values()].reduce((t,m)=>t+Math.min(m,s.M),0);checks++;
  }
  ck(endings.size===direct.size&&[...endings].every(([a,m])=>direct.get(a)===m),"global endpoint replay");
  const Lend=sumF(endings)/N,Lw=endWindow/N,B0=Math.ceil((3*T+6)/W)+2;
  for(let s of stat){
   let M=s.M;
   ck(s.clip+s.clipEnd===N&&s.clip===s.clipMix+s.clipOld&&s.clipMix<=s.youngMass&&s.clipOld<=s.clipMinor,"clipped telescope and bounds");
   s.clipEndGlobal=[...endings.values()].reduce((t,m)=>t+Math.min(m,B0*M),0);
   ck(s.clipEndGlobal>=s.clipEnd,"window cap transfer");
   let delta=s.clipEnd/N,threshold=Math.ceil(2*B0*M/delta);
   let light=[...endings.values()].reduce((t,m)=>t+(m<=threshold?m:0),0)/N;
   ck(light+1e-12>=delta/2,"positive light cohort");
   Object.assign(s,{delta,threshold,light,clipFraction:s.clip/N,mixedClipFraction:s.clipMix/N,oldClipFraction:s.clipOld/N,minorClipFraction:s.clipMinor/N,frontierClipBound:(s.youngMass+s.clipMinor)/N});
   ck(s.youngMass<=N&&s.early<=N*Math.log(M)+1e-6*N,"frontier bounds");
   ck(Math.abs((s.early+s.mixed+s.oldOld)/N-Lw)<1e-8,"entropy telescope");
   ck(Math.abs((s.oldOldHigh+s.oldOldLow+s.oldOldMix-s.oldOld)/N)<1e-8,"old split");
   ck(s.oldExposure<=s.lowTicks,"low exposure");
   const bound=phi(s.oldExposure/N,s.youngMass/N),coarse=phi(s.lowTicks/N,1),minor=phi(s.minority/N,s.majority/N)+s.rank/N,lowMinor=phi(s.lowMinority/N,s.lowMajority/N)+s.lowRank/N;
   ck(s.mixed/N<=bound+1e-8&&bound<=coarse+1e-8&&s.oldOld/N<=minor+1e-8&&s.oldOldLow/N<=lowMinor+1e-8,"logsum");
   for(let k of ["early","mixed","oldOld","oldExposure","youngMass","oldOldHigh","oldOldLow","oldOldMix","highReset","lowTicks","minority","majority","rank","lowMinority","lowMajority","lowRank"])s[k]/=N;
   Object.assign(s,{M,mixedBound:bound,lowBound:coarse,earlyBound:Math.log(M),minorityBound:minor,lowMinorityBound:lowMinor});
  }
  rows.push({R,T,N,Lend,Lw,events,merges,checks,stat});
 }
 return rows
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000,1000000,2000000]),null,2));
