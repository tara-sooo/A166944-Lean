// Structural checks for progress-weighted record counting and hard-budget prefix transfer. Finite proxies, not asymptotic estimates.
function audit(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 const mod=(a,b)=>((a%b)+b)%b;
 const maxR=768000, f=new Int32Array(2*maxR+100);
 for(let p=2;p<f.length;p++)if(!f[p]){f[p]=p;if(p*p<f.length)for(let n=p*p;n<f.length;n+=p)if(!f[n])f[n]=p;}
 const fac=x=>{let a=[];while(x>1){const p=f[x];assert(p>0,"factor domain");a.push(p);while(x%p===0)x/=p;}return a;};
 function next(x,h,z){
   let best=Infinity,p=0,s=0;const n=h-x/2;
   for(const e of [1,-1])for(const q of fac(x+e)){
     if(q>z)break;
     let w=mod((e===1?0:q+2)-n,2*q);if(!w)w=2*q;
     if(w<best||(w===best&&q<p)){best=w;p=q;s=e;}
   }
   return {w:best,p,s};
 }
 function run(A,H,B,z=Infinity,start=null,save=false){
   let x=start?.x??A,h=start?.h??3,M=start?.M??3,k=start?.k??0,events=0;
   const rec=[];
   while(A-x<=B){
     const {w,p,s}=next(x,h,z);
     if(h+w-1>=H)return {x,h:H,M,k,G:A-x,events,rec,terminalIdle:H-h};
     const before=x,old=h;
     x-=p-1;h+=w-(p-1)/2;events++;
     assert(h>=0&&h<H&&p>=3,"postheight");
     if(h>M){
       if(save)rec.push({prev:old,oldM:M,h,p,s,w,x,source:before});
       M=h;k++;
     }
   }
   return null;
 }
 function bands(H,b,rec,m,check){
   const d0=H-3,ell=Math.log(d0/b);
   assert(ell>0,"positive span");
   let mu=d0,good=0,bad=0,nGood=0,gainGood=0,clipped=0,crossBelow=0,steps=0;
   const byBand=new Map();
   for(const r of rec){
     if(mu<=b)break;
     const d=H-r.h,dprev=H-r.prev;
     assert(H-r.oldM===mu&&d<mu&&dprev>=mu,"record descent");
     assert(r.p<=2*d+1&&dprev<=6*d&&dprev-d<=2*r.p,"deficit inequalities");
     assert(r.w>(r.p-1)/2&&2*Math.min(f[r.source-1],f[r.source+1])>=r.w,"slow record");
     if(d<b){crossBelow++;assert(d>b/6-1e-12,"crossing landing bound");}
     const delta=Math.log(mu/Math.max(d,b));clipped+=delta;steps++;
     let j=Math.floor(Math.log2(d/(b/6))),D=b/6*2**j;
     while(d<D){j--;D/=2;}while(d>=2*D){j++;D*=2;}
     assert(j>=0&&d>=D&&d<2*D,"landing band");
     assert(delta<=2*r.p/D+1e-9,"weighted record drop");
     const bb=byBand.get(j)||{D,actual:0,major:0};
     bb.actual+=delta;
     if(r.p>=D/m){
       bad+=delta;bb.major+=delta;
       check?.(r,j,D,delta);
     }else{
       good+=delta;nGood++;gainGood+=r.p-1;
       assert(delta<=2/m+1e-9,"small label drop");
     }
     byBand.set(j,bb);mu=d;
   }
   assert(mu<=b,"target crossed");
   assert(Math.abs(clipped-ell)<1e-8&&Math.abs(good+bad-ell)<1e-8,"log ledger");
   assert(good<=2*nGood/m+1e-8,"small label count");
   assert(gainGood+1e-8>=good*b/18,"small label gain");
   for(const {actual} of byBand.values())assert(actual<=Math.log(12)+1e-9,"band capacity");
   if(m>=4*rec.length/ell)assert(bad>=ell/2-1e-8,"weighted major progress");
   return {good,bad,nGood,gainGood,crossBelow,steps,ell,byBand};
 }
 let roots=0,successful=0,recordInc=0,profiles=0,belowCross=0,majorKeyChecks=0,minorGainChecks=0,majorWeightChecks=0,actualRows=[];
 for(const R of [12000,48000,192000,768000]){
   const H=Math.floor(R**.4),Q=Math.max(1,Math.floor((H-3)/8)), B=4*H;
   const selected=new Map();
   let nr=0,ns=0,nrinc=0,np=0,ncross=0;
   for(let A=6*Math.ceil(R/6);A<=2*R;A+=6){
     nr++;
     const e=run(A,H,B,Infinity,null,true);if(!e)continue;
     ns++;nrinc+=e.k;
     if(Math.min(f[e.x-1],f[e.x+1])<=Q){
       assert(e.terminalIdle<2*Q,"terminal deficit");
       if(!selected.has(e.x)||selected.get(e.x).k>e.k)selected.set(e.x,e);
       for(const b of [2*Q,(H-3)/2]){
         const ell=Math.log((H-3)/b);
         const m=Math.max(1,Math.ceil(4*e.k/ell));
         const a=bands(H,b,e.rec,m);np++;ncross+=a.crossBelow;minorGainChecks++;
       }
     }
   }
   // Each selected distinct sink gets one actual witness. A physical key
   // cannot be used by two distinct selected sinks. Count the actual major
   // log drop against its geometry-only weight.
   let totalKeys=0,weight=0,drop=0;
   for(const m of [1,2,4,8,16,32]){
     const used=new Map();let localDrop=0,localWeight=0;
     for(const [sink,e] of selected){
       const a=bands(H,2*Q,e.rec,m,(r,j,D,delta)=>{
         const key=[r.x,r.h,r.p,r.s].join(",");
         assert(!used.has(key),"distinct sinks cannot share physical key");
         used.set(key,sink);
         assert(mod(r.x-(1-r.s),r.p)===0&&mod(r.h-(r.s===1?0:3),r.p)===0,"arrival pin");
         assert(r.p>=D/m&&r.p<=4*D+1,"major band p");
         if(r.p>=5)assert(5*Math.min(f[r.source-1],f[r.source+1])>=r.p,"rough source");
         localWeight+=2*r.p/D;localDrop+=delta;majorKeyChecks++;
       });
       np++;ncross+=a.crossBelow;minorGainChecks++;
     }
     assert(localDrop<=localWeight+1e-8,"aggregate key weight");
     majorWeightChecks++;totalKeys+=used.size;weight+=localWeight;drop+=localDrop;
   }
   roots+=nr;successful+=ns;recordInc+=nrinc;profiles+=np;belowCross+=ncross;
   actualRows.push({R,H,Q,roots:nr,successful:ns,recordInc:nrinc,distinctActive:selected.size,profiles:np,clippedBelow:ncross,majorKeys:totalKeys,majorDrop:drop,majorWeight:weight});
 }
 // Independent hard-budget transfer using the common FIRST lower section.
 let transferRoots=0,prefixChecks=0,continuationChecks=0,sinkSetChecks=0,stationaryPrefixChecks=0,changedGood=0,nonstationaryPrefix=0,lowPrefixCharges=0,midPrefixCharges=0;
 const transferRows=[];
 for(const R of [12000,48000,192000]){
   const H=Math.floor(R**.4), B=4*H;
   for(const z of [...new Set([Math.floor(2*H/3),Math.floor(H/3),Math.max(9,Math.floor(H/6)),2*H+3])]){
     if(z>=2*H+1)continue;
     const h0=Math.floor((z-1)/2);if(h0<=3||4*h0<=z)continue;
     const caps=[0,1,2,4,8,16,32], packets=[];
     for(let A=6*Math.ceil(R/6);A<=2*R;A+=6){
       transferRoots++;
       const pre=run(A,h0,B),ptr=run(A,h0,B,z);
       assert(JSON.stringify(pre)===JSON.stringify(ptr),"common prefix");
       prefixChecks++;
       const a=run(A,H,B),b=run(A,H,B,z);
       if(!pre){assert(!a&&!b,"first-section necessity");continue;}
       for(const [r,zz] of [[a,Infinity],[b,z]]){
         const s=run(A,H,B,zz,pre);
         assert((!r&&!s)||(r&&s&&r.x===s.x&&r.k===s.k&&r.G===s.G&&r.M===s.M),"exact continuation with record maximum");
         continuationChecks++;
       }
       const qmin=Math.min(f[pre.x-1],f[pre.x+1]);
       if(qmin>=4*h0){stationaryPrefixChecks++;assert(b&&b.x===pre.x&&b.k===pre.k&&b.G===pre.G,"stationary trial suffix");}
       if(qmin>2*H+1){changedGood++;assert(a&&b&&a.x===b.x&&a.k===b.k&&a.G===b.G,"unchanged good prefix");}
       packets.push({A,pre,a,b,qmin});
     }
     for(const k of caps){
       const sa=new Set(),sb=new Set(),low=new Set(),mid=new Set(),am=new Map(),bm=new Map();
       for(const r of packets){
         if(r.pre.k<=k){if(r.qmin<4*h0)low.add(r.pre.x);else if(r.qmin<=2*H+1)mid.add(r.pre.x);}
         if(r.a&&r.a.k<=k){
           sa.add(r.a.x);if(!am.has(r.a.x))am.set(r.a.x,r.pre.x);
         }
         if(r.b&&r.b.k<=k){
           sb.add(r.b.x);if(!bm.has(r.b.x))bm.set(r.b.x,r.pre.x);
         }
       }
       const da=[...sa].filter(x=>!sb.has(x)),db=[...sb].filter(x=>!sa.has(x));
       const ca=new Set(),cb=new Set();
       for(const x of da){const p=am.get(x);assert(low.has(p)||mid.has(p),"true-only charged bad prefix");assert(!ca.has(p),"true-only distinct prefix");ca.add(p);}
       for(const x of db){const p=bm.get(x);assert(low.has(p)||mid.has(p),"trial-only charged bad prefix");assert(!cb.has(p),"trial-only distinct prefix");cb.add(p);}
       assert(da.length<=low.size+mid.size&&db.length<=low.size+mid.size,"symmetric difference charge");
       sinkSetChecks++;nonstationaryPrefix+=low.size;lowPrefixCharges+=ca.size;midPrefixCharges+=cb.size;
       transferRows.push({R,H,z,h0,k,trueSinks:sa.size,trialSinks:sb.size,trueOnly:da.length,trialOnly:db.length,low:low.size,mid:mid.size});
     }
   }
 }
 assert(majorKeyChecks>0&&belowCross>0&&stationaryPrefixChecks>0&&nonstationaryPrefix>0&&midPrefixCharges>0,"nonvacuity");
 return {roots,successful,recordInc,profiles,belowCross,majorKeyChecks,minorGainChecks,majorWeightChecks,actualRows,transferRoots,prefixChecks,continuationChecks,sinkSetChecks,stationaryPrefixChecks,unchangedGoodPrefixes:changedGood,nonstationaryPrefix,trueOnlyCharges:lowPrefixCharges,trialOnlyCharges:midPrefixCharges,transferExamples:transferRows.filter(r=>r.k===8||r.k===0),transferCases:transferRows.length};
}
console.log(JSON.stringify(audit(),null,2));
