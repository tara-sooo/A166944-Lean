// Finite exact section slicing and gain-localized cutoff controls. Proxy cutoffs, not an asymptotic density test.
function audit(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 const mod=(a,b)=>((a%b)+b)%b;
 const f=new Int32Array(1536100);
 for(let p=2;p<f.length;p++)if(!f[p]){f[p]=p;if(p*p<f.length)for(let x=p*p;x<f.length;x+=p)if(!f[x])f[x]=p;}
 function next(x,h,z=Infinity){
   const n=h-x/2;let w=Infinity,p=0;
   for(const s of [1,-1]){let v=x+s;while(v>1){const q=f[v];if(q>z)break;let d=mod((s===1?0:q+2)-n,2*q);if(!d)d=2*q;if(d<w||(d===w&&q<p)){w=d;p=q;}while(v%q===0)v/=q;}}
   return {w,p};
 }
 function first(A,H,B,start=null,z=Infinity){
   let x=start?.x??A,h=start?.h??3,W=0,S=0,G=0,events=0,maxp=0;
   while(A-x<=B){
     const {w,p}=next(x,h,z);
     if(h+w-1>=H)return {x,h:H,W,S,G,events,maxp,I:H-h,age:H-(start?.h??3)+G/2};
     x-=p-1;h+=w-(p-1)/2;W+=w;G+=p-1;S+=Math.max(0,p-281);events++;maxp=Math.max(maxp,p);
   }
   return null;
 }
 let roots=0,sinks=0,active=0,sectionChecks=0,localChecks=0,trialChecks=0,lowerChecks=0,positiveLower=0,shortGain=0,stationaryChecks=0,excessCounts=0;
 const rows=[];
 for(const R of [12000,48000,192000,768000]){
   const H=Math.floor(R**.4),B=4*H,h0=Math.floor(H/3),D=Math.max(4,Math.floor(H/3)),Q=Math.max(2,Math.floor(D/3)),M=8;
   const heights=[h0];while(heights.at(-1)+D<=H)heights.push(heights.at(-1)+D);
   const map=new Map();
   for(let A=6*Math.ceil(R/6);A<=2*R;A+=6){
     roots++;const t=first(A,H,B);if(!t)continue;
     if(!map.has(t.x))map.set(t.x,{A,t});
   }
   sinks+=map.size;
   const counts=Array(heights.length-1).fill(0), pairs=Array.from({length:heights.length},()=>new Set());
   let nact=0,nlocal=0,ntrial=0,ngain=0,nrough=0;
   for(const [x,{A,t}] of map){
     if(Math.min(f[x-1],f[x+1])>=4*H){stationaryChecks++;continue;}
     active++;nact++;
     const states=heights.map(h=>first(A,h,B));
     let gain=0,large=0;
     for(let i=0;i<states.length;i++){
       const s=states[i];assert(s,"first-section existence");
       assert(!pairs[i].has(s.x),"distinct final sinks have distinct lower-section states");
       pairs[i].add(s.x);sectionChecks++;
       assert(Math.min(f[s.x-1],f[s.x+1])<4*H,"no globally rough state on nonstationary witness");
       if(i===states.length-1)break;
       const r=first(A,heights[i+1],B,s);
       assert(r&&r.x===states[i+1].x,"exact local continuation");
       assert(r.G===s.x-r.x&&r.age===D+r.G/2,"local gain and age");
       assert(24*r.W<=51*r.G+790-3*r.S,"arbitrary section complete-block bound");
       assert(r.I<D+r.G/2+1&&r.I<2*Math.min(f[r.x-1],f[r.x+1]),"local terminal idle");
       gain+=r.G;
       if(r.G>M*D){large++;continue;}
       shortGain++;ngain++;
       assert(r.maxp<=M*D+1,"gain bounds every selected label");
       const b=first(A,heights[i+1],B,s,M*D+1);
       assert(b&&JSON.stringify(b)===JSON.stringify(r),"exact small-alphabet section continuation");
       trialChecks++;ntrial++;
       if(Math.min(f[s.x-1],f[s.x+1])<=Q&&Math.min(f[r.x-1],f[r.x+1])<=Q){
         assert(24*(D-2*Q)<=39*r.G+790-3*r.S,"active segment lower gain");
         lowerChecks++;counts[i]++;nlocal++;
         if(24*(D-2*Math.min(f[r.x-1],f[r.x+1]))>790)positiveLower++;
       }else nrough++;
       localChecks++;
     }
     assert(gain<=B&&large*M*D<=B,"aggregate section budget");
     excessCounts+=large;
   }
   rows.push({R,H,D,Q,M,sections:heights.length,distinct:map.size,nonstationary:nact,cheapIntervals:ngain,trialChecks:ntrial,activeCheap:nlocal,roughEndpointIntervals:nrough,perInterval:counts});
 }
 assert(lowerChecks>0&&trialChecks>0&&stationaryChecks>0,"nonvacuity");
 return {roots,sinks,active,sectionChecks,localChecks,trialChecks,lowerChecks,positiveLower,shortGain,stationaryChecks,excessCounts,rows};
}
console.log(JSON.stringify(audit(),null,2));
