// First-height section transport, local/routed residuals and roughness-restricted canonical witnesses.
// Run: node research/lean/negative_min_height_section_flow_audit.mjs
// Floating point for discounted mass only; exact integer reachability and literal winner checks.
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},rows=[];
 for(const R of [12000,48000,192000]){
  const H=Math.floor(R**.4),L=Math.log(R),lo=2*Math.floor((R-4*H)/2),hi=2*R,Nx=(hi-lo)/2+1,S=H+1,N=Nx*S;
  let sp=new Int32Array(2*R+3);for(let p=2;p<sp.length;p++)if(!sp[p]){sp[p]=p;if(p*p<sp.length)for(let j=p*p;j<sp.length;j+=p)if(!sp[j])sp[j]=p}
  function fac(v){v=Math.abs(v);let a=[];while(v>1){let p=sp[v];a.push(p);while(v%p===0)v/=p}return a}
  const plus=[],minus=[];for(let h=0;h<H;h++){plus.push(fac(2*h+3));minus.push(fac(2*h-3))}
  const qm=new Int32Array(Nx);for(let i=0;i<Nx;i++){let x=lo+2*i;qm[i]=Math.min(sp[x-1],sp[x+1])}
  const winners=new Uint16Array(N),to=new Int32Array(N);to.fill(-1);
  for(let i=Nx-1;i>=0;i--){let x=lo+2*i;for(let h=0;h<H;h++){let a=i*S+h,n=h+1-x/2,s=n%2===0?1:-1,p=0;for(let q of(s===1?plus[h]:minus[h]))if((x+s)%q===0){p=q;break}winners[a]=p;let j=i-(p?(p-1)/2:0),hh=h+1-(p?(p-1)/2:0);if(j>=0&&hh>=0)to[a]=j*S+hh}}
  // Literal check via independently trial-factored neighbor, on sampled states.
  let literalChecks=0;
  for(let i=0;i<Nx;i+=17)for(let h=0;h<H;h+=7){let x=lo+2*i,n=h+1-x/2,s=n%2===0?1:-1,v=x+s,p=0;for(let q=3;q*q<=v;q+=2)if(v%q===0){if(!p&&((n%(2*q)+2*q)%(2*q)===(s===1?0:q+2)))p=q;while(v%q===0)v/=q}if(!p&&v>1&&((n%(2*v)+2*v)%(2*v)===(s===1?0:v+2)))p=v;ok(p===winners[i*S+h],"literal winner");literalChecks++}
  const trueRoute=new Int32Array(N),trueDist=new Int32Array(N);trueRoute.fill(-1);
  for(let i=0;i<Nx;i++){trueRoute[i*S+H]=i;for(let h=H-1;h>=0;h--){let a=i*S+h,b=to[a];if(b>=0&&trueRoute[b]>=0){trueRoute[a]=trueRoute[b];trueDist[a]=i-trueRoute[a]}}}
  const weights=Array.from({length:2*H+4},(_,i)=>Math.exp(-2*i*Math.log(L)/H));
  function wt(a,b){return weights[Math.floor(a/S)-Math.floor(b/S)]}
  let full=null;
  const restricted=[];
  // Exact max-ancestor (integer root coordinate) recurrence, disallow
  // every center with qmin above cutoff, not just the terminal center.
  for(let K of [Math.floor(H/10),Math.floor(H/4),Math.floor(H/2),H,Math.floor(R**.2855)]){
   let best=new Int32Array(N);best.fill(-1);
   for(let i=Nx-1;i>=0;i--){if(qm[i]>K)continue;let x=lo+2*i;for(let h=0;h<=H;h++){let a=i*S+h;if(h===3&&x>=R&&x%6===0)best[a]=i;if(h===H||best[a]<0)continue;let b=to[a];if(b>=0&&qm[Math.floor(b/S)]<=K&&(best[b]<0||best[a]<best[b]))best[b]=best[a]}}
   let count=0;for(let i=0;i<Nx;i++)if(best[i*S+H]>=0&&2*(best[i*S+H]-i)<=4*H)count++;
   restricted.push({K,count});
  }
  for(let z of [...new Set([2*H+3,Math.floor(1.5*H),H,Math.floor(H/2),Math.floor(H/4),7])]){
   let F=new Float64Array(N),actualIncoming=new Float64Array(N),best=new Int32Array(N),safe=new Int32Array(N);best.fill(-1);safe.fill(-1);
   let defect=0,routeDefect=0,changed=0,occ=0,look1=0,look8=0,look64=0;
   for(let i=Nx-1;i>=0;i--){let x=lo+2*i;for(let h=0;h<=H;h++){let a=i*S+h;if(h===3&&x>=R&&x%6===0){F[a]=1;best[a]=i;safe[a]=i;actualIncoming[a]+=1}if(h===H||F[a]===0)continue;occ++;let p=winners[a],b=to[a],diff=p>z;
    if(b>=0)actualIncoming[b]+=wt(a,b)*F[a];
    if(diff){changed++;defect+=F[a];b=a+1;if(trueRoute[b]>=0)routeDefect+=F[a]*Math.exp(-2*trueDist[b]*Math.log(L)/H)}
    if(b<0)continue;F[b]=Math.min(1,F[b]+wt(a,b)*F[a]);if(best[a]>=0&&(best[b]<0||best[a]<best[b]))best[b]=best[a];if(!diff&&safe[a]>=0&&(safe[b]<0||safe[a]<safe[b]))safe[b]=safe[a];
   }}
   let res=0,resRoute=0,positive=0,bySink=new Float64Array(Nx);
   for(let a=0;a<N;a++){let r=Math.max(0,F[a]-Math.min(1,actualIncoming[a]));if(r<1e-12)continue;res+=r;positive++;if(trueRoute[a]>=0){let w=r*Math.exp(-2*trueDist[a]*Math.log(L)/H);resRoute+=w;bySink[trueRoute[a]]+=w;}
    let b=a,w=1;for(let k=1;k<=64;k++){if(b%S!==H){let t=to[b];if(t<0){w=0;break}w*=wt(b,t);b=t}if(k===1)look1+=r*w;if(k===8)look8+=r*w;if(k===64)look64+=r*w}
   }
   let perSinkLower=0,perSinkPositive=0,mass=0,sinks=0,good=0,safeSinks=0,safeMass=0,bestMass=0,nonrough=0,nonrough10=0,shortGain=0;for(let i=0;i<Nx;i++){let a=i*S+H;mass+=F[a];let lb=Math.max(0,F[a]-bySink[i]);perSinkLower+=lb;if(lb>1e-10)perSinkPositive++;if(best[a]>=0){sinks++;let g=2*(best[a]-i);if(g<=4*H){good++;if(qm[i]<=H/2)nonrough++;if(qm[i]<=H/10)nonrough10++;if(g<=H/2)shortGain++}bestMass+=Math.exp(-g*Math.log(L)/H)}if(safe[a]>=0){safeSinks++;safeMass+=Math.exp(-2*(safe[a]-i)*Math.log(L)/H)}}
   if(z===2*H+3)full={mass,sinks,good,nonrough,nonrough10,shortGain,restricted,literalChecks};
   for(let d of [defect,routeDefect,res,resRoute,look1,look8,look64])ok(full.mass+1e-6>=mass-d,"residual lower");
   ok(res<=defect+1e-6&&resRoute<=routeDefect+1e-6&&resRoute<=look64+1e-6&&look64<=look8+1e-6&&look8<=look1+1e-6&&look1<=res+1e-6,"residual order");
   ok(perSinkLower<=full.mass+1e-6&&perSinkLower+1e-6>=Math.max(0,mass-resRoute)&&perSinkPositive<=full.sinks,"localized sink bound");
   ok(safeSinks<=full.sinks&&safeMass<=full.mass+1e-6,"safe witnesses");
   let fmt=x=>+x.toFixed(3);
   rows.push({R,H,z,mass:fmt(mass),sinks,good,bestMass:fmt(bestMass),defect:fmt(defect),localResidual:fmt(res),positive,margin:fmt(mass-defect),localMargin:fmt(mass-res),look8Margin:fmt(mass-look8),look64Margin:fmt(mass-look64),routedMargin:fmt(mass-resRoute),perSinkLower:fmt(perSinkLower),perSinkPositive,safeSinks,safeMass:fmt(safeMass),changed,occ,full});
  }
 }
 return rows;
}
console.log(JSON.stringify(audit(),null,2));
