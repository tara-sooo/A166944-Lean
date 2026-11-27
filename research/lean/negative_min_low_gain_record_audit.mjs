// Exact finite record-mass objective for low-band gain costs (not asymptotic evidence).
// Run: node research/lean/negative_min_low_gain_record_audit.mjs
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},mod=(a,b)=>((a%b)+b)%b;
 const Rmax=384000,sp=new Int32Array(2*Rmax+3);for(let p=2;p<sp.length;p++)if(!sp[p]){sp[p]=p;if(p*p<sp.length)for(let j=p*p;j<sp.length;j+=p)if(!sp[j])sp[j]=p}
 const factors=n=>{let a=[];while(n>1){const p=sp[n];a.push(p);while(n%p===0)n/=p}return a};
 const twin=x=>sp[x-1]===x-1&&sp[x+1]===x+1;
 const next=(x,n)=>{let best=Infinity,p0=0;for(const p of [...new Set([...factors(x-1),...factors(x+1)])]){const c=(x+1)%p===0?0:p+2,w=mod(c-n,2*p)||2*p;if(w<best||(w===best&&p<p0)){best=w;p0=p}}return {w:best,p:p0}};
 const rows=[];
 for(const [R,T,M] of [[12000,48,4],[48000,96,8],[192000,192,16],[384000,288,24]]){
  const W=6*Math.floor(T/6),lo=Math.ceil(R/6)*6,Y=Math.floor(T/Math.sqrt(Math.log(R))),windows=Math.floor((2*R-lo)/W)+1;
  let N=0,total=0,old=0,raw=0,energy=0,twinMass=0,nonTwinTerminal=0,interior=0,recordChecks=0,binChecks=0,prefixRoots=0,ticks=0,highFires=0;
  for(let J=0;J<windows;J++){
   const a0=lo+J*W,a1=Math.min(2*R,a0+W-6),obs=3-a0/2,end=obs+T;
   const bins=new Map();
   for(let A=a0;A<=a1;A+=6){
    N++;let x=A,n=3-A/2,net=0,oldNet=0,peak=0,oldPeak=0,rootRec=0;
    let e=next(x,n),fire=n+e.w;
    for(;n<end;n++){
     const p=n+1===fire?e.p:0;
     const rew=n>=obs?8:0,c=p>0&&p<Y?17*(p-1):0,c0=p>0&&p<Y?18*(p-1):0;
     net+=rew-c;oldNet+=rew-c0;let gain=Math.max(0,net-peak),g0=Math.max(0,oldNet-oldPeak);peak+=gain;oldPeak+=g0;
     ok(gain>=g0&&gain<=8,"monotone record profit");recordChecks++;rootRec+=gain;
     if(n>=obs&&gain){let k=x+","+n,b=bins.get(k);if(!b){b={x,n,fire,hist:new Uint32Array(9),oldHist:new Uint32Array(9)};bins.set(k,b)}ok(b.fire===fire,"shared physical next event");b.hist[gain]++;if(g0)b.oldHist[g0]++}
     if(p){if(p>=Y)highFires++;x-=p-1;e=next(x,n+1);fire=n+1+e.w}
     ticks++;
    }
    ok(rootRec===peak,"record telescoping");raw+=rootRec;if(rootRec>0)prefixRoots++;
   }
   for(const b of bins.values()){
    let m=0,m0=0,v=0,v0=0,br=0,be=0;
    for(let k=8;k>=1;k--){m+=b.hist[k];m0+=b.oldHist[k];v+=Math.min(M,m);v0+=Math.min(M,m0);br+=m;be+=m*m}
    ok(v>=v0,"clip monotonicity");binChecks++;total+=v;old+=v0;energy+=be;
    if(twin(b.x))twinMass+=v;else if(b.fire>end)nonTwinTerminal+=v;else interior+=v;
   }
  }
  ok(total===twinMass+nonTwinTerminal+interior,"mass partition");
  // record threshold mass is normalized by 8NT; old comparator uses the same scale.
  rows.push({R,T,M,Y,N,ticks,recordChecks,binChecks,highFires,prefixRoots,rawRecord:raw/(8*N*T),meanThresholdMultiplicity:raw?energy/raw:0,optimal:total/(8*N*T),oldPotentialCost:old/(8*N*T),twin:twinMass/(8*N*T),nonTwinTerminal:nonTwinTerminal/(8*N*T),interior:interior/(8*N*T)});
 }
 return rows
}
console.log(JSON.stringify(audit(),null,2));
