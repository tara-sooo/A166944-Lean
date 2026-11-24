// Fresh-high landing exclusion and repeat horizon separation.
function audit(Y,N=2048){
 const V=8*Y,T=Math.floor(Y*Math.sqrt(Math.log(Y))),z=Math.ceil(T**.8),R=Math.max(0,Math.floor(T**.3)),ps=[];
 for(let p=3;p<V;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 let rng=(0x7c981231^Y)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let l=4294967296-4294967296%p,x;do{x=u32()}while(x>=l);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)};
 let fresh=0,bad=0,badRuns=0,repeat=0,repeatChecks=0,known=0,resetQuiet=0,lowEnds=0,lowEndsInside=0,firstHigh=0,firstGain=0,totalGain=0,maxGain=0,live=0,repeatGain=0,checks=0,threeExceptions=0;
 let P=ps.filter(p=>p>=z),recip=P.reduce((s,p)=>s+1/p**2,0);
 for(let j=0;j<N;j++){
  let parity=uni(2);for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let v=uni(p);t[i]=v%2===parity?v:v+p}
  let e=0,g=0,seen=new Map(),runBad=false,had=false;
  function next(e,g,lim){let w=Infinity,k=-1;for(let i=0;i<ps.length&&ps[i]<lim;i++){let p=ps[i],cc=mod(c[i]+g,p);if(cc!==1&&cc!==p-1)continue;let ph=cc===1?0:p+2,f=2*p-mod(t[i]+e-ph,2*p);if(f<w||(f===w&&p<ps[k])){w=f;k=i}}return {w,k}}
  for(;;){let {w,k}=next(e,g,V);if(k<0||e+w>T)break;
   let p=ps[k],g0=g;e+=w;g+=p-1;
   if(seen.has(k)){let old=seen.get(k);ck(e-old.e>=p-2,"clock");if(p>=5)ck(g0-old.g>=p-1,"gain return");else if(g0-old.g<p-1)threeExceptions++;repeatChecks++;if(p>=z){repeat++;repeatGain+=p-1}}
   else{firstGain+=p-1;if(p>=z){
     fresh++;if(!had){firstHigh++;had=true}
     let danger=false;
     for(let [i,o] of seen)if(ps[i]>=z){known++;let q=ps[i],hit=false;
      for(let d=0;d<=R;d+=2){let cc=mod(c[i]+g+d,q);if(cc===1||cc===q-1){hit=true;break}}
      let residues=new Set();for(let d=0;d<=R;d+=2)for(let s of [-1,1])residues.add(mod(s-c[i]-g0+1-d,q));
      ck(hit===residues.has(p%q),"reactivation congruence");checks++;if(hit)danger=true;
     }
     for(let d=0;d<=Math.min(R,p-2);d+=2){let cc=mod(c[k]+g+d,p);ck(cc!==1&&cc!==p-1,"own exclusion")}
     if(danger){bad++;runBad=true}else{
      resetQuiet++;
      let f=e,h=g;for(;;){let v=next(f,h,z);if(v.k<0){lowEnds++;if(h-g<=R&&f-e<=R)lowEndsInside++;break}if(f+v.w-e>R||h+ps[v.k]-1-g>R)break;f+=v.w;h+=ps[v.k]-1;}
     }
   }}
   seen.set(k,{e,g});
  }
  if(runBad)badRuns++;totalGain+=g;maxGain=Math.max(maxGain,g);live+=e>0;
 }
 return {Y,V,T,z,R,N,fresh,bad,badRuns,repeat,repeatChecks,threeExceptions,known,resetQuiet,lowEnds,lowEndsInside,firstHigh,firstGain,totalGain,maxGain,repeatGain,checks,recip,meanFresh:fresh/N,meanBad:bad/N,meanGain:totalGain/N,meanFirstGain:firstGain/N};
}
for(const y of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(y)));
