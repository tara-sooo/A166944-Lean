// Asymmetric source/target cutoffs: exact relay partition and band-event charging.
// node research/min_local_negative_asymmetric_band_charge_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+10),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},q=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1);
 let rows=[];
 for(let R of Rs){
  const T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1,Pmax=T/2;
  let specs=[[3,11,47],[5,23,97],[7,47,193],[5,97,193],[7,193,389]].filter(s=>s[2]<=T).map(([z,Y,P])=>({z,Y,P,Q:2*[3,5,7].filter(p=>p<=z).reduce((a,p)=>a*p,1),high:0,near:0,last:0,band:0,small:0,sourceFast:0,targetFast:0,bothSlow:0,low:0,bandCount:0,repCount:0,broadRep:0,pairs:0,asymmetric:0,sourceChecks:0,targetChecks:0}));
  let events=0,checks=0;
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,j=Math.floor((A-lo)/W),n0=3-(lo+j*W)/2,end=n0+T,trace=[],used=new Set();
   for(;;){
    let e=next(a,n),fire=n+e.w;if(fire>end)break;trace.push({a,n,fire,dt:Math.max(0,fire-Math.max(n,n0)),p:e.p,w:e.w,repeat:used.has(e.p)});used.add(e.p);a-=e.p-1;n=fire;events++;
   }
   for(let s of specs){
    let k=trace.filter(e=>e.p>s.z&&e.p<s.Y).length,rep=trace.filter(e=>e.p>s.z&&e.p<s.Y&&e.repeat).length,broad=trace.filter(e=>e.p>s.z&&e.p<s.P).length,broadRep=trace.filter(e=>e.p>s.z&&e.p<s.P&&e.repeat).length;
    s.bandCount+=k;s.repCount+=rep;s.broadRep+=broadRep;ck(k-rep<=s.Y&&broad-broadRep<=s.P,"first-use bound");
    let highs=trace.map((e,i)=>e.p>=s.Y?i:-1).filter(i=>i>=0),charged=0,low=0,tiny=0,nP=0;
    for(let e of trace){if(e.p<s.P)low+=e.dt/T;else nP++;if(e.p<=s.z)tiny+=e.p-1}
    ck(tiny<=s.Q*(1+nP+broad),"broad tiny runs");
    ck(low<=3*(s.Q*(1+nP+broad)+s.P*broad)/T+1e-8,"broad low occupation");s.low+=low;
    for(let j=0;j<highs.length;j++){
     let i=highs[j],e=trace[i];if(e.p<s.P||!e.dt)continue;
     let w=e.dt/T;s.high+=w;
     if(e.p>=Pmax){s.near+=w;continue}
     if(j+1===highs.length){s.last+=w;continue}
     let t=highs[j+1],r=trace[t],relay=trace.slice(i+1,t),E=e.a-e.p+1-r.a;
     s.pairs++;s.asymmetric+=+(r.p<s.P);
     ck(relay.every(x=>x.p<s.Y)&&relay.reduce((v,x)=>v+x.p-1,0)===E,"asymmetric first high pair");
     if(relay.some(x=>x.p>s.z)){s.band+=w;charged++;continue}
     ck(E<s.Q,"periodic confined relay");
     s.small+=w;
     if(e.dt<e.p**.8){s.sourceFast+=w;continue}
     if(r.w<Math.max(r.p**.8,2*s.z+1)){s.targetFast+=w;continue}
     s.bothSlow+=w;
     ck(q(e.a)>=e.p**.8/2&&q(r.a)>=r.p**.8/2,"asymmetric roughness");
     for(let l of [5,7,11,13,17,19,23,29,31,37])if(l>s.z&&l<e.p**.8/2){
      ck((e.a-1)%l!==0&&(e.a+1)%l!==0,"source two forms");s.sourceChecks++;
      if(l<s.Y**.8/2){ck((r.a-1)%l!==0&&(r.a+1)%l!==0,"target two extra forms");s.targetChecks++}
     }
    }
    ck(charged<=k,"disjoint asymmetric band charges");checks++;
   }
  }
  for(let s of specs){
   ck(Math.abs(s.high-s.near-s.last-s.band-s.small)<1e-6*N&&Math.abs(s.small-s.sourceFast-s.targetFast-s.bothSlow)<1e-6*N,"partition");
   ck(s.band<=2*Pmax/T*s.bandCount+1e-6*N&&s.last<=2*Pmax/T*N+1e-6*N,"charge aggregate");
  }
  rows.push({R,N,T,events,checks,controls:specs.map(s=>({...s,...Object.fromEntries(["high","near","last","band","small","sourceFast","targetFast","bothSlow","low","bandCount","repCount","broadRep"].map(k=>[k,s[k]/N]))}))});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000]),null,2));
