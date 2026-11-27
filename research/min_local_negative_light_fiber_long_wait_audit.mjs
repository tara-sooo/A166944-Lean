// Light-fiber long-dwell extraction and mass-capped negative first-pair arithmetic.
// node research/min_local_negative_light_fiber_long_wait_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+5),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity,e=0;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d;e=s}}return {p,w,e}}
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},add=(m,k,v=1)=>m.set(k,(m.get(k)||0)+v),q=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1);
 const rows=[];
 for(let R of Rs){
  const S=Math.sqrt(2*R+1),T=Math.ceil(S),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1,B0=Math.ceil((3*T+6)/W)+2,L=Math.log(R),m=Math.ceil(L**2.25);
  const endMap=new Map(),paths=[],thresholds=[.125,.25,.5].map(alpha=>({alpha,P:T*Math.exp(-(L**alpha))/2,short:0,longBad:0,longTwin:0,countBad:0,bound:0,phase:new Map()}));
  const bands=[11,23,47,97,193,389,769].filter(P=>P<=T).map(P=>({P,B:Math.min(12,P-4),pairs:0,mass:0,keys:new Map(),phases:new Map()}));
  let checks=0,events=0,scaleChecks=0,lightLabelEntropy=0,scaleRows=[4,8,16].map(K=>({K,weight:0,last:0,up:0,shortRelay:0,longRelay:0,fast:0,gainCharge:0})),light=0,lightEntropy=0,lightTwin=0,allEntropy=0,endEntropy=0,lowEventRoots=0;
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,j=Math.floor((A-lo)/W),n0=3-(lo+j*W)/2,end=n0+T,trace=[],seen=0;
   for(;;){
    let e=next(a,n),fire=n+e.w,last=fire>end,dt=Math.max(0,Math.min(fire,end)-Math.max(n,n0));
    if(dt)seen+=dt;
    trace.push({a,n,fire,dt,last,p:e.p,e:e.e,j});
    if(last)break;
    ck(q(a)<=S,"completed source not twin");a-=e.p-1;n=fire;events++;
   }
   ck(seen===T&&A-a<=3*T+6,"synchronized");
   add(endMap,a);paths.push({A,Y:a,trace});
  }
  for(let {A,Y,trace} of paths){
   let fiber=endMap.get(Y),H=0;endEntropy+=Math.log(fiber);
   let Hlabel=0;
   for(let e of trace)if(e.dt){H-=e.dt/T*Math.log(e.dt/T);Hlabel+=e.dt/T*Math.log(T/(e.last?S:e.p));}
   ck(H-Hlabel>=-Math.log(2)-1e-8&&H-Hlabel<=Math.log(6)+1e-8,"time partition vs label logarithm");
   allEntropy+=H;if(fiber>m)continue;
   light++;lightEntropy+=H;lightLabelEntropy+=Hlabel;if(q(Y)>S)lightTwin++;
   if(trace.length<=Math.exp(L**.5))lowEventRoots++;
   for(let e of trace)if(e.dt){
    for(let c of thresholds){let w=e.dt/T;
     if(e.dt<2*c.P)c.short+=w;
     else{
      ck(q(e.a)>=c.P,"long wait roughness");
      if(q(e.a)>S){ck(e.last&&Y===e.a,"twin terminal");c.longTwin+=w;}
      else{c.longBad+=w;add(c.phase,e.a,w);}
     }
    }
   }
   // Scale-up charging: next label >= the dyadic lower edge of the current label.
   // Include only source labels 5<=p<=Pmax and charge full relay gain, not its time.
   let Pmax=T*Math.exp(-Math.pow(L,.125)/2),Bcut=Math.max(0,Math.floor(L**.25));
   for(let c of scaleRows){
    let charge=new Map(),lastGain=0,sourceGain=0;
    for(let i=0;i<trace.length-1;i++){
     let e=trace[i],p=e.p,P=2**Math.floor(Math.log2(p));
     if(p<5||p>Pmax||!e.dt)continue;
     let w=e.dt/T;c.weight+=w;sourceGain+=p;
     let k=i+1;while(k<trace.length-1&&trace[k].p<P)k++;
     if(k===trace.length-1){c.last+=w;lastGain+=p;}
     else if(trace[k].p>c.K*P){c.up+=w;add(charge,k,p);}
     else if(e.dt<p/4)c.fast+=w;
     else{
      let E=e.a-p+1-trace[k].a;
      ck(E>=0&&E%2===0,"relay gain");
      if(E<=Bcut)c.shortRelay+=w;else c.longRelay+=w;
     }
    }
    // At most one source per band charged to each target.  Sum upper band
    // edges for all P < r/K is < 4r/K.
    ck(lastGain<=4*Pmax+1e-8,"last source per band");
    for(let [k,g] of charge){ck(g<=4*trace[k].p/c.K+1e-8,"geometric scale-up charge");c.gainCharge+=g;scaleChecks++;}
   }
   for(let c of bands){
    let prev=null;
    for(let e of trace){if(e.last)break;if(e.p<c.P)continue;
     if(prev&&prev.p<=2*c.P&&e.p<=2*c.P&&prev.dt>=prev.p/4){
      let E=prev.a-(prev.p-1)-e.a;
      if(E>=0&&E<=c.B){
       let u=(prev.a-prev.e)/prev.p,v=(e.a-e.e)/e.p,b=prev.e+1-E-e.e;
       ck(Number.isInteger(u)&&Number.isInteger(v)&&b%2!==0&&Math.abs(b)<prev.p&&e.p*v===prev.p*(u-1)+b&&prev.p!==e.p,"negative hyperbola");
       for(let l of [5,7,11,13,17,19,23,29,31])if(l<c.P&&l<prev.p/8){
        ck(e.p%l!==0&&mod(e.p*v-(b-prev.p),l)!==0&&mod(e.p*v-(b-prev.p-2*prev.e),l)!==0,"three exclusions");checks++;
       }
       let key=[prev.a,prev.p,prev.e,e.p,e.e,E].join(":"),phase=[prev.a,prev.j,prev.fire].join(":");
       c.keys.set(key,prev.a);add(c.phases,phase,1);c.pairs++;c.mass+=prev.dt/T;checks++;
      }
     }
     prev=e;
    }
   }
  }
  for(let a=2*Math.ceil((lo-3*T-6)/2);a<=hi;a+=2)if(q(a)<=S)for(let c of thresholds)if(q(a)>=c.P)c.countBad++;
  for(let c of thresholds){for(let v of c.phase.values()){ck(v<=B0*m+1e-8,"light mass cap");checks++}
   c.bound=B0*m*c.countBad/N;
   ck(c.longBad/N<=c.bound+1e-8&&Math.abs(c.short+c.longBad+c.longTwin-light)<=1e-6*N,"long dwell bound");
   ck(c.short*L**c.alpha<=lightEntropy+1e-6*N,"short entropy bound");
   ck(lightTwin>=light-c.short-c.longBad-1e-6*N,"twin mass");
  }
  for(let c of bands){for(let v of c.phases.values()){ck(v<=m,"light phase count");checks++}
   ck(c.mass<=c.keys.size*B0*m*6+1e-8,"bounded time weight per source tuple");
  }
  for(let c of scaleRows){ck(Math.abs(c.weight-c.last-c.up-c.fast-c.shortRelay-c.longRelay)<=1e-7*N,'scale partition');}
  rows.push({R,N,T,m,events,checks,scaleChecks,lightLabelEntropy:lightLabelEntropy/N,scaleRows:scaleRows.map(c=>({K:c.K,weight:c.weight/N,last:c.last/N,up:c.up/N,fast:c.fast/N,shortRelay:c.shortRelay/N,longRelay:c.longRelay/N})),light:light/N,lightTwin:lightTwin/N,meanEntropy:allEntropy/N,Lend:endEntropy/N,lightEntropy:lightEntropy/N,lowEventRoots:lowEventRoots/N,thresholds:thresholds.map(c=>({alpha:c.alpha,P:c.P,short:c.short/N,longBad:c.longBad/N,longTwin:c.longTwin/N,countBad:c.countBad,bound:c.bound})),bands:bands.map(c=>({P:c.P,B:c.B,pairs:c.pairs,mass:c.mass/N,sourceTuples:c.keys.size,phaseCount:c.phases.size}))});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000]),null,2));
