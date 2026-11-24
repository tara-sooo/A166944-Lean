// Repeated high prime arithmetic relation and modular support certificate audit.
function audit(Y,N=512){
 const T=Math.floor(Y*Math.sqrt(Math.log(Y))),w=2*Y,U=T+w,V=8*Y,ps=[];
 for(let p=3;p<V;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 let rng=(0x76c3a921^Y)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let l=4294967296-4294967296%p,x;do{x=u32()}while(x>=l);return x%p}
 const mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)},c=new Int32Array(ps.length),t=new Int32Array(ps.length);
 const zs=[Math.max(11,Math.ceil(U/Math.log(U)**1.2)),Math.max(11,Math.ceil(U/Math.log(U)**1.4)),Math.max(11,Math.ceil(T**.8))].filter((x,i,a)=>a.indexOf(x)===i);
 const out=zs.map(z=>({z,highFresh:0,highRepeat:0,repeatPaths:0,terminalRepeats:0,repeatSameHigh:0,maxK:0,lowGain:0,repeatLowGain:0,minRepeatLowGain:null,maxRepeatLowGain:0,repeatTime:0,repeatHighGain:0,maxRepeatMultiplicity:0,firstLastModulus:0,firstLastSummand:0,relations:0,dpPaths:0,dpLabels:0,dpMin:[],actualMin:[],caps:[.5,.75,.9].map(e=>({R:Math.floor(U**e),badRelationPaths:0,smallRepeat:0,smallTerminalRepeat:0,repeatPathsWithCert:0,certificateChecks:0})),countBoundChecks:0,active:0}));
 function next(e,g,k){let w=Infinity,i0=-1;for(let i=0;i<k;i++){let p=ps[i],cc=mod(c[i]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[i]+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i0])){w=f;i0=i}}return {w,i:i0}}
 for(let j=0;j<N;j++){
  let parity=uni(2);for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let b=uni(p);t[i]=b%2===parity?b:b+p}
  let path=[],e=0,g=0;for(;;){let a=next(e,g,ps.length);if(e+a.w>U)break;e+=a.w;let oldg=g;g+=ps[a.i]-1;path.push({s:e,g,oldg,i:a.i})}
  for(let b of out){
   let k=ps.findIndex(p=>p>=b.z);if(k<0)k=ps.length;
   let first=new Map(),last=new Map(),counts=new Map(),low=0,reps=[],prev=0,active=0;
   for(let ix=0;ix<path.length;ix++){
    let a=path[ix],p=ps[a.i],dt=a.s-prev;if(next(prev,a.oldg,k).i>=0)active+=dt;prev=a.s;
    if(a.i<k){low+=p-1;continue}
    let n=counts.get(a.i)||0;counts.set(a.i,n+1);ck(n+1<=1+Math.floor(U/(p-2)),"count");
    if(!n){first.set(a.i,ix);b.highFresh++}
    else{
     b.highRepeat++;let o=last.get(a.i),d=low-o.low,coeff=new Map(),big=0;
     for(let h=o.ix+1;h<ix;h++)if(path[h].i>=k){let m=path[h].i;ck(m!==a.i,"consecutive repeat");coeff.set(m,(coeff.get(m)||0)+1);big+=ps[m]-1}
     ck(a.oldg-path[o.ix].g===d+big&&d%2===0&&d+big>=p-1&&a.s-path[o.ix].s>=p-2,"repeat resource");
     let cs=[-1,1,3].filter(c=>mod(d+big-c,p)===0);ck(cs.length>0,"repeat congruence");
     let lastLabel=[a.i,...coeff.keys()].reduce((x,y)=>first.get(x)>first.get(y)?x:y);
     if(lastLabel===a.i){b.firstLastModulus++;ck((d+big-cs[0])%p===0&&d+big-cs[0]!==0,"modulus divisor")}
     else{b.firstLastSummand++;let n=coeff.get(lastLabel),q=ps[lastLabel];ck(n<p,"invertible count");ck(mod(n*(q-1)+d+big-n*(q-1)-cs[0],p)===0,"last summand")}
     let terminal=next(ix?path[ix-1].s:0,a.oldg,k).i<0;
     reps.push({i:a.i,d,terminal});b.terminalRepeats+=terminal;b.repeatSameHigh+=coeff.size===0;b.relations++;b.repeatLowGain+=d;b.repeatHighGain+=big;b.repeatTime+=a.s-path[o.ix].s;b.minRepeatLowGain=b.minRepeatLowGain===null?d:Math.min(b.minRepeatLowGain,d);b.maxRepeatLowGain=Math.max(b.maxRepeatLowGain,d);
    }
    last.set(a.i,{ix,low});
   }
   b.lowGain+=low;b.maxK=Math.max(b.maxK,first.size);b.repeatPaths+=reps.length>0;b.active+=active;
   let labels=[...counts.keys()];b.maxRepeatMultiplicity=Math.max(b.maxRepeatMultiplicity,...counts.values(),0);
   // Full bounded-coefficient modular support: actual repeat relations are in this conservative set.
   // Nonzero high coefficients can be arbitrary up to the per-label clock bound.
   let minimum=Infinity,dm=new Map();
   if(labels.length<=24){
    b.dpPaths++;
    for(let i of labels){
     let p=ps[i],reachable=new Set([0]);
     for(let q of labels)if(q!==i){
      let cap=1+Math.floor(U/(ps[q]-2)),r=new Set();
      for(let a of reachable)for(let n=0;n<=cap;n++){r.add(mod(a+n*(ps[q]-1),p));if(r.size===p)break}
      reachable=r;if(r.size===p)break;
     }
     let dmin=Infinity;
     for(let a of reachable)for(let c of [-1,1,3]){let d=mod(c-a,p);if(d%2)d+=p;dmin=Math.min(dmin,d)}
     ck(Number.isFinite(dmin)&&dmin%2===0,"support min");dm.set(i,dmin);minimum=Math.min(minimum,dmin);b.dpLabels++;
    }
    if(Number.isFinite(minimum))b.dpMin.push(minimum);
    for(let a of reps)ck(a.d>=dm.get(a.i),"relation lower bound");
    for(let x of b.caps){let bad=minimum<=x.R;x.badRelationPaths+=bad;x.certificateChecks++;x.repeatPathsWithCert+=!bad&&reps.length>0;if(!bad)ck(reps.length*x.R<=first.size*low,"global low resource")}
   }
   for(let x of b.caps){x.smallRepeat+=reps.filter(a=>a.d<=x.R).length;x.smallTerminalRepeat+=reps.filter(a=>a.terminal&&a.d<=x.R).length;}
   if(reps.length)b.actualMin.push(Math.min(...reps.map(a=>a.d)));
   let by=new Map();for(let a of reps)by.set(a.i,(by.get(a.i)||0)+a.d);
   ck([...by.values()].every(a=>a<=low),"disjoint low resource");b.countBoundChecks++;
  }
 }
 for(let b of out){for(let x of ["dpMin","actualMin"]){let a=b[x].sort((a,b)=>a-b);b[x]={n:a.length,min:a[0]??null,median:a[Math.floor(a.length/2)]??null,max:a.at(-1)??null}}}
 return {Y,T,U,V,N,rows:out}
}
for(const y of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(y)));
