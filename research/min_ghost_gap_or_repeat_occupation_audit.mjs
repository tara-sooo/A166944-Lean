// Low-terminal active occupation and gap-or-repeat test audit.
function audit(Y,N=512){
 const T=Math.floor(Y*Math.sqrt(Math.log(Y))),w=2*Y,U=T+w,V=8*Y,ps=[];
 for(let p=3;p<V;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 let rng=(0x31acb9df^Y)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let l=4294967296-4294967296%p,x;do{x=u32()}while(x>=l);return x%p}
 const mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)},c=new Int32Array(ps.length),t=new Int32Array(ps.length);
 const cutoffs=[Math.max(11,Math.ceil(Math.sqrt(U))),Math.max(11,Math.ceil(T**.8)),Math.max(11,Math.floor(Y/Math.sqrt(Math.log(Y))))].filter((x,i,a)=>a.indexOf(x)===i);
 const out=cutoffs.map(z=>({z,active:0,inactive:0,initialActive:0,freshActive:0,repeatActive:0,tests:0,gap:0,repeatOutcome:0,freshOutcome:0,noGapPaths:0,noGapActive:0,noGapInactive:0,noGapRepeat:0,noGapTests:0,halfInactive:0,halfInactiveNoGap:0,halfInactiveNoGapRepeat:0,highFresh:0,highRepeat:0,highRepeatBound:0,occupationChecks:0,trialChecks:0,weightedChecks:0,weightedCandidateMass:0,actualFreshActive:0,knownBlocked:0,knownQuiet:0,maxTests:0}));
 for(let j=0;j<N;j++){
  let parity=uni(2);for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let b=uni(p);t[i]=b%2===parity?b:b+p}
  function next(e,g,k){let n=Infinity,i0=-1;for(let i=0;i<k;i++){let p=ps[i],cc=mod(c[i]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[i]+e-(cc===1?0:p+2),2*p);if(f<n||(f===n&&p<ps[i0])){n=f;i0=i}}return {w:n,i:i0}}
  function lifetime(s,g,k,cap){let e=s,h=g;for(;;){let a=next(e,h,k);if(a.i<0)return e-s;if(e+a.w>s+cap)return cap;e+=a.w;h+=ps[a.i]-1}}
  let path=[],e=0,g=0,seen=new Set(),noGap=true;
  for(;;){let a=next(e,g,ps.length);if(e<=T&&a.w>w)noGap=false;if(e+a.w>U)break;e+=a.w;let oldg=g;g+=ps[a.i]-1;path.push({s:e,g,oldg,i:a.i,fresh:!seen.has(a.i)});seen.add(a.i)}
  for(let b of out){
   let k=ps.findIndex(p=>p>=b.z);if(k<0)k=ps.length;
   let active=0,inactive=0,initAct=0,freshAct=0,repeatAct=0,tests=0,reps=0,gaps=0,freshOut=0,highFresh=0,highRepeat=0,byPrime=new Map(),start=0,h=0,kind=0,activeUntil=lifetime(0,0,k,T),intervalActive=0;
   const known=new Set();
   for(let a of path)if(a.i>=k){let n=byPrime.get(a.i)||0;byPrime.set(a.i,n+1);if(n)highRepeat++;else highFresh++}
   let repBound=0;for(let [i,n] of byPrime){let cap=Math.floor(U/(ps[i]-2));ck(n-1<=cap,"repeat cap");repBound+=cap}
   b.highFresh+=highFresh;b.highRepeat+=highRepeat;b.highRepeatBound+=repBound;
   let events=[...path,{s:Infinity,g:NaN,i:-1,fresh:false}];e=0;g=0;
   for(let a of events){
    if(e>T)break;
    let len=Math.min(T,a.s)-e;if(len<0)throw Error("time");
    let lo=next(e,g,k),isActive=lo.i>=0;
    if(isActive){active+=len;intervalActive+=len;if(kind===0)initAct+=len;else if(kind===1)freshAct+=len;else repeatAct+=len;}
    else{
     inactive+=len;tests++;let deadline=a.s-e;
     if(deadline>w){gaps++;ck(!noGap,"gap")}
     else {ck(a.i>=k,"terminal next high");if(known.has(a.i))reps++;else freshOut++;}
     let knownMatch=Infinity;for(let i of known){if(i<k)continue;let p=ps[i],cc=mod(c[i]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[i]+e-(cc===1?0:p+2),2*p);knownMatch=Math.min(knownMatch,f)}
     if(knownMatch<=w)b.knownBlocked++;else b.knownQuiet++;
     // Exact event classification if no unused match before min(w,known clock).
     let unusedBefore=false,limit=Math.min(w,knownMatch);
     for(let i=k;i<ps.length;i++){if(known.has(i))continue;let p=ps[i],cc=mod(c[i]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[i]+e-(cc===1?0:p+2),2*p);if(f<=limit){unusedBefore=true;break}}
     if(!unusedBefore)ck(deadline>w||known.has(a.i),"gap or repeat");
     b.trialChecks++;
    }
    if(a.s>T||a.i>=k){ck(intervalActive===Math.min(Math.min(T,a.s)-start,activeUntil),"active prefix exact");b.occupationChecks++;intervalActive=0;
     if(a.s<=T){
      start=a.s;h=a.g;kind=known.has(a.i)?2:1;activeUntil=lifetime(start,h,k,T-start);
      if(kind===1){
       if(j<32){let sum=0;for(let i=k;i<ps.length;i++){if(known.has(i))continue;sum+=lifetime(start,a.oldg+ps[i]-1,k,T-start)/ps[i]**2;}b.weightedCandidateMass+=sum;b.actualFreshActive+=activeUntil;b.weightedChecks++;}
      }
     }
    }
    if(a.s>T)break;known.add(a.i);e=a.s;g=a.g;
   }
   ck(active+inactive===T&&initAct+freshAct+repeatAct===active&&tests===gaps+reps+freshOut,"conservation");
   if(noGap){ck(gaps===0&&inactive<=w*tests&&reps<=highRepeat,"no gap accounting");b.noGapPaths++;b.noGapActive+=active;b.noGapInactive+=inactive;b.noGapRepeat+=reps;b.noGapTests+=tests;if(inactive>=T/2){b.halfInactiveNoGap++;b.halfInactiveNoGapRepeat+=reps;}}
   b.halfInactive+=inactive>=T/2;b.active+=active;b.inactive+=inactive;b.initialActive+=initAct;b.freshActive+=freshAct;b.repeatActive+=repeatAct;b.tests+=tests;b.gap+=gaps;b.repeatOutcome+=reps;b.freshOutcome+=freshOut;b.maxTests=Math.max(b.maxTests,tests);
  }
 }
 return {Y,T,w,U,V,N,rows:out};
}
for(const y of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(y)));
