// Global seen-clock isolation, return-block absorption and signed active drift audit.
function audit(Y,N=512){
 const T=Math.floor(Y*Math.sqrt(Math.log(Y))),w=2*Y,U=T+w,V=8*Y,ps=[];
 for(let p=3;p<V;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const zs=[Math.max(11,Math.ceil(U/Math.log(U)**1.2)),Math.max(11,Math.ceil(T**.8))],mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x72ab91cd^Y)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let l=4294967296-4294967296%p,x;do{x=u32()}while(x>=l);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length);
 const out=zs.map(z=>({z,highFresh:0,repeat:0,termRepeat:0,lowActive:0,lowGain:0,highGain:0,negativeActive:0,positiveActive:0,blocks:0,clockPairs:0,minClockSeparation:null,checks:0,rows:[.5,.75,.9].map(a=>({R:Math.floor(U**a),certified:0,repeatCertified:0,relationGood:0,repeatGood:0,largeBlocks:0,slow:0,drop:0,noLargeRepeats:0,largeTouchedRepeats:0,boundChecks:0})),guards:[Math.max(1,Math.floor(U/Math.log(U)**3)),Math.max(1,Math.floor(U**.5))].map(v=>({v,badPaths:0,pairBad:0,actualHighClose:0,actualMediumClose:0,mediumBadPaths:0,mediumPairBad:0,actualChecks:0,mediumChecks:0}))}));
 for(let j=0;j<N;j++){
  let parity=uni(2);for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let b=uni(p);t[i]=b%2===parity?b:b+p}
  function next(e,g,k){let w=Infinity,i0=-1;for(let i=0;i<k;i++){let p=ps[i],cc=mod(c[i]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[i]+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i0])){w=f;i0=i}}return {w,i:i0}}
  let path=[],e=0,g=0;
  for(;;){let a=next(e,g,ps.length);if(e+a.w>U)break;e+=a.w;let oldg=g;g+=ps[a.i]-1;path.push({s:e,g,oldg,i:a.i})}
  const seenAll=new Set(path.map(a=>a.i));
  function clocks(i){let p=ps[i],a=[];for(let ph of [0,p+2]){let f=1+mod(ph-t[i]-1,2*p);for(let u=f;u<=U;u+=2*p)a.push(u)}return a.sort((a,b)=>a-b)}
  for(let b of out){
   let k=ps.findIndex(p=>p>=b.z);if(k<0)k=ps.length;
   const highSeen=[...seenAll].filter(i=>i>=k),mediumP=Math.max(5,Math.ceil(U**.65)),midSeen=[...seenAll].filter(i=>ps[i]>=mediumP&&ps[i]<b.z),K=highSeen.length,clockMap=new Map([...new Set([...highSeen,...midSeen])].map(i=>[i,clocks(i)]));
   let pairs=[],mediumPairs=[];
   for(let i of highSeen)for(let h of highSeen)if(i<h){let a=Infinity;for(let x of clockMap.get(i))for(let y of clockMap.get(h))a=Math.min(a,Math.abs(x-y));pairs.push(a);b.clockPairs++;if(Number.isFinite(a))b.minClockSeparation=b.minClockSeparation===null?a:Math.min(b.minClockSeparation,a)}
   for(let i of highSeen)for(let h of midSeen){let a=Infinity;for(let x of clockMap.get(i))for(let y of clockMap.get(h))a=Math.min(a,Math.abs(x-y));mediumPairs.push(a)}
   const blocks=[{gain:0,active:0,time:0,start:0}],last=new Map(),returns=[];let hG=0,lG=0,A=0,old=0,h=0,F=0,rep=0,term=0,highIx=[];
   for(let ix=0;ix<=path.length;ix++){
    let a=path[ix]||{s:U,i:-1,g:h,oldg:h},len=a.s-old,act=next(old,h,k).i>=0,bl=blocks.at(-1);bl.time+=len;if(act){bl.active+=len;A+=len}
    if(a.i<0)break;
    let p=ps[a.i];
    if(a.i<k){bl.gain+=p-1;lG+=p-1;}
    else{
     highIx.push(ix);hG+=p-1;
     if(last.has(a.i)){let st=last.get(a.i),end=blocks.length-1,d=blocks.slice(st,end+1).reduce((s,x)=>s+x.gain,0);rep++;term+=!act;returns.push({i:a.i,st,end,d});}
     else F++;
     blocks.push({gain:0,active:0,time:0,start:a.s});last.set(a.i,blocks.length-1);
    }
    h=a.g;old=a.s;
   }
   ck(blocks.length===1+F+rep&&F===K,"partition");
   ck(blocks.reduce((s,a)=>s+a.time,0)===U&&blocks.reduce((s,a)=>s+a.active,0)===A&&blocks.reduce((s,a)=>s+a.gain,0)===lG,"occupation");
   let net=blocks.reduce((s,a)=>s+2*a.active-a.gain,0);
   ck(2*U-h===2*(U-A)+net-hG&&h===hG+lG,"signed ledger");
   b.highFresh+=F;b.repeat+=rep;b.termRepeat+=term;b.lowActive+=A;b.lowGain+=lG;b.highGain+=hG;b.blocks+=blocks.length;b.negativeActive+=blocks.reduce((s,a)=>s+Math.max(0,a.gain-2*a.active),0);b.positiveActive+=blocks.reduce((s,a)=>s+Math.max(0,2*a.active-a.gain),0);
   for(let x of b.rows){
    if(!K)continue;
    const R=x.R,D=R/(2*K),big=blocks.map(a=>a.gain>D),large=big.filter(Boolean).length,slow=blocks.filter(a=>a.active>=D/4).length,drop=blocks.filter(a=>a.gain-2*a.active>D/2).length;
    ck(large<=slow+drop,"gain/duration dichotomy");x.largeBlocks+=large;x.slow+=slow;x.drop+=drop;
    // Verify on paths satisfying actual necessary return-gain bound, regardless of whether full relation-set certificate succeeds.
    if(returns.every(a=>a.d>R)){
     x.relationGood++;x.repeatGood+=rep;
     let touched=returns.filter(a=>big.slice(a.st,a.end+1).some(Boolean)),small=returns.filter(a=>!big.slice(a.st,a.end+1).some(Boolean));ck(touched.length<=K*large,"large charge");
     ck(small.length<=K*D*blocks.length/R+1e-8,"small charge");
     ck(rep<=2*K*large+F+1,"absorption");x.boundChecks++;x.noLargeRepeats+=small.length;x.largeTouchedRepeats+=touched.length;
    }
   }
   for(let a of b.guards){
    let v=Math.min(a.v,b.z-3),bad=pairs.some(x=>x<=v),mbad=bad||mediumPairs.some(x=>x<=v);a.badPaths+=bad;a.pairBad+=pairs.filter(x=>x<=v).length;a.mediumBadPaths+=mbad;a.mediumPairBad+=mediumPairs.filter(x=>x<=v).length;
    for(let ix of highIx){
     let q=path[ix];for(let h=ix+1;h<path.length&&path[h].s-q.s<=v;h++){
      if(path[h].i>=k){a.actualHighClose++;ck(bad,"global high isolation");}
      if(ps[path[h].i]>=mediumP){a.actualMediumClose++;ck(mbad,"global asymmetric isolation");}
     }
     if(!bad){a.actualChecks++;let a0=next(q.s,q.g,k); // No need to terminate; compare actual LOW prefix up to capped end.
      let e=q.s,g=q.g,ix2=ix+1,end=Math.min(U,q.s+v);
      for(;;){let x=next(e,g,k);if(e+x.w>end)break;e+=x.w;g+=ps[x.i]-1;let real=path[ix2++];ck(real&&real.s===e&&real.g===g&&real.i===x.i,"guarded prefix")}
      ck(ix2>=path.length||path[ix2].s>end,"prefix completeness");
     }
    }
   }
   b.checks++;
  }
 }
 return {Y,T,U,V,N,rows:out};
}
for(const y of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(y)));
