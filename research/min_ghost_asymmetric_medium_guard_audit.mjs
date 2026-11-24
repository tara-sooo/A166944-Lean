// Asymmetric fresh-high/medium clock guards and restricted support audit.
function audit(Y,N=1024){
 const V=8*Y,T=Math.floor(Y*Math.sqrt(Math.log(Y))),z=Math.ceil(T**.96),P=Math.max(5,Math.ceil(T**.64)),v=Math.max(1,Math.floor(T**.22)),ps=[];
 for(let p=3;p<V;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const k=ps.findIndex(p=>p>=z),l=ps.findIndex(p=>p>=P),mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x3bc129ad^Y)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let lim=4294967296-4294967296%p,x;do{x=u32()}while(x>=lim);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length);
 let fresh=0,previousClock=0,actualMedium=0,actualFreshMedium=0,actualKnownMedium=0,finished=0,finishedNoMedium=0,initialFinish=0,initialHalf=0,initialResidual=0,tests=0,supportMax=0,supportSum=0,restrictedCandidates=0,badWeight=0,fullSupportMax=0,clockChecks=0,couplingChecks=0,terminalBad=0,mediumEvents=0,firstFresh=0;
 const caps=[v,Math.max(v,Math.floor(P/4))].filter((x,i,a)=>a.indexOf(x)===i).map(v=>({v,fresh:0,knownGuard:0,actualMedium:0,actualFreshMedium:0,actualKnownMedium:0,finished:0,finishedNoMedium:0,guardedFinished:0,initialFinish:0,initialHalf:0,initialResidual:0,terminalBad:0,tests:0,supportMax:0,supportSum:0,fullSupportMax:0,candidates:0,badWeight:0,checks:0}));
 for(let j=0;j<N;j++){
  let parity=uni(2);for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let b=uni(p);t[i]=b%2===parity?b:b+p}
  function next(e,g,k){let w=Infinity,i0=-1;for(let i=0;i<k;i++){let p=ps[i],cc=mod(c[i]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[i]+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i0])){w=f;i0=i}}return {w,i:i0}}
  function trace(e,g,k,cap){let a=[],s=e,h=g;for(;;){let x=next(s,h,k);if(x.i<0)return {done:true,events:a,dt:s-e,d:h-g};if(s+x.w>e+cap)return {done:false,events:a,dt:s-e,d:h-g};s+=x.w;h+=ps[x.i]-1;a.push({s,h,i:x.i})}}
  function clockIn(i,s,v){let p=ps[i];return Math.min(2*p-mod(t[i]+s,2*p),2*p-mod(t[i]+s-(p+2),2*p))<=v}
  function elig(i,g){let p=ps[i],cc=mod(c[i]+g,p);return cc===1||cc===p-1}
  let top=trace(0,0,ps.length,T+Math.max(...caps.map(b=>b.v))),history=top.events,first=history.find(a=>a.i>=k&&a.s<=T/2);
  let init=trace(0,0,k,Math.floor(T/2));for(let b of caps){b.initialHalf+=init.done;b.initialResidual+=!init.done&&!first;b.initialFinish+=trace(0,0,k,b.v).done}
  let seen=new Set(),oldg=0;
  for(let ix=0;ix<history.length;ix++){let a=history[ix];if(a.s>T)break;let i=a.i,s=a.s,g=a.h;
   if(i>=k&&!seen.has(i)){fresh++;let known=[...seen].filter(x=>x>=l),knownHigh=known.filter(x=>x>=k);
    for(let b of caps){
     b.fresh++;let v=b.v,guard=known.some(x=>clockIn(x,s,v));b.knownGuard+=guard;ck(v<ps[i]-2&&!clockIn(i,s,v),"own clock");
     let mid=history.slice(ix+1).filter(x=>x.s<=s+v&&x.i>=l),freshM=mid.some(x=>!seen.has(x.i)&&x.i!==i),knownM=mid.some(x=>seen.has(x.i)||x.i===i);
     b.actualMedium+=mid.length>0;b.actualFreshMedium+=freshM;b.actualKnownMedium+=knownM;ck(!knownM||guard,"known clock necessary");
     let suffix=trace(s,g,k,v),small=trace(s,g,l,v);
     if(!mid.length){ck(JSON.stringify(suffix.events)===JSON.stringify(small.events),"no medium suffix equivalence");b.checks++;}
     if(suffix.done){b.finished++;let nom=suffix.events.every(x=>x.i<l);b.finishedNoMedium+=nom;if(!mid.length){ck(nom&&suffix.d<=v*(P-1),"restricted gain");b.guardedFinished++;}
      if(nom&&(knownHigh.some(x=>elig(x,g+suffix.d))||elig(i,g+suffix.d)))b.terminalBad++;
     }
     if(b.tests<24){b.tests++;let restricted=new Set(),all=new Set();
      for(let q=k;q<ps.length;q++){if(seen.has(q))continue;let p=ps[q],x=trace(s,oldg+p-1,k,v);if(!x.done)continue;all.add(x.d);if(x.events.some(a=>a.i>=l))continue;ck(x.d<=v*(P-1)&&x.d%2===0,"counterfactual gain");restricted.add(x.d);b.candidates++;if(knownHigh.some(a=>elig(a,oldg+p-1+x.d))||(x.d-1)%p===0||(x.d+1)%p===0||(x.d-3)%p===0)b.badWeight+=1/p**2}
      ck(restricted.size<=1+Math.floor(v*(P-1)/2),"support");b.supportMax=Math.max(b.supportMax,restricted.size);b.supportSum+=restricted.size;b.fullSupportMax=Math.max(b.fullSupportMax,all.size);
     }
    }
   }
   seen.add(i);oldg=g;
  }
 }
 return {Y,V,T,z,P,N,fresh,caps};
}
for(const y of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(y,512)));
