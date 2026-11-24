// Reverse depth, medium clock guard, and infinite CRT support witnesses.
function audit(Y,N=256){
 const V=8*Y,T=Math.floor(Y*Math.sqrt(Math.log(Y))),z=Math.ceil(T**.8),v=Math.max(1,Math.floor(z/4)),k=Math.max(1,Math.floor(Math.log(T)/Math.log(Math.log(T)))),r=Math.max(5,Math.floor(z/(2*k)));
 const ps=[];for(let p=3;p<V;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const low=ps.findIndex(p=>p>=z);let rng=(0x49b3d8a1^Y)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let l=4294967296-4294967296%p,x;do{x=u32()}while(x>=l);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)};
 let fresh=0,short=0,smallDepth=0,smallDepthGain=0,guard=0,mediumKnownBad=0,mediumFreshBad=0,mediumActualBad=0,ownBad=0,knownBad=0,reverseChecks=0,maxReverseDegree=0,maxFiber=0,fiberCases=0,histories=0,shortCandidates=0,maxActualDepth=0,depthTotal=0,maxGain=0,initialShort=0,initialDepth=0,terminalGood=0;
 for(let j=0;j<N;j++){
  let parity=uni(2);for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let a=uni(p);t[i]=a%2===parity?a:a+p}
  function next(e,g,limit){let w=Infinity,b=-1;for(let i=0;i<limit;i++){let p=ps[i],cc=mod(c[i]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[i]+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[b])){w=f;b=i}}return {w,b}}
  function suffix(e,g){let u=e,h=g,a=[];for(;;){let w=next(u,h,low);if(w.b<0)return {done:true,dt:u-e,d:h-g,a};if(u+w.w-e>v)return {done:false,dt:u-e,d:h-g,a};u+=w.w;h+=ps[w.b]-1;a.push({p:ps[w.b],h});}}
  function eligible(i,g){let x=mod(c[i]+g,ps[i]);return x===1||x===ps[i]-1}
  function clockIn(i,e,v){let p=ps[i];return Math.min(2*p-mod(t[i]+e,2*p),2*p-mod(t[i]+e-(p+2),2*p))<=v}
  let init=suffix(0,0);initialShort+=init.done;initialDepth+=init.done&&init.a.length<=k;
  let e=0,g=0,seen=new Set(),events=[];
  for(;;){let a=next(e,g,ps.length);if(a.b<0||e+a.w>T+v)break;let i=a.b,p=ps[i],g0=g;e+=a.w;g+=p-1;events.push({e,p,i,fresh:!seen.has(i),g0,g,prior:[...seen]});seen.add(i)}
  for(let f of events){if(f.e>T||!f.fresh||f.p<z)continue;fresh++;
   let l=suffix(f.e,f.g),known=f.prior.filter(i=>ps[i]>=r),oldHigh=f.prior.filter(i=>ps[i]>=z);
   let cb=known.some(i=>clockIn(i,f.e,v)),nb=events.some(a=>a.e>f.e&&a.e<=f.e+v&&a.fresh&&a.p>=r),actual=events.some(a=>a.e>f.e&&a.e<=f.e+v&&a.p>=r);
   mediumKnownBad+=cb;mediumFreshBad+=nb;mediumActualBad+=actual;ck(!actual||cb||nb,"medium guard");
   if(!cb&&!nb){guard++;ck(!l.a.some(a=>a.p>=r),"LOW ghost follows guarded path")}
   if(l.done){short++;maxActualDepth=Math.max(maxActualDepth,l.a.length);depthTotal+=l.a.length;maxGain=Math.max(maxGain,l.d);
    if(l.a.length<=k){smallDepth++;if(!cb&&!nb){smallDepthGain++;ck(l.d<=k*(r-1)&&l.d<f.p-1&&!eligible(f.i,f.g+l.d),"own exclusion");}
     if(eligible(f.i,f.g+l.d))ownBad++;if(oldHigh.some(i=>eligible(i,f.g+l.d)))knownBad++;else if(!cb&&!nb)terminalGood++;
    }
   }
   if(histories>=32)continue;histories++;
   let fibers=new Map(),used=new Set(f.prior),min=f.g0+z-1,max=f.g0+V+k*z;
   let degree=0;
   for(let h=min;h<=max;h+=2){let n=0;for(let i=0;i<low;i++){let p=ps[i],a=mod(c[i]+h,p);if(a===0||a===p-2)n++;}degree=Math.max(degree,n);}
   maxReverseDegree=Math.max(maxReverseDegree,degree);
   for(let i=low;i<ps.length;i++){if(used.has(i))continue;let q=ps[i],l=suffix(f.e,f.g0+q-1);if(!l.done||l.a.length>k)continue;shortCandidates++;
    for(let a of l.a){let p=a.p,idx=ps.indexOf(p),u=mod(c[idx]+a.h,p);ck(u===0||u===p-2,"reverse edge");reverseChecks++;}
    let h=f.g0+q-1+l.d;if(!fibers.has(h))fibers.set(h,[]);fibers.get(h).push(q);
   }
   for(let [h,qs] of fibers){fiberCases++;maxFiber=Math.max(maxFiber,qs.length);ck(qs.length<=(degree+1)**k,"reverse fiber");}
  }
 }
 return {Y,V,T,z,v,k,r,N,fresh,short,smallDepth,smallDepthGain,guard,mediumKnownBad,mediumFreshBad,mediumActualBad,ownBad,knownBad,reverseChecks,maxReverseDegree,maxFiber,fiberCases,histories,shortCandidates,maxActualDepth,depthTotal,maxGain,initialShort,initialDepth,terminalGood};
}
function supportAudit(z,N=64){
 let ps=[];for(let p=3;p<z;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const v=Math.floor(z**.75),lo=Math.ceil(z**.85),mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x6f9e1245^z)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let l=4294967296-4294967296%p,x;do{x=u32()}while(x>=l);return x%p}
 let eligible=ps.filter(p=>p>=lo&&p%15===1),sum=0,min=Infinity,max=0,verified=0,prefixCases=0,clockChecks=0,probSum=eligible.reduce((s,p)=>s+1/p,0);
 let c=new Int32Array(ps.length),t=new Int32Array(ps.length);
 for(let j=0;j<N;j++){
  let parity=uni(2),s=uni(2*z),g=2*uni(z*z);for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let a=uni(p);t[i]=a%2===parity?a:a+p}
  let prefix=mod(c[0]+g,3)===1,ell=prefix?6-mod(t[0]+s,6):0,d0=prefix?2:0;if(prefix)prefixCases++;
  let count=0;
  for(let p of eligible){let i=ps.indexOf(p),want=prefix?-3:-1,forbid=mod(c[i]+g-1,p);if(mod(want,p)===forbid)continue;let w=2*p-mod(t[i]+s+ell-(p+2),2*p);if(ell+w>v)continue;
   count++;clockChecks++;
   // Construct unit CRT residue for high q at every low prime. Verify intended full eligibility sequence.
   let states=prefix?[0,2,2+p-1]:[0,p-1],res=[];
   for(let a=0;a<ps.length;a++){
    let h=ps[a],bad=mod(c[a]+g-1,h),x=-1;
    if(h===3)x=prefix?1:0;else if(h===p)x=mod(want,h);else for(let b=0;b<h;b++){if(b===bad)continue;if(states.every(d=>{let u=mod(b+d,h);return u!==1&&u!==h-1})){x=b;break}}
    ck(x>=0&&x!==bad,"unit CRT");res.push(x);
   }
   for(let b=0;b<states.length;b++){let active=[];for(let a=0;a<ps.length;a++){let h=ps[a],u=mod(res[a]+states[b],h);if(u===1||u===h-1)active.push(h)}
    let expected=prefix&&b===0?[3]:b===states.length-2?[p]:[];ck(active.length===expected.length&&active.every((x,i)=>x===expected[i]),"exact itinerary");
   }verified++;
  }
  sum+=count;min=Math.min(min,count);max=Math.max(max,count);
 }
 return {z,v,lo,N,primeCandidates:eligible.length,reciprocal:probSum,meanSupportLower:sum/N,min,max,verified,prefixCases,clockChecks};
}
for(const y of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(y)));
for(const z of [997,4001,16001,32003])console.log(JSON.stringify(supportAudit(z)));
