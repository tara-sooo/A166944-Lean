// First primorial-cell exit: pre-exit stationary certificate and actual statistics.
// node research/min_local_negative_first_cell_exit_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+5),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},add=(m,k,v=1)=>m.set(k,(m.get(k)||0)+v);
 let rows=[];
 for(let R of Rs){
  let S=Math.sqrt(2*R+1),T=Math.ceil(S),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1,L=Math.log(S);
  let widths=[6,30,210,2310].filter(Q=>Q<=2*T),stats=widths.map(Q=>({Q,exit:0,noExit:0,preWeight:0,boundWeight:0,bestWeight:0,exitLabel:0,exitAge:0,largeExit:[0,0,0,0],largeGood:[0,0,0,0],visited:new Set(),pre:new Map(),best:new Map(),cells:new Map(),checks:0,exitSmall:0}));
  let w=q=>{q=Math.max(3,Math.min(S,q));let d=Math.log(S/q);return (Math.log(q)/L)**2/((1+d)*(1+Math.log1p(d))**2)};
  const q=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1);
  let thresholds=[R**.125,R**.25,R**.375,S/4];
  for(let A=lo;A<=hi;A+=6){
   let birth=3-A/2,end=birth+T,a=A,n=birth,G=0;
   let live=stats.map(s=>({s,b:Math.floor(A/s.Q)*s.Q,best:A,done:false}));
   for(;;){
    let e=next(a,n),fire=n+e.w,b=a-e.p+1;
    for(let v of live)if(!v.done){
     let s=v.s,Q=s.Q;ck(a>=v.b&&a<v.b+Q&&A-a===G,"cell confinement");
     if(q(a)>q(v.best))v.best=a;s.visited.add(a);
     let exit=fire<=end&&b<v.b,terminal=fire>end;
     if(exit||terminal){
      v.done=true;let prior=n-birth;
      ck(prior<=3*G&&G<=Q-2,"prior gain and time");
      let lower;
      if(exit){
       ck(Q%e.p!==0,"small prime barrier");
       ck(fire+b/2>=0,"height");
       lower=Math.max(3,(e.p-1)/4-1.25*G-1.5);
       ck(e.w>= (e.p-1)/2-2.5*G-3-1e-8&&q(a)>=lower-1e-8,"first exit wait");
       s.exit++;s.exitLabel+=e.p;s.exitAge+=fire-birth;s.exitSmall+=+(e.p<=10*Q);
      }else{
       lower=Math.max(3,(T-3*G)/2);ck(q(a)>=lower-1e-8,"terminal wait");s.noExit++;
      }
      s.preWeight+=w(q(a));s.boundWeight+=w(lower);s.bestWeight+=w(q(v.best));add(s.pre,a);add(s.best,v.best);
      let z=s.cells.get(v.b)||0;s.cells.set(v.b,Math.max(z,w(q(v.best))));
      for(let i=0;i<thresholds.length;i++){if(exit&&e.p>=thresholds[i])s.largeExit[i]++;if(!exit||e.p>=thresholds[i])s.largeGood[i]++;}
      s.checks++;
     }
    }
    if(live.every(v=>v.done))break;
    ck(fire<=end,"unfinished path");G+=e.p-1;a=b;n=fire;
   }
  }
  let cap=0,twins=0;for(let a=2*Math.ceil((lo-3*T-6)/2);a<=hi;a+=2){if(a<4)continue;if(q(a)<=S)cap+=w(q(a));else twins++}
  for(let s of stats){
   const M=s.Q/6;
   let preSupport=0,bestSupport=0,visitedSupport=0,maxFiber=0;
   for(let [a,m] of s.pre){ck(m<=M,"pre-exit multiplicity");preSupport+=w(q(a));maxFiber=Math.max(maxFiber,m);}
   for(let [a,m] of s.best){ck(m<=M,"best multiplicity");bestSupport+=w(q(a));}
   for(let a of s.visited)visitedSupport+=w(q(a));
   const cellCert=[...s.cells.values()].reduce((t,x)=>t+x,0);
   ck(preSupport+1e-8>=s.preWeight/M&&bestSupport+1e-8>=s.bestWeight/M&&bestSupport+1e-8>=cellCert&&visitedSupport+1e-8>=bestSupport,"support certificate");
   s.summary={Q:s.Q,M,N,exitFrac:s.exit/N,noExitFrac:s.noExit/N,smallExitFrac:s.exitSmall/N,largeExit:s.largeExit.map(x=>x/N),largeGood:s.largeGood.map(x=>x/N),meanExitLabel:s.exitLabel/s.exit,meanExitAge:s.exitAge/s.exit,meanPreWeight:s.preWeight/N,meanBoundWeight:s.boundWeight/N,meanBestWeight:s.bestWeight/N,lowerSupport:s.boundWeight/M,preSupport,bestSupport,cellCert,visitedSupport,maxFiber,checks:s.checks};
  }
  rows.push({R,S,T,N,thresholds,cap,twins,controls:stats.map(s=>s.summary)});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000,1000000,2000000]),null,2));
