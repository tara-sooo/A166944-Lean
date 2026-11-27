// Primorial-barrier coarse entropy and exact transfer cancellation, actual Negative MIN.
// node research/min_local_negative_primorial_flux_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+5),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const f=x=>x?x*Math.log(x):0,phi=(a,b)=>f(a+b)-f(a)-f(b),add=(m,k,v)=>m.set(k,(m.get(k)||0)+v),sumF=m=>[...m.values()].reduce((s,v)=>s+f(v),0),ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 function processFlux(state,moves,t){
  const {Q,offset,counts}=state,cell=x=>Math.floor((x-offset)/Q);
  let edges=new Map(),out=new Map(),inc=new Map(),st=state.stats;
  for(const e of moves){
   let i=cell(e.a),j=cell(e.b);ck(j<=i,"monotone");
   if(Q%e.p===0){ck(i===j,["barrier",Q,e]);st.barrierChecks++}
   if(i===j)continue;
   ck(Q%e.p!==0,"crossing label");
   st.crossMass+=e.m;st.crossGain+=e.m*(e.a-e.b);st.crossBoundaries+=e.m*(i-j);
   let k=i+":"+j,v=edges.get(k);if(v)v.c+=e.m;else edges.set(k,{i,j,c:e.m});
   add(out,i,e.m);add(inc,j,e.m);
  }
  if(!edges.size)return;
  let touched=new Set([...out.keys(),...inc.keys()]),initial=0,final=0,mixing=0,splitting=0;
  for(let k of touched){
   let m=counts.get(k)||0,s=m-(out.get(k)||0),b=inc.get(k)||0;
   ck(s>=0,"stay mass");initial+=f(m);final+=f(s+b);
   mixing+=f(s+b)-f(s);splitting+=f(m)-f(s);
  }
  for(let e of edges.values()){mixing-=f(e.c);splitting-=f(e.c)}
  ck(mixing>=-1e-7&&splitting>=-1e-7,"merge/split nonnegative");
  let delta=final-initial;ck(Math.abs(delta-mixing+splitting)<1e-6,"contingency telescope");
  st.mixing+=mixing;st.splitting+=splitting;st.tickPositive+=Math.max(0,delta);
  // Source cells low-to-high: an actual outgoing group is transferred before any arrivals
  // from higher cells. Within source, choose destination low-to-high.
  let transfer=0,up=0,excess=0,positiveMass=0,logRatio=0;
  for(let e of [...edges.values()].sort((a,b)=>a.i-b.i||a.j-b.j)){
   let c=e.c,r=(counts.get(e.i)||0)-c,s=counts.get(e.j)||0;ck(r>=0,"transfer source");
   let d=phi(c,s)-phi(c,r);transfer+=d;
   if(s>r){
    up+=d;excess+=s-r;positiveMass+=c;
    let lr=c*Math.log((s+c)/(r+c))+c;logRatio+=lr;
    ck(d<=phi(c,s-r)+1e-7&&d<=lr+1e-7,"positive excess bounds");
    st.localExcessBound+=phi(c,s-r);
   }else ck(d<=1e-7,"nonpositive transfer");
   counts.set(e.i,r);counts.set(e.j,s+c);
   st.edges++;st.checks++;
  }
  ck(Math.abs(transfer-delta)<1e-6&&up>=Math.max(0,delta)-1e-7,"ordered transfer");
  st.net+=delta;st.edgePositive+=up;st.excess+=excess;st.positiveMass+=positiveMass;st.logRatio+=logRatio;st.checks++;
 }
 let rows=[];
 for(let R of Rs){
  let T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
  let controls=[6,30,210,2310].filter(Q=>Q<=2*T).map(Q=>({Q,offset:0,stats:{Q,offset:0,initial:0,final:0,fine:0,mixing:0,splitting:0,net:0,tickPositive:0,edgePositive:0,localExcessBound:0,crossMass:0,crossGain:0,crossBoundaries:0,positiveMass:0,excess:0,logRatio:0,edges:0,barrierChecks:0,checks:0}}));
  let fine=0,events=0,merges=0;
  for(let l=lo;l<=hi;l+=W){
   let maxA=Math.min(hi,l+W-6),start=3-maxA/2,n0=3-l/2,end=n0+T,active=new Map(),buckets=new Map();
   let states=controls.map(c=>({...c,counts:new Map()}));
   // Prebirth ghosts are stationary at their own A; thus no mass appears at birth.
   for(let A=l;A<=maxA;A+=6)for(let s of states)add(s.counts,Math.floor((A-s.offset)/s.Q),1);
   for(let s of states)s.stats.initial+=sumF(s.counts);
   const sched=(a,n,v)=>{const e=next(a,n),t=n+e.w;if(t<=end){let b=buckets.get(t)||[];b.push({a,p:e.p,v});buckets.set(t,b)}};
   for(let n=start;n<=end;n++){
    let arrivals=new Map(),moves=[];
    for(let e of buckets.get(n)||[]){
     let v=active.get(e.a);if(v!==e.v)continue;
     active.delete(e.a);let b=e.a-e.p+1;add(arrivals,b,v.m);moves.push({a:e.a,b,p:e.p,m:v.m});events++;
    }
    let A=2*(3-n);if(A>=l&&A<=maxA&&A%6===0)add(arrivals,A,1);
    for(let [a,m] of arrivals){
     let v=active.get(a);if(v){m+=v.m;merges++}
     let z={m};active.set(a,z);sched(a,n,z);
    }
    for(let s of states)processFlux(s,moves,n);
   }
   let fmass=new Map([...active].map(([a,v])=>[a,v.m]));fine+=sumF(fmass);
   for(let s of states){
    let actual=new Map();for(let [a,m] of fmass)add(actual,Math.floor((a-s.offset)/s.Q),m);
    ck([...actual].every(([k,v])=>s.counts.get(k)===v)&&[...s.counts].every(([k,v])=>(actual.get(k)||0)===v),"final coarse replay");
    s.stats.final+=sumF(actual);s.stats.checks++;
   }
  }
  for(let {Q,stats:s} of controls){
   ck(Math.abs(s.initial+s.net-s.final)<1e-6*N,"global net");
   ck(s.final>=fine-1e-6*N&&s.final-fine<=N*Math.log(Q/2)+1e-6*N,"fine/coarse entropy");
   ck(s.initial<=N*Math.log(Q/6)+1e-6*N,"initial root spacing");
   ck(s.edgePositive<=s.localExcessBound+1e-6*N&&s.localExcessBound<=N*phi(s.positiveMass/N,s.excess/N)+1e-6*N,"aggregate bound");
   for(let k of ["initial","final","mixing","splitting","net","tickPositive","edgePositive","localExcessBound","crossMass","crossGain","crossBoundaries","positiveMass","excess","logRatio"])s[k]/=N;
   s.fine=fine/N;s.globalExcessBound=phi(s.positiveMass,s.excess);s.excessCoarse=s.final-s.fine;
  }
  rows.push({R,T,N,events,merges,controls:controls.map(c=>c.stats)});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000,1000000,2000000]),null,2));
