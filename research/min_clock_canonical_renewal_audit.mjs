// Canonical renewal graph, even reset bridge and light near-renewal departure gain.
// Run node research/min_clock_canonical_renewal_audit.mjs 1024 4096 16384 65536
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,startAge=mode==='full'?0:mode==='early'?B:2*B,a=startAge,N=X/2,G=2*H+B+6,U=7*X+4,W=16*B,u=Math.log(B),ell=Math.log(u);
 const ok=(b,m)=>{if(!b)throw Error(m);};
 ok(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(U);
 for(let p=2;p<U;p++)if(!spf[p]){spf[p]=p;if(p*p<U)for(let j=p*p;j<U;j+=p)if(!spf[j])spf[j]=p;}
 let z=2,L=2;
 if(mode==='analytic'){for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>B**(1/16))break;L*=p;z=p;}}
 else {z=3;L=6;}
 const T=mode==='analytic'?Math.max(z+1,Math.ceil(B**.25)):Math.ceil(Math.sqrt(B));
 const mH=mode==='analytic'?Math.max(1,Math.floor(u**2.75)):mode==='diagnostic'||mode==='stress'?8:16;
 const mM=mode==='analytic'?Math.max(1,Math.floor(B**.625)):mode==='diagnostic'||mode==='stress'?12:24;
 const D0=mode==='analytic'?Math.ceil(40*ell)+1:4;
 const lo=X,hi=7*X/2-1,len=hi+1,r=new Int32Array(len),degrees=new Uint8Array(len);
 function fac(n,cb){while(n>1){const p=spf[n];if(p>B)break;if(p>2)cb(p);while(n%p===0)n/=p;}}
 let rare=0,maxDegree=0;
 for(let j=lo;j<=hi;j++){const q=Math.min(spf[2*j-1],spf[2*j+1]);if(q<=B)r[j]=q;for(const C of [2*j,2*j+2])fac(C,()=>degrees[j]++);maxDegree=Math.max(maxDegree,degrees[j]+1);rare+=+(degrees[j]+1>D0);}
 function hit(t,C,K){let v=K+1,p=0;for(const side of [-1,1])fac(C+side,q=>{const m=2*q,res=side===-1?0:q+2,w=t+1+(res-(t+1)%m+m)%m;if(w<v||(w===v&&w<=K&&q<p)){v=w;p=q;}});return [v,p];}
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a;};
 const paths=[],at=new Map(),W0=new Float64Array(len),WM=new Float64Array(len),WH=new Float64Array(len);
 let R=0,RM=0,RH=0,events=0,literal=0,twins=0;
 for(let i=0;i<N;i++){const M=X+1+2*i,s=M+2,K=Math.floor((7*M-1)/4),path=[];let t=s,C=2*M-2,inc=0,rr=0;
  for(;;){const e={i,M,C,t,inc,p:0,w:0};path.push(e);let row=at.get(C);if(!row){row=[];at.set(C,row);}row.push(e);
   ok(C<=2*t&&C-(2*M-2)<=G,'prefix gain');
   if(t>=s+H)break;
   const [v,p]=hit(t,C,K);
   if(X===1024){let vv=K+1,pp=0;for(let j=t+1;j<=K;j++){const n=gcd(j%2?j-2:j,j%2?C+1:C-1);if(n>1&&spf[n]<=B){vv=j;pp=spf[n];break;}}ok(v===vv&&p===pp,'literal');literal++;}
   if(!p){ok(!r[C/2]&&spf[C-1]===C-1&&spf[C+1]===C+1,'twin');twins++;break;}
   const q=r[C/2],cost=Math.max(0,Math.min(v,s+H)-Math.max(t,s+a))/2;
   ok(v-t<=2*q&&q<=p,'wait');e.p=p;e.w=cost/q;rr+=cost;R+=cost;W0[C/2]+=e.w;
   if(p>z&&p<=T){RM+=cost;WM[C/2]+=e.w;}if(p>T){RH+=cost;WH[C/2]+=e.w;}
   t=v;C+=p-1;inc=p;events++;
  }
  ok(rr<=(H-startAge)/2,'root cost');paths.push(path);
 }






 const L0=mode==='analytic'?Math.floor(u**.125):mode==='wide'?12:4;
 const Y=mode==='analytic'?Math.max(17,Math.ceil(B**.125)):mode==='wide'?7:17;
 const Q=Math.max(Y,10*L0+16),m=mode==='analytic'?Math.floor(u**2.75):mode==='wide'?8:2;
 const eps0=mode==='analytic'?u**(-1/16):mode==='wide'?.05:.1;
 const bridge=(J)=>{let k=0,labels=[];while(J%3===2||J%5===1){if(J%3===2)labels.push(3,3);else labels.push(5);J+=4;k++;ok(k<=2,'even bridge length');}return {J,t:J/2+3,k,labels};};
 let bridgeChecks=0,maxBridge=0,bridgeActual=0,bridgeCut=0,bridgeTwin=0,virtual=0,canonical=0,renewalInc=0,elementaryInc=0,directCheck=0,nearCheck=0;
 for(let J=2*X;J<7*X-20;J+=4){
  const b=bridge(J);let t=J/2,C=J;
  for(const p of b.labels){const [v,q]=hit(t,C,t+3);ok(p===q&&v-t===(p===3?1:2),'even bridge explicit event');t=v;C+=p-1;}
  ok(C===b.J&&t+3===b.t&&!hit(t,C,t+3)[1],'even bridge quiet suffix');bridgeChecks++;maxBridge=Math.max(maxBridge,b.k);
 }
 const actualVisits=[],basins=new Map(),arcs=new Map(),renew=new Map(),elementary=new Map(),groups=new Map(),rootGroups=Array.from({length:N},()=>[]),canRoots=new Set();
 let rawGain=[0,0],rawClock=[0,0],origFirst=0,origFirstHigh=0;
 for(const path of paths){
  const root=path[0],cut=root.t+H,cs=[];
  for(let j=0;j<path.length;j++){
   const e=path[j],n=path[j+1],v=e.C/2+3;
   if(e.C%4===0&&e.t<=v&&v<=cut&&((n&&v<n.t)||!n&&v===e.t)){
    const M=e.C/2+1;ok(M%2===1&&v===M+2,'canonical odd source');
    cs.push({j,t:v,M,C:e.C});canonical++;virtual+=+(v!==e.t);canRoots.add(M);
    if(n){const [tt,p]=hit(v,e.C,Math.floor((7*root.M-1)/4));ok(tt===n.t&&p===n.inc,'canonical replay');}
   }
  }
  ok(cs.length&&cs[0].M===root.M,'original canonical start');
  actualVisits.push(cs.map(v=>v.M));
  for(const v of cs){let b=basins.get(v.M);if(!b){b=[];basins.set(v.M,b);}b.push(root.M);}
  // Store clock segments of a single deterministic arc, independently of tags.
  // Actual segment ledger on the original tags includes virtual roots inside waits.
  let cur=0;
  function segment(c,C,l,h,w){
   if(h<=l)return;
   let a=arcs.get(c);if(!a){a=new Map();arcs.set(c,a);}let e=a.get(C);
   if(!e){e={l,h,w:0};a.set(C,e);}else{ok(e.l===l,'canonical arc common left endpoint');e.h=Math.max(e.h,h);}
   e.w+=w;
  }
  for(let j=0;j+1<path.length;j++){
   const e=path[j],n=path[j+1],q=r[e.C/2],l=e.t,h=Math.min(n.t,cut);
   if(h<=l)continue;
   const mark=cur+1<cs.length&&cs[cur+1].j===j?cs[cur+1]:null;
   const mid=mark?mark.t:h;
   const w=(a,b)=>Math.max(0,Math.min(b,cut)-Math.max(a,root.t+2*B))/(2*q);
   if(mark){segment(cs[cur].M,e.C,l,mid,w(l,mid));cur++;segment(cs[cur].M,e.C,mid,h,w(mid,h));}
   else segment(cs[cur].M,e.C,cur===0&&j===0?root.t:l,h,w(l,h));
  }
  const byC=new Set(cs.map(v=>v.C));
  for(let j=0;j<path.length;j++){const e=path[j];if(e.t%2||2*e.t!==e.C)continue;const b=bridge(e.C);
   if(b.t>cut){bridgeCut++;continue;}
   if(b.t>path[path.length-1].t){bridgeTwin++;continue;}
   ok(byC.has(b.J),'actual even reset reaches canonical bridge');bridgeActual++;
  }
  for(let i=1;i<cs.length;i++){
   const a=cs[i-1],b=cs[i],d=b.M-a.M;
   ok(d>0&&d%2===0&&b.t-a.t===d&&b.C-a.C===2*d,'renewal displacement');
   const prev=renew.get(a.M);ok(prev===undefined||prev===b.M,'unique first return map');renew.set(a.M,b.M);renewalInc++;
   let gain=0;for(let j=a.j;j<b.j;j++)gain+=path[j+1].inc-1;
   ok(gain===2*d,'renewal gain identity');
   const p=path[a.j+1].inc,post=path[a.j+1],s=post.t%2;
   if(p>=Y&&2*post.t-post.C===6*s){
    const dest=s?post.C/2+1:bridge(post.C).J/2+1;
    ok(dest===b.M,'elementary high return destination');const k=s?0:bridge(post.C).k;
    ok(s?b.M%p===0:(b.M-1-2*k)%p===0,'elementary inverse divisor');
    const id=a.M+':'+b.M;const old=elementary.get(id);ok(!old||old.p===p,'fixed elementary edge');elementary.set(id,{M:a.M,dest:b.M,p,s,k});elementaryInc++;
   }
  }
  let ci=0;
  for(let j=0;j+1<path.length;j++){
   if(ci+1<cs.length&&cs[ci+1].j===j)ci++;
   const a=cs[ci],e=path[j],n=path[j+1],p=n.inc,g=e.C-a.C;
   ok(a.j<=j&&g>=0,'latest canonical');
   let type=-1;if(g===0)type=0;else if(g<=L0&&p>=Q)type=1;
   if(type<0)continue;
   const t0=j===a.j?a.t:e.t,w=n.t-t0,ds=2*t0-e.C;
   ok(w>0&&w<=2*r[e.C/2]&&ds<=6+5*g,'departure wait and deficit');
   if(type===0){ok((2*w+(n.t%2?1:7))%p===0,'direct departure divisor');directCheck++;}
   else nearCheck++;
   if(p>=Math.max(17,10*g+16))ok(w>=p/4&&r[e.C/2]>=p/8,'rough near departure');
   if(type===0&&j===0){origFirst+=p-1;origFirstHigh+=+(p>=Y);}
   const id=type+':'+a.M;let row=groups.get(id);
   if(!row){row={id,type,M:a.M,D:e.C,p,n:0,gain:0,clock:0};groups.set(id,row);}
   ok(row.D===e.C&&row.p===p,'unique canonical departure per type');
   row.n++;row.gain+=p-1;row.clock+=r[e.C/2]*e.w;rootGroups[root.i].push(row);
   rawGain[type]+=p-1;rawClock[type]+=r[e.C/2]*e.w;
  }
 }
 // Independent enumerate actual canonical starts, including starts outside source interval.
 // Only arithmetic roots with a first event in the allowed pre-gain window are needed.
 const sums=[0,0],support=[0,0],seen=new Set();
 for(let C=2*X;C<7*X;C+=4){let t=C/2+3,D=C,M=C/2+1;
  for(let j=0;D-C<=L0;j++){
   const [v,p]=hit(t,D,t+2*B);if(!p)break;
   const g=D-C,type=g===0?0:g<=L0&&p>=Q?1:-1;
   if(type>=0){const id=type+':'+M;seen.add(id);sums[type]+=p-1;support[type]++;const row=groups.get(id);if(row)ok(row.D===D&&row.p===p,'independent departure replay');}
   if(p-1>L0-g)break;
   t=v;D+=p-1;if(D>=7*X)break;
  }
 }
 const thinGain=[0,0],thinClock=[0,0],thinN=[0,0],groupN=[0,0],maxMass=[0,0],weightedSupport=[0,0];
 for(const g of groups.values()){
  ok(seen.has(g.id)&&g.gain===g.n*(g.p-1),'actual group in replay support');
  groupN[g.type]++;maxMass[g.type]=Math.max(maxMass[g.type],g.n);weightedSupport[g.type]+=g.p-1;
  if(g.n<=m){thinN[g.type]++;thinGain[g.type]+=g.gain;thinClock[g.type]+=g.clock;}
 }
 for(let b=0;b<2;b++)ok(thinGain[b]<=m*sums[b]&&weightedSupport[b]<=sums[b],'thin gain support');
 const counts=new Map([...groups].map(([id,g])=>[id,g.n])),charges=new Map(),deleted=new Uint8Array(N);
 let removed=0,rounds=0,chargedGain=0,chargedClock=0;
 for(;;){let changes=0;for(let i=0;i<N;i++){if(deleted[i])continue;const gs=rootGroups[i],thin=gs.filter(g=>counts.get(g.id)<=m),cost=thin.reduce((s,g)=>s+g.p-1,0);if(cost<eps0*B)continue;
  for(const g of thin){const k=(charges.get(g.id)||0)+1;ok(k<=m,'lifetime departure charge');charges.set(g.id,k);chargedGain+=g.p-1;}
  deleted[i]=1;removed++;changes++;for(const g of gs){const n=counts.get(g.id);ok(n>0,'active group count');counts.set(g.id,n-1);}
  }if(!changes)break;rounds++;
 }
 let retainedThin=0,retainedThick=0,maxRootThin=0;const remain=[0,0];
 for(let i=0;i<N;i++)if(!deleted[i]){let n=0;for(const g of rootGroups[i]){ok(counts.get(g.id)>0,'retained group');if(counts.get(g.id)<=m){n+=g.p-1;remain[g.type]+=g.p-1;}else retainedThick+=g.p-1;}ok(n<eps0*B,'peel fixed point');retainedThin+=n;maxRootThin=Math.max(maxRootThin,n);}
 ok(chargedGain>=removed*eps0*B-1e-8&&chargedGain<=m*(sums[0]+sums[1])&&retainedThin<=eps0*B*(N-removed),'peeling bound');
 // Reconstruct every tag's canonical history solely from the first-return
 // graph and its absolute source cutoff. Reconstruct arc occupancy from ancestor lists.
 let mapChecks=0,basinChecks=0,arcChecks=0,arcR=0,arcE=0,arcSelf=0,maxBasin=0,nonemptyArcs=0;
 const reconstructed=new Map(),byHorizon=new Float64Array(len);
 for(let i=0;i<N;i++){const M=X+1+2*i,actual=actualVisits[i],got=[M];let x=M;
  while(renew.has(x)&&renew.get(x)<=M+H){x=renew.get(x);got.push(x);}
  ok(got.length===actual.length&&got.every((v,j)=>v===actual[j]),'return map exact composition');
  for(const c of got){let a=reconstructed.get(c);if(!a){a=[];reconstructed.set(c,a);}a.push(M);mapChecks++;}
 }
 for(const [c,bs] of basins){const b=reconstructed.get(c);ok(b&&b.length===bs.length&&b.every((v,i)=>v===bs[i]),'exact sliding basin');
  for(const M of bs)ok(M<=c&&M>=c-H,'basin age interval');basinChecks++;maxBasin=Math.max(maxBasin,bs.length);
 }
 for(const [c,rows] of arcs){const bs=reconstructed.get(c);let has=false;
  for(const [C,e] of rows){const q=r[C/2];let sum=0;
   for(const M of bs)sum+=Math.max(0,Math.min(e.h,M+2+H)-Math.max(e.l,M+2+2*B))/(2*q);
   ok(Math.abs(sum-e.w)<=1e-7*Math.max(1,sum),'arc ancestor interval convolution');
   byHorizon[C/2]+=sum;arcR+=q*sum;arcSelf+=q*sum*sum;arcChecks++;has||=sum>0;
  }nonemptyArcs+=+has;
 }
 let E=0;for(let j=lo;j<=hi;j++){ok(Math.abs(byHorizon[j]-W0[j])<=1e-7*Math.max(1,W0[j]),'arc reconstruction full occupation');arcE+=r[j]*byHorizon[j]**2;E+=r[j]*W0[j]**2;}
 ok(Math.abs(arcR-R)<=1e-6*Math.max(1,R)&&Math.abs(arcE-E)<=1e-6*Math.max(1,E)&&arcSelf<=E+1e-6*Math.max(1,E),'exact reconstructed energy');
 const inv=new Map();let maxIn=0;for(const a of elementary.values()){let s=inv.get(a.dest);if(!s){s=new Set();inv.set(a.dest,s);}s.add(a.M);maxIn=Math.max(maxIn,s.size);}
 for(const [M,s] of inv){let cap=0;for(const n of [M,M-1,M-3,M-5])fac(n,p=>{if(p>=Y)cap++;});ok(s.size<=cap,'elementary inverse degree');}
 return {mapChecks,basinChecks,arcChecks,arcR,arcE,arcSelf,maxBasin,nonemptyArcs,X,B,mode,L0,Y,Q,m,eps0,N,R,events,literal,bridgeChecks,maxBridge,bridgeActual,bridgeCut,bridgeTwin,canonical,virtual,canonicalKeys:canRoots.size,renewalInc,renewalKeys:renew.size,elementaryInc,elementaryKeys:elementary.size,maxIn,directCheck,nearCheck,origFirst,origFirstHigh,rawGain,rawClock,sums,support,groupN,maxMass,weightedSupport,thinN,thinGain,thinClock,removed,rounds,chargedGain,retainedThin,retainedThick,remain,maxRootThin};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','wide'])console.log(JSON.stringify(audit(X,mode)));
