// Reverse-horizon Kraft mass and expiry charging for canonical MIN [2B,4B) slab.
// Run: node research/min_clock_ancestry_kraft_audit.mjs 1024 4096 16384 65536 262144
function audit(X,variant='adaptive'){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,U=7*X+2,logU=Math.log(U);
 const check=(x,m)=>{if(!x)throw Error(m)};
 check(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(7*X+4);
 for(let p=2;p<spf.length;p++)if(!spf[p]){
  spf[p]=p;if(p*p<spf.length)for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 }
 let L=2,y=2;
 for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>6*Math.max(1,Math.log(Math.log(B)))**.25)break;L*=p;y=p;}
 if(variant==='noLOW'){L=2;y=2;}
 const thresholds=[Math.log(B)**1.75,4096,262144],logs=thresholds.map(Math.log),nModes=thresholds.length;
 const exact=X<=65536;
 const V=new Map(),key=(t,C)=>t*(7*X+4)+C;
 function get(t,C){
  const k=key(t,C);let v=V.get(k);
  if(!v){v={n:0,g:[0,0,0],edges:new Map(),good:[[],[],[]],exp:[[],[],[]],slab:[]};V.set(k,v);}
  return v;
 }
 const len=7*X/2+1, divisorCount=new Int16Array(len), divisorLog=new Float64Array(len);
 function probability(D,p){
  const i=D/2;if(!divisorCount[i]){
   for(let v of [D,D+2])while(v>1){const q=spf[v];if(q>B)break;if(q>y){divisorCount[i]++;divisorLog[i]+=Math.log(q);}while(v%q===0)v/=q;}
  }
  check(divisorCount[i]>0&&divisorLog[i]>=Math.log(p)-1e-10,'eligible reverse divisor');
  return .5/divisorCount[i]+.5*Math.log(p)/divisorLog[i];
 }
 const mass=new Float64Array(len),allW=new Float64Array(len);
 const G=thresholds.map(()=>new Int32Array(len)),GW=thresholds.map(()=>new Float64Array(len));
 const F=thresholds.map(()=>({gg:0,gb:0,bb:0,expiry:0,goodCost:0,maxGood:0,goodShared:0,goodCurrentShared:0,goodPairEnergyBound:0,goodHorizonEnergyRemoved:0,expiredPairCount:0,goodRootsAtStart:0}));
 let pairs=0,events=0,vertices=0,literal=0,R=0,finished=0;
 function hit(t,C,K){
  let T=K+1,P=0;
  for(const side of [-1,1]){
   let v=C+side;while(v>1){const p=spf[v];if(p>B)break;
    const m=2*p,res=side===-1?0:p+2,u=t+1+(res-(t+1)%m+m)%m;
    if(p>2&&(u<T||(u===T&&u<=K&&p<P))){T=u;P=p;}
    while(v%p===0)v/=p;
   }
  }return [T,P];
 }
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a};
 function visit(t,C,prev,i,b,last){
  const v=get(t,C),j=C/2;
  let e=prev===null?{n:0,g:[0,0,0]}:v.edges.get(prev);
  if(!e){e={n:0,g:[0,0,0]};v.edges.set(prev,e)}
  const fresh=v.n-e.n;pairs+=fresh;
  for(let m=0;m<nModes;m++){
   const good=b<=logs[m]+1e-12,priorGood=v.g[m]-e.g[m],priorBad=fresh-priorGood;
   check(priorGood>=0&&priorBad>=0,'first meet partition');
   if(good){F[m].gg+=priorGood;F[m].gb+=priorBad;v.g[m]++;e.g[m]++;v.good[m].push(i);last[m]=v;G[m][j]++;}
   else{F[m].gb+=priorGood;F[m].bb+=priorBad;}
  }
  mass[j]+=Math.exp(-b);v.n++;e.n++;vertices++;
  return v;
 }
 for(let M=X+1;M<2*X;M+=2){
  const i=(M-X-1)/2,s=M+2,C0=2*M-2,K=Math.floor((7*M-1)/4),last=[null,null,null];
  let t=s,C=C0,b=Math.log(variant==='log'?2*L:L),prev=null,lowGain=0,cost=0;
  for(let m=0;m<nModes;m++)if(b<=logs[m]+1e-12)F[m].goodRootsAtStart++;
  for(;;){
   const v=visit(t,C,prev,i,b,last);
   if(t>=s+H)break;
   const [u,p]=hit(t,C,K);
   if(X<=1024){
    let aa=K+1,bb=0;for(let j=t+1;j<=K;j++){
     const g=gcd(j%2?j-2:j,j%2?C+1:C-1);
     if(g>1&&spf[g]<=B){aa=j;bb=spf[g];break;}
    }check(aa===u&&bb===p,'literal MIN');literal++;
   }
   if(!p){check(spf[C-1]===C-1&&spf[C+1]===C+1,'terminal twin');finished++;break;}
   const r=Math.min(spf[C-1],spf[C+1]),ell=Math.max(0,Math.min(u-s,H)-Math.max(t-s,a)),w=ell/(2*r);
   check(u-t<=2*r&&C<=2*t,'clock invariant');
   if(ell){
    R+=ell/2;cost+=ell/2;allW[C/2]+=w;
    const good=logs.map(x=>b<=x+1e-12);
    v.slab.push({i,w,r,good});
    for(let m=0;m<nModes;m++)if(good[m]){GW[m][C/2]+=w;F[m].goodCost+=ell/2;}
   }
   const D=C+p-1;
   if(p<=y){lowGain+=p-1;check(lowGain<L,'LOW barrier');}
   else{
    check(D%p===0||(D+2)%p===0,'reverse horizon divisibility');
    b+=Math.log(variant==='log'?4*L*logU/Math.log(p):L/probability(D,p));lowGain=0;
   }
   prev=key(t,C);t=u;C=D;events++;
  }
  check(cost<=B,'slab cost');
  for(let m=0;m<nModes;m++)if(last[m])last[m].exp[m].push(i);
 }
 const sets=exact?thresholds.map(()=>new Set()):null;
 const choose=n=>n*(n-1)/2;
 let maxMass=0,E=0,shared=0,S0=0;
 for(let C=2*X;C<7*X;C+=2){
  const j=C/2,r=Math.min(spf[C-1],spf[C+1]);maxMass=Math.max(maxMass,mass[j]);
  check(mass[j]<=1+1e-8,'Kraft mass');
  if(r>B){check(allW[j]===0,'twin no occupation');continue;}
  S0+=r;E+=r*allW[j]**2;
  for(let m=0;m<nModes;m++){
   const f=F[m];check(G[m][j]<=thresholds[m]+1e-8,'good root cap');
   f.maxGood=Math.max(f.maxGood,G[m][j]);
   f.goodHorizonEnergyRemoved+=r*(2*allW[j]*GW[m][j]-GW[m][j]**2);
  }
 }
 for(const v of V.values()){
  for(let m=0;m<nModes;m++){
   const g=v.g[m],e=v.exp[m].length,f=F[m];
   check(g===v.good[m].length&&e<=g,'expiry subset');
   f.expiry+=e*(g-e)+choose(e);
   if(exact&&e){
    const exp=new Set(v.exp[m]);
    for(const i of v.exp[m])for(const j of v.good[m])if(i!==j&&(!exp.has(j)||i<j)){
     const k=Math.min(i,j)*N+Math.max(i,j);
     check(!sets[m].has(k),'unique expiry charge');sets[m].add(k);
    }
   }
  }
  if(v.slab.length){
   let total=0,diag=0;const r=v.slab[0].r;
   const wGood=[0,0,0],diagGood=[0,0,0];
   for(const e of v.slab){total+=e.w;diag+=e.w**2;for(let m=0;m<nModes;m++)if(e.good[m]){wGood[m]+=e.w;diagGood[m]+=e.w**2;}}
   shared+=r*(total*total-diag);
   for(let m=0;m<nModes;m++)F[m].goodCurrentShared+=r*(wGood[m]**2-diagGood[m]);
  }
 }
 // Expiry sets have to be complete before evaluating shared suffix, not dependent on Map order.
 if(exact){
  for(const f of F)f.goodShared=0;
  for(const v of V.values())if(v.slab.length)for(let i=0;i<v.slab.length;i++)for(let j=0;j<i;j++){
   const e=v.slab[i],b=v.slab[j],k=Math.min(e.i,b.i)*N+Math.max(e.i,b.i),w=2*e.r*e.w*b.w;
   for(let m=0;m<nModes;m++)if(sets[m].has(k))F[m].goodShared+=w;
  }
 }
 for(let m=0;m<nModes;m++){
  const f=F[m],tau=thresholds[m];
  check(f.gg+f.gb+f.bb===pairs&&f.gg===f.expiry,'exact first-meeting expiry identity');
  check(f.gg<=N*Math.max(0,Math.floor(tau)-1),'first pair count cap');
  f.goodPairEnergyBound=2*B*f.gg;
  check(f.goodHorizonEnergyRemoved<=2*tau*R+1e-7*Math.max(1,E),'energy removal cap');
  if(exact){check(sets[m].size===f.gg,'marked pair set');check(f.goodShared<=f.goodPairEnergyBound+1e-7*Math.max(1,E)&&f.goodShared+1e-7*Math.max(1,E)>=f.goodCurrentShared,'suffix pair energy');}
  else f.goodShared=null;
 }
 return {X,B,H,L,y,variant,thresholds,events,vertices,physical:V.size,pairs,literal,R,E,shared,S0,maxMass,finished,exact,F};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536,262144]){
 console.log(JSON.stringify(audit(X)));
 console.log(JSON.stringify(audit(X,'noLOW')));
 if(X<=16384)console.log(JSON.stringify(audit(X,'log')));
}
