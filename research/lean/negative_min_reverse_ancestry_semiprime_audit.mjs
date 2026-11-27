// Exact event-compressed reverse ancestry versus full forward enumeration; semiprime canonical controls.
// Run: node research/lean/negative_min_reverse_ancestry_semiprime_audit.mjs
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},mod=(a,m)=>(a%m+m)%m;
 const MAX=400010,spf=new Int32Array(MAX);
 for(let p=2;p<MAX;p++)if(!spf[p]){spf[p]=p;if(p*p<MAX)for(let j=p*p;j<MAX;j+=p)if(!spf[j])spf[j]=p}
 function fac(n){let f=[];while(n>1){let p=spf[n];ok(p>0,"factor bounds");f.push(p);while(n%p===0)n/=p}return f}
 function trial(n){let f=[];for(let p=3;p*p<=n;p+=2)if(n%p===0){f.push(p);while(n%p===0)n/=p}if(n>1)f.push(n);return f}
 function win(x,n){let s=mod(n,2)?-1:1;for(let p of fac(x+s))if(p>2&&mod(n,2*p)===(s===1?0:p+2))return p;return 0}
 function next(x,n){let w=Infinity,p=0,s=0;for(let t of [-1,1])for(let q of fac(x+t)){let u=mod((t===1?0:q+2)-n,2*q)||2*q;if(u<w||u===w&&q<p){w=u;p=q;s=t}}return {w,p,s}}
 function literal(x,n,w){let f=[trial(x+1),trial(x-1)];ok(f[0][0]===spf[x+1]&&f[1][0]===spf[x-1],"SPF oracle");for(let u=1;u<=w;u++){let t=n+u,sgn=mod(t,2)?-1:1;let hits=f[sgn===1?0:1].filter(p=>mod(t,2*p)===(sgn===1?0:p+2));if(hits.length)return {w:u,p:Math.min(...hits),s:sgn}}return null}
 function last(x,n){let out=-Infinity;for(let s of [-1,1])for(let p of fac(x+s)){let b=s===1?0:p+2;out=Math.max(out,n-mod(n-b,2*p))}return out}
 let rows=[],queries=0,localQueries=0,knownQueries=0,reverseStates=0,reverseEdges=0,reverseRejected=0,reverseBirths=0,reversePins=0,reverseMatches=0,forwardRoots=0,forwardEvents=0,resetSources=0,highSources=0,initialTicks=0,localCount=0,localReached=0,localMass=0,maxMass=0,nonresetChecks=0,depth=0,depthChecks=0,knownReached=0;
 for(let R of [12000,48000,192000]){
  let T=Math.ceil(8*Math.sqrt(2*R+1)),B=2*T,targets=new Map(),proxyP=Math.max(13,Math.floor(T/(Math.log(R)**2))),rs=0,hs=0;
  const add=(x,n,kind)=>{let k=x+","+n;if(!targets.has(k))targets.set(k,{x,n,kinds:new Set(),f:0});targets.get(k).kinds.add(kind)};
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   let p=spf[A+1],v=(A+1)/p;
   if(p<11||v<=4*p||spf[v]!==v||spf[A-1]<4*p||![1,7].includes(v%12))continue;
   // Deliberately finite proxy: actual p range is broad, not the asymptotic bands.
   if(p>Math.floor(R**.42))continue;
   let e=next(A,3-A/2),w=((v%4)*p-7)/2,l=literal(A,3-A/2,w);
   ok(l&&l.w===w&&l.p===p&&e.p===p&&e.w===w,"first actual semiprime firing");
   let x=A-p+1,n=3-A/2+w,h=x/2+n;
   ok(A%6===0&&x%6===0&&h===(v%4===1?0:p),"actual height");
   initialTicks+=w;
   if(v%4===1){resetSources++;rs++;if(Math.min(spf[x-1],spf[x+1])>=11){ok(literal(x,n,3)===null&&n+3===3-x/2,"canonical reset");add(x,n+3,"known");}}
   else{highSources++;hs++;nonresetChecks++;add(x,n,"known");
    let g=0,t=0;
    // finite control of actual short nonreset suffixes (not asymptotic low-label claim)
    for(let j=0;j<3;j++){let z=next(x,n);if(z.p>p/4||z.w>p/4)break;let ll=literal(x,n,z.w);ok(ll&&ll.p===z.p&&ll.w===z.w,"suffix literal");x-=z.p-1;n+=z.w;g+=z.p-1;t+=z.w;ok(x/2+n===p+t-g/2,"high height ledger");depthChecks++;add(x,n,"known");}
   }
  }
  // Same local proxy as last checkpoint. Test actual local recurrence first;
  // include all such local targets, not just those reached by the forward cohort.
  for(let p=proxyP;p<=2*proxyP;p++)if(spf[p]===p&&p%12===1)for(let v=Math.ceil((R+1)/p);v<=Math.floor((2*R+1)/p);v++){
   if(spf[v]!==v||v%12!==1||v<=p)continue;
   let a=p*v-1,x=p*(v-1);
   if(spf[a-1]<7||spf[x-1]<7||spf[x+1]<7||spf[x+1]===x+1)continue;
   for(let m=Math.ceil(T/(4*proxyP));m<=Math.floor(T/(3*proxyP));m++)if(m%2===0){
    let n=m*p-x/2,e=literal(a,n-8,8);
    if(!e||e.p!==p||e.w!==8||literal(x,n,3)!==null)continue;
    add(x,n,"local");localCount++;
   }
  }
  // Add arbitrary small sample of actual canonical states, including zero-event births.
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=600){let x=A,n=3-A/2;add(x,n,"known");for(let t=0;t<Math.min(T,80);t++){let p=win(x,n+1);x-=p?p-1:0;n++;if(t===79)add(x,n,"known")}}
  let byX=new Map();for(let q of targets.values()){if(!byX.has(q.x))byX.set(q.x,[]);byX.get(q.x).push(q)}
  let localForwardEvents=0;
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   let x=A,n=3-A/2,t=0;forwardRoots++;
   while(true){let e=next(x,n),span=Math.min(e.w-1,B-t);for(let q of byX.get(x)||[])if(n<=q.n&&q.n<=n+span)q.f++;
    if(t+e.w>B)break;
    x-=e.p-1;n+=e.w;t+=e.w;forwardEvents++;localForwardEvents++;
   }
  }
  let localR=0,localM=0,states0=reverseStates;
  for(let target of targets.values()){
   let upper=Math.min(2*R,2*(B+3-target.n));upper=6*Math.floor(upper/6);
   let earliest=3-upper/2,memo=new Map();
   function count(x,n,dep=0){
    if(x>upper||x/2+n<0||n<earliest||x<=2)return 0;
    let k=x+","+n;if(memo.has(k))return memo.get(k);
    reverseStates++;depth=Math.max(depth,dep);
    let ell=Math.max(last(x,n),earliest),sum=0,bt=3-x/2;
    if(x>=R&&x%6===0&&bt>=ell&&bt<=n){sum++;reverseBirths++}
    for(let s of [-1,1]){
     let b=s===1?0:3,c=1-s;
     for(let p of fac(x-c)){
      if(p===2)continue;
      let res=s===1?0:p+2,t0=ell+mod(res-ell,2*p);
      for(let t=t0;t<=n;t+=2*p){
       let y=x+p-1;if(y>upper||t-1<earliest||y/2+t-1<0)continue;
       ok(mod(x-c,p)===0&&mod(x/2+t-b,p)===0,"reverse pins");reversePins++;
       if(win(y,t)!==p){reverseRejected++;continue}
       reverseEdges++;
       sum+=count(y,t-1,dep+1);
      }
     }
    }
    memo.set(k,sum);return sum;
   }
   let r=count(target.x,target.n);
   ok(r===target.f,"forward/reverse mismatch "+JSON.stringify({R,x:target.x,n:target.n,r,f:target.f}));
   queries++;reverseMatches++;maxMass=Math.max(maxMass,r);
   if(target.kinds.has("known")){knownQueries++;ok(r>0,"known actual root");knownReached++}
   if(target.kinds.has("local")){localQueries++;if(r){localReached++;localR++;localMass+=r;localM+=r}}
  }
  rows.push({R,T,resetProxies:rs,nonresetProxies:hs,targets:targets.size,localTargets:[...targets.values()].filter(a=>a.kinds.has("local")).length,localReached:localR,localMass:localM,reverseStates:reverseStates-states0,forwardEvents:localForwardEvents});
 }
 // Exact exponent-level margins for the concrete proof, rational arithmetic.
 // nu in [.2855,.2856], level exponent .5713, distribution margin .0001.
 let a=2855n,b=2856n,d=5713n,e=1n,Q=10000n;
 ok(d>2n*b&&3n*(d+e)<2n*Q-b&&7n*b<2n*Q,"level margins");
 return {rows,queries,localQueries,knownQueries,reverseStates,reverseEdges,reverseRejected,reverseBirths,reversePins,reverseMatches,forwardRoots,forwardEvents,resetSources,highSources,initialTicks,localCount,localReached,localMass,maxMass,nonresetChecks,depth,depthChecks,knownReached,levelMargin:{scale:String(Q),sieve:String(d-2n*b),distributionNumerator:String(2n*Q-b-3n*(d+e)),distributionDenominator:String(3n*Q)}}
}
console.log(JSON.stringify(audit(),null,2));
