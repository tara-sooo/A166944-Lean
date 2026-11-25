// Exact finite canonical first-return graph and initial-clock density audit.
function audit(N=200000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const gcd=(a,b)=>{b=Math.abs(b);while(b)[a,b]=[b,a%b];return Math.abs(a)},mod=(a,b)=>(a%b+b)%b;
 const primes=n=>{let a=[];for(let p=3;p<=n;p+=2)if(spf[p]===p)a.push(p);return a};
 const isPrime=p=>p>=2&&spf[p]===p;
 function tick(n,H){let e=n%2?-1:1,g=gcd(e===1?n:n-2,H-e);if(g===1)return 0;let p=spf[g];return p*p<=H+1?p:0}
 function next(t,H){let best=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}}return best}
 function wait(p,e){let a=e===1?3:1;for(let j=e===1?1:2;j<=2*p;j+=2)if(mod(2*j+(e===1?7:1),p)===0)return j;throw Error("wait")}
 function formal(M,T,trace=false){let E=0,first=0;for(let j=1;j<=T;j++){let g=j%2?gcd(M+j+2,2*j+7-E):gcd(M+j,2*j+1-E),p=g===1?0:spf[g];if(p){E+=p-1;if(!first)first=j}if(E>2*j+6)throw Error("envelope");if(j%2===0&&E===2*j)return {gap:j,first};}return {gap:0,first}}
 let s={N,steps,events:0,roots:0,reentries:0,sourcePrimeTests:0,sourcePrimeReentries:0,primeTargets:0,abstractPredecessorChecks:0,firstWaitChecks:0,formalComparisons:0,edges:0,undefinedWithinCap:0,terminalBeforeReturn:0,edgeCollisionExcess:0,zeroIndegree:0,crossingEdges:0,completePeriodTests:0,periods:[],examples:{},maxFiniteGap:0};
 for(let T of [2,4,6]){
  let ps=primes(2*T+7),P=ps.reduce((a,p)=>a*p,1),allowed=ps.map(p=>{let r=0;for(let e of [1,-1])if(wait(p,e)<=T)r++;return {p,r}}),quiet=allowed.reduce((a,v)=>a*(v.p-v.r),1);
  let arr=new Uint8Array(P),counts={},quietActual=0,firstHist={},base=2*P+1;
  for(let i=0;i<P;i++){let M=base+2*i,v=formal(M,T);arr[i]=v.gap;counts[v.gap]=(counts[v.gap]||0)+1;
   let expected=allowed.every(({p})=>!(wait(p,1)<=T&&mod(2*M-3,p)===0)&&!(wait(p,-1)<=T&&mod(2*M-1,p)===0));
   // formal() stops upon return; a first event has then already happened.
   if(expected!==!v.first)throw Error("quiet");if(!v.first)quietActual++;
   if(i%10000===0){let v2=formal(M+2*P,T);if(v2.gap!==v.gap||v2.first!==v.first)throw Error("period")}
   s.completePeriodTests++;
  }
  if(quietActual!==quiet)throw Error("quiet count");
  // Acyclic functional graph: edges i -> i+gap/2 mod P.
  let color=new Uint8Array(P),depth=new Uint32Array(P),maxDepth=0;
  for(let i=0;i<P;i++){if(color[i])continue;let j=i,path=[];while(color[j]===0&&arr[j]){color[j]=1;path.push(j);j=(j+arr[j]/2)%P}if(color[j]===1)throw Error("short return cycle");if(!color[j])color[j]=2;let d=depth[j];for(let k=path.length-1;k>=0;k--){let v=path[k];color[v]=2;depth[v]=++d;maxDepth=Math.max(maxDepth,d)}}
  s.periods.push({T,P,counts,quiet,quietDensity:quiet/P,maxDepth,allowed});
 }
 const indeg=new Uint32Array(N+1),known=new Uint8Array(N+1);
 for(let M=13;M<=N;M+=2){
  s.roots++;let t=M+2,H=2*M-2,F=0,done=false,firstWait=0;
  let pr=isPrime(M),src=pr&&(M%3===2||M%5===4);
  if(src)s.sourcePrimeTests++;
  // For the other prime residues, p=3 is an abstract predecessor
  // of the formal root via the last even reset and three quiet ticks.
  if(pr&&!src){let n=M-1,pre=2*M-4;if(tick(n,pre)!==3)throw Error("abstract predecessor");let Z=pre+2;for(let j=1;j<=3;j++)if(tick(n+j,Z))throw Error("quiet predecessor");s.abstractPredecessorChecks++}
  for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+30>=cap)break;let v=next(t,H);
   if(i===0){let min=Infinity;for(let p of primes(Math.min(1000,Math.floor(Math.sqrt(H+1))))){for(let e of [1,-1])if((H-e)%p===0)min=Math.min(min,wait(p,e))}if((v?v.w:Infinity)!==min)throw Error("first wait");s.firstWaitChecks++;firstWait=v?.w||0}
   if(!v){done=true;break}
   let n=t+v.w,rt=H/2+3;
   if(H%4===0&&t<rt&&rt<n){F=H/2+1;if(H%3===2||H%5===1||2*t!==H)throw Error("quiet root target");break}
   H+=v.p-1;t=n;s.events++;
   if(H%4===0&&2*t-H===6){F=H/2+1;if(n%2!==1||F%v.p!==0)throw Error("event root target");break}
  }
  if(F){if(F<=M||F%2!==1||F-M<firstWait)throw Error("return");s.reentries++;s.edges++;s.maxFiniteGap=Math.max(s.maxFiniteGap,F-M);
   if(isPrime(F)){s.primeTargets++;if(F%3===2||F%5===4)throw Error("source prime target");}
   if(F<=N){indeg[F]++;known[M]=1}else{s.crossingEdges++;known[M]=1;}
   if(F-M<=6){if(formal(M,6).gap!==F-M)throw Error("short actual");s.formalComparisons++}
   if(src&&!s.examples.sourceReturn)s.examples.sourceReturn={M,F,gap:F-M};
   if(pr&&!s.examples.primeRoot)s.examples.primeRoot={M,F};
  }else if(done)s.terminalBeforeReturn++;else s.undefinedWithinCap++;
 }
 for(let M=13;M<=N;M+=2){if(indeg[M]===0)s.zeroIndegree++;else if(indeg[M]>1)s.edgeCollisionExcess+=indeg[M]-1;if(isPrime(M)&&(M%3===2||M%5===4)){if(indeg[M])throw Error("source indegree")}}
 if(s.zeroIndegree-s.edgeCollisionExcess!==s.crossingEdges+s.terminalBeforeReturn+s.undefinedWithinCap)throw Error("graph balance");
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||200000),Number(process.argv[3]||180)),null,2));
