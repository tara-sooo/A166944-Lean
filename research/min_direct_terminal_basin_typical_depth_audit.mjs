// Terminal inverse horizons and fresh-prime extension of finite prefixes.
function audit(N=200000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 function factors(n){let a=[];while(n>1){let p=spf[n];if(!p)throw Error("range");a.push(p);while(n%p===0)n/=p}return a}
 const gcd=(a,b)=>{b=Math.abs(b);while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function next(t,H){let best=null;for(let e of [1,-1])for(let p of factors(H-e)){if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}return best}
 function reverse(Z){let a=[];for(let e of [1,-1])for(let p of factors(Z+1-e)){if(p===2)continue;let H=Z-p+1;if(H>=8&&p*p<=H+1)a.push(H)}return [...new Set(a)]}
 const s={N,steps,roots:0,events:0,reverseChecks:0,terminal:0,capped:0,shortTerminal:[0,0,0,0,0],terminalByTick:[0,0,0,0],windows:[],terminalCentersChecked:0,reverseLayerChecks:0,reverseAncestorChecks:0,maxReverseCandidates:0,maxObservedBasin:0,conditionalTests:0,freshPrimeChecks:0,crtEventChecks:0,crtTicks:0};
 let basins=new Map(),win=new Map();
 for(let M=5;M<=N;M+=2){
  let H=2*M-2,t=M+2,ev=0,first=0,term=false;
  for(;ev<steps;ev++){if(H+Math.sqrt(H+1)+20>=cap)throw Error("cap");let a=next(t,H);if(!a){term=true;break}let Z=H+a.p-1;if((Z+1-a.e)%a.p||!reverse(Z).includes(H))throw Error("inverse");s.reverseChecks++;H=Z;t+=a.w;s.events++;}
  s.roots++;let bin=Math.floor(Math.log2(M)),v=win.get(bin)||{bin,roots:0,terminal:0,short:[0,0,0,0,0]};v.roots++;win.set(bin,v);
  if(term){s.terminal++;v.terminal++;for(let k=0;k<=4;k++)if(ev<=k){s.shortTerminal[k]++;v.short[k]++}
   for(let i=0;i<4;i++)if(t-M-2<=[6,12,24,48][i])s.terminalByTick[i]++;
   if(ev<=4){let a=basins.get(H)||[];a.push({M,ev});basins.set(H,a)}
  }else s.capped++;
 }
 for(let [Z,a] of basins){let layers=[new Set([Z])],all=new Set([Z]);for(let k=1;k<=4;k++){let x=new Set(layers[k-1]);for(let h of layers[k-1])for(let g of reverse(h))x.add(g);layers.push(x);s.reverseLayerChecks++}
  for(let {M,ev} of a){if(!layers[ev].has(2*M-2))throw Error("basin");s.reverseAncestorChecks++}
  s.maxReverseCandidates=Math.max(s.maxReverseCandidates,layers[4].size);s.maxObservedBasin=Math.max(s.maxObservedBasin,a.length);s.terminalCentersChecked++;
 }
 s.windows=[...win.values()].slice(-5);
 // Verify CRT independence for actual finite prefixes, then force a fresh clock.
 function primes(n){let a=[];for(let p=3;p<=n;p+=2)if(spf[p]===p)a.push(p);return a}
 function run(M,T){let H=2n*M-2n,word=[];for(let j=1;j<=T;j++){let n=M+2n+BigInt(j),e=n%2n?-1n:1n,A=e===1n?n:n-2n,D=H-e;while(D)[A,D]=[D,A%D];let p=A===1n?0:spf[Number(A)];if(A!==1n&&!p)throw Error("small gcd");word.push(p);if(p)H+=BigInt(p-1);s.crtTicks++}return {H,word}}
 for(let T of [0,1,2,4,6]){let ps=primes(2*T+7),P=ps.reduce((a,p)=>a*BigInt(p),2n);
  for(let M0=101;M0<=119;M0+=2){let M=BigInt(M0)+P*100n,a=run(M,T);s.conditionalTests++;
   for(let p of primes(2*T+60).filter(p=>p>2*T+7).slice(0,4)){let f=BigInt(p),res=new Set();for(let j=0;j<p;j++){let H=a.H+2n*P*BigInt(j);if((H-1n)%f===0n||(H+1n)%f===0n)res.add(j)}
    if(res.size!==2)throw Error("fresh classes");s.freshPrimeChecks++;
    for(let j of res){let M2=M+P*BigInt(j)+P*f*10000n,b=run(M2,T+2*p);if(b.word.slice(0,T).join()!==a.word.join()||!b.word.slice(T).some(x=>x))throw Error("forced clock");s.crtEventChecks++}
   }
  }
 }
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||200000),Number(process.argv[3]||180)),null,2));
