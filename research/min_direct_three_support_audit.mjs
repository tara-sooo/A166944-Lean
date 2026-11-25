function audit(N=100000,steps=100){
 const max=8*N+10000,spf=new Int32Array(max+1);for(let i=2;i<=max;i++)if(!spf[i]){spf[i]=i;if(i*i<=max)for(let j=i*i;j<=max;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function factors(z){let a=[];while(z>1){if(z>max)throw Error("range");let p=spf[z];if(!p)throw Error("spf");a.push(p);while(z%p===0)z/=p}return a}
 function next(t,C){let best=null,B=Math.floor(Math.sqrt(C+1));for(let s of [-1,1])for(let p of factors(C+s)){if(p>B)continue;let r=s===-1?0:p+2,w=mod(r-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,s,w}}return best}
 function literal(t,C){for(let w=1;w<=2*Math.floor(Math.sqrt(C+1));w++){let n=t+w,s=n%2?1:-1,g=gcd(n%2?n-2:n,C+s);if(g>1&&spf[g]**2<=C+1)return {p:spf[g],s,w}}return null}
 function relaxed(S){let Q=S.reduce((a,b)=>a*b,1),D=new Uint16Array(Q+1),top=0,j0=0;for(let j=Q-1;j>=0;j--)for(let p of S){let r=2*j%p;if(r!==1&&r!==p-1)continue;let k=j+(p-1)/2;if(k>Q)throw Error("barrier");let v=D[k]+1;if(v>D[j])D[j]=v;if(v>top){top=v;j0=j}}let j=j0,word=[];while(D[j]){let p=S.find(p=>{let r=2*j%p;return (r===1||r===p-1)&&D[j+(p-1)/2]+1===D[j]});if(!p)throw Error("witness");word.push(p);j+=(p-1)/2}return {max:top,start:2*j0,end:2*j,word}}
 // All phase states, with an arbitrarily increasing enabled initial segment of S.
 // This relaxes adaptive eligibility but retains earliest-hit/least-prime competition.
 function clockDP(S){const Q=S.reduce((a,b)=>a*b,1),P=2*Q,k=S.length,stride=P*(k+1),D=new Uint16Array((Q+1)*stride);let top=0,all=0,start=null,states=0,clockChecks=0;
  for(let j=Q-1;j>=0;j--){const active=S.map(p=>{let r=2*j%p;return r===1?0:r===p-1?p+2:-1});for(let t=0;t<P;t++){
   let bp=0,bw=Infinity;const v=new Uint16Array(k+1);
   for(let m=1;m<=k;m++){let p=S[m-1],r=active[m-1];if(r>=0){let w=mod(r-t,2*p)||2*p;if(w<bw){bp=p;bw=w}}
    if((j*P+t)%197===0){let p0=0,w0=Infinity;for(let w=1;w<=2*S[m-1];w++){let n=t+w;let hit=S.slice(0,m).find(p=>(n%2?n-2:n)%p===0&&(2*j+(n%2?1:-1))%p===0);if(hit){p0=hit;w0=w;break}}if(p0!==bp||w0!==bw)throw Error("restricted literal clock");clockChecks++}
    if(bp){let J=j+(bp-1)/2,T=(t+bw)%P;if(J>Q)throw Error("barrier");v[m]=1+D[J*stride+T*(k+1)+m]}
   }
   const base=j*stride+t*(k+1);let z=0;for(let m=k;m>=1;m--){z=Math.max(z,v[m]);D[base+m]=z;states++}D[base]=z;
   if(z>top){top=z;start={j,t}}all=Math.max(all,v[k]);
  }}
  return {max:top,allEnabledMax:all,start,states,clockChecks}
 }
 const exceptions=[[3,5,7],[3,5,11],[3,5,13],[3,5,17],[3,11,13],[3,7,11],[3,13,17],[3,7,13],[5,7,11],[5,13,17]].map(S=>({S,relaxed:relaxed(S),clock:clockDP(S)}));
 if(exceptions.some(e=>e.relaxed.max>18||e.clock.max>11))throw Error("exception bound");
 // Exhaustively test the general algebraic bounds on a bounded family (not the proof).
 const primes=[];for(let p=3;p<=59;p+=2)if(spf[p]===p)primes.push(p);
 let tripleChecks=0,nonexceptionMax=0,nonexceptionNo3Max=0,apChecks=0;
 for(let i=0;i<primes.length;i++)for(let j=i+1;j<primes.length;j++)for(let k=j+1;k<primes.length;k++){const S=[primes[i],primes[j],primes[k]],v=relaxed(S).max;tripleChecks++;if(v>18)throw Error("three relaxed");if(!exceptions.some(e=>e.S.every((p,x)=>p===S[x]))){nonexceptionMax=Math.max(nonexceptionMax,v);if(S[0]>=5){nonexceptionNo3Max=Math.max(nonexceptionNo3Max,v);if(v>11)throw Error("no3") }else if(S[1]>=7&&v>12)throw Error("3 with large q");else if(S[1]===5&&v>13)throw Error("3,5")}}
 for(let p=5;p<=300;p+=2)if(spf[p]===p)for(let q=p+2;q<=500;q+=2)if(spf[q]===q){let r=p+q-3;if(spf[r]!==r)continue;let a=[0,2,p-1,p+1].map(x=>mod(x,q)),d=mod(2*(p-3),q);for(let x of a){apChecks++;if([1,2].every(i=>a.includes(mod(x+i*d,q))))throw Error("three-term progression")}}
 let stats={N,steps,edges:0,truncatedByRange:0,forced3:0,max:{1:0,2:0,3:0},primeRootMax:{1:0,2:0,3:0},witness:{},primeWitness:{},exceptions,tripleChecks,nonexceptionMax,nonexceptionNo3Max,apChecks,actualUpper:{1:2,2:5,3:11}};
 for(let M=5;M<=N;M+=2){let t=M+2,C=2*M-2,word=[],ts=[],Cs=[];for(let i=0;i<steps;i++){if(C+Math.floor(Math.sqrt(C+1))+1>max){stats.truncatedByRange++;break}let e=next(t,C);if(!e)break;ts.push(t);Cs.push(C);word.push(e.p);t+=e.w;C+=e.p-1;stats.edges++;if(e.p===3&&e.s===1){let f=next(t,C);if(f?.p!==3||f.s!==-1||f.w!==1)throw Error("forced3");stats.forced3++}for(let k=1;k<=3;k++){let set=new Set(),j=word.length-1;while(j>=0){set.add(word[j]);if(set.size>k)break;j--}let len=word.length-1-j;if(len>stats.actualUpper[k])throw Error("actual support bound");if(len>stats.max[k]){stats.max[k]=len;stats.witness[k]={M,startT:ts[j+1],startC:Cs[j+1],word:word.slice(j+1)}}if(spf[M]===M&&len>stats.primeRootMax[k]){stats.primeRootMax[k]=len;stats.primeWitness[k]={M,startT:ts[j+1],startC:Cs[j+1],word:word.slice(j+1)}}}}}
 // Independent literal tickwise GCD replay from the canonical root.
 for(let rec of [...Object.values(stats.witness),...Object.values(stats.primeWitness)]){let t=rec.M+2,C=2*rec.M-2;while(t<rec.startT){let e=literal(t,C);if(!e)throw Error("premature stop");t+=e.w;C+=e.p-1}if(t!==rec.startT||C!==rec.startC)throw Error("start replay");rec.events=[];for(let p of rec.word){let e=literal(t,C);if(e?.p!==p)throw Error("literal witness");t+=e.w;C+=p-1;rec.events.push([t,C,p,e.s,e.w])}}
 if(stats.max[1]!==2||stats.max[2]!==5||stats.max[3]!==11||stats.primeRootMax[3]!==11)throw Error("missing equality witnesses");
 return stats
}

console.log(JSON.stringify(audit(Number(process.argv[2] || 100000),Number(process.argv[3] || 100)),null,2));
