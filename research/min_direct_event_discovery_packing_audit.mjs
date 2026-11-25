// Event-index discovery CRT packing: independent relative clock, mixed and total-wait codes.
function audit(N=6000){
 const lim=500000,spf=new Int32Array(lim),primes=[];
 for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i%2)primes.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b, gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)}, assert=(v,msg)=>{if(!v)throw Error(msg)};
 const fac=n=>{let a=[];while(n>1){assert(n<lim,"sieve bound");let p=spf[n];a.push(p);while(n%p===0)n/=p}return a};
 const choose=(n,k)=>{if(k<0||k>n)return 0n;let v=1n;for(let i=1;i<=k;i++)v=v*BigInt(n-i+1)/BigInt(i);return v};
 const prod=a=>a.reduce((v,p)=>v*BigInt(p),1n);
 const cmp=(a,b)=>a.w-b.w||a.p-b.p;
 const st={abstractStarts:0,canonicalRoots:0,canonicalEvents:0,clockComparisons:0,literalTicks:0,reconstructions:0,reconstructedEvents:0,knownHighReuses:0,knownLow:0,knownLongWaits:0,shortDiscoveries:0,longDiscoveries:0,mixedPrefixes:0,totalWaitPrefixes:0,groups:0,spacingChecks:0,boundChecks:0,supportChecks:0,extendedTimeExamples:0,maxElapsed:0,completedRecoveries:0,qualifyingRecoveries:0};
 function event(H,t){
  let best=null;
  for(let I=0;I<2;I++){let e=1-2*I;for(let p of fac(H-e)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;let x={H,t,d:2*t-H,p,w,I};if(!best||cmp(x,best)<0)best=x}}
  return best
 }
 // Independent relative clock: no absolute H or t needed.
 function clock(p,I,d,par){
  let w=mod((-d-1+6*I)*((p+1)/2),p);if(mod(w+par,2)!==I)w+=p;if(!w)w=2*p;
  assert(w>=1&&w<=2*p&&mod(d+2*w+1-6*I,p)===0,"relative clock");
  return w
 }
 function trace(H,t,K){
  let a=[];for(let i=0;i<K;i++){let z=event(H,t);if(!z)break;if((st.clockComparisons++%73)===0){let found=null;for(let w=1;w<=z.w;w++){let n=t+w,I=n%2,g=gcd(n-2*I,H-(1-2*I)),p=g>1?spf[g]:0;if(p&&p*p<=H+1){found={p,w,I};break}st.literalTicks++}assert(found&&cmp(found,z)===0&&found.I===z.I,"literal gcd");st.literalTicks++}
   assert(clock(z.p,z.I,z.d,t%2)===z.w,"actual relative clock");
   a.push(z);H+=z.p-1;t+=z.w;assert(2*t-H>=0,"envelope");
  }return a
 }
 function prep(A,G,D,K,S,R,j,W,h,U){
  assert(R*R<=A+1&&j<=K,"parameters");
  let low=primes.filter(p=>p<=S),P=prod(low),Q=primes.filter(p=>p>S&&p<=R).length,b=0;
  while(BigInt(S+1)**BigInt(b+1)<=BigInt(D+4*R*K+3))b++;
  return {A,G,D,K,S,R,j,W,h,U,low,P,Q,b,mixed:new Map,wait:new Map}
 }
 function inspect(rows,c){
  if(!rows.length)return;let {A,G,D,K,S,R,j,W,h,U,low,P,Q,b}=c,r=rows[0];
  if(r.H<A||r.H>A+G||r.d<0||r.d>D)return;
  let seen=new Set,disc=[],total=0,allGain=0;
  for(let i=0;i<Math.min(K,rows.length);i++){
   let z=rows[i];if(z.p>R)break;allGain+=z.p-1;total+=z.w;
   if(z.p>S&&!seen.has(z.p)){seen.add(z.p);disc.push({i,p:z.p,w:z.w,I:z.I});}
   assert(BigInt(allGain)<2n*P*prod([...seen]),"support capacity");st.supportChecks++;
   if(disc.length===j)break;
  }
  if(disc.length!==j)return;
  let last=disc.at(-1).i,ell=disc.filter(z=>z.w>W).length,u=disc.reduce((v,z)=>v+z.w,0);
  let modes=[];if(ell<=h)modes.push("mixed");if(u<=U)modes.push("wait");
  for(let mode of modes){
   let known=new Map(low.map(p=>[p,mod(r.H,p)])),d=r.d,par=r.t%2,g=0,elapsed=0,k=0,highProd=1n,encoded=[],reuse=0,lowCount=0,longKnown=0;
   for(let i=0;i<=last;i++){
    let best=null;
    for(let [p,res] of known){let v=mod(res+g,p),I=v===1?0:v===p-1?1:-1;if(I<0)continue;let w=clock(p,I,d,par),z={p,I,w};if(!best||cmp(z,best)<0)best=z}
    let z=best;
    if(k<disc.length&&disc[k].i===i){
     let a=disc[k++],p=a.p,I,w,short=mode==="wait"||a.w<=W;
     assert(!known.has(p),"new label");
     if(short){w=a.w;I=(par+w)%2;let F=d+2*w+1-6*I;assert(F!==0&&F%p===0,"factor");
      let cand=fac(Math.abs(F)).filter(q=>q>S&&q<=R&&!known.has(q));assert(cand.includes(p)&&cand.length<=b,"branch size");encoded.push([i,"w",w,p]);st.shortDiscoveries++;
     }else{I=a.I;w=clock(p,I,d,par);encoded.push([i,"p",p,I]);st.longDiscoveries++}
     z={p,I,w};assert(!best||cmp(z,best)<0,"new precedes known");known.set(p,mod(1-2*I-g,p));highProd*=BigInt(p);
    }else if(z){if(z.p>S)reuse++;else lowCount++;if(z.w>W)longKnown++}
    assert(z&&cmp(z,rows[i])===0&&z.I===rows[i].I,"reconstruction");
    g+=z.p-1;d+=2*z.w-(z.p-1);par=(par+z.w)%2;elapsed+=z.w;st.reconstructedEvents++;
    assert(d>=0&&d<=D+4*R*K,"deficit bound");
   }
   assert(elapsed===total,"elapsed");
   st.reconstructions++;st.knownHighReuses+=reuse;st.knownLow+=lowCount;st.knownLongWaits+=longKnown;st.maxElapsed=Math.max(st.maxElapsed,elapsed);
   if(mode==="mixed"){if(ell>0&&ell<j)st.mixedPrefixes++;if(elapsed>K*W&&longKnown)st.extendedTimeExamples++}else st.totalWaitPrefixes++;
   let key=JSON.stringify([r.d,r.t%2,String(BigInt(r.H)%P),encoded]),map=c[mode],entry=map.get(key);
   if(!entry){entry={m:4n*P*highProd,hs:new Set,word:JSON.stringify(rows.slice(0,last+1).map(z=>[z.p,z.w,z.I]))};map.set(key,entry)}
   assert(entry.word===JSON.stringify(rows.slice(0,last+1).map(z=>[z.p,z.w,z.I])),"code uniqueness");entry.hs.add(r.H);
  }
 }
 function verify(c){
  let {G,D,K,S,j,W,h,U,P,Q,b}=c,den=4n*BigInt(S+1)**BigInt(j),mix=0n;
  for(let e=0;e<=Math.min(h,j);e++)mix+=choose(j,e)*BigInt(W*b)**BigInt(j-e)*BigInt(2*Q)**BigInt(e);
  for(let [mode,cost] of [["mixed",mix],["wait",choose(U,j)*BigInt(b)**BigInt(j)]]){
   let count=0n;
   for(let a of c[mode].values()){
    let v=[...a.hs].sort((x,y)=>x-y);for(let i=1;i<v.length;i++){assert(BigInt(v[i]-v[i-1])%a.m===0n,"CRT spacing");st.spacingChecks++}
    assert(BigInt(v.length)<=1n+BigInt(G)/a.m,"individual capacity");count+=BigInt(v.length);st.groups++;
   }
   assert(count*den<=BigInt(D+2)*choose(K,j)*cost*(P*den+BigInt(G)),"aggregate");st.boundChecks++;
  }
 }
 for(let args of [[1000,2600,24,8,3,31,1,3,0,5],[4000,2400,48,10,5,61,2,4,1,20],[4000,2400,60,14,7,61,3,6,2,32],[20000,4000,100,16,5,101,2,3,1,30],[20000,4000,100,16,3,101,3,5,2,40]]){
  let c=prep(...args);
  for(let H=c.A;H<=c.A+c.G;H+=2)for(let d=0;d<=c.D;d+=2){inspect(trace(H,(H+d)/2,c.K),c);st.abstractStarts++}
  verify(c)
 }
 let cs=[prep(1000,Math.max(10000,4*N),100,14,3,31,2,5,1,30),prep(4000,Math.max(10000,4*N),160,20,5,61,2,5,1,40)];
 for(let M=5;M<=N;M+=2){let rows=trace(2*M-2,M+2,180);st.canonicalRoots++;st.canonicalEvents+=rows.length;
  for(let i=0;i<rows.length;i++){let z=rows[i];for(let c of cs)inspect(rows.slice(i,i+c.K),c);
   if(z.p>=47&&z.p>=5*z.d+15&&z.d+2*z.w-(z.p-1)-6*z.I===2*z.p){
    let post=2*z.p+6*z.I,end=i+1;while(end<rows.length){let a=rows[end];if(a.d+2*a.w-(a.p-1)+3<=z.p){st.completedRecoveries++;let rest=rows.slice(i+1,end+1);if(rest.length<=20&&rest.every(v=>v.p<=61)&&rest[0].H>=4000)st.qualifyingRecoveries++;break}end++}
   }
  }
 }for(let c of cs)verify(c);
 assert(st.reconstructions&&st.longDiscoveries&&st.shortDiscoveries&&st.knownHighReuses&&st.knownLow&&st.mixedPrefixes&&st.extendedTimeExamples&&st.spacingChecks,"nonvacuous coverage");
 return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||6000)),null,2));
