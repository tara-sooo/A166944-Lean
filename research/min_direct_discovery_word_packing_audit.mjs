// Discovery-only CRT compression of MIN tick words and clock gain budgets.
function audit(N=8000){
 const cap=300000,spf=new Int32Array(cap);for(let i=2;i<cap;i++)if(!spf[i]){spf[i]=i;if(i*i<cap)for(let j=i*i;j<cap;j+=i)if(!spf[j])spf[j]=i}
 const gcd=(a,b)=>{a=Math.abs(a);while(b)[a,b]=[b,a%b];return a},mod=(a,b)=>(a%b+b)%b;
 function step(H,t){let n=t+1,I=n%2,e=1-2*I,g=gcd(n-2*I,H-e),p=g>1?spf[g]:0;if(p&&p*p>H+1)p=0;return p}
 const ps=[];for(let p=3;p<cap;p+=2)if(spf[p]===p)ps.push(p);
 let st={abstractStarts:0,roots:0,ticks:0,events:0,prefixes:0,reconstructedTicks:0,discoveries:0,reusedHigh:0,lowEvents:0,groups:0,spacingChecks:0,capacityChecks:0,clockGainChecks:0,recoveryChecks:0,forcedDiscoveries:0,withLowRelays:0,withRepeats:0,maxDiscoveries:0};
 function choose(n,k){let v=1n;for(let i=1;i<=k;i++)v=v*BigInt(n-i+1)/BigInt(i);return v}
 function inspect(rows,L,S,j,D,A,G,groups){
  const low=ps.filter(p=>p<=S),P=low.reduce((a,p)=>a*BigInt(p),1n);
  const B=Math.floor(Math.log(D+2*L+3)/Math.log(S+1)+1e-12);
  for(let i=0;i+L<=rows.length;i++){
   let r=rows[i];if(r.d>D||r.d<0||r.H<A||r.H>A+G||D+2*L+3>Math.sqrt(A+1))continue;
   let word=rows.slice(i,i+L).map(x=>x.p),known=new Map(low.map(p=>[p,r.H%p])),seen=new Set,disc=[],off=0,d=r.d,counts=new Map;
   for(let z=0;z<L;z++){let p=word[z];if(p)counts.set(p,(counts.get(p)||0)+1);if(p>S&&!seen.has(p)){seen.add(p);disc.push([z,p]);if(disc.length===j)break}}
   if(disc.length!==j)continue;
   let end=disc.at(-1)[0],highProd=1n,idx=0,reuse=0,loct=0;
   for(let z=0;z<=end;z++){
    let I=(r.t+z+1)%2,e=1-2*I,F=d+3-6*I,candidate=0;
    for(let [p,res] of known)if(F%p===0&&mod(res+off-e,p)===0&&(!candidate||p<candidate))candidate=p;
    let p=candidate;
    if(idx<disc.length&&disc[idx][0]===z){
     p=disc[idx++][1];
     if(known.has(p)||F%p!==0||candidate&&candidate<p)throw Error("discovery");
     let available=ps.filter(f=>f>S&&f<=Math.abs(F)&&F%f===0&&!known.has(f));
     if(available.length>B||!available.includes(p))throw Error("branch");
     known.set(p,mod(e-off,p));highProd*=BigInt(p);st.discoveries++;
    }else if(p>S)reuse++;else if(p)loct++;
    if(p!==word[z])throw Error("reconstruct");
    if(p)off+=p-1;d+=2-(p?p-1:0);if(d!==rows[i+z+1]?.d&&i+z+1<rows.length)throw Error("deficit");
    st.reconstructedTicks++;
   }
   st.prefixes++;st.reusedHigh+=reuse;st.lowEvents+=loct;if(reuse)st.withRepeats++;if(loct)st.withLowRelays++;
   st.maxDiscoveries=Math.max(st.maxDiscoveries,j);
   let key=[r.d,r.t%2,String(BigInt(r.H)%P),JSON.stringify(disc)].join(":"),g=groups.get(key);
   if(!g){g={modulus:4n*P*highProd,hs:new Set};groups.set(key,g)}
   g.hs.add(r.H);
  }
 }
 function verify(groups,L,S,j,D,G){
  let P=ps.filter(p=>p<=S).reduce((a,p)=>a*BigInt(p),1n),B=Math.floor(Math.log(D+2*L+3)/Math.log(S+1)+1e-12),sum=0n;
  for(let g of groups.values()){
   let hs=[...g.hs].sort((a,b)=>a-b);
   for(let i=1;i<hs.length;i++){if(BigInt(hs[i]-hs[i-1])%g.modulus!==0n)throw Error("spacing");st.spacingChecks++}
   if(BigInt(hs.length)>BigInt(G)/g.modulus+1n)throw Error("individual bound");
   sum+=BigInt(hs.length);st.groups++;
  }
  let bound=BigInt(D+2)*choose(L,j)*BigInt(B)**BigInt(j)*(P+BigInt(G)/(4n*BigInt(S+1)**BigInt(j)));
  if(sum>bound)throw Error("global");
  st.capacityChecks++;
 }
 // Exhaustive starts large enough for all candidate primes to be eligible.
 for(let [L,S,j,D] of [[8,5,1,24],[12,5,2,36],[24,7,2,48],[40,11,3,60],[60,5,3,100]]){
  let A=(D+2*L+3)**2+2;A+=A%2;let G=1200,groups=new Map;
  for(let H=A;H<=A+G;H+=2)for(let d=0;d<=D;d+=2){
   let h=H,t=(H+d)/2,rows=[];
   for(let z=0;z<L;z++){let p=step(h,t);rows.push({H:h,t,d:2*t-h,p});h+=p?p-1:0;t++}
   st.abstractStarts++;inspect(rows,L,S,j,D,A,G,groups);
   let counts=new Map;for(let r of rows)if(r.p)counts.set(r.p,(counts.get(r.p)||0)+1);
   for(let [p,c] of counts){if(c>1+Math.floor((L+1)/p)||c*(p-1)>=(L+p))throw Error("clock gain");st.clockGainChecks++}
   let high=[...counts.keys()].filter(p=>p>S),lowGain=[...counts].filter(([p])=>p<=S).reduce((v,[p,c])=>v+c*(p-1),0),R=Math.max(S,...counts.keys()),capLow=ps.filter(p=>p<=S).reduce((v,p)=>v+(p-1)*(1+Math.floor((L+1)/p)),0);
   let total=h-H;
   if(lowGain>capLow||total>capLow+high.length*(L+R))throw Error("gain forcing");
   if(total>capLow+(j-1)*(L+R)){if(high.length<j)throw Error("forced");st.forcedDiscoveries++}
  }verify(groups,L,S,j,D,G)
 }
 for(let M=5;M<=N;M+=2){
  let H=2*M-2,t=M+2,rows=[],ev=[];st.roots++;
  for(let z=0;z<3000;z++){let p=step(H,t);rows.push({H,t,d:2*t-H,p});t++;st.ticks++;if(p){H+=p-1;st.events++;ev.push(z)}if(H+3>=cap)throw Error("cap");if(spf[H-1]===H-1&&spf[H+1]===H+1)break}
  for(let [L,S,j,D] of [[8,5,1,24],[12,5,2,36],[24,7,2,48]]){let A=(D+2*L+3)**2+2,G=Math.max(0,H-A),groups=new Map;inspect(rows,L,S,j,D,A,G,groups);verify(groups,L,S,j,D,G)}
  // Actual recoveries from post-A1 (identify pre-wait event state).
  let prevD=6;
  for(let idx=0;idx<ev.length;idx++){let z=ev[idx],r=rows[z],p=r.p,I=(r.t+1)%2,dp=r.d+3-p;
   if(p>=47&&p>=5*prevD+15&&dp-6*I===2*p){
    let end=z+1;while(end<rows.length&&end-z<=60&&rows[end].d+3>p)end++;
    if(end<rows.length&&end-z<=60&&rows[end].d+3<=p){
     let w=rows.slice(z+1,end),L=w.length,counts=new Map;for(let a of w)if(a.p)counts.set(a.p,(counts.get(a.p)||0)+1);
     let S=7,R=Math.max(S,...counts.keys()),gain=w.reduce((a,b)=>a+(b.p?b.p-1:0),0),lowCap=ps.filter(q=>q<=S).reduce((a,q)=>a+(q-1)*(1+Math.floor((L+1)/q)),0);
     if(gain< p+3||gain>lowCap+[...counts.keys()].filter(q=>q>S).length*(L+R))throw Error("recovery");st.recoveryChecks++
    }
   }prevD=dp;
  }
 }
 if(!st.withRepeats||!st.withLowRelays||!st.prefixes||!st.forcedDiscoveries)throw Error("coverage");
 return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||8000)),null,2));
