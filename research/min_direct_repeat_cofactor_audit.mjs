function audit(N=150000,maxEvents=180){
 const cap=4*N+50000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function factors(z){let a=[];while(z>1){if(z>cap||!spf[z])throw Error("factor range");let p=spf[z];a.push(p);while(z%p===0)z/=p}return a}
 function next(t,H){let best=null;for(let e of [1,-1])for(let p of factors(H-e)){if(p*p>H+1)continue;let r=e===1?0:p+2,w=mod(r-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}return best}
 function literal(t,H){for(let w=1;w<=2*Math.floor(Math.sqrt(H+1));w++){let n=t+w,e=n%2?-1:1,g=gcd(n%2?n-2:n,H-e);if(g>1&&spf[g]**2<=H+1)return {p:spf[g],e,w}}return null}
 let s={N,maxEvents,events:0,rangeTruncated:0,repeatChecks:0,qualifiedEvents:0,qualifiedPairs:0,minimalPairs:0,minimalQualifiedPairs:0,qualifiedResetPairs:0,resetMinQualifiedPairs:0,equalStratumChecks:0,conditionalStratumChecks:0,conditionalGeneralChecks:0,nonTwinDeficitChecks:0,threeSupportMinimalPairs:0,threeSupportQualifiedPairs:0,threeSupportPrimePairs:0,threeSupportPrimeExamples:[],twinExamples:[],resetExamples:[],maxQ:0,largestWitness:null,primeRootWitness:null,primeResetWitness:null,threeSupportPrimeWitness:null,distinctTwinLower:new Set(),distinctPhysicalPairs:new Set(),lowDeficitQualified:0,literalReplays:0};
 for(let M=5;M<=N;M+=2){let t=M+2,H=2*M-2,ev=[],last=new Map(),lastQualified=new Map(),lastReset=new Map(),lastStratum=new Map();for(let i=0;i<maxEvents;i++){if(H+Math.sqrt(H+1)+1>=cap){s.rangeTruncated++;break}let a=next(t,H);if(!a)break;let {p,e,w}=a,n=t+w,Z=H+p-1,I=e===-1?1:0,q=(H-e)/p,U=n-2*I,V=Z+2*I,D=2*U-V,d=2*t-H,delta=2*n-Z;
 let r={i,p,e,w,n,H,Z,q,U,V,D,d,delta,qualified:q<p*p&&w>=2*Math.floor(Math.sqrt(q))&&w>6};
 if(!Number.isInteger(q)||q<p||q%2!==1||V!==p*(q+1)||U%p||D%(2*p)||p>=5&&D<0)throw Error("event");
 if(r.qualified){if(spf[q]!==q||H%3!==0)throw Error("cofactor or mod3");s.qualifiedEvents++;if(d<p/2&&p*p*p>100*H)s.lowDeficitQualified++}
 function witness(a,b){return {M,p,first:a,second:b,word:ev.slice(a.i+1,b.i).map(v=>v.p)}}
 function check(a,b,kind){let m=(b.q-a.q)/2,l=(b.U-a.U)/p,G=b.H-a.Z;if(!Number.isInteger(m)||m<1||!Number.isInteger(l)||l<1||mod(l,2)!==(a.e===b.e?0:1)||b.D-a.D!==2*p*(l-m)||G!==(2*m-1)*p+1+b.e-a.e)throw Error("return identity");
 if(kind==="consecutive"){s.repeatChecks++;if(m===1){s.minimalPairs++;if(a.q<p*p&&b.q<p*p&&(spf[a.q]!==a.q||spf[b.q]!==b.q)){let bad=[a,b].filter(x=>spf[x.q]!==x.q);if(bad.some(x=>x.d<p+1+x.delta-4*spf[x.q]))throw Error("composite deficit");s.nonTwinDeficitChecks++}}
 let labels=new Set(ev.slice(a.i+1,b.i).map(v=>v.p));labels.add(p);if(labels.size<=3&&[...labels].every(q=>q<=p)){if(m!==1)throw Error("three support");s.threeSupportMinimalPairs++;if(a.qualified&&b.qualified)s.threeSupportQualifiedPairs++;if(spf[a.q]===a.q&&spf[b.q]===b.q){s.threeSupportPrimePairs++;let rec=witness(a,b);if(s.threeSupportPrimeExamples.length<3)s.threeSupportPrimeExamples.push(rec);if(!s.threeSupportPrimeWitness||b.q>s.threeSupportPrimeWitness.second.q)s.threeSupportPrimeWitness=rec}}
 }
 if(a.qualified&&b.qualified){if(spf[a.q]!==a.q||spf[b.q]!==b.q)throw Error("prime");let r1=mod(a.e*p,3)===1?1:-1,r2=mod(b.e*p,3)===1?1:-1;if(a.e===b.e){if(m%3)throw Error("same sign mod3")}else if(mod(m-a.e*p,3))throw Error("opposite mod3");
 if(m!==1){if(m<3+(r1-r2)/2)throw Error("general conditional gap");s.conditionalGeneralChecks++}
 if(m===1&&kind==="consecutive"){s.minimalQualifiedPairs++;s.distinctTwinLower.add(a.q);s.distinctPhysicalPairs.add(`${p}:${a.n}:${a.H}:${b.n}:${b.H}`);let rec=witness(a,b);if(s.twinExamples.length<3)s.twinExamples.push(rec);if(b.q>s.maxQ){s.maxQ=b.q;s.largestWitness=rec}if(spf[M]===M&&(!s.primeRootWitness||b.q>s.primeRootWitness.second.q))s.primeRootWitness=rec}
 if(kind==="qualified")s.qualifiedPairs++;
 if(a.D===b.D){if(l!==m||mod(m,2)!==(a.e===b.e?0:1))throw Error("equal stratum");if(a.e===b.e&&m%6||a.e!==b.e&&mod(m,6)!==(r1===1?1:5))throw Error("equal stratum residue");s.equalStratumChecks++;
 if(m!==1){if(m<6+(r1-r2)/2)throw Error("conditional stratum gap");s.conditionalStratumChecks++}
 }
 }
 if(kind==="reset"){s.qualifiedResetPairs++;if(m===1){s.resetMinQualifiedPairs++;let rec=witness(a,b);if(s.resetExamples.length<3)s.resetExamples.push(rec);if(spf[M]===M&&(!s.primeResetWitness||b.q>s.primeResetWitness.second.q))s.primeResetWitness=rec}}
 }
 if(p>=5){let prev=last.get(p);if(prev)check(prev,r,"consecutive");last.set(p,r);if(r.qualified){let a=lastQualified.get(p);if(a)check(a,r,"qualified");lastQualified.set(p,r);let key=p+":"+D,a2=lastStratum.get(key);if(a2)check(a2,r,"stratum");lastStratum.set(key,r);if(D===0){let a3=lastReset.get(p);if(a3)check(a3,r,"reset");lastReset.set(p,r)}}}
 ev.push(r);H=Z;t=n;s.events++;
 }}
 for(let rec of [s.largestWitness,s.primeRootWitness,s.primeResetWitness,s.threeSupportPrimeWitness,...s.twinExamples,...s.resetExamples]){if(!rec)continue;let t=rec.M+2,H=2*rec.M-2;for(let i=0;i<=rec.second.i;i++){let a=literal(t,H);if(!a)throw Error("replay stop");if(i===rec.first.i||i===rec.second.i){let r=i===rec.first.i?rec.first:rec.second;if(a.p!==r.p||a.e!==r.e||a.w!==r.w||t+a.w!==r.n||H!==r.H)throw Error("replay mismatch")}t+=a.w;H+=a.p-1;s.literalReplays++}}
 s.distinctTwinLower=[...s.distinctTwinLower].sort((a,b)=>a-b);s.distinctPhysicalPairs=s.distinctPhysicalPairs.size;return s
}

console.log(JSON.stringify(audit(Number(process.argv[2]||150000),Number(process.argv[3]||180)),null,2));
