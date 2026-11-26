// Repeated certified cofactor clusters: exact return identities and higher-dimensional Selberg sieve controls.
function audit(N=60000){
 const lim=1000000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i%2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a<0n?-a:a};
 const st={roots:0,events:0,cap:0,longPrimeEvents:0,groups:0,pairChecks:0,twinPairs:0,noTwinPairs:0,mod3Pairs:0,stratumPairs:0,components:0,componentWindowChecks:0,windowsByJ:{2:0,3:0,4:0},patternChecks:0,determinantChecks:0,residueChecks:0,sieveControls:0,sieveWeights:0,quadraticChecks:0,majorantChecks:0,productTruncationChecks:0,nearFlatControls:0,nearFlatLabelChecks:0,nearFlatTwinPairs:0,nearFlatPositiveGain:0,flatControls:0,flatPositiveGain:0,exactSupportDivisibilityChecks:0,nearFlatExamples:[],selectedStratumControls:0,selectedStratumRepeatChecks:0,selectedStratumTwinPairs:0,selectedStratumExamples:[],examples:[]};
 function factors(x){ok(x>0&&x<lim,"range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<=1;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let e=1-2*I,q=(H-e)/p;z={H,t,p,w,I,e,q,d:2*t-H,dp:2*t-H+2*w-p+1,D:2*t-H+2*w-p+1-6*I}}}return z}
 function forms(p,a,e){return a.flatMap((v,i)=>[[1,v],[p,p*v+2*e[i]]])}
 function delta(fs){let d=1n;for(let i=0;i<fs.length;i++)for(let j=i+1;j<fs.length;j++){let x=BigInt(fs[i][0])*BigInt(fs[j][1])-BigInt(fs[j][0])*BigInt(fs[i][1]);ok(x!==0n,"nonzero discriminant");d*=x<0n?-x:x;st.determinantChecks++}return d}
 function residues(fs,f){let s=[];for(let x=0;x<f;x++)if(fs.some(([a,b])=>mod(a*x+b,f)===0))s.push(x);return s}
 function pattern(p,list){
  let a=list.map(z=>z.q-list[0].q),e=list.map(z=>z.e),fs=forms(p,a,e),D=delta(fs),q=list[0].q;
  for(let i=0;i<list.length;i++){let z=list[i];ok(fs[2*i][0]*q+fs[2*i][1]===z.q&&fs[2*i+1][0]*q+fs[2*i+1][1]===z.H+z.e,"forms exact")}
  let W=Math.min(...list.map(z=>z.w));
  for(let f of pr.filter(f=>f<=Math.min(97,Math.floor((W-1)/2))&&f>fs.length&&f!==p)){
   let r=residues(fs,f);if(D%BigInt(f)!==0n)ok(r.length===fs.length,"generic dimension");ok(!r.includes(q%f),"actual avoided residue");st.residueChecks++
  }
  st.patternChecks++;st.windowsByJ[list.length]++;if(list.length>=3&&st.examples.length<5&&p>=11)st.examples.push({p,q:list.map(z=>z.q),w:list.map(z=>z.w),H:list.map(z=>z.H),D:list.map(z=>z.D)})
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,groups=new Map,rows=[],j=0;st.roots++;
  for(;j<180;j++){let z=next(H,t);if(!z)break;rows.push(z);st.events++;if(z.p>=5&&4*z.w>=z.p-1&&spf[z.q]===z.q){if(!groups.has(z.p))groups.set(z.p,[]);groups.get(z.p).push(z);st.longPrimeEvents++}H+=z.p-1;t+=z.w}
  if(j===180)st.cap++;
  // Greedy actual blocks with at most two post-deficit values in a narrow tube.
  for(let T of [17,47]){
   for(let a=0;a<rows.length;){let b=a+1,ds=new Set([rows[a].dp]);
    while(b<rows.length){let t=new Set([...ds,rows[b].dp]);if(t.size>2||Math.max(...t)-Math.min(...t)+6>=2*T)break;ds=t;b++}
    let G=rows[b-1].H+rows[b-1].p-1-rows[a].H,ls=new Map,F=0,W=0,Q=0;
    for(let i=a;i<b;i++){let z=rows[i];if(z.p<T||z.D<=0||z.w<=6||4*z.w<z.p-1||spf[z.q]!==z.q)continue;ok(z.dp>=2*z.p&&z.D%(2*z.p)===0,"tube support");if(!ls.has(z.p))ls.set(z.p,[]);ls.get(z.p).push(z);F+=z.p-1;st.exactSupportDivisibilityChecks++}
    let pool=1n;for(let d of new Set([...ds].flatMap(d=>[d,d-6])))if(d>0)pool*=BigInt(d/2);let prod=[...ls.keys()].reduce((v,p)=>v*BigInt(p),1n);ok(pool%prod===0n,"tube product");
    for(let [p,l] of ls){let R=0;for(let i=1;i<l.length;i++){ok(l[i].D===l[0].D,"one stratum");if(l[i].q-l[i-1].q===2)R++}ok(12*p*l.length<=G+14*p+2+12*p*R,"weighted stratum capacity");W+=p*R;Q+=14*p+2;st.nearFlatLabelChecks++;st.nearFlatTwinPairs+=R}
    ok(12*F<=ls.size*G+Q+12*W,"tube capacity");st.nearFlatControls++;if(F){st.nearFlatPositiveGain++;if(W&&st.nearFlatExamples.length<3)st.nearFlatExamples.push({T,M,G,F,W,levels:[...ds],labels:[...ls.keys()]})}
    a=b
   }
   for(let a=0;a<rows.length;){if(rows[a].dp!==rows[a].d){a++;continue}let b=a+1,d=rows[a].d;while(b<rows.length&&rows[b].d===d&&rows[b].dp===d)b++;
    let G=rows[b-1].H+rows[b-1].p-1-rows[a].H,ls=new Map,F=0,sum=0;
    for(let i=a;i<b;i++){let z=rows[i];if(z.p<T||z.D<=0||z.w<=6)continue;if(!ls.has(z.p))ls.set(z.p,[]);ls.get(z.p).push(z);F+=z.p-1}
    for(let [p,l] of ls){for(let i=1;i<l.length;i++){ok(l[i].I===l[0].I&&l[i].D===l[0].D&& (l[i].q-l[i-1].q)%12===0,"flat phase")}ok(12*p*(l.length-1)<=G,"flat span");sum+=p}
    ok(12*F<=ls.size*G+12*sum,"flat capacity");st.flatControls++;if(F)st.flatPositiveGain++;a=b
   }
  }
  for(let [p,list] of groups){if(list.length<2)continue;st.groups++;
   // Same-D selected nonreset visits, with arbitrary physical intervening events.
   let strata=new Map;for(let z of list)if(z.D>0&&z.w>6){if(!strata.has(z.D))strata.set(z.D,[]);strata.get(z.D).push(z)}
   for(let [D,l] of strata){if(l.length<2)continue;let G=l.at(-1).H+p-1-l[0].H,R=0,ds=new Set(l.map(z=>z.dp));ok(ds.size<=2&&Math.max(...ds)-Math.min(...ds)<=6,"selected tube");for(let i=1;i<l.length;i++){if(l[i].q-l[i-1].q===2)R++;st.selectedStratumRepeatChecks++}ok(12*p*l.length<=G+14*p+2+12*p*R,"selected stratum charge");st.selectedStratumControls++;st.selectedStratumTwinPairs+=R;
    if(R&&st.selectedStratumExamples.length<4)st.selectedStratumExamples.push({M,p,D,q:l.map(z=>z.q),H:l.map(z=>z.H),w:l.map(z=>z.w),d:l.map(z=>z.dp),G,R})
   }
   for(let i=1;i<list.length;i++){let a=list[i-1],b=list[i],m=(b.q-a.q)/2;ok(Number.isInteger(m)&&m>=1&&b.H-a.H===2*m*p+b.e-a.e,"return");st.pairChecks++;if(m===1)st.twinPairs++;else st.noTwinPairs++;
    if(a.w>6&&b.w>6){let s1=mod(a.e*p,3)===1?1:-1,s2=mod(b.e*p,3)===1?1:-1;ok(m>=3+(s1-s2)/2-3*Number(m===1),"corrected mod3");st.mod3Pairs++;if(a.D===b.D){ok(m>=6+(s1-s2)/2-6*Number(m===1),"corrected stratum");st.stratumPairs++}}
   }
   for(let K of [2,8,32]){let start=0;while(start<list.length){let end=start+1;while(end<list.length&&list[end].q-list[end-1].q<=2*K)end++;let len=end-start;st.components++;
     for(let j of [2,3,4]){let n=Math.max(0,len-j+1);ok(len<j||len<=j*n,"component covering");st.componentWindowChecks++;if(K===8)for(let i=start;i+j<=end;i++)pattern(p,list.slice(i,i+j))}
     start=end;
   }}
  }
 }
 // Exact finite Selberg weights for arbitrary forbidden-residue systems from 2j forms.
 // f>nu ensures rho(f)<f. Use common integer denominator for all g and weights.
 function sieve(p,a,e,z,N,start){
  let fs=forms(p,a,e),nu=fs.length,D=delta(fs),F=pr.filter(f=>f>nu&&f<=z&&f!==p).map(f=>({f,r:residues(fs,f)}));
  for(let {f,r} of F){ok(r.length>0&&r.length<f,"rho range");if(D%BigInt(f)!==0n)ok(r.length===nu,"generic");}
  let B=F.reduce((x,v)=>x*BigInt(v.f-v.r.length),1n),R=F.reduce((x,v)=>x*BigInt(v.r.length),1n),P=F.reduce((x,v)=>x*BigInt(v.f),1n),ds=[];
  function rec(i,d,rho,den,sgn){if(d>z)return;ds.push({d,rho,den,sgn,b:B*rho/den});for(let h=i;h<F.length;h++){let {f,r}=F[h];if(d*f<=z)rec(h+1,d*f,rho*BigInt(r.length),den*BigInt(f-r.length),-sgn)}}
  rec(0,1,1n,1n,1n);let G=ds.reduce((s,v)=>s+v.b,0n),scale=G*R;
  for(let d of ds){let s=ds.filter(v=>v.d%d.d===0).reduce((s,v)=>s+v.b,0n);d.l=BigInt(d.sgn)*BigInt(d.d)*s*(R/d.rho);ok((d.l<0n?-d.l:d.l)<=BigInt(d.d)*scale,"weight bound");st.sieveWeights++}
  ok(ds[0].l===scale,"lambda1");let Q=0n;for(let d of ds)for(let e of ds){let l=BigInt(d.d)*BigInt(e.d)/gcd(BigInt(d.d),BigInt(e.d)),rho=1n;for(let f of F)if(l%BigInt(f.f)===0n)rho*=BigInt(f.r.length);Q+=d.l*e.l*rho*(P/l);st.quadraticChecks++}
  ok(Q*G===scale*scale*P*B,"exact optimal quadratic");
  let count=0n,sum=0n;for(let x=start;x<start+N;x++){let mask=F.filter(f=>f.r.includes(mod(x,f.f))),D=mask.reduce((s,v)=>s*BigInt(v.f),1n),v=ds.filter(d=>D%BigInt(d.d)===0n).reduce((s,d)=>s+d.l,0n);if(D===1n){count++;ok(v===scale,"survivor majorant")}sum+=v*v;st.majorantChecks++}
  ok(count*scale*scale<=sum&&sum*G<=BigInt(N)*B*scale*scale+BigInt(z)**6n*scale*scale*G,"finite sieve");
  // Exact truncated Euler mass on a small support; compare Markov bound in product units.
  let E=F.filter(f=>f.f<=Math.min(z,19)&&D%BigInt(f.f)!==0n),total=0n,kept=0n,den=E.reduce((v,f)=>v*BigInt(f.f-f.r.length),1n);
  for(let m=0;m<2**E.length;m++){let d=1,w=den;for(let i=0;i<E.length;i++)if(m&(1<<i)){d*=E[i].f;w=w/BigInt(E[i].f-E[i].r.length)*BigInt(E[i].r.length)}total+=w;if(d<=z)kept+=w}
  ok(kept*B<=G*den&&kept<=total,"truncated product lower");st.productTruncationChecks++;st.sieveControls++
 }
 for(let j of [2,3,4])for(let p of [53,101,107])for(let z of [13,23,43])for(let typ of [0,1]){let a=Array.from({length:j},(_,i)=>2*i*(typ?3:1)),e=a.map((_,i)=>typ&&i%2?-1:1);sieve(p,a,e,z,200,typ?-100:1)}
 ok(st.windowsByJ[2]>0&&st.windowsByJ[3]>0&&st.sieveControls&&st.stratumPairs&&st.nearFlatPositiveGain&&st.flatPositiveGain&&st.selectedStratumRepeatChecks&&st.selectedStratumTwinPairs,"coverage");
 return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
