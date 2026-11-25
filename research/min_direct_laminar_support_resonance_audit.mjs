// Laminar visible repeats: exact support resonance and disjoint outside-gain budget.
function audit(N=12000){
 const limit=600000,spf=new Int32Array(limit),primes=[];for(let i=2;i<limit;i++)if(!spf[i]){spf[i]=i;if(i%2&&i<10000)primes.push(i);if(i*i<limit)for(let j=i*i;j<limit;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,p)=>(a%p+p)%p,assert=(x,msg)=>{if(!x)throw Error(msg)};
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function factors(a){let f=[];assert(a>0&&a<limit,"factor range");while(a>1){let p=spf[a];f.push(p);while(a%p===0)a/=p}return f}
 function event(H,t){let best=null;for(let I=0;I<=1;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={H,t,p,w,e:1-2*I}}return best}
 const st={roots:0,canonicalEvents:0,canonicalTruncated:0,clockComparisons:0,literalTicks:0,controls:0,highEvents:0,outsideEvents:0,visibleIntervals:0,nestedIntervals:0,leaves:0,zeroResonanceLeaves:0,positiveLeaves:0,leafVectorChecks:0,leafCostChecks:0,forestChecks:0,rankChecks:0,combinedChecks:0,allSupportBlocks:0,allSupportLong:0,narrowSupportChecks:0,narrowBlockChecks:0,pairFormulaChecks:0,resonanceTuples:0,resonantTuples:0,nonresonantTuples:0,linearWitnessChecks:0,syntheticPaths:0,maxDepth:0,maxK:0,maxLeafOutside:0,exactResonantExample:null,non3ResonantExample:null};
 const memo=new Map;
 function resonance(F){
  let key=F.join(","),old=memo.get(key);if(old)return old;
  let delta=[],witness=[];
  for(let r=0;r<F.length;r++){
   let p=F[r],best=Infinity,win=null,m=[];
   function walk(i,G){if(i===r){for(let eps of [-2,0,2]){let E=mod(eps-(p-1)-G,p);if(E%2)E+=p;if(E<best){best=E;win={m:m.slice(),eps,E}}}return}
    for(let c=0;c<=2**(r-1-i);c++){m.push(c);walk(i+1,G+c*(F[i]-1));m.pop()}
   }walk(0,0);delta.push(best);witness.push(win);
  }
  let mn=Math.min(...delta),ans={delta,mn,witness};memo.set(key,ans);
  if(F.length===2){assert(delta[0]===(F[0]===3?0:F[0]-1)&&delta[1]===F[1]-F[0],"pair formula "+F+" "+delta);st.pairFormulaChecks++}
  let T=F[0],U=F.at(-1),k=F.length;
  if(T>=5&&k>=2&&2**(k-1)*(U-T+1)+2<T){let gap=Math.min(...F.slice(1).map((p,i)=>p-F[i]));assert(mn>=gap,"narrow spectrum");st.narrowSupportChecks++}
  return ans
 }
 function inspect(rows,F,actual=true){
  if(!rows.length||!F.length||F.length>5)return;
  F=[...new Set(F)].sort((a,b)=>a-b);let k=F.length,Kmax=2**k-1,rank=new Map(F.map((p,i)=>[p,i])),res=resonance(F);
  let high=[],out=[0],B=0;
  for(let i=0;i<rows.length;i++){let z=rows[i];assert(z.H%2===0&&mod(z.H-z.e,z.p)===0,"relaxed");if(i+1<rows.length)assert(rows[i+1].H===z.H+z.p-1,"contiguous");if(rank.has(z.p))high.push({i,p:z.p,r:rank.get(z.p),e:z.e,H:z.H});else{B+=z.p-1;st.outsideEvents++}out.push(B)}
  let K=high.length;if(!K)return;st.controls++;st.highEvents+=K;st.maxK=Math.max(st.maxK,K);
  let last=new Map,visible=[],counts=new Array(k).fill(0),v=new Array(k).fill(0);
  for(let j=0;j<K;j++){let a=high[j],i=last.get(a.p);counts[a.r]++;if(i!==undefined&&!high.slice(i+1,j).some(q=>q.p>a.p)){visible.push({i,j,r:a.r,p:a.p,kids:[]});v[a.r]++;}last.set(a.p,j)}
  visible.sort((a,b)=>a.i-b.i||b.j-a.j);let stack=[],leaves=[];
  for(let I of visible){while(stack.length&&stack.at(-1).j<=I.i)stack.pop();if(stack.length){let P=stack.at(-1);assert(I.j<P.j&&I.i>P.i&&I.p<P.p,"laminar");P.kids.push(I);st.nestedIntervals++}stack.push(I);st.maxDepth=Math.max(st.maxDepth,stack.length);assert(stack.length<=k,"depth")}
  let Vw=0,weights=0,paid=0,zero=0;
  for(let I of visible){Vw+=2**I.r;if(I.kids.length)continue;
   leaves.push(I);let a=high[I.i],b=high[I.j],m=new Array(I.r).fill(0),G=0;
   for(let j=I.i+1;j<I.j;j++){let z=high[j];assert(z.r<I.r,"leaf interior smaller");m[z.r]++;G+=z.p-1}
   for(let r=0;r<I.r;r++){assert(m[r]<=2**(I.r-1-r),"leaf multiplicity");st.leafVectorChecks++}
   assert(I.j-I.i<=2**I.r,"leaf length");
   let E=out[b.i]-out[a.i];assert(E>=0&&E%2===0&&b.H-a.H===a.p-1+G+E,"physical outside gain");
   assert(mod(a.p-1+G+E-(b.e-a.e),a.p)===0,"return congruence");
   assert(E>=res.delta[I.r],"resonance charge");st.leafCostChecks++;st.maxLeafOutside=Math.max(st.maxLeafOutside,E);
   if(!res.delta[I.r]){zero++;st.zeroResonanceLeaves++;if(E===0){let ex={F,labels:high.slice(I.i,I.j+1).map(x=>x.p),H:a.H,actual};if(!st.exactResonantExample)st.exactResonantExample=ex;if(F[0]>3&&!st.non3ResonantExample)st.non3ResonantExample=ex;}}else st.positiveLeaves++;
   paid+=E;
  }
  for(let i=1;i<leaves.length;i++)assert(leaves[i-1].j<=leaves[i].i,"disjoint leaves");
  assert(paid<=B,"no double charge");st.forestChecks++;
  for(let I of visible){let L=I;while(L.kids.length)L=L.kids[0];L.weight=(L.weight||0)+2**I.r}
  for(let L of leaves){assert(L.weight<=Kmax,"weighted ancestor bound");weights+=L.weight}
  assert(weights===Vw,"all assigned");st.rankChecks++;
  let above=0;for(let r=k-1;r>=0;r--){assert(counts[r]<=1+v[r]+above,"rank recurrence");above+=counts[r]}
  assert(K<=Kmax+Vw&&K<=Kmax*(1+leaves.length),"weighted word bound");
  let pos=res.delta.filter(x=>x>0),D=pos.length?Math.min(...pos):Infinity;
  if(D!==Infinity)assert((K-Kmax*(1+zero))*D<=Kmax*B,"mixed resonance charge");
  if(res.mn>0)assert((K-Kmax)*res.mn<=Kmax*B,"combined budget");
  if(k===2&&F[0]>=5)assert((K-3)*((F[0]-1)*(F[1]-F[0]))<=B*Math.max(3*(F[1]-F[0]),2*(F[0]-1)),"pair budget");
  st.combinedChecks++;st.visibleIntervals+=visible.length;st.leaves+=leaves.length;
  if(B===0){st.allSupportBlocks++;if(K>Kmax){st.allSupportLong++;assert(res.mn===0,"exact resonance forced")}}
  if(k>=2&&F[0]>=5&&2**(k-1)*(F.at(-1)-F[0]+1)+2<F[0]){let gap=Math.min(...F.slice(1).map((p,i)=>p-F[i]));assert((K-Kmax)*gap<=Kmax*B,"narrow block");st.narrowBlockChecks++}
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;
  for(let z=0;z<180;z++){let a=event(H,t);if(!a)break;if(st.clockComparisons++%67===0){let hit=null;for(let w=1;w<=a.w;w++){let n=t+w,I=n%2,g=gcd(n-2*I,H-(1-2*I)),p=g>1?spf[g]:0;st.literalTicks++;if(p&&p*p<=H+1){hit={p,w,e:1-2*I};break}}assert(hit&&hit.p===a.p&&hit.w===a.w&&hit.e===a.e,"independent tick clock")}
   rows.push(a);H+=a.p-1;t+=a.w;
  }st.canonicalEvents+=rows.length;if(rows.length===180&&event(H,t))st.canonicalTruncated++;
  let freq=new Map;for(let a of rows)freq.set(a.p,(freq.get(a.p)||0)+1);let order=[...freq].sort((a,b)=>b[1]-a[1]||a[0]-b[0]).map(a=>a[0]);
  for(let k of [2,3,4,5])if(order.length>=k)inspect(rows,order.slice(0,k));
  for(let i=0;i<rows.length;i+=7){let sub=rows.slice(i,i+12),f=[...new Set(sub.map(a=>a.p))];if(f.length<=5)inspect(sub,f)}
 }
 let seed=24681357;function rand(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n}
 const pool=primes.filter(p=>p<=199);
 for(let z=0;z<12000;z++){
  let H=100+2*rand(40000),rows=[],F=[];
  if(z%2===0){let j=rand(pool.length-5);F=pool.slice(j,j+2+rand(3))}else while(F.length<3){let p=pool[rand(pool.length)];if(!F.includes(p))F.push(p)}
  for(let i=0;i<90;i++){let cand=pool.filter(p=>mod(H,p)===1||mod(H,p)===p-1);if(!cand.length)break;let preferred=cand.filter(p=>F.includes(p)),p=preferred.length&&rand(4)!==0?preferred[rand(preferred.length)]:cand[rand(cand.length)];rows.push({H,p,e:H%p===1?1:-1});H+=p-1}
  if(rows.length){inspect(rows,F,false);st.syntheticPaths++}
 }
 for(let T of [11,31,71,131,251]){
  let ps=primes.filter(p=>p>=T&&p<=2*T);
  for(let k of [2,3,4]){let v=[];function rec(i){if(v.length===k){let a=resonance(v);st.resonanceTuples++;
    if(a.mn<=2){st.resonantTuples++;let r=a.delta.indexOf(a.mn),p=v[r],w=a.witness[r],sum=w.m.reduce((s,c,i)=>s+c*(v[i]-1),0),numer=p-1+sum+w.E-w.eps;assert(numer%p===0,"linear resonance");assert(numer/p>=0&&numer/p<=2**k+2,"bounded quotient");if(!w.m.some(Boolean))assert(w.E>=p-1,"empty not near resonant");st.linearWitnessChecks++}else st.nonresonantTuples++;
    return}for(let j=i;j<=ps.length-(k-v.length);j++){v.push(ps[j]);rec(j+1);v.pop()}}rec(0)}
 }
 assert(st.visibleIntervals&&st.nestedIntervals&&st.positiveLeaves&&st.zeroResonanceLeaves&&st.narrowBlockChecks&&st.allSupportLong&&st.linearWitnessChecks,"nonvacuous coverage");
 return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||12000)),null,2));
