// Varying-support leaf CRT packing and disjoint cluster gain bound.
function audit(N=18000){
 const cap=500000,spf=new Int32Array(cap),ps=[];
 for(let i=2;i<cap;i++)if(!spf[i]){spf[i]=i;if(i%2&&i<=1000)ps.push(i);if(i*i<cap)for(let j=i*i;j<cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b,assert=(x,m)=>{if(!x)throw Error(m)};
 function choose(n,k){if(k<0||k>n)return 0n;let v=1n;for(let i=1;i<=k;i++)v=v*BigInt(n-i+1)/BigInt(i);return v}
 function factors(a){assert(a>0&&a<cap,"sieve");let v=[];while(a>1){let p=spf[a];v.push(p);while(a%p===0)a/=p}return v}
 function next(H,t){let best=null;for(let e of [1,-1])for(let p of factors(H-e)){if(p===2||p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={H,t,p,e,w}}return best}
 const cfgs=[[5,4,3,0],[5,4,3,2],[7,4,4,4],[11,4,4,6],[23,4,4,12],[47,3,3,16],[71,2,4,8]].map(([T,C,k,U])=>{assert(U<T-1,"threshold");return {T,C,k,U,groups:new Map,minH:Infinity,maxH:0}});
 let st={canonicalRoots:0,canonicalEvents:0,capUnresolved:0,relaxedPaths:0,explicitControls:0,rayControls:0,nonemptyBlocks:0,varyingSupportRays:0,selectedHigh:0,leaves:0,smallLeaves:0,smallCanonical:0,smallRelaxed:0,zeroLeaves:0,positiveSmallLeaves:0,largeLeaves:0,leafShapeChecks:0,linearSolveChecks:0,gapVectorChecks:0,groupChecks:0,spacingChecks:0,aggregateCapacityChecks:0,aggregateRayChecks:0,uniqueCodeStarts:0,largeGainChecks:0,largestSmallArity:0,zeroExample:null,positiveExample:null};
 function inspect(rows,F,c,actual){
  let high=[],out=[0],B=0,set=new Set(F);
  for(let i=0;i<rows.length;i++){let z=rows[i];assert(z.H%2===0&&mod(z.H-z.e,z.p)===0,"relaxed step");if(i+1<rows.length)assert(rows[i+1].H===z.H+z.p-1,"contiguous");if(set.has(z.p))high.push({...z,i});else B+=z.p-1;out.push(B)}
  let K=high.length;if(!K)return {K:0,B,L:0,s:0,big:0};
  let last=new Map,vis=[];
  for(let j=0;j<K;j++){let a=high[j],i=last.get(a.p);if(i!==undefined&&!high.slice(i+1,j).some(b=>b.p>a.p))vis.push({i,j,kids:0});last.set(a.p,j)}
  vis.sort((a,b)=>a.i-b.i||b.j-a.j);let stack=[];
  for(let a of vis){while(stack.length&&stack.at(-1).j<=a.i)stack.pop();if(stack.length){let b=stack.at(-1);assert(a.i>b.i&&a.j<b.j,"laminar");b.kids++}stack.push(a)}
  let leaves=vis.filter(a=>!a.kids),small=0,large=0,pay=0,prev=-1;
  for(let a of leaves){
   assert(a.i>=prev,"disjoint");prev=a.j;let seq=high.slice(a.i,a.j+1),E=out[seq.at(-1).i]-out[seq[0].i],l=new Set(seq.map(z=>z.p)).size,m=seq.length-1,p=seq[0].p;
   assert(seq.at(-1).p===p&&seq.slice(1,-1).every(z=>z.p<p)&&m<=2**(l-1)&&m>=l,"leaf shape");st.leafShapeChecks++;
   pay+=E;st.leaves++;
   if(E>c.U){large++;st.largeLeaves++;continue}
   small++;st.smallLeaves++;if(actual)st.smallCanonical++;else st.smallRelaxed++;
   assert(l>=2&&l<=c.k&&c.U<c.T-1,"small arity");if(E===0){assert(l>=3,"pair nonresonance");st.zeroLeaves++}else st.positiveSmallLeaves++;
   let gaps=[];for(let i=0;i<m;i++)gaps.push(out[seq[i+1].i]-out[seq[i].i]);
   assert(gaps.every(x=>x>=0&&x%2===0)&&gaps.reduce((x,y)=>x+y,0)===E,"gap vector");st.gapVectorChecks++;
   let missing=seq[1].p,coef=0,other=0;for(let z of seq.slice(1,-1)){if(z.p===missing)coef++;else other+=z.p-1}
   let eps=seq.at(-1).e-seq[0].e,diff=seq.at(-1).H-seq[0].H,Z=(diff-eps)/p;
   assert(Number.isInteger(Z)&&Z>=0&&Z<=Math.ceil(m*c.C+(c.U+2)/c.T),"quotient");
   assert((Z*p+eps-(p-1)-E-other)/coef+1===missing,"linear solve");st.linearSolveChecks++;
   let support=[...new Set(seq.map(z=>z.p))],P=2n*support.reduce((v,q)=>v*BigInt(q),1n),g=0,h=seq[0].H;
   for(let i=0;i<=m;i++){assert(seq[i].H===h+g&&mod(h+g-seq[i].e,seq[i].p)===0,"horizon code");if(i<m)g+=seq[i].p-1+gaps[i]}
   let key=JSON.stringify([seq.map(z=>[z.p,z.e]),gaps]),r=c.groups.get(key);if(!r){r={P,h:new Set};c.groups.set(key,r)}
   r.h.add(h);c.minH=Math.min(c.minH,h);c.maxH=Math.max(c.maxH,h);st.largestSmallArity=Math.max(st.largestSmallArity,l);
   let example={T:c.T,C:c.C,k:c.k,U:c.U,labels:seq.map(z=>z.p),gaps,H:h,actual};
   if(E===0&&!st.zeroExample)st.zeroExample=example;if(E>0&&!st.positiveExample)st.positiveExample=example;
  }
  let Q=2**c.k-1,Uplus=2*(Math.floor(c.U/2)+1);
  assert(pay<=B&&large*Uplus<=B,"large leaf charge");st.largeGainChecks++;
  assert(K<=Q*(1+small+large),"forest count");st.nonemptyBlocks++;st.selectedHigh+=K;
  return {K,B,L:1,s:small,big:large}
 }
 function ray(rows,c,actual,blockSize=18){
  let K=0,B=0,L=0,s=0,big=0,types=new Set;
  for(let i=0;i<rows.length;i+=blockSize){let a=rows.slice(i,i+blockSize),cnt=new Map;
   for(let z of a)if(z.p>=c.T&&z.p<=c.C*c.T)cnt.set(z.p,(cnt.get(z.p)||0)+1);
   let F=[...cnt].sort((x,y)=>y[1]-x[1]||x[0]-y[0]).slice(0,c.k).map(x=>x[0]).sort((a,b)=>a-b);
   if(F.length)types.add(F.join(","));let z=inspect(a,F,c,actual);K+=z.K;B+=z.B;L+=z.L;s+=z.s;big+=z.big;
  }
  if(types.size>1)st.varyingSupportRays++;
  let Q=2**c.k-1,Uplus=2*(Math.floor(c.U/2)+1);
  assert(K<=Q*(L+s+big)&&((K-Q*(L+s))*Uplus<=Q*B),"aggregate disjoint-block inequality");
  st.aggregateRayChecks++;st.rayControls++;
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.canonicalRoots++;
  for(let i=0;i<180;i++){let a=next(H,t);if(!a)break;rows.push(a);H+=a.p-1;t+=a.w}
  if(rows.length===180&&next(H,t))st.capUnresolved++;st.canonicalEvents+=rows.length;for(let c of cfgs)ray(rows,c,true)
 }
 let seed=13579;const rand=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n};
 const pool=ps.filter(p=>p<=199);
 for(let z=0;z<9000;z++){
  let H=100+2*rand(50000),rows=[],c=cfgs[z%cfgs.length],band=pool.filter(p=>p>=c.T&&p<=c.C*c.T);
  let want=[];while(want.length<Math.min(band.length,c.k)){let a=band[rand(band.length)];if(!want.includes(a))want.push(a)}
  for(let i=0;i<75;i++){let cand=pool.filter(p=>mod(H,p)===1||mod(H,p)===p-1);if(!cand.length)break;let p0=cand.filter(p=>want.includes(p)),p=p0.length&&rand(5)!==0?p0[rand(p0.length)]:cand[rand(cand.length)];rows.push({H,p,e:H%p===1?1:-1});H+=p-1}
  if(rows.length){ray(rows,c,false,25);st.relaxedPaths++}
 }
 function explicit(word,H,F,c){let rows=[];for(let p of word){let a=mod(H,p);assert(a===1||a===p-1,"explicit");rows.push({H,p,e:a===1?1:-1});H+=p-1}let z=inspect(rows,F,c,false);assert(z.s>0,"explicit small leaf");st.explicitControls++}
 explicit([13,5,7,5,13],73462,[5,7,13],cfgs[0]);
 let found=false;
 for(let H=100;H<10000;H+=2){if(H%13!==1)continue;let h=H+12;if(![1,10].includes(h%11))continue;h+=10;if(![1,2].includes(h%3))continue;h+=2;if(h%13!==12)continue;explicit([13,11,3,13],H,[11,13],cfgs[1]);found=true;break}
 assert(found,"positive explicit");
 let summaries=[];
 for(let c of cfgs){
  let G=Number.isFinite(c.minH)?c.maxH-c.minH:0,n=ps.filter(p=>p>=c.T&&p<=c.C*c.T).length,cap=0n,starts=0n;
  for(let l=2;l<=c.k;l++){
   if(c.U===0&&l===2)continue;
   let codes=0n;
   for(let m=l;m<=2**(l-1);m++){let Z=Math.ceil(m*c.C+(c.U+2)/c.T);codes+=BigInt(l-1)**BigInt(m-1)*2n**BigInt(m+1)*BigInt(Z+1)*choose(Math.floor(c.U/2)+m,m)*BigInt(n)**BigInt(l-1)}
   cap+=codes*(1n+BigInt(G)/(2n*BigInt(c.T)**BigInt(l)));
  }
  for(let r of c.groups.values()){let v=[...r.h].sort((a,b)=>a-b);for(let i=1;i<v.length;i++){assert(BigInt(v[i]-v[i-1])%r.P===0n,"CRT gap");st.spacingChecks++}assert(BigInt(v.length)<=1n+BigInt(G)/r.P,"code capacity");st.groupChecks++;starts+=BigInt(v.length)}
  assert(starts<=cap,"total code/start bound");st.aggregateCapacityChecks++;st.uniqueCodeStarts+=Number(starts);
  summaries.push({T:c.T,C:c.C,k:c.k,U:c.U,n,G,groups:c.groups.size,starts:String(starts),finiteBound:String(cap)})
 }
 assert(st.zeroLeaves&&st.positiveSmallLeaves&&st.smallCanonical&&st.smallRelaxed&&st.spacingChecks&&st.varyingSupportRays&&st.largeLeaves,"coverage");
 return {stats:st,controls:summaries}
}
console.log(JSON.stringify(audit(Number(process.argv[2]||18000)),null,2));
