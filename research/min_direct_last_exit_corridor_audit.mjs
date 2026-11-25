// Last-exit A1 recovery corridors: actual/relaxed checks and disjoint band covers.
function audit(N=60000){
 const cap=1000000,spf=new Int32Array(cap),pr=[];
 for(let i=2;i<cap;i++)if(!spf[i]){spf[i]=i;if(i%2)pr.push(i);if(i*i<cap)for(let k=i*i;k<cap;k+=i)if(!spf[k])spf[k]=i}
 const mod=(a,b)=>(a%b+b)%b,assert=(v,m)=>{if(!v)throw Error(m)},gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a<0n?-a:a};
 const prod=a=>a.reduce((v,p)=>v*BigInt(p),1n);
 const fct=a=>{let a0=a,f=[];assert(a>0&&a<cap,"sieve "+a0);while(a>1){let p=spf[a];f.push(p);while(a%p===0)a/=p}return f};
 function next(H,t){let best=null;for(let I=0;I<2;I++)for(let p of fct(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={H:BigInt(H),d:2*t-H,p,w,I}}return best}
 const stat={canonicalRoots:0,canonicalEvents:0,unresolved:0,actualWitnessRoots:0,witnessTicks:0,witnessResidues:0,relaxedControls:0,bandControls:0,marks:0,completeCores:0,pending:0,goodCorridors:0,badReset:0,badHighB:0,goodActual:0,goodRelaxed:0,goodEvents:0,corridorGain:0,corridorDrop:0,nearExclusion:0,allCorridorEvents:0,resetWeightChecks:0,highBWeightChecks:0,overlapChecks:0,colorChecks:0,maxOverlap:0,supportChecks:0,recordSupportChecks:0,recordEvents:0,recordDistinctForced:0,maxRecordDistinct:0,recordMultiplicityChecks:0,discoveryChecks:0,distinctForced:0,maxDistinct:0,laminarChecks:0,lowRunChecks:0,goodWitness:null,badWitness:null};
 const reset=z=>z.p>=5&&z.dp===6*z.I;
 const a1=z=>z.p>=47&&z.p>=5*(z.d+3)&&z.dp-6*z.I===2*z.p;
 function validate(rows){
  for(let i=0;i<rows.length;i++){
   let z=rows[i];z.dp=z.d+2*z.w-z.p+1;assert(z.d>=0&&z.dp>=0&&z.d%2===0&&z.dp%2===0&&z.w>=1,"envelope");
   let e=1n-2n*BigInt(z.I),p=BigInt(z.p),n=(z.H+BigInt(z.d))/2n+BigInt(z.w);
   assert((z.H-e)%p===0n&&(n-2n*BigInt(z.I))%p===0n&&n%2n===BigInt(z.I)&&p*p<=z.H+1n,"clock");
   if(z.p>=5)assert((z.dp-6*z.I)%(2*z.p)===0&&z.dp>=6*z.I,"multiplier");
   if(i+1<rows.length)assert(rows[i+1].d===z.dp&&rows[i+1].H===z.H+p-1n,"contiguous")
  }
 }
 function inspect(rows,R,T0,kind){
  if(!rows.length)return;
  let xs=[...rows.map(z=>z.d+3),rows.at(-1).dp+3],C=Math.max(...rows.map(z=>z.p)),all=[],badR=new Map,badB=new Map,totalPendingWeight=0;
  let G=Number(rows.at(-1).H+BigInt(rows.at(-1).p-1)-rows[0].H),Psmall=new Map;
  const primeProd=S=>{if(!Psmall.has(S))Psmall.set(S,prod(pr.filter(p=>p<=S)));return Psmall.get(S)};
  let runs=new Map,run=-1;
  for(let i=0;i<rows.length;i++)if(rows[i].p<=R){if(i===0||rows[i-1].p>R)run=i;runs.set(i,run)}
  for(let T=T0,band=0;T<=C;T*=2,band++){
   let marks=[];for(let i=0;i<rows.length;i++)if(a1(rows[i])&&rows[i].p>R&&rows[i].p>=T&&rows[i].p<2*T)marks.push(i);
   if(!marks.length)continue;stat.bandControls++;stat.marks+=marks.length;let prev=-1,pending=0,prevRun=-1;
   for(let i of marks){
    let b=i+1;while(b<xs.length&&5*xs[b]>2*T)b++;
    if(b===xs.length){pending++;stat.pending++;totalPendingWeight+=rows[i].p;continue}
    assert(i>=prev,"disjoint cores");prev=b;stat.completeCores++;
    let a=b-1;while(10*xs[a]<19*T)a--;
    assert(a>=i+1&&a<b&&10*xs[a]>=19*T&&5*xs[b]<=2*T,"corridor endpoints");
    let zr=-1,zb=-1,gain=0,time=0,F=new Set;
    for(let h=a;h<b;h++){
     let z=rows[h];assert(5*xs[h]>2*T&&10*xs[h+1]<19*T&&!a1(z),"no A1 corridor");
     if(reset(z)){assert(h===b-1&&z.p>=7&&5*(z.p+6)>2*T,"reset location");zr=h}
     if(z.p>R&&!reset(z)){
      assert(z.p>=47&&z.p<5*xs[h]&&20*z.p<19*T&&20*xs[h]<57*T,"localized high B");
      let q=(z.H-(1n-2n*BigInt(z.I)))/BigInt(z.p),gap=q-BigInt(z.p);
      if(z.H>=6250001n){assert(gap*gap>q+BigInt(z.p),"near exclusion");stat.nearExclusion++}
      if(zb<0)zb=h
     }
     gain+=z.p-1;time+=z.w;F.add(z.p);stat.allCorridorEvents++;
    }
    assert(gain===xs[a]-xs[b]+2*time&&2*gain>=3*T,"drop and gain");
    if(zr>=0){stat.badReset++;badR.set(zr,(badR.get(zr)||0)+rows[i].p);continue}
    if(zb>=0){stat.badHighB++;let list=badB.get(zb)||[];list.push(rows[i].p);badB.set(zb,list);if(kind==="witness"&&!stat.badWitness)stat.badWitness={R,T,mark:rows[i].p,high:rows[zb].p,pre:xs[zb],post:xs[zb+1]};continue}
    assert(20*xs[a]<57*T&&15*xs[b]>4*T,"bounded corridor");
    assert([...F].every(p=>p<=R),"low support");
    let run0=runs.get(a);assert(run0!==undefined&&run0!==prevRun&&runs.get(b-1)===run0,"different maximal low runs");prevRun=run0;stat.lowRunChecks++;
    const P=prod([...F]),drop=xs[a]-xs[b];
    assert(BigInt(gain)<2n*P&&BigInt(drop)<P+5n&&2n*P>BigInt(3*T-10),"support barriers");stat.supportChecks++;
    let recMin=xs[a],recF=new Set,recCount=new Map;
    for(let h=a;h<b;h++)if(xs[h+1]<recMin){let z=rows[h];assert(z.p>=5&&!reset(z)&&z.dp>=2*z.p,"record nonreset");recMin=xs[h+1];recF.add(z.p);recCount.set(z.p,(recCount.get(z.p)||0)+1);stat.recordEvents++}
    assert(recMin===xs[b],"last is first low crossing");
    let Pr=prod([...recF]);
    assert(BigInt(drop)<Pr+5n&&2n*Pr>BigInt(3*T-10),"record-only deficit barrier");
    for(let [p,n] of recCount){assert(n<=2*(1+Math.floor((xs[a]-xs[b])/(2*p))),"record multiplier multiplicity");stat.recordMultiplicityChecks++}
    stat.recordSupportChecks++;stat.maxRecordDistinct=Math.max(stat.maxRecordDistinct,recF.size);
    for(let S of [3,7,Math.max(7,Math.floor(R/4)),Math.max(7,Math.floor(R/2)),R]){
     let j=[...F].filter(p=>p>S).length,upper=primeProd(S)*BigInt(R)**BigInt(j);
     assert(upper>=P&&2n*upper>BigInt(3*T-10),"discovery product");
     let forced=0,v=primeProd(S);while(2n*v<=BigInt(3*T-10)){forced++;v*=BigInt(R)}
     assert(j>=forced,"forced distinct");let jr=[...recF].filter(p=>p>S).length;assert(jr>=forced,"forced record labels");stat.recordDistinctForced+=forced;stat.discoveryChecks++;stat.distinctForced+=forced
    }
    // For a distinguished subset of at most 3 comparable labels, check a disjoint-leaf outside budget.
    let cand=[...F].filter(p=>p>=R/4).sort((a,b)=>b-a).slice(0,3),set=new Set(cand),q=2**cand.length-1,word=rows.slice(a,b).filter(z=>set.has(z.p)),B=rows.slice(a,b).filter(z=>!set.has(z.p)).reduce((s,z)=>s+z.p-1,0);
    let vis=[],last=new Map;for(let j=0;j<word.length;j++){let p=word[j].p,k=last.get(p);if(k!==undefined&&!word.slice(k+1,j).some(v=>v.p>p))vis.push([k,j]);last.set(p,j)}
    let leaves=vis.filter(([i,j])=>!vis.some(([u,v])=>i<u&&v<j));
    assert(word.length<=q*(1+leaves.length)&&gain<=B+(R-1)*q*(1+leaves.length),"laminar cover");stat.laminarChecks++;
    all.push({a,b,band,T,gain,drop,mark:rows[i].p});stat.goodCorridors++;if(kind==="relaxed")stat.goodRelaxed++;else stat.goodActual++;
    stat.goodEvents+=b-a;stat.corridorGain+=gain;stat.corridorDrop+=drop;stat.maxDistinct=Math.max(stat.maxDistinct,F.size);
    if(kind==="witness"&&!stat.goodWitness)stat.goodWitness={R,T,mark:rows[i].p,labels:rows.slice(a,b).map(z=>z.p),startX:xs[a],endX:xs[b],gain,time,drop,distinct:F.size}
   }
   assert(pending<=1,"pending per band")
  }
  assert(totalPendingWeight<4*C+1,"pending weight");
  for(let [i,W] of badR){assert(W<10*(rows[i].p+6),"reset weight");stat.resetWeightChecks++}
  for(let [i,marks] of badB){assert(marks.length<=3&&marks.reduce((a,b)=>a+b,0)<10*xs[i],"B overlap/weight");stat.highBWeightChecks++}
  for(let color=0;color<3;color++){let a=all.filter(v=>v.band%3===color).sort((x,y)=>x.a-y.a);for(let i=1;i<a.length;i++){assert(a[i-1].b<=a[i].a,"same color disjoint");stat.colorChecks++}}
  let counts=new Int32Array(rows.length);for(let z of all)for(let i=z.a;i<z.b;i++)counts[i]++;
  for(let i=0;i<counts.length;i++){assert(counts[i]<=3,"overlap 3");stat.maxOverlap=Math.max(stat.maxOverlap,counts[i]);stat.overlapChecks++}
  assert(all.reduce((s,z)=>s+z.gain,0)<=3*G,"aggregate gain")
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];stat.canonicalRoots++;
  for(let i=0;i<180;i++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.p-1;t+=z.w}
  if(rows.length===180&&next(H,t))stat.unresolved++;stat.canonicalEvents+=rows.length;
  validate(rows);for(let R of [47,71,101])inspect(rows,R,47,"actual")
 }
 function crtWord(word,actual){
  let shift=[0];for(let p of word)shift.push(shift.at(-1)+p-1);
  let H=0n,P=4n,primes=actual?pr.filter(p=>p<=3*Math.max(...word)+6):[...new Set(word)];
  assert(new Set(word).size===word.length,"distinct word");
  for(let s of primes){
   let at=word.indexOf(s),r=at>=0?mod(1-shift[at],s):0;
   let valid=x=>shift.slice(0,-1).every((g,i)=>word[i]===s?mod(x+g,s)===1:!actual||![1,s-1].includes(mod(x+g,s)));
   if(at<0)while(r<s&&!valid(r))r++;
   assert(r<s&&valid(r),"CRT rivals");
   let a=Number(P%BigInt(s)),b=s,u=1,v=0;while(b){let q=Math.floor(a/b);[a,b]=[b,a-q*b];[u,v]=[v,u-q*v]}
   assert(a===1,"inverse");H+=P*BigInt(mod(u*mod(r-Number(H%BigInt(s)),s),s));P*=BigInt(s);if(actual)stat.witnessResidues+=word.length
  }
  while(H<BigInt(Math.max(...word))**2n+8n)H+=P;
  let t=H/2n+3n,rows=[];
  for(let p of word){let d=Number(2n*t-H),w=(3*p-d-1)/2;assert(Number.isInteger(w)&&w>0,"even wait");
   if(actual)for(let j=1;j<=w;j++){let n=t+BigInt(j),I=n%2n,g=gcd(n-2n*I,H-(1n-2n*I));assert(g===BigInt(j===w?p:1),"literal witness");stat.witnessTicks++}
   rows.push({H,d,p,w,I:0});H+=BigInt(p-1);t+=BigInt(w)
  }
  validate(rows);return rows
 }
 let word=[7687,5233,3541,2389,1621,1093,733,7369],witness=crtWord(word,true);stat.actualWitnessRoots++;
 for(let R of [47,733,1093,1700,3600,5233,6000,7500])for(let T0 of [47,3500,7000])inspect(witness,R,T0,"witness");
 // Timed relaxed paths: selected clocks and adaptive eligibility exact, rivals NOT excluded.
 // Nested larger A1, then a long decreasing chain, plus multiple band cutoffs.
 for(let p of [2551,3391,8431,12007]){
  if(spf[p]!==p||p%4!==3)continue;
  let w=[p],used=new Set(w),cur=p;
  function down(to){while(cur>to){let s=pr.find(s=>s>0.68*cur&&s<0.73*cur&&s%4===1&&!used.has(s));assert(s,"descending control");used.add(s);w.push(s);cur=s}}
  down(.28*p);
  let q=pr.find(q=>q>4*p&&q<5*p&&q%4===1&&!used.has(q));assert(q&&q>=10*cur+15,"nested mark");w.push(q);used.add(q);cur=q;down(.12*p);
  let rows=crtWord(w,false);stat.relaxedControls++;for(let R of [47,Math.floor(.5*p),p-2,q-2])for(let T0 of [47,Math.floor(p/2),p])inspect(rows,R,T0,"relaxed")
 }
 assert(stat.goodActual&&stat.goodRelaxed&&stat.badHighB&&stat.pending&&stat.witnessTicks&&stat.discoveryChecks&&stat.laminarChecks,"coverage");
 return stat
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
