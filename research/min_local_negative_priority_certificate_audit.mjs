// Canonical affine priority certificates, conditional winner laws and rough skeleton factors.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(x,p)=>(x%p+p)%p;
 const A=[3,5,7,11],B=[5,7,11,13],N=180000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)spf[n]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
 function clock(p,e){return e===-1?0:p+2}
 function wait(v,p,e){return mod(clock(p,e)-v,2*p)||2*p}
 function winner(j,G,W,P){let a=6*j-G,v=3-3*j+W,p=Infinity,w=Infinity,e=0;for(let q of P)for(let f of [-1,1])if(mod(a-f,q)===0){let t=wait(v,q,f);if(t<w||t===w&&q<p){p=q;w=t;e=f}}return {p,w,e}}
 function winFull(a,v){let p=Infinity,w=Infinity,e=0;for(let [d,f] of [[a+1,-1],[a-1,1]])for(let q of fs(d)){let t=wait(v,q,f);if(t<w||t===w&&q<p){p=q;w=t;e=f}}return {p,w,e}}
 // Root parameter j parity fixed, with q=3 special: 6j-G=e
 // may hold for ALL j of a parity; handle 3 as exact separate gate.
 function residue(q,G,e){return q===3?null:mod((G+e)*inv(6,q),q)}
 function inv(a,q){for(let x=1;x<q;x++)if(mod(a*x,q)===1)return x;throw Error("inverse")}
 function possible(q,G,W,e,par){let r=residue(q,G,e);
  if(q===3){if(mod(-G-e,3)!==0)return null;let j=par;return {r:null,w:wait(3-3*j+W,q,e)}}
  let j=r+q*mod(par-r,2);return {r,w:wait(3-3*j+W,q,e)}
 }
 function cert(P,word,par){
  let sets=new Map(P.filter(q=>q!==3).map(q=>[q,new Set(Array.from({length:q},(_,i)=>i))])),gate=true,G=0,W=0,denied=0,selected=0;
  for(let x of word){
   for(let q of P)for(let e of [-1,1]){let h=possible(q,G,W,e,par);if(!h)continue;
    let early=h.w<x.w||h.w===x.w&&q<x.p;
    if(early){if(q===3)gate=false;else if(sets.get(q).delete(h.r))denied++}
    if(q===x.p&&e===x.e){selected++;if(h.w!==x.w)gate=false;if(q!==3){let s=sets.get(q);for(let a of s)if(a!==h.r)s.delete(a)}}
   }
   // Selected q=3 with unavailable side cannot pass.
   if(!P.includes(x.p)||!possible(x.p,G,W,x.e,par))gate=false;
   G+=x.p-1;W+=x.w
  }
  return {sets,gate,denied,selected,product:gate?[...sets.values()].reduce((a,b)=>a*b.size,1):0}
 }
 function accepts(c,j){return c.gate&&[...c.sets].every(([q,s])=>s.has(mod(j,q)))}
 let stats={alphabetControls:0,roots:0,events:0,words:0,fullPeriodChecks:0,emptyWords:0,nonemptyWords:0,strictPriorityWords:0,priorityDenials:0,intervalChecks:0,adaptiveBranches:0,adaptivePartitionChecks:0,adaptiveNewLabels:0,adaptiveHazardChecks:0,actualRoots:0,actualPrefixes:0,actualEvents:0,actualPrimeChecks:0,actualPriorityChecks:0,actualRoughChecks:0,offsetControls:0,offsetResidueChecks:0,rows:[]};
 for(let P of [A,B])for(let par of [0,1]){
  let Q=P.filter(q=>q!==3).reduce((a,b)=>a*b,1),words=new Map(),depth=4,row={P,par,Q,words:0,empty:0,strict:0,maxCount:0,allRootCount:0};
  for(let l=0;l<Q;l++){let j=2*l+par,G=0,W=0,word=[];
   for(let i=0;i<depth;i++){let x=winner(j,G,W,P);if(!isFinite(x.p))break;word.push(x);G+=x.p-1;W+=x.w;stats.events++}
   let key=JSON.stringify(word);let obj=words.get(key)||{word,roots:[]};obj.roots.push(j);words.set(key,obj);stats.roots++
  }
  // Prefixes from actual words plus corrupted waits/signs for negative controls.
  let controls=new Map();for(let {word} of words.values()){
   for(let i=1;i<=word.length;i++){let a=word.slice(0,i);controls.set(JSON.stringify(a),a)}
   if(word.length){let a=word.map(x=>({...x}));a[a.length-1].w+=1;controls.set(JSON.stringify(a),a)}
  }
  for(let word of controls.values()){
   let c=cert(P,word,par),actual=0,positive=0;
   for(let l=0;l<Q;l++){
    let j=2*l+par,G=0,W=0,ok=true,pos=true;
    for(let x of word){
     let y=winner(j,G,W,P);if(y.p!==x.p||y.w!==x.w||y.e!==x.e)ok=false;
     if(mod(6*j-G-x.e,x.p)!==0||wait(3-3*j+W,x.p,x.e)!==x.w)pos=false;
     G+=x.p-1;W+=x.w
    }
    ck(accepts(c,j)===ok,"exact word certificate");if(ok)actual++;if(pos)positive++;stats.fullPeriodChecks++
   }
   ck(actual===c.product&&actual<=positive,"product count");
   if(actual<positive){stats.strictPriorityWords++;row.strict++}
   if(!actual){stats.emptyWords++;row.empty++}else{stats.nonemptyWords++;row.maxCount=Math.max(row.maxCount,actual)}
   for(let [start,n] of [[17,43],[Q-7,37]]){let a=0;for(let l=start;l<start+n;l++)if(accepts(c,2*l+par))a++;ck(a<=Math.ceil(n/Q)*actual,"interval count");stats.intervalChecks++}
   stats.words++;stats.priorityDenials+=c.denied;row.words++;
   if(actual){
    // Exact conditional next-winner law from the surviving Cartesian product.
    let G=word.reduce((a,x)=>a+x.p-1,0),W=word.reduce((a,x)=>a+x.w,0),cand=[];
    for(let q of P)for(let e of [-1,1]){let h=possible(q,G,W,e,par);if(h)cand.push({p:q,e,w:h.w,r:h.r})}
    cand.sort((a,b)=>a.w-b.w||a.p-b.p);let rem=new Map([...c.sets].map(([q,s])=>[q,new Set(s)])),surv=1,distribution=new Map(),sum=0;
    for(let x of cand){
     let mass=x.p===3?1:rem.get(x.p).has(x.r)?1/rem.get(x.p).size:0;
     if(surv===0)break;
     let hit=surv*mass;distribution.set([x.p,x.w,x.e].join(":"),hit);sum+=hit;
     if(x.p!==3&&mass){stats.adaptiveHazardChecks++;if(!word.some(y=>y.p===x.p))stats.adaptiveNewLabels++}
     surv*=1-mass;if(x.p!==3)rem.get(x.p).delete(x.r);stats.adaptiveBranches++
    }
    ck(Math.abs(sum+surv-1)<1e-9,"probability partition");
    let hist=new Map();for(let l=0;l<Q;l++){let j=2*l+par;if(!accepts(c,j))continue;let x=winner(j,G,W,P),k=isFinite(x.p)?[x.p,x.w,x.e].join(":"):"stop";hist.set(k,(hist.get(k)||0)+1)}
    for(let [key,n] of hist){let pr=key==="stop"?surv:distribution.get(key)||0;ck(Math.abs(pr-n/actual)<1e-9,"adaptive law");stats.adaptivePartitionChecks++}
   }
  }
  row.allRootCount=Q;stats.alphabetControls++;stats.rows.push(row)
 }
 // Actual uncut canonical prefix: every competing prime up to cutoff
 // must obey the conditional clock order, with 3 included exactly.
 let P=[3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97];
 for(let a0=120;a0<=N;a0+=198){let a=a0,v=3-a0/2,j=a0/6,par=mod(j,2),G=0,W=0,word=[];
  while(a>a0/2&&word.length<12){let x=winFull(a,v);if(v+x.w>-1||a-x.p+1<=a0/2)break;
   for(let q of P)for(let e of [-1,1]){let h=possible(q,G,W,e,par),eligible=mod(a-e,q)===0;if(eligible){ck(h&&h.w===wait(v,q,e),"affine wait");ck(!(h.w<x.w||h.w===x.w&&q<x.p),"priority");stats.actualPriorityChecks++}stats.actualPrimeChecks++}
   if(x.w>=7){for(let q of P)if(2*q<x.w){ck(mod(a-1,q)!==0&&mod(a+1,q)!==0,"rough");stats.actualRoughChecks++}}
   word.push(x);G+=x.p-1;W+=x.w;a-=x.p-1;v+=x.w;stats.actualEvents++;
  }
  // Partial certificate: include all selected labels as well as test alphabet.
  let C=[...new Set([...P,...word.map(x=>x.p)])]; // avoid large arrays below: explicit forbidden membership test
  let gg=0,ww=0;for(let x of word){for(let q of C)for(let e of [-1,1]){let h=possible(q,gg,ww,e,par);if(h&&mod(6*j-gg-e,q)===0)ck(h.w>x.w||h.w===x.w&&q>=x.p,"partial certificate")}gg+=x.p-1;ww+=x.w}
  stats.actualPrefixes++;stats.actualRoots++
 }
 // Long-wait skeleton local factors: distinct offsets give 2m forbidden
 // classes away from divisors of differences of the shifted offsets.
 for(let offsets of [[0,10],[0,16,34],[4,18,38,64],[0,12,42,88,120]]){
  let shifts=offsets.flatMap(g=>[g-1,g+1]);ck(new Set(shifts).size===2*offsets.length,"distinct shifts");
  for(let q of P.filter(x=>x>=5)){let residues=new Set(shifts.map(x=>mod(x*inv(6,q),q))),bad=shifts.some((x,i)=>shifts.slice(i+1).some(y=>mod(x-y,q)===0));ck(bad||residues.size===2*offsets.length,"dimension");stats.offsetResidueChecks++}
  stats.offsetControls++
 }
 return stats
}
console.log(JSON.stringify(audit(),null,2));
