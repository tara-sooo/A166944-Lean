// Adaptive local transcript certificates and block Bonferroni sieve controls.
function audit(){
 const ck=(b,m)=>{if(!b)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p;
 const max=2000,pr=[],fac=Array.from({length:max+1},()=>[]);
 for(let p=3;p<=max;p+=2)if(!fac[p].length){pr.push(p);for(let n=p;n<=max;n+=p)fac[n].push(p)}
 const cap=g=>Math.floor(9*g/4+8),gcd=(a,b)=>{while(b){let t=a%b;a=b;b=t}return a},rat=(n,d)=>{let g=gcd(n,d);return [n/g,d/g]},str=a=>a[0]+"/"+a[1],num=a=>Number(a[0])/Number(a[1]);
 let z={periodControls:0,lowClasses:0,tupleControls:0,treeNodes:0,queryBranches:0,acceptingLeaves:0,pinBudgetChecks:0,leafWeightChecks:0,roughPinRejects:0,knownDenialChecks:0,knownPinChecks:0,oneMediumFactorChecks:0,integerMomentChecks:0,blockControls:0,pointwiseChecks:0,blockExpectationChecks:0,crtProgressions:0,crtRemainderChecks:0,coefficientChecks:0,physicalControls:0,physicalReachChecks:0,physicalPinChecks:0,results:[],physical:[]};
 function tree(L,cut,j,gs,opts={}){
  let Z=2*cap(L)+7,T=gs.reduce((s,g)=>s+cap(g),0),high=pr.filter(p=>p>cut&&p<=Z),low=pr.filter(p=>p<=cut&&p<=Z);
  let denied=new Map(high.map(p=>[p,new Set([1,p-1])])),pins=new Map(),mass=0n,leaves=0,weight=0,nodes=0,branches=0,maxPins=0,par=mod(3*j,2),lastLeaves=[];
  function finish(){
   let ct=1n,P=1;for(let p of high){if(pins.has(p)){P*=p;continue}ct*=BigInt(p-denied.get(p).size)}
   mass+=ct;weight+=1/P;leaves++;maxPins=Math.max(maxPins,pins.size);z.acceptingLeaves++;
   ck(pins.size<=gs.reduce((s,g)=>s+g,0)/(cut-1)+1e-9,"pin gain cap");z.pinBudgetChecks++;
   if(opts.capture&&lastLeaves.length<opts.capture)lastLeaves.push({pins:[...pins],denied:[...denied].filter(([p])=>!pins.has(p)).map(([p,S])=>[p,[...S]])});
  }
  function dfs(idx,d,h,t){
   nodes++;z.treeNodes++;
   if(d===0){if(idx+1===gs.length){finish();return}dfs(idx+1,gs[idx+1],3,0);return}
   if(d<0||t>=cap(gs[idx]))return;
   let np=mod(h+1-par-d/2,2),b=h+1,list=fac[Math.abs(np?2*b-5:2*b+1)];
   ck(list.filter(p=>p>cut).length<=1,"one medium factor");z.oneMediumFactorChecks++;
   function fire(p){if(p-1<=d)dfs(idx,d-p+1,b-(p-1)/2,t+1)}
   for(let p of list){
    let r=mod(-d+(np?1:-1),p);
    if(p<=cut){if(mod(6*j,p)===r){fire(p);return}continue}
    if(pins.has(p)){z.knownPinChecks++;if(pins.get(p)===r){fire(p);return}continue}
    let S=denied.get(p);ck(S!==undefined,"height factor range");
    if(S.has(r)){z.knownDenialChecks++;if(r===1||r===p-1)z.roughPinRejects++;continue}
    // At most one medium factor and all lower factors have been tested.
    branches++;z.queryBranches++;
    if(p-1<=d){pins.set(p,r);fire(p);pins.delete(p)}
    S.add(r);if(S.size<p)dfs(idx,d,b,t+1);S.delete(r);return;
   }
   dfs(idx,d,b,t+1)
  }
  dfs(0,gs[0],3,0);
  ck(weight<=Math.exp(T/cut)*(1+1e-9),"sum reciprocal positive pins");z.leafWeightChecks++;
  return {mass,leaves,weight,nodes,branches,maxPins,lastLeaves}
 }
 const known={
  6:["6028126/3660525","3587776/1220175"],
  12:["701632591/343823130","6588081083/1383678450"],
  18:["5106396847732215463/2097086682985544250","193920225430694299891/27262126878812075250"],
  24:["181984488679496561979311/65066308512992481444750","317468208346167912148457/32449949258397784863750"]
 };
 for(let [L,cut] of [[6,7],[12,7],[18,11],[24,11],[24,13]]){
  let Z=2*cap(L)+7,M=2*pr.filter(p=>p>=5&&p<=cut).reduce((s,p)=>s*p,1),hi=pr.filter(p=>p>cut&&p<=Z),highTotal=hi.reduce((s,p)=>s*BigInt(p-2),1n),classes=0,A=0n,B=0n,offsets=Array.from({length:L/6+1},(_,i)=>6*i),maxPins=0,maxWeight=0;
  for(let j=0;j<M;j++){
   if(pr.some(p=>p>=5&&p<=cut&&(mod(6*j,p)===1||mod(6*j,p)===p-1)))continue;
   classes++;z.lowClasses++;
   for(let g of offsets){
    let a=tree(L,cut,j,[g]);A+=a.mass;maxPins=Math.max(maxPins,a.maxPins);maxWeight=Math.max(maxWeight,a.weight);z.tupleControls++;
    for(let h of offsets){let b=tree(L,cut,j,[g,h]);B+=b.mass;maxPins=Math.max(maxPins,b.maxPins);maxWeight=Math.max(maxWeight,b.weight);z.tupleControls++}
   }
  }
  let den=BigInt(classes)*highTotal,m1=rat(A,den),m2=rat(B,den);
  ck(str(m1)===known[L][0]&&str(m2)===known[L][1],{L,cut,m1:str(m1),m2:str(m2)});
  z.integerMomentChecks+=2;z.periodControls++;z.results.push({L,cut,Z,M,classes,maxPins,maxWeight,mu1:num(m1),mu2:num(m2)})
 }
 // Abstract product Bonferroni: medium block plus geometrically
 // partitioned free blocks. Every squarefree coefficient has size <=1.
 function choose(n,k){if(k>n||k<0)return 0;let a=1;for(let i=1;i<=k;i++)a=a*(n-i+1)/i;return a}
 function poly(v,k){let s=0;for(let i=0;i<=Math.min(v,k);i++)s+=(i%2?-1:1)*choose(v,i);return s}
 let rng=41721;function rand(){rng=(Math.imul(rng,1664525)+1013904223)>>>0;return rng/4294967296}
 for(let t=0;t<120;t++){
  let n=5+t%6,blocks=[[],[],[]],ps=pr.slice(1,1+n),orders=[2,2+2*(t%2),2];
  for(let i=0;i<n;i++)blocks[Math.min(2,Math.floor(3*i/n))].push(i);
  let probs=ps.map(p=>(1+Math.floor(rand()*Math.min(4,p-1)))/p),truth=0,eu=0,el=0,vs=probs.reduce((s,p)=>s*(1-p),1);
  let coefU=new Map(),coefL=new Map();
  for(let mask=0;mask<(1<<n);mask++){
   let ct=blocks.map(B=>B.filter(i=>(mask>>i)&1).length),tot=ct.reduce((a,b)=>a+b,0),sign=tot%2?-1:1;
   let U=ct.every((c,i)=>c<=orders[i])?sign:0,L=U;
   for(let j=0;j<3;j++)if(ct[j]===orders[j]+1&&ct.every((c,i)=>i===j||c<=orders[i]))L+=sign;
   ck(Math.abs(U)<=1&&Math.abs(L)<=1,"coefficient");z.coefficientChecks++;
   coefU.set(mask,U);coefL.set(mask,L);
  }
  for(let mask=0;mask<(1<<n);mask++){
   let ct=blocks.map(B=>B.filter(i=>(mask>>i)&1).length),upper=ct.reduce((s,v,i)=>s*poly(v,orders[i]),1),lower=upper;
   for(let i=0;i<3;i++)lower-=choose(ct[i],orders[i]+1)*ct.reduce((s,v,j)=>i===j?s:s*poly(v,orders[j]),1);
   ck(lower<=(mask===0?1:0)&&upper>=(mask===0?1:0),"pointwise sandwich");
   let u=0,l=0,sub=mask;while(true){u+=coefU.get(sub);l+=coefL.get(sub);if(!sub)break;sub=(sub-1)&mask}
   ck(u===upper&&l===lower,"expanded polynomial");
   let w=probs.reduce((a,p,i)=>a*(((mask>>i)&1)?p:1-p),1);eu+=w*upper;el+=w*lower;if(mask===0)truth+=w;z.pointwiseChecks++;
  }
  let blockU=blocks.map((B,i)=>{let e=0;for(let mask=0;mask<(1<<B.length);mask++){let cnt=0,w=1;for(let j=0;j<B.length;j++)if((mask>>j)&1){cnt++;w*=probs[B[j]]}else w*=1-probs[B[j]];e+=w*poly(cnt,orders[i])}return e});
  ck(Math.abs(truth-vs)<1e-10&&el<=vs+1e-10&&eu>=vs-1e-10&&Math.abs(eu-blockU.reduce((a,b)=>a*b,1))<1e-10,"block expected sandwich");z.blockExpectationChecks++;z.blockControls++;
 }
 // Check exact CRT polynomial counts and the divisor-sum error
 // in actual finite arithmetic progressions, including q pins.
 for(let t=0;t<80;t++){
  let ps=[7,11,13,17,19,23],q=29,M=60,P=5,step=M*P*q,base=1+t%13,n=80+t%21;
  let forbidden=ps.map((p,i)=>{let r=mod(t+i*3,p);return [r,mod(r+1+i%2,p)]}),orders=[2,2,2],blocks=[[0,1,2],[3,4],[5]];
  let exact=0,upper=0,lower=0,mainU=0,mainL=0,error=0;
  const hit=(v,i)=>forbidden[i].includes(mod(base+step*v,ps[i]));
  for(let v=0;v<n;v++){
   let ct=blocks.map(B=>B.reduce((s,i)=>s+Number(hit(v,i)),0)),u=ct.reduce((s,v,i)=>s*poly(v,orders[i]),1),l=u;
   for(let i=0;i<3;i++)l-=choose(ct[i],orders[i]+1)*ct.reduce((s,v,j)=>i===j?s:s*poly(v,orders[j]),1);
   exact+=Number(ct.every(c=>!c));upper+=u;lower+=l;
  }
  let expandedU=0,expandedL=0;
  for(let mask=0;mask<64;mask++){
   let ct=blocks.map(B=>B.filter(i=>(mask>>i)&1).length),tot=ct.reduce((a,b)=>a+b,0),sign=tot%2?-1:1,U=ct.every((c,i)=>c<=orders[i])?sign:0,L=U;
   for(let j=0;j<3;j++)if(ct[j]===orders[j]+1&&ct.every((c,i)=>i===j||c<=orders[i]))L+=sign;
   if(!U&&!L)continue;let d=1,nu=1,actual=0;
   for(let i=0;i<6;i++)if((mask>>i)&1){d*=ps[i];nu*=forbidden[i].length}
   for(let v=0;v<n;v++)if(ps.every((p,i)=>!((mask>>i)&1)||hit(v,i)))actual++;
   let ideal=n*nu/d;
   ck(Math.abs(actual-ideal)<=nu+1e-9,"CRT remainder");z.crtRemainderChecks++;
   expandedU+=U*actual;expandedL+=L*actual;mainU+=U*ideal;mainL+=L*ideal;error+=nu;
  }
  ck(expandedU===upper&&expandedL===lower&&lower<=exact&&exact<=upper&&Math.abs(upper-mainU)<=error+1e-8&&Math.abs(lower-mainL)<=error+1e-8,"progression polynomial");z.crtProgressions++;
 }
 // Finite physical controls: replay actual arrival using only low
 // residues, pinned medium labels and denied residue lists.
 const N=2100000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let a=p*p;a<=N+2;a+=p)spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,v){let p=Infinity,w=Infinity;for(let [d,c] of [[a+1,0],[a-1,2]])for(let r of fs(d)){let t=mod((c===0?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}}return {p,w}}
 for(let R of [12000,48000,192000,1000000])for(let [L,cut] of [[24,13],[48,17],[96,23]]){
  let Z=2*cap(L)+7,H=Math.max(Math.ceil(4*Math.sqrt(2*R+1)),Math.ceil(35*L/4+73)),row={R,L,cut,H,centers:0,roots:0,hits:0,pins:0,denials:0,maxPins:0};
  for(let a=6*Math.ceil(R/6);a<=2*R;a+=6){
   if(next(a,3-a/2).w+3<=H)continue;
   if(row.centers++%17)continue;
   ck(fs(a-1).every(p=>p>Z)&&fs(a+1).every(p=>p>Z),"rough local domain");
   for(let g=0;g<=L;g+=6){
    let d=g,h=3,t=0,pins=new Map(),denials=new Map();
    while(d>0&&t<cap(g)){
     let b=h+1,np=mod(b-a/2-d/2,2),list=fac[Math.abs(np?2*b-5:2*b+1)],p=1;
     ck(list.filter(p=>p>cut).length<=1,"physical one medium");
     for(let q of list){let r=mod(-d+(np?1:-1),q),actual=mod(a,q);
      if(q>cut){if(pins.has(q))ck(pins.get(q)===actual,"known medium");
       else if(actual===r){ck(r!==1&&r!==q-1&&!(denials.get(q)||new Set()).has(r),"valid pin");pins.set(q,r);z.physicalPinChecks++}
       else{let S=denials.get(q)||new Set([1,q-1]);S.add(r);denials.set(q,S);row.denials++}}
      if(actual===r){p=q;break}
     }
     d-=p-1;h=b-(p-1)/2;t++;
    }
    let A=a+g,x=A,v=3-A/2,elapsed=0;while(x>a){let e=next(x,v);if(elapsed+e.w>cap(g))break;x-=e.p-1;v+=e.w;elapsed+=e.w}
    ck((d===0)===(x===a),"physical replay agrees");
    if(d===0){ck(pins.size<=g/(cut-1)+1e-9,"physical pin budget");row.hits++}
    row.pins+=pins.size;row.maxPins=Math.max(row.maxPins,pins.size);row.roots++;z.physicalReachChecks++;
   }
  }
  z.physicalControls++;z.physical.push(row)
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
