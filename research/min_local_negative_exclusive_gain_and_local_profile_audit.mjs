// Exclusive slow-gain cut energy and finite-budget endpoint profile.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=2100000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let a=p*p;a<=N+2;a+=p)spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,v){let p=Infinity,w=Infinity;for(let [d,c] of [[a+1,0],[a-1,2]])for(let r of fs(d)){let t=mod((c===0?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}}return {p,w}}
 function twin(a){return !spf[a-1]&&!spf[a+1]}
 let z={roots:0,events:0,successes:0,badSuccesses:0,fastBalanceChecks:0,fastRunChecks:0,allDepthBasinChecks:0,exclusivePairChecks:0,pairMergeChecks:0,cutLaminarChecks:0,mixedWaitKeys:0,localProfileControls:0,localProfileRootChecks:0,localProfileEndpointChecks:0,localProfileBoundaryChecks:0,formalProfileChecks:0,exactIntegerChecks:0,jointIntegerChecks:0,creditCutChecks:0,rows:[],local:[]};
 for(let R of [3000,12000,48000,192000,480000,1000000]){
  const H=4*Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),L=Math.floor(H/4),basins=new Map(),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6);
  for(let A=lo;A<=hi;A+=6){
   let a=A,h=3,v=3-A/2,F=0,S=0,run=0,runH=3,path=[];
   while(true){
    let x=next(a,v);if(h+x.w>H){let ar=basins.get(a)||[];ar.push({A,path,S,F});basins.set(a,ar);z.successes++;if(!twin(a))z.badSuccesses++;break;}
    let g=x.p-1;if(A-a+g>L)break;
    let slow=4*x.w>=x.p;if(slow){S+=g;run=0;runH=h+x.w-g/2}else{F+=g;run+=g}
    let key=a+":"+(v+x.w);path.push({key,a,n:v+x.w,g,slow,credit:Math.max(0,4*x.w-g)});
    a-=g;v+=x.w;h+=x.w-g/2;z.events++;
    ck(4*h+F<=10*S+12,"gain budget");z.fastBalanceChecks++;
    ck(4*h+run<=4*runH,"fast run");z.fastRunChecks++;
   }z.roots++;
  }
  let row={R,H,L,success:0,bad:0,energy:0,badEnergy:0,badSlowGain:0,badExclusive:0,badCreditCut:0,badMinRepresentative:0,badPairWeighted:0,badThird:0,badPairDistance:0,allSlowGain:0,allExclusive:0,maxBasin:0};
  for(let [a,ar] of basins){
   const m=ar.length,bad=!twin(a),keys=new Map(),rep=new Set(ar[0].path.map(e=>e.key));
   for(let [i,r] of ar.entries())for(let e of r.path){let x=keys.get(e.key);if(!x){x={...e,roots:[],s:0,creditSum:0};keys.set(e.key,x)}x.roots.push(i);if(e.slow)x.s++;x.creditSum+=e.credit}
   let S=ar.reduce((x,y)=>x+y.S,0),cut=0,ref=0,pair=0,third=m*(m*m-1),slowSum=0,creditCut=0,creditPair=0;
   for(let e of keys.values()){let n=e.roots.length,s=e.s;slowSum+=e.g*s;creditCut+=e.creditSum*(1-n/m);creditPair+=e.creditSum*(m-n);if(s&&s<n)z.mixedWaitKeys++;cut+=e.g*s*(1-n/m);pair+=e.g*s*(m-n);if(!rep.has(e.key))ref+=e.g*s}
   let dist=0;for(let i=0;i<m;i++)for(let j=i+1;j<m;j++)dist+=ar[j].A-ar[i].A;
   ck(dist>=third,"pair displacement");ck(dist<=11*pair+6*m*(m-1)+1e-6,"pair charge");
   ck(m*m<=11*cut+6*m-5+1e-6,"cut energy");ck(m*m<=creditCut+6*m-5+1e-6&&dist<=creditPair+6*m*(m-1)+1e-6,'actual-credit cut');z.creditCutChecks++;
   ck(3*m*(m-1)<=11*ref+12*(m-1)+1e-6,"min-root energy");
   ck(slowSum===S&&cut<=S+1e-6&&ref<=S,"exclusive subset");z.allDepthBasinChecks++;
   if(bad||a%246===0)for(let i=0;i<m;i++)for(let j=i+1;j<m;j++){
    let low=ar[i],high=ar[j],K=new Set(low.path.map(e=>e.key)),s=0,g=0,common=false;
    for(let e of high.path){if(K.has(e.key)){common=true;break}g+=e.g;if(e.slow)s+=e.g}
    ck(g>=high.A-low.A,"prefix displacement");ck(high.A-low.A<=11*s+12,"exclusive pair credit");z.exclusivePairChecks++;
    if(common){let e=high.path.find(e=>K.has(e.key)),f=low.path.find(f=>f.key===e.key);ck(e.a===f.a&&e.n===f.n,"merge key");z.pairMergeChecks++}
   }
   if(bad||a%246===0){for(let e of keys.values())if(e.roots.length>1){let path=ar[e.roots[0]].path,idx=path.findIndex(f=>f.key===e.key);if(idx+1<path.length){let f=keys.get(path[idx+1].key),set=new Set(f.roots);ck(e.roots.every(i=>set.has(i)),"laminar nesting");z.cutLaminarChecks++}}}
   row.success+=m;row.energy+=m*m;row.allSlowGain+=S;row.allExclusive+=cut;row.maxBasin=Math.max(row.maxBasin,m);
   if(bad){row.bad+=m;row.badEnergy+=m*m;row.badSlowGain+=S;row.badExclusive+=cut;row.badCreditCut+=creditCut;row.badMinRepresentative+=ref;row.badPairWeighted+=pair;row.badThird+=m*m*m;row.badPairDistance+=dist}
  }z.rows.push(row)
 }
 const cap=g=>Math.floor(9*g/4+8),Pmax=5000,fac=Array.from({length:Pmax+1},()=>[]),pr=[];
 for(let p=3;p<=Pmax;p+=2)if(!fac[p].length){pr.push(p);for(let n=p;n<=Pmax;n+=p)fac[n].push(p)}
 function tick(d,h,par,res){let b=h+1,np=mod(b-par-d/2,2),p=1;for(let q of fac[Math.abs(np?2*b-5:2*b+1)])if(mod(res[q]+d+(np?-1:1),q)===0){p=q;break}return [d-p+1,b-(p-1)/2,p]}
 function reach(g,par,res){let d=g,h=3;for(let t=0;t<cap(g)&&d>0;t++){[d,h]=tick(d,h,par,res);if(d<0)return false;}return d===0}
 for(let R of [12000,48000,192000,480000,1000000])for(let L of [6,12,24,48]){
  const H=Math.max(160,Math.ceil(4*Math.sqrt(2*R+1)),Math.ceil(35*L/4+73)),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),counts=new Map();
  for(let A=lo;A<=hi;A+=6){let a=A,h=3,v=3-A/2;while(true){let e=next(a,v);if(h+e.w>H){let ar=counts.get(a)||[];ar.push(A);counts.set(a,ar);break}if(A-a+e.p-1>L)break;a-=e.p-1;v+=e.w;h+=e.w-(e.p-1)/2}}
  let staticN=0,mass=0,energy=0,boundary=0,res=new Int32Array(Pmax+1);
  for(let a=lo-L;a<=hi;a+=6){
   let e=next(a,3-a/2),staticOK=e.w+3>H,actual=counts.get(a)||[];
   if(!staticOK){ck(actual.length===0,"static inclusion");z.localProfileBoundaryChecks++;continue}
   for(let p of pr){if(p>2*cap(L)+7)break;res[p]=mod(a,p)}
   let ar=[];for(let g=0;g<=L;g+=6){if(a+g<lo||a+g>hi)continue;let yes=reach(g,mod(a/2,2),res);if(yes)ar.push(a+g);z.localProfileRootChecks++}
   ck(JSON.stringify(ar)===JSON.stringify(actual),{R,L,H,a,ar,actual});z.localProfileEndpointChecks++;
   if(a>=lo&&a<=hi){staticN++;mass+=ar.length;energy+=ar.length*ar.length}else boundary+=ar.length;
  }
  z.localProfileControls++;z.local.push({R,L,H,staticN,mass,energy,boundary,mean:mass/staticN,meanSq:energy/staticN})
 }
 z.exact=[];
 for(let g of [6,12,18,24,30,36,42,48]){
  let nodes=0,leaves=0;
  function probability(par){const sets=Array(Pmax+1);
   for(let p of pr){if(p>2*cap(g)+7)break;sets[p]=Array.from({length:p},(_,i)=>i).filter(x=>x!==1&&x!==p-1)}
   function dfs(d,h,t){nodes++;if(d===0){leaves++;return 1}if(d<0||t>=cap(g))return 0;
    let np=mod(h+1-par-d/2,2),b=h+1,list=fac[Math.abs(np?2*b-5:2*b+1)];
    function go(i){if(i===list.length)return dfs(d,b,t+1);
     let p=list[i],s=sets[p],r=mod(-d+(np?1:-1),p),ix=s.indexOf(r);
     if(ix<0)return go(i+1);
     let v=0;if(p-1<=d){sets[p]=[r];v=dfs(d-p+1,b-(p-1)/2,t+1)/s.length;}
     if(s.length>1){sets[p]=s.filter(x=>x!==r);v+=(s.length-1)/s.length*go(i+1)}
     sets[p]=s;return v
    }return go(0)
   }return dfs(g,3,0)
  }
  let v0=probability(0),v1=probability(1);z.exact.push({g,v0,v1,mean:(v0+v1)/2,nodes,leaves});z.formalProfileChecks+=nodes;
 }
 // Exact rational probability evaluation: count product-measure
 // assignments by integer branching, including joint events.
 const gcd=(a,b)=>{while(b){let t=a%b;a=b;b=t}return a};
 const rat=(n,d)=>{let g=gcd(n,d);return [n/g,d/g]};
 const add=(a,b)=>rat(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
 const mul=(a,n)=>rat(a[0]*BigInt(n),a[1]);
 const dec=a=>Number(a[0])/Number(a[1]);
 const str=a=>a[0].toString()+"/"+a[1].toString();
 function integerProb(gs,par){
  let lim=2*cap(Math.max(...gs))+7,total=1n,sets=Array(Pmax+1),nodes=0;
  for(let p of pr){if(p>lim)break;sets[p]=Array.from({length:p},(_,i)=>i).filter(x=>x!==1&&x!==p-1);total*=BigInt(p-2)}
  function dfs(idx,d,h,t,ct){
   nodes++;if(d===0){if(idx+1===gs.length)return ct;return dfs(idx+1,gs[idx+1],3,0,ct)}
   if(d<0||t>=cap(gs[idx]))return 0n;
   let np=mod(h+1-par-d/2,2),b=h+1,list=fac[Math.abs(np?2*b-5:2*b+1)];
   function go(i,num){if(i===list.length)return dfs(idx,d,b,t+1,num);
    let p=list[i],s=sets[p],r=mod(-d+(np?1:-1),p);if(!s.includes(r))return go(i+1,num);
    ck(num%BigInt(s.length)===0n,'integer count');let u=num/BigInt(s.length),v=0n;
    if(p-1<=d){sets[p]=[r];v=dfs(idx,d-p+1,b-(p-1)/2,t+1,u)}
    if(s.length>1){sets[p]=s.filter(x=>x!==r);v+=go(i+1,u*BigInt(s.length-1))}
    sets[p]=s;return v
   }return go(0,ct)
  }
  let result=rat(dfs(0,gs[0],3,0,total),total);
  if(gs.length===1)z.exactIntegerChecks+=nodes;else z.jointIntegerChecks+=nodes;
  return result
 }
 const average=gs=>{let a=add(integerProb(gs,0),integerProb(gs,1));return rat(a[0],2n*a[1])};
 let mu=[1n,1n],marg=new Map(),moments=[];
 for(let e of z.exact){let p=average([e.g]);ck(Math.abs(dec(p)-e.mean)<1e-10,'integer vs probability tree');marg.set(e.g,p);mu=add(mu,p);moments.push({L:e.g,mu1:dec(mu),mu1Rational:str(mu),arrivalProbabilityRational:str(p)})}
 for(let e of moments.filter(e=>e.L<=24)){
  let m2=[1n,1n];
  for(let g=6;g<=e.L;g+=6){m2=add(m2,mul(marg.get(g),3));for(let j=6;j<g;j+=6)m2=add(m2,mul(average([j,g]),2))}
  e.mu2=dec(m2);e.mu2Rational=str(m2);
 }
 z.integerMoments=moments;
 let rng=123456789;function rnd(){rng=(Math.imul(1664525,rng)+1013904223)>>>0;return rng/4294967296}
 let counts=[6,12,24,48,96,192,384,768].map(L=>({L,N:0,sum:0,sq:0,max:0,first:0}));const samples=4000;
 for(let i=0;i<samples;i++){let par=rnd()<.5?0:1,res=new Int32Array(Pmax+1);for(let p of pr){if(p>2*cap(768)+7)break;let n=Math.floor(rnd()*(p-2));res[p]=n===0?0:n+1}
  let m=1,idx=0;for(let g=6;g<=768;g+=6){if(reach(g,par,res))m++;if(g===counts[idx].L){let c=counts[idx++];c.N++;c.sum+=m;c.sq+=m*m;c.max=Math.max(c.max,m);if(m===1)c.first++}}
 }
 z.formal=counts.map(c=>({...c,mean:c.sum/c.N,meanSq:c.sq/c.N}));return z
}
console.log(JSON.stringify(audit(),null,2));
