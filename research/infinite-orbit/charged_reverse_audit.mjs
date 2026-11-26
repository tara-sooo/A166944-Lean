// Run: node research/infinite-orbit/charged_reverse_audit.mjs
function audit(){
 const limit=4*65536+2048,spf=new Int32Array(limit+1);
 for(let p=2;p*p<=limit;p++)if(!spf[p])for(let n=p*p;n<=limit;n+=p)if(!spf[n])spf[n]=p;
 function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function mod(a,b){return (a%b+b)%b}
 function elig(H){let b=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=b),fac(H+1).filter(p=>p<=b)]}
 function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let z=1+mod((i?q+2:0)-t-1,2*q);if(z<w||(z===w&&q<p)){p=q;w=z;s=i}}return {p,w,s}}
 function gap(n,p,s,f){let W=2*p;for(let i=0;i<2;i++)for(let q of f[i])if(q!==p){let z=mod(n-(i?q+2:0),2*q);if(!z&&q<p)return 0;W=Math.min(W,z||2*q)}return W}
 function ok(a,m){if(!a)throw Error(m)}
 function logChoose(n,k){let z=0;for(let j=1;j<=k;j++)z+=Math.log((n-k+j)/j);return z}
 const D0=32, m0=1+Math.floor(D0/4);
 let totals={events:0,rootIncidences:0,targetedIncidences:0,pairChecks:0,unitChecks:0,unitPositive:0,unitRepeatChecks:0,sourceChecks:0,reverseCalls:0,reverseInclusion:0,reverseBrute:0,reverseResults:0,perOffsetChecks:0,exactUnitCostChecks:0,entropyChecks:0},results=[],examples=[],cohortExamples=[];
 for(let X of [4096,16384,65536]){
  const Y=4*X,T=Math.ceil(Math.sqrt(X)/2),Bmax=Math.floor(Math.sqrt(Y+1));
  let configs=[];
  for(let B of [Math.floor(3*T/2),Bmax])for(let [R,M,r] of [[3,4,5],[7,34,11]])if(T>2*R+2&&T>3+M)configs.push({B,R,M,r,C:8*(1+B/T),goodVisits:0,unitVisits:0,goodPairs:0,unitReturns:0,unitRepeat:0,unitPositive:0,minUnitCost:null,sourceGroups:new Map(),reverseSamples:[],maxReverse:0,maxMultiplicity:0,maxUnitMultiplicity:0,maxUnitFree:0,multiUnitCostGroups:0,cohortChecks:0,maxK:0,reverseResultCount:0,reverseBad:0,reverseGoodOnly:0,bruteCount:0});
  function isGood(e,z){return e.p>=T&&e.p<=z.B&&e.w>=e.p-2}
  function event(H,t,a){let J=H+a.p-1,n=t+a.w,d=2*n-J,h=(d-6*a.s)/(2*a.p);ok(d>=0&&Number.isInteger(h),"event coordinates");return {H,t,p:a.p,w:a.w,s:a.s,J,n,d,h,g:a.p-1}}
  function inv(J,n,z){
   let s=n%2,A=J+2*s,C=n-2*s,res=[];
   for(let p of fac(A)){if(p<T||p>z.B||C%p)continue;
    let H=J-p+1;if(H<X||H>=Y||p*p>H+1)continue;
    let f=elig(H);if(!f[s].includes(p))continue;
    let W=gap(n,p,s,f),l=Math.max(p-2,n-(3*H+3)),u=Math.min(W,n-H/2);
    if(l<=u)res.push({p,H,l,u})
   }
   ok(res.length<=2,"two inverse labels");return res
  }
  function verifyRelay(J0,n0,H,targetJ,targetN,z){
   let h=J0,t=n0,um=0,uh=0,L=0,nm=0,nh=0;
   while(h<H){
    if(h>=Y)return null;
    let a=first(t,elig(h));if(!a.p)return null;let e=event(h,t,a);
    if(isGood(e,z)||e.J>H)return null;
    if(e.p<=z.R)L+=e.g;else if(e.p<T){um+=e.g;nm++}else{uh+=e.g;nh++}
    h=e.J;t=e.n;
   }
   if(h!==H||h>=Y)return null;
   let a=first(t,elig(h));if(!a.p)return null;let e=event(h,t,a);
   if(!isGood(e,z)||e.J!==targetJ||e.n!==targetN)return null;
   ok(L<=z.M*(1+nm+nh),"one gap low budget");
   return {um,uh,L,E:H-J0,b:t-n0}
  }
  function reverse(J,n,z,cap,brute=false){
   let ret=new Map(),byE=new Map();
   for(let cur of inv(J,n,z))for(let E=0;E<=cap;E+=2){
    let J0=cur.H-E;if(J0<X)continue;
    let lo=n-cur.u-3*E,hi=n-cur.l;
    let candidates=new Set();
    if(brute){for(let t=Math.max(2,J0/2,lo);t<=hi;t++)if(inv(J0,t,z).length)candidates.add(t)}
    else for(let s=0;s<2;s++)for(let r of fac(J0+2*s)){
     if(r<T||r>z.B)continue;
     let a=s?r+2:0;for(let t=lo+mod(a-lo,2*r);t<=hi;t+=2*r)if(t>=2&&inv(J0,t,z).some(v=>v.p===r))candidates.add(t)
    }
    for(let t of candidates){let v=verifyRelay(J0,t,cur.H,J,n,z);if(v){let key=J0+","+t;ok(v.E===E&&v.b<=3*E,"relay transfer");ret.set(key,v);if(!byE.has(E))byE.set(E,new Set());byE.get(E).add(key);}}
   }
   if(!brute)for(let E=0;E<=cap;E+=2){ok((byE.get(E)?.size||0)<=z.C*(1+E/T)+1e-9,"per exact E degree");totals.perOffsetChecks++}
   return ret
  }
  function scan(H0,t0,can){
   let H=H0,t=t0,ev=[];
   for(let i=0;i<3000&&H<Y;i++){
    let a=first(t,elig(H));if(!a.p)break;let e=event(H,t,a);ev.push(e);H=e.J;t=e.n;totals.events++;
    if(i===2999)ok(H>=Y,"unresolved");
   }
   for(let z of configs){
    let last=null,firstGood=null,k=0,eligible=false,um=0,uh=0,relay=0,unitStart=null,unitUm=0,unitUh=0,unitDrift=0,priorDrift=0,entryE=0;
    const cm=1+z.M/(z.r-1),ch=1+z.M/(T-1);
    for(let e of ev){
     if(!isGood(e,z)){
      if(last){relay+=e.g;if(e.p>z.R&&e.p<T)um+=e.g;else if(e.p>=T)uh+=e.g;}
      if(unitStart){if(e.p>z.R&&e.p<T)unitUm+=e.g;else if(e.p>=T)unitUh+=e.g}
      continue;
     }
     ok(e.h>=1,"long nonreset");z.goodVisits++;if(e.h===1)z.unitVisits++;
     if(last){
      z.goodPairs++;totals.pairChecks++;ok(e.H-last.J===relay,"actual relay E");
      let prior=last.J+","+last.n;
      if(relay<=128&&z.reverseSamples.length<35&&z.goodPairs%7===0)z.reverseSamples.push({J:e.J,n:e.n,key:prior,E:relay});
     }else{
      firstGood=e;entryE=e.H-H0;eligible=can&&entryE<=D0;
      if(eligible&&e.p>Math.max(9,2*e.t-e.H+1))ok(e.h===1,"shallow frozen");
     }
     k++;z.maxK=Math.max(z.maxK,k);
     if(k>1){
      priorDrift+=e.p-3-z.M;
      let pay=cm*um+ch*uh;
      ok(pay+1e-9>=firstGood.d-e.d+priorDrift,"signed gap cost");
      if(e.h===1){
       z.unitReturns++;totals.unitChecks++;
       let req=2*firstGood.h*firstGood.p-e.p-z.M-9+(k-2)*(T-3-z.M);
       ok(pay+1e-9>=req,"unit return cost");
       if(req>0){z.unitPositive++;totals.unitPositive++;let v={X,B:z.B,R:z.R,from:[firstGood.J,firstGood.n,firstGood.p,firstGood.h],to:[e.J,e.n,e.p,e.h],k,um,uh,pay,req};if(examples.length<8&&!examples.some(q=>JSON.stringify(q)===JSON.stringify(v)))examples.push(v)}
       z.minUnitCost=z.minUnitCost===null?um+uh:Math.min(z.minUnitCost,um+uh);
      }
     }
     if(unitStart){unitDrift+=e.p-3-z.M;if(e.h===1){
      totals.unitRepeatChecks++;z.unitRepeat++;
      ok(cm*unitUm+ch*unitUh+1e-9>=unitStart.d-e.d+unitDrift,"disjoint unit return");
      unitStart=e;unitUm=unitUh=unitDrift=0;
     }}else if(e.h===1){unitStart=e;unitUm=unitUh=unitDrift=0}
     if(eligible){
      let key=e.J+","+e.n,rec=z.sourceGroups.get(key);
      if(!rec){rec={unit:e.h===1,records:[]};z.sourceGroups.set(key,rec)}
      ok(rec.unit===(e.h===1),"unit property of post-state");
      rec.records.push({k,um,uh,E:entryE,root:H0,firstUnit:firstGood.h===1});
     }
     last=e;relay=0;
    }
   }
  }
  for(let H=X;H<Y;H+=4){scan(H,(H+6)/2,true);totals.rootIncidences++}
  for(let H=X;H<Y;H+=2){
   let f=elig(H);
   for(let s=0;s<2;s++)for(let p of f[s]){
    if(p<T)continue;
    for(let h of [1,2,4,8]){
     let J=H+p-1,n=(J+2*h*p+6*s)/2,w=p-2,t=n-w;
     if(n%2!==s||mod(n-(s?p+2:0),2*p)!==0||t<H/2||t>3*H+3)continue;
     let a=first(t,f);if(a.p!==p||a.w!==w)continue;
     scan(H,t,false);totals.targetedIncidences++;
    }
   }
  }
  for(let z of configs){
   const cm=1+z.M/(z.r-1),ch=1+z.M/(T-1),c=Math.max(cm,ch);
   for(let a of z.reverseSamples){
    let v=reverse(a.J,a.n,z,128);totals.reverseCalls++;ok(v.has(a.key),"reverse forward inclusion");totals.reverseInclusion++;
    z.maxReverse=Math.max(z.maxReverse,v.size);z.reverseResultCount+=v.size;totals.reverseResults+=v.size;
    for(let r of v.values())if(r.um+r.uh>0)z.reverseBad++;else z.reverseGoodOnly++;
    if(z.bruteCount<2){let b=reverse(a.J,a.n,z,128,true);ok(b.size===v.size&&[...b.keys()].every(k=>v.has(k)),"independent time enumeration");totals.reverseBrute++;z.bruteCount++;}
   }
   for(let [key,v] of z.sourceGroups){
    let records=v.records.filter(r=>r.firstUnit);
    z.maxMultiplicity=Math.max(z.maxMultiplicity,records.length);if(v.unit)z.maxUnitMultiplicity=Math.max(z.maxUnitMultiplicity,records.length);
    if(v.unit){
     let free=records.filter(r=>r.k===1||cm*r.um+ch*r.uh<2*T-z.B-z.M-9-1e-8);
     ok(free.every(r=>r.k===1),"unit narrow return threshold");
     ok(free.length<=m0,"first entry multiplicity");z.maxUnitFree=Math.max(z.maxUnitFree,free.length);totals.exactUnitCostChecks++;
     let sum=records.reduce((a,r)=>a+cm*r.um+ch*r.uh,0),threshold=Math.max(0,2*T-z.B-z.M-9);
     ok(sum+1e-8>=threshold*Math.max(0,records.length-m0),"unit cohort gain");
     if(threshold>0&&records.length>m0){z.multiUnitCostGroups++;cohortExamples.push({X,T,B:z.B,R:z.R,target:key,threshold,sources:records.length,first:records.filter(r=>r.k===1).length,weightedCost:sum,records})}
    }
    if(!records.length)continue;
    for(let U of [0,16,64,256])for(let maxK of [1,2,4,8]){
     let n=records.filter(r=>r.um+r.uh<=U&&r.k<=maxK).length;if(!n)continue;
     let cap=1;
     for(let j=1;j<maxK;j++){
      let S=z.M*j+c*U;
      let lg=j*Math.log(z.C)+logChoose(Math.floor(S/2)+j,j)+j*Math.log(1+S/(j*T));
      cap+=Math.exp(lg);
     }
     ok(n<=m0*cap+1e-6,"cost-depth multiplicity");totals.entropyChecks++;z.cohortChecks++;
    }
    totals.sourceChecks++;
   }
   results.push({X,T,B:z.B,R:z.R,M:z.M,goodVisits:z.goodVisits,unitVisits:z.unitVisits,goodPairs:z.goodPairs,unitReturns:z.unitReturns,unitPositive:z.unitPositive,unitRepeat:z.unitRepeat,minUnitCost:z.minUnitCost,reverseCalls:z.reverseSamples.length,maxReverse:z.maxReverse,reverseResults:z.reverseResultCount,reverseBad:z.reverseBad,reverseGoodOnly:z.reverseGoodOnly,sourceStates:z.sourceGroups.size,maxMultiplicity:z.maxMultiplicity,maxUnitMultiplicity:z.maxUnitMultiplicity,maxUnitFree:z.maxUnitFree,multiUnitCostGroups:z.multiUnitCostGroups,cohortChecks:z.cohortChecks,maxK:z.maxK});
  }
 }
 return {totals,examples,cohortExamples,results}
}
console.log(JSON.stringify(audit(),null,2));
