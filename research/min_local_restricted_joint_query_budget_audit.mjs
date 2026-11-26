// Joint CRT discovery budgets: finite supermartingale audit with exact restricted clocks.
function audit(){
 const mod=(a,b)=>(a%b+b)%b,ck=(x,m)=>{if(!x)throw Error(m)},ps=[3,5,7,11,13,17];
 function next(u,v,A){let p=Infinity,w=Infinity;for(let r of A){let e=mod(u,r)===1?1:mod(u,r)===r-1?-1:0;if(!e)continue;let t=mod((e===1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}}return {p,w}}
 function choose(n,k){if(k===0)return 1;let v=1;for(let i=1;i<=k;i++)v*=i;return n**k/v}
 const controls=[
 {z:7,D:20,bands:[{p:[5],B:.21,k:1},{p:[7],B:.15,k:1}]},
 {z:11,D:24,bands:[{p:[5,7],B:.40,k:2},{p:[11],B:.19,k:1}]},
 {z:13,D:28,bands:[{p:[5,7],B:.40,k:2},{p:[11,13],B:.25,k:2}]},
 {z:17,D:36,bands:[{p:[5,7],B:.45,k:1},{p:[11,13],B:.25,k:1},{p:[17],B:.12,k:1}]},
 {z:17,D:36,bands:[{p:[5,7],B:.42,k:2},{p:[11,13,17],B:.27,k:2}]}
 ];
 let out=[];
 for(let {z,D,bands} of controls){
  let A=ps.filter(p=>p<=z),P=4*A.reduce((a,b)=>a*b,1),base=P,idx=new Map();bands.forEach((a,i)=>a.p.forEach(p=>idx.set(p,i)));
  let s={z,D,bands,roots:0,actualEvents:0,unknownQueries:0,activeQueries:0,knownQueries:0,conditionalChecks:0,budgetStops:0,jointHits:0,terminalStops:0,gainStops:0,fullHits:0,eligibleOriginalHits:0,supermartingaleChecks:0,meanFinalPotential:0,initialPotential:bands.reduce((a,b)=>a*choose(b.B/(1-b.B),b.k),1),maxPotential:0,posteriorGroups:0};
  function run(X,truncated,record){
   let u=X,v=X/2+3,seen=new Map(),hit=new Set(),C=bands.map(()=>0),F=bands.map(()=>0),K=bands.map(()=>0),stopped=false,reason=null;
   const val=()=>bands.reduce((a,b,i)=>a*choose(Math.max(0,(b.B-C[i])/(1-b.B)),Math.max(0,b.k-K[i])),1);
   function query(t,win,terminal){
    let e=t%2?-1:1,h=t-u/2,def=2*h+(e===1?1:-5);
    for(let p of A){if(p>win||def%p!==0)continue;
     let r=mod(e-(u-X),p),j=idx.get(p),yes=mod(X,p)===r;
     if(p===3){if(yes)return true;continue}
     if(!seen.has(p))seen.set(p,new Set());let S=seen.get(p);
     if(hit.has(p)||S.has(r)){if(record)s.knownQueries++;if(yes){ck(hit.has(p)&&win===p&&!terminal,"known hit");return true}continue}
     if(record)s.unknownQueries++;
     let active=j!==undefined&&K[j]<bands[j].k;
     if(active){
      let b=bands[j],cost=1/p;
      if(truncated&&C[j]+cost>b.B+1e-12){stopped=true;reason="budget";return false}
      if(truncated){
       let q=1/(p-S.size),rem=b.k-K[j],left=(b.B-C[j])/(1-b.B),d=cost/(1-b.B),after=Math.max(0,left-d);
       ck(q<=d+1e-12&&d<=left+1e-12,"hazard");
       let before=choose(left,rem),expected=(1-q)*choose(after,rem)+q*choose(after,rem-1);
       ck(expected<=before+1e-12,"one-step supermartingale");
       if(record)s.supermartingaleChecks++;
      }
      C[j]+=cost;if(!yes)F[j]+=cost;else K[j]++;
      if(record)s.activeQueries++;
     }
     if(yes){ck(win===p&&!terminal,"positive");hit.add(p);return true}
     S.add(r);
    }return false
   }
   while(u-X<D&&!stopped){
    if(truncated&&K.every((k,i)=>k>=bands[i].k)){reason="success";break}
    let a=next(u,v,A);
    if(!isFinite(a.p)){for(let j=1;j<=2*z&&!stopped;j++)query(v+j,Infinity,true);if(!stopped)reason="terminal";break}
    for(let j=1;j<=a.w&&!stopped;j++)query(v+j,j===a.w?a.p:Infinity,false);
    if(stopped)break;
    u+=a.p-1;v+=a.w;if(record)s.actualEvents++;
   }
   if(!reason)reason=u-X>=D?"gain":"success";
   return {K,C,F,reason,value:val(),all:K.every((k,i)=>k>=bands[i].k)};
  }
  for(let X=base;X<base+P;X+=6){
   let full=run(X,false,false),a=run(X,true,true);s.roots++;
   let eligible=full.all&&full.C.every((c,i)=>c<=bands[i].B+1e-12);
   if(full.all)s.fullHits++;
   if(eligible){s.eligibleOriginalHits++;ck(a.all,"eligible original survives")}
   if(a.all)s.jointHits++;
   if(a.reason==="budget")s.budgetStops++;else if(a.reason==="terminal")s.terminalStops++;else if(a.reason==="gain")s.gainStops++;
   s.meanFinalPotential+=a.value;s.maxPotential=Math.max(s.maxPotential,a.value);
  }
  s.meanFinalPotential/=s.roots;
  ck(s.meanFinalPotential<=s.initialPotential+1e-10,"global supermartingale");ck(s.jointHits/s.roots<=s.initialPotential+1e-10,"joint tail");ck(s.eligibleOriginalHits===s.jointHits,"exact eligible success correspondence");
  out.push(s)
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
