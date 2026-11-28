// Macro-to-small connector isolation and terminal record tests. Finite proxies, not asymptotic sieve verification.
// Run: node research/lean/negative_min_macro_small_connector_audit.mjs
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},mod=(a,m)=>(a%m+m)%m;
 const MAX=1600010,sp=new Int32Array(MAX),pr=[];
 for(let p=2;p<MAX;p++)if(!sp[p]){sp[p]=p;pr.push(p);if(p*p<MAX)for(let j=p*p;j<MAX;j+=p)if(!sp[j])sp[j]=p}
 function fac(n){let a=[];while(n>1){let p=sp[n];ok(p>0,"factor domain");a.push(p);while(n%p===0)n/=p}return a}
 function trial(n){let a=[];for(let p of pr){if(p*p>n)break;if(n%p===0){a.push(p);while(n%p===0)n/=p}}if(n>1)a.push(n);return a}
 function next(x,n){let w=Infinity,p=0,s=0;for(let t of [-1,1])for(let q of fac(x+t)){let u=mod((t===1?0:q+2)-n,2*q)||2*q;if(u<w||u===w&&q<p){w=u;p=q;s=t}}return {w,p,s}}
 function literal(x,n){let s=mod(n,2)?-1:1;return trial(x+s).find(p=>mod(n,2*p)===(s===1?0:p+2))||0}
 let rows=[],rootCount=0,eventCount=0,anchorPinChecks=0,wallChecks=0,roughBad=0,nonresetGood=0,resetGood=0,nearPairs=0,nearPinChecks=0,distinctRecords=0,connectorTicks=0,connectorEvents=0,connectorHits=0,connectorExits=0,terminalCases=0,terminalRough=0,terminalShort=0,terminalSinkCount=0,lowOnly=0,terminalLowRoughChecks=0,blockChecks=0,resetNearChecks=0,distinctMacroSites=0;
 for(let R of [192000,768000]){
  let H=Math.floor(R**.4),Y=Math.ceil(H/2),K=Math.max(5,Math.floor(H/32)),z=3,Q=6,B=4*H,C=Math.ceil(17*Q/8+395/12+2*K);
  ok(C+Q/2+3<Y,"separation margins");
  let keys=new Map(),sinks=new Set(),term=new Set(),localRoots=0,localEvents=0;
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   rootCount++;localRoots++;let x=A,n=3-A/2,h=3,lastNonSmall=null;
   while(A-x<=B){
    let e=next(x,n),I=H-h;
    if(e.w>I){
     ok(I>=1,"first H idle");sinks.add(x);
     if(lastNonSmall&&lastNonSmall.p>=Y){
      terminalCases++;term.add(x);let a=lastNonSmall,d=a.x-x;
      ok(d>=0&&d<Q&&d%2===0,"terminal wall");
      ok(mod(x+d-(1-a.s),a.p)===0,"terminal spatial pin");
      let qm=Math.min(sp[x-1],sp[x+1]);
      if(qm>=K){terminalRough++;ok(mod(x-1,a.p)!==0&&mod(x+1,a.p)!==0,"terminal sieve forms distinct")}
      else{terminalShort++;ok(H-a.h<=13*d/8+395/12+2*K,"terminal alignment")}
     }else if(!lastNonSmall){
      lowOnly++;ok(A-x<Q,"all-small wall");ok(Math.min(sp[x-1],sp[x+1])>(H-3-13*(A-x)/8-395/12)/2,"all-small roughness");terminalLowRoughChecks++;
     }
     break;
    }
    x-=e.p-1;n+=e.w;h=x/2+n;eventCount++;localEvents++;
    ok(h>=0&&h<H,"actual event height");
    if(e.p>z){let a={x,n,h,p:e.p,s:e.s,w:e.w,m:(h-(e.s===1?0:3))/e.p};lastNonSmall=a;
     if(e.p>=Y&&A-x<=B){
      ok(a.m>=0&&Number.isInteger(a.m)&&mod(x-(1-a.s),a.p)===0,"macro pins");anchorPinChecks++;
      keys.set(`${x},${n},${e.p}`,a)
     }
    }
   }
  }
  let good=[],localBad=0,localReset=0,localNonreset=0;
  for(let a of keys.values()){
   let bad=false;
   for(let d=0;d<=Q;d+=2)if(Math.min(sp[a.x-d-1],sp[a.x-d+1])>=K){bad=true;break}
   if(bad){roughBad++;localBad++;continue}
   if(a.m===0){resetGood++;localReset++}else{nonresetGood++;localNonreset++}
   good.push(a)
  }
  good.sort((a,b)=>a.x-b.x);let del=new Set(),lp=0;
  for(let i=0;i<good.length;i++)for(let j=i+1;j<good.length&&good[j].x-good[i].x<=Q;j++){
   let a=good[i],b=good[j];if(Math.abs(a.n-b.n)>C)continue;
   ok(a.p!==b.p,"same-label near exclusion");
   ok((a.m===0)===(b.m===0),"reset/nonreset exclusion");nearPinChecks++;
   if(!a.m){resetNearChecks++;continue}
   let ba=a.s===1?0:3,bb=b.s===1?0:3;
   ok(Math.abs(a.m*a.p-b.m*b.p)<=C+Q/2+3,"near height relation");
   nearPairs++;lp++;del.add(i);del.add(j);
  }
  let owner=new Map(),localStates=0,localEnd=0,localExits=0;
  for(let i=0;i<good.length;i++){
   if(del.has(i))continue;let a=good[i],x=a.x,n=a.n,h=a.h,W=0,G=0,lastN=n;
   for(let t=0;;t++){
    ok(t<=C,"connector time cap");ok(a.x-x<Q,"connector wall");wallChecks++;
    let key=x+","+n;
    if(a.m){ok(!owner.has(key),"disjoint nonreset connectors");owner.set(key,i);distinctRecords++;localStates++}
    else if(owner.has(key))throw Error("reset connector collision");
    if(h===H){connectorHits++;localEnd++;break}
    let p=literal(x,n+1);
    if(p>z){connectorExits++;localExits++;break}
    if(p){let w=n+1-lastN;W+=w;G+=p-1;lastN=n+1;connectorEvents++;ok(48*W<=102*G+1580,"complete block bound");blockChecks++;x-=p-1}
    n++;h=x/2+n;connectorTicks++;
   }
  }
  // Check reset-vs-nonreset even when reset connector was processed first.
  for(let a of good.filter(a=>!a.m)){
   let x=a.x,n=a.n;
   for(let t=0;t<=C;t++){
    ok(!owner.has(x+","+n),"reset/nonreset full connector separation");
    if(x/2+n===H)break;let p=literal(x,n+1);if(p>z)break;if(p)x-=p-1;n++;
   }
  }
  terminalSinkCount+=term.size;distinctMacroSites+=keys.size;
  rows.push({R,H,Y,K,z,Q,C,roots:localRoots,events:localEvents,allSinks:sinks.size,terminalMacroSinks:term.size,macroKeys:keys.size,roughBad:localBad,nonresetGood:localNonreset,resetGood:localReset,nearPairs:lp,distinctNonresetStates:localStates,connectorHits:localEnd,connectorExits:localExits});
 }
 return{rows,rootCount,eventCount,anchorPinChecks,wallChecks,roughBad,nonresetGood,resetGood,nearPairs,nearPinChecks,distinctRecords,connectorTicks,connectorEvents,connectorHits,connectorExits,terminalCases,terminalRough,terminalShort,terminalSinkCount,lowOnly,terminalLowRoughChecks,blockChecks,resetNearChecks,distinctMacroSites}
}
console.log(JSON.stringify(audit(),null,2));
