// Exact last-entry section closure, strip trial certificate and terminal prime-scale checks.
// Run: node research/lean/negative_min_last_entry_strip_audit.mjs
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},mod=(a,m)=>(a%m+m)%m;
 const max=1600010,sp=new Int32Array(max),pr=[];
 for(let p=2;p<max;p++)if(!sp[p]){sp[p]=p;pr.push(p);if(p*p<max)for(let j=p*p;j<max;j+=p)if(!sp[j])sp[j]=p}
 function fac(n){let a=[];while(n>1){let p=sp[n];ok(p>0,"factor domain");a.push(p);while(n%p===0)n/=p}return a}
 function next(x,h,z=Infinity){let n=h-x/2,w=Infinity,p=0,s=0;for(let t of [-1,1])for(let q of fac(x+t)){if(q>z)continue;let u=mod((t===1?0:q+2)-n,2*q)||2*q;if(u<w||u===w&&q<p){w=u;p=q;s=t}}return{w,p,s}}
 function literal(x,h){let n=h-x/2+1,s=mod(n,2)?-1:1,m=x+s;for(let q=3;q<=m;q+=2){if(q*q>m){q=m;if(q===1)break}if(m%q===0){if(mod(n,2*q)===(s===1?0:q+2))return q;while(m%q===0)m/=q}}return 0}
 function setmin(m,x,A){let o=m.get(x);if(o===undefined||A<o)m.set(x,A)}
 function same(a,b,msg){ok(a.size===b.size,msg+" size");for(let [x,A] of a)ok(b.get(x)===A,msg+" value")}
 let rows=[],roots=0,events=0,entryInc=0,returnChecks=0,closureChecks=0,trialSinks=0,commonSinks=0,trueSinks=0,defects=0,defectPinChecks=0,terminalAnchorChecks=0,terminalDistinct=0,comparable=0,gapDown=0,gapUp=0,literalChecks=0,terminalHeightChecks=0;
 for(let R of [48000,192000,768000]){
  let H=Math.floor(R**.4),B=4*H;
  let widths=[Math.max(3,Math.floor(H/16)),Math.floor(H/4)];
  for(let W of widths){
   let lo=H-W,Z=Math.max(2*W+3,Math.floor(H*.65)),first=new Map(),all=new Map(),direct=new Map(),terms=new Set(),entryHits=0,ev=0;
   for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
    roots++;let x=A,h=3,seen=false,last=[],hit=false;
    while(A-x<=B){
     let e=next(x,h),span=Math.min(e.w-1,H-h);
     if(h<lo&&lo<=h+span){setmin(all,x,A);if(!seen){setmin(first,x,A);seen=true}entryInc++;entryHits++}
     if(h+span===H){setmin(direct,x,A);hit=true;
      let q=Math.min(sp[x-1],sp[x+1]);
      for(let a of last){
       let d=a.x-x;if(d>6||a.p<11)continue;
       let s=x%q===1?-1:1;
       ok(mod(x+d-(1-a.s),a.p)===0&&mod(x+s,q)===0,"terminal spatial pins");
       ok(a.p!==q,"even-offset distinct primes");
       ok(H-a.h<=13*d/8+395/12+2*q,"terminal alignment");terminalHeightChecks++;
       terminalAnchorChecks++;let k=x+","+a.p+","+q+","+d;if(terms.has(k))continue;terms.add(k);
       if(a.p*3<q)gapUp++;else if(a.p>3*q)gapDown++;else comparable++;
      }break
     }
     x-=e.p-1;h+=e.w-(e.p-1)/2;events++;ev++;
     last=last.filter(a=>a.x-x<=6);last.push({x,h,p:e.p,s:e.s});
     ok(h>=0&&h<H,"event height");
    }
   }
   // Full confined map: a successful trial path stays within [lo,H].
   function confined(x,A,z,check=false){
    let h=lo,bad=new Set();
    while(A-x<=B){
     let e=next(x,h,z),I=H-h;
     let span=Math.min(e.w-1,I);
     if(check){
      for(let i=0;i<span;i++){
       let actual=literal(x,h+i);if(actual){ok(actual>z,"trial idle discrepancy");bad.add(x+","+(h+i))}
      }
     }
     if(e.w>I)return{x,bad};
     if(check)ok(literal(x,h+e.w-1)===e.p,"literal trial winner");
     x-=e.p-1;h+=e.w-(e.p-1)/2;
     if(h<lo)return null;
    }
    return null
   }
   // Actual excursion from a bottom entry: if it dips below lo, follow until
   // the next UPWARD entry. Calendar transitions skip idle ticks exactly.
   function excursion(x,A){
    let h=lo,down=false;
    while(A-x<=B){
     let e=next(x,h),target=down?lo:H,I=target-h;
     ok(I>0,"excursion target");
     if(e.w>I)return{kind:down?"return":"sink",x};
     x-=e.p-1;h+=e.w-(e.p-1)/2;
     if(h<lo)down=true;
    }
    return null
   }
   let closure=new Map(first),closedSink=new Map(),ret=0,closed=0;
   for(let x=2*R-(2*R%2);x>=R-B;x-=2){
    let A=closure.get(x);if(A===undefined)continue;closed++;
    let v=excursion(x,A);if(!v)continue;
    if(v.kind==="return"){ok(v.x<x,"strict return spatial");setmin(closure,v.x,A);returnChecks++;ret++}else setmin(closedSink,v.x,A);
   }
   same(closure,all,"all entry closure");same(closedSink,direct,"closed sink");closureChecks+=2;
   let fc=new Map(),ac=new Map(),tc=new Map(),trialRep=new Map();
   for(let [x,A] of first){let v=confined(x,A,Infinity);if(v)setmin(fc,v.x,A)}
   for(let [x,A] of all){
    let v=confined(x,A,Infinity);if(v)setmin(ac,v.x,A);
    let q=confined(x,A,Z);if(q){let old=trialRep.get(q.x);if(!old||A<old.A){trialRep.set(q.x,{x,A});setmin(tc,q.x,A)}}
   }
   same(ac,direct,"last-entry confined sink");closureChecks++;
   // Enumerate exact changed state set in band, true winner >Z.
   let D=new Set();
   for(let h=lo;h<H;h++)for(let s of [-1,1]){
    let F=2*h+(s===1?3:-3);
    for(let p of fac(F))if(p>Z&&p>2){
     let x0=R-B+mod(-s-(R-B),p);
     for(let x=x0;x<=2*R;x+=p){
      if(x%2)continue;
      let n=h-x/2+1;if(mod(n,2)!==(s===1?0:1))continue;
      let e=next(x,h);if(e.w===1&&e.p>Z){D.add(x+","+h);defectPinChecks++;ok(e.p<=2*H+3,"defect height cap")}
     }
    }
   }
   let usedBad=new Set(),common=new Map(),nBad=0;
   for(let [sink,r] of trialRep){
    let x=r.x,h=lo,dirty=false;
    while(h<H){
     let key=x+","+h;
     if(D.has(key)){ok(!usedBad.has(key),"distinct trial sinks cannot share bad state");usedBad.add(key);dirty=true}
     let e=next(x,h,Z),I=H-h;
     if(e.w>I){
      for(let i=1;i<I;i++){let k=x+","+(h+i);if(D.has(k)){ok(!usedBad.has(k),"distinct trial sinks cannot share idle bad state");usedBad.add(k);dirty=true}}
      h=H;break
     }
     for(let i=1;i<e.w;i++){let k=x+","+(h+i);if(D.has(k)){ok(!usedBad.has(k),"distinct trial sinks cannot share idle bad state");usedBad.add(k);dirty=true}}
     x-=e.p-1;h+=e.w-(e.p-1)/2;ok(h>=lo,"trial success stays band")
    }
    ok(x===sink,"trial replay sink");
    if(dirty)nBad++;else{setmin(common,sink,r.A);ok(direct.has(sink)&&direct.get(sink)<=r.A,"actual witness common");if(common.size%100===1){let a=confined(r.x,r.A,Z,true);ok(a&&a.x===sink&&a.bad.size===0,"independent common literal");literalChecks++}}
   }
   ok(nBad<=D.size&&common.size>=tc.size-D.size,"uniform loss certificate");
   // Directly check defect enumeration completeness at a deterministic sample.
   for(let h=lo;h<H;h++)for(let x=R-B;x<=2*R;x+=602){let xx=x-x%2,e=next(xx,h);ok(D.has(xx+","+h)===(e.w===1&&e.p>Z),"defect enumeration oracle")}
   trialSinks+=tc.size;commonSinks+=common.size;trueSinks+=direct.size;defects+=D.size;terminalDistinct+=terms.size;
   rows.push({R,H,W,lo,Z,firstEntries:first.size,allEntries:all.size,entryInc:entryHits,returns:ret,closed,firstConfined:fc.size,allConfined:ac.size,trueSinks:direct.size,trialSinks:tc.size,commonSinks:common.size,badTrialSinks:nBad,defects:D.size,uniformLower:Math.max(0,tc.size-D.size),terminalAnchors:terms.size,events:ev});
  }
 }
 return{rows,roots,events,entryInc,returnChecks,closureChecks,trialSinks,commonSinks,trueSinks,defects,defectPinChecks,terminalAnchorChecks,terminalDistinct,comparable,gapDown,gapUp,literalChecks,terminalHeightChecks}
}
console.log(JSON.stringify(audit(),null,2));
