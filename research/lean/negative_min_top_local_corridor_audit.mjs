// Two-sided top-band local corridors and separate canonical-reachability finite audit.
// Run: node research/lean/negative_min_top_local_corridor_audit.mjs
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},mod=(a,m)=>(a%m+m)%m;
 const MAX=400002,sp=new Int32Array(MAX+2);
 for(let p=2;p<sp.length;p++)if(!sp[p]){sp[p]=p;if(p*p<sp.length)for(let j=p*p;j<sp.length;j+=p)if(!sp[j])sp[j]=p}
 function fac(n){let a=[];while(n>1){let p=sp[n];ok(p>0,"factor range");a.push(p);while(n%p===0)n/=p}return a}
 function trial(n){let a=[];for(let p=3;p*p<=n;p+=2)if(n%p===0){a.push(p);while(n%p===0)n/=p}if(n>1)a.push(n);return a}
 function hits(x,n,fs){let s=mod(n,2)===0?1:-1;return fs[s===1?0:1].filter(p=>mod(n,2*p)===(s===1?0:p+2)).map(p=>({p,s,b:s===1?0:3}))}
 function literal(x,n,T){let fs=[trial(x+1),trial(x-1)];ok(sp[x+1]===fs[0][0]&&sp[x-1]===fs[1][0],"SPF oracle");for(let i=1;i<=T;i++){let hh=hits(x,n+i,fs);if(hh.length)return{w:i,...hh[0]}}return null}
 function next(x,n){let w=Infinity,p=0,s=0;for(let e of [-1,1])for(let q of fac(x+e)){let t=mod((e===1?0:q+2)-n,2*q)||2*q;if(t<w||t===w&&q<p){w=t;p=q;s=e}}return{w,p,s}}
 let rows=[],sourceCount=0,rawKeys=0,preBad=0,postBad=0,goodKeys=0,prePins=0,postPins=0,preTicks=0,postTicks=0,nearPairs=0,pairControls=0,localStates=0,canonicalRoots=0,canonicalEvents=0,canonicalHitRoots=0,canonicalKeys=0,canonicalFullKeys=0,canonicalHitChecks=0,gatewayChecks=0,entryPorts=0,entryPinChecks=0,forcedSmallSourceKeys=0,canonicalEntryChecks=0,canonicalFirstTop=0,canonicalFirstTopRoughChecks=0;
 for(let R of [12000,48000,192000]){
  let L=Math.log(R),T=Math.ceil(8*Math.sqrt(2*R+1)),P=Math.max(13,Math.floor(T/(L*L))),K=7,K0=7,U=8,H=3,D=6,W=12;
  let lo=Math.ceil(T/(4*P)),hi=Math.floor(T/(3*P));let arr=[],sources=0,raw=0,pb=0,qb=0;
  for(let p=P;p<=2*P;p++)if(sp[p]===p&&p%12===1){
   for(let v=Math.ceil((R+1)/p);v<=Math.floor((2*R+1)/p);v++){
    if(sp[v]!==v||v%12!==1||v<=p)continue;
    let a=p*v-1,x=p*(v-1);
    if(sp[a-1]<K||sp[x-1]<K0||sp[x+1]<K0||sp[x+1]===x+1)continue;
    sources++;sourceCount++;
    let af=[trial(a+1),trial(a-1)],xf=[trial(x+1),trial(x-1)];
    for(let m=lo;m<=hi;m++)if(m%2===0){
     raw++;rawKeys++;let n=m*p-x/2;
     ok(a%6===0&&x%12===0&&mod(n,2*p)===0&&x/2+n===m*p,"top pins");
     ok(n<0&&m*p+(p-1)/2-U>0,"height range");
     let bad=false;
     for(let u=0;u<=U;u++)for(let e of hits(a,n-u,af)){
      if(e.p===p&&u===0)continue;
      ok(e.p!==p&&e.p>=K&&mod((2*m+1)*p-2*u-2*e.b,e.p)===0,"pre candidate pin");prePins++;bad=true;
     }
     if(bad){pb++;preBad++;continue}
     let lit=literal(a,n-U,U);ok(lit&&lit.w===U&&lit.p===p&&lit.s===1,"actual top event from local state");preTicks+=U;
     for(let u=1;u<=H;u++)for(let e of hits(x,n+u,xf)){
      ok(e.p!==p&&e.p>=K0&&mod(2*m*p+2*u+1-2*e.b,e.p)===0,"post candidate pin");postPins++;bad=true;
     }
     if(bad){qb++;postBad++;continue}
     ok(literal(x,n,H)===null,"actual quiet suffix");postTicks+=H;
     arr.push({a,x,n,p,m});goodKeys++;
    }
   }
  }
  // Count near pairs of either source or destination anchor, including
  // source/destination pairs. Remove both distinct local keys.
  const points=arr.flatMap((a,i)=>[{x:a.a,n:a.n,k:2*a.m+1,c:-1,p:a.p,i},{x:a.x,n:a.n,k:2*a.m,c:0,p:a.p,i}]).sort((a,b)=>a.x-b.x);
  let bad=new Set(),localNear=0;
  for(let i=0;i<points.length;i++)for(let j=i+1;j<points.length&&points[j].x-points[i].x<=D;j++){
   let a=points[i],b=points[j];if(a.i===b.i||Math.abs(a.n-b.n)>W)continue;
   ok(Math.abs(a.k*a.p-b.k*b.p)<=2*W+D+1,"two-sided height relation");
   ok(a.p!==b.p,"same-label near exclusion");pairControls++;nearPairs++;localNear++;bad.add(a.i);bad.add(b.i);
  }
  let keep=arr.filter((a,i)=>!bad.has(i)),owner=new Set(),keymap=new Map();
  for(let a of keep){
   // Guaranteed literal 3-gateway, arriving during the certified idle interval.
   let tau=a.n-U+mod(-(a.n-U),6);
   ok(tau<a.n&&tau>=a.n-U,"gateway time");
   let gate=literal(a.a+2,tau-1,1);ok(gate&&gate.p===3&&gate.s===1,"literal 3 gateway");
   ok(literal(a.a,tau,a.n-tau)?.p===a.p&&literal(a.a,tau,a.n-tau)?.w===a.n-tau,"gateway continuation");gatewayChecks++;
   // Latest eligible source clock strictly before n, and exact entry ports.
   let sourceFactors=[trial(a.a+1),trial(a.a-1)],last=-Infinity;
   for(let s of [-1,1])for(let r of sourceFactors[s===1?0:1]){
    let c=s===1?0:r+2,back=mod(a.n-c,2*r)||2*r;last=Math.max(last,a.n-back);
   }
   ok(last<a.n-U,"preceding source calendar");a.last=last;
   let small=sourceFactors[1].some(r=>r<=31);if(small)forcedSmallSourceKeys++;
   for(let nn=last;nn<=a.n-U;nn++)for(let s of [-1,1])for(let q of fac(a.a-(1-s))){
    if(q===2||mod(nn,2*q)!==(s===1?0:q+2))continue;
    let b=s===1?0:3,u=a.n-nn;
    ok(q!==a.p&&mod((2*a.m+1)*a.p-1-2*u-2*b,q)===0,"entry height divisor");
    entryPinChecks++;
    let par=a.a+q-1,g=literal(par,nn-1,1);if(g&&g.p===q)entryPorts++;
   }
   let key=a.x+","+a.n+","+a.p;ok(!keymap.has(key),"distinct top key");keymap.set(key,{...a,seen:false,full:false});
   for(let u=1;u<=U;u++){let k=a.a+","+(a.n-u);ok(!owner.has(k),"pre states disjoint");owner.add(k);localStates++}
   for(let u=0;u<=H;u++){let k=a.x+","+(a.n+u);ok(!owner.has(k),"post states disjoint");owner.add(k);localStates++}
  }
  let hitRoots=0,hitKeys=0,fullKeys=0,ev=0;
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   canonicalRoots++;let x=A,n=3-A/2,t=0,seen=false,depth=0;
   while(t<2*T){
    let e=next(x,n);if(t+e.w>2*T)break;
    let y=x-e.p+1,nn=n+e.w,k=y+","+nn+","+e.p,rec=keymap.get(k);
    canonicalEvents++;ev++;
    if(depth===0&&e.p>=P){
     canonicalFirstTop++;let qm=Math.min(sp[A-1],sp[A+1]);ok(e.p<=4*qm+7,"canonical first top rough bound");canonicalFirstTopRoughChecks++;
    }
    depth++;
    if(rec){
     ok(x===rec.a&&nn===rec.n,"canonical anchor equality");
     let l=literal(x,n,e.w);ok(l&&l.w===e.w&&l.p===e.p,"canonical match literal");canonicalHitChecks++;
     ok(n>=rec.last&&n<rec.n,"last source calendar entry");canonicalEntryChecks++;
     rec.seen=true;if(e.w>=U)rec.full=true;seen=true;
    }
    x=y;n=nn;t+=e.w;
   }
   if(seen){hitRoots++;canonicalHitRoots++}
  }
  for(let a of keymap.values()){if(a.seen){hitKeys++;canonicalKeys++}if(a.full){fullKeys++;canonicalFullKeys++}}
  rows.push({R,T,P,lo,hi,sources,raw,preBad:pb,postBad:qb,localKeys:arr.length,nearPairs:localNear,kept:keep.length,states:owner.size,canonicalEvents:ev,hitRoots,hitKeys,fullKeys});
 }
 return {sourceCount,rawKeys,preBad,postBad,goodKeys,prePins,postPins,preTicks,postTicks,nearPairs,pairControls,localStates,canonicalRoots,canonicalEvents,canonicalHitRoots,canonicalKeys,canonicalFullKeys,canonicalHitChecks,gatewayChecks,entryPorts,entryPinChecks,forcedSmallSourceKeys,canonicalEntryChecks,canonicalFirstTop,canonicalFirstTopRoughChecks,rows}
}
console.log(JSON.stringify(audit(),null,2));
