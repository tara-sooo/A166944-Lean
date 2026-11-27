// Nonreset anchor isolation and high-height quiet supply: actual finite orbit and local arithmetic controls.
// Run: node research/lean/negative_min_nonreset_anchor_isolation_audit.mjs
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},mod=(a,m)=>(a%m+m)%m;
 const MAX=2400002,sp=new Int32Array(MAX+2);
 for(let p=2;p<sp.length;p++)if(!sp[p]){sp[p]=p;if(p*p<sp.length)for(let n=p*p;n<sp.length;n+=p)if(!sp[n])sp[n]=p}
 function fac(n){let a=[];while(n>1){let p=sp[n];ok(p>0,"factor domain");a.push(p);while(n%p===0)n/=p}return a}
 function trial(n){let a=[];for(let p=3;p*p<=n;p+=2)if(n%p===0){a.push(p);while(n%p===0)n/=p}if(n>1)a.push(n);return a}
 function next(x,n){let w=Infinity,p=0,s=0;for(let e of [-1,1])for(let q of fac(x+e)){let t=mod((e===1?0:q+2)-n,2*q)||2*q;if(t<w||t===w&&q<p){w=t;p=q;s=e}}return {w,p,s}}
 function literal(x,n,T){let a=trial(x-1),b=trial(x+1);ok(sp[x-1]===a[0]&&sp[x+1]===b[0],"least-factor oracle");for(let i=1;i<=T;i++){let nn=n+i,qs=mod(nn,2)===0?b:a,hit=qs.filter(p=>mod(nn,2*p)===(mod(nn,2)===0?0:p+2));if(hit.length)return {w:i,p:Math.min(...hit),s:mod(nn,2)===0?1:-1}}return null}
 function record(x,n,p,s,w){let b=s===1?0:3,c=1-s,h=x/2+n;ok(h>=0&&mod(h-b,p)===0&&mod(x-c,p)===0,"anchor pins");return{x,n,p,s,w,h,b,c,m:(h-b)/p}}
 let rows=[],events=0,literalTicks=0,anchorCount=0,resetCount=0,nearPairs=0,nonresetPairs=0,sameLabelNear=0,ratioChecks=0,connectorStates=0,connectorEvents=0,connectorExits=0,connectorFull=0,sourceCount=0,forcedComposite=0,idleCount=0,fastCount=0,fastPins=0,localResidues=0,sourceTicks=0,sourceNear=0,sourceConnectorStates=0;
 for(let R of [12000,48000,192000,768000]){
  let T=Math.ceil(8*Math.sqrt(2*R+1)),U=Math.max(7,Math.floor(R**.25)),Y=Math.max(41,Math.floor(T/30)),H=8,D=10;
  ok(Y>H+D/2+3,"near bounds");let map=new Map();
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   let x=A,n=3-A/2,t=0,depth=0;
   while(t<T){
    let e=next(x,n);if(t+e.w>T)break;
    let l=literal(x,n,e.w);ok(l&&l.p===e.p&&l.w===e.w&&l.s===e.s,"literal recurrence");events++;literalTicks+=e.w;
    t+=e.w;n+=e.w;x-=e.p-1;depth++;
    if(e.p>=Y&&e.w>=U){
     let a=record(x,n,e.p,e.s,e.w);ok(a.m>=0,"nonnegative coefficient");ok(a.h<=T+3,"height strip");map.set(`${x},${n},${e.p}`,a);
    }
    if(A%294!==0&&depth>=1)break;
   }
  }
  let arr=[...map.values()].sort((a,b)=>a.x-b.x),bad=new Set(),localPairs=0,localReset=0;
  for(let a of arr){anchorCount++;if(a.m===0){bad.add(a);resetCount++;localReset++}}
  for(let i=0;i<arr.length;i++)for(let j=i+1;j<arr.length&&arr[j].x-arr[i].x<=D;j++){
   let a=arr[i],b=arr[j];if(Math.abs(a.n-b.n)>H)continue;nearPairs++;localPairs++;
   if(a.p===b.p){sameLabelNear++;throw Error("same label near distinct anchors")}
   ok((a.m===0)===(b.m===0),"reset/nonreset exclusion");
   if(a.m&&b.m){
    nonresetPairs++;let S=H+D/2+3;ok(Math.abs(a.m*a.p-b.m*b.p)<=S,"rational ratio restriction");ratioChecks++;
    bad.add(a);bad.add(b);
   }
  }
  let good=arr.filter(a=>!bad.has(a)),owner=new Map(),localExit=0,localFull=0;
  for(let a of good){
   let x=a.x,n=a.n;
   for(let i=0;i<=H;i++){
    ok(a.x-x<=D,"connector envelope");let key=x+","+n;
    ok(!owner.has(key)||owner.get(key)===a,"distinct anchored connector");owner.set(key,a);connectorStates++;
    if(i===H){connectorFull++;localFull++;break}
    let l=literal(x,n,1);if(l){connectorEvents++;let nx=x-l.p+1;if(a.x-nx>D){connectorExits++;localExit++;break}x=nx;}
    n++;
   }
  }
  let src=[],localSources=0,localIdle=0,localFast=0;
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   let p=sp[A+1],v=(A+1)/p;
   if(p<13||p%12!==1||v%12!==7||sp[v]!==v||v<=4*p||sp[A-1]<4*p)continue;
   let x=A-p+1,K=11,Hs=4;
   if(Math.min(sp[x-1],sp[x+1])<K)continue;
   let aux=fac(x+1).find(r=>r>=K&&r<=199&&r<x+1);if(!aux)continue;
   ok(mod(x+1,aux)===0&&mod(p-1,aux)!==0&&mod(p-3,aux)!==0,"aux pin admissibility");forcedComposite++;
   let n=3-A/2,w=(3*p-7)/2,e=next(A,n),l=literal(A,n,w);
   ok(e.p===p&&e.s===1&&e.w===w&&l&&l.p===p&&l.w===w,"nonreset first event");
   let a=record(x,n+w,p,1,w);ok(a.h===p&&a.m===1,"height retained");sourceCount++;localSources++;sourceTicks+=w;
   for(let q of [11,13,17,19,23,29,31]){
    if(q===p||q===aux)continue;
    let hit=0;for(let v0=1;v0<q;v0++)if(mod(p*v0-2,q)===0||mod(p*(v0-1)-1,q)===0||mod(p*(v0-1)+1,q)===0)hit++;
    ok(hit<=3&&hit<q-1,"local dim3");localResidues++;
   }
   let f=literal(x,a.n,Hs);
   if(f){let b=f.s===1?0:3;ok(f.p!==p&&mod(2*p+2*f.w+1-2*b,f.p)===0&&f.p<=2*(p+f.w)+1,"fast stationary pin");fastCount++;fastPins++;localFast++;continue}
   idleCount++;localIdle++;src.push(a);
  }
  src.sort((a,b)=>a.x-b.x);let badS=new Set();
  for(let i=0;i<src.length;i++)for(let j=i+1;j<src.length&&src[j].x-src[i].x<=D;j++){
   let a=src[i],b=src[j];if(Math.abs(a.n-b.n)>H)continue;
   ok(a.p!==b.p&&Math.abs(a.p-b.p)<=H+D/2,"source near ratio");sourceNear++;badS.add(a);badS.add(b);
  }
  let own=new Map();for(let a of src)if(!badS.has(a))for(let i=0;i<=4;i++){
   let key=a.x+","+(a.n+i);ok(!own.has(key),"separated high-height idle states");own.set(key,a);sourceConnectorStates++;
  }
  rows.push({R,T,U,Y,H,D,anchors:arr.length,resets:localReset,near:localPairs,good:good.length,full:localFull,exit:localExit,sources:localSources,idle:localIdle,fast:localFast});
 }
 // Nonvacuous arithmetic-only near-pair controls with exact clock pins.
 let pinPairs=0,oppositeSignPinPairs=0,example=null;
 for(let p of [41,43,47,53,59,61])for(let q of [41,43,47,53,59,61])for(let s of [-1,1])for(let t of [-1,1])for(let m=0;m<=3;m++)for(let k=0;k<=3;k++){
  let h=m*p+(s===1?0:3),hh=k*q+(t===1?0:3);
  if(Math.abs(h-hh)>13)continue;
  // n pin: x/2=h-n; n residue 0 or p+2 mod2p.
  let x0=mod(2*(h-(s===1?0:p+2)),4*p);
  for(let d=-10;d<=10;d+=2){
   let e=hh-h-d/2;if(Math.abs(e)>8)continue;
   for(let x=x0+4*p;x<=x0+4*p*q;x+=4*p){
    let y=x+d,n=h-x/2,nn=hh-y/2;if(mod(nn,2*q)!==(t===1?0:q+2))continue;
    let a=record(x,n,p,s,1),b=record(y,nn,q,t,1);
    if(a.x===b.x&&a.n===b.n&&p===q)continue;
    ok(p!==q&&(m===0)===(k===0),"arithmetic near-key exclusion");
    if(m&&k){ok(Math.abs(m*p-k*q)<=13+3,"ratio bound");pinPairs++;if(s!==t)oppositeSignPinPairs++;if(!example)example={a,b,d,e};}
    break;
   }
  }
 }
 ok(pinPairs>0&&oppositeSignPinPairs>0,"nonvacuous pin pair controls");
 return {pinPairs,oppositeSignPinPairs,example,events,literalTicks,anchorCount,resetCount,nearPairs,nonresetPairs,sameLabelNear,ratioChecks,connectorStates,connectorEvents,connectorExits,connectorFull,sourceCount,forcedComposite,idleCount,fastCount,fastPins,localResidues,sourceTicks,sourceNear,sourceConnectorStates,rows};
}
console.log(JSON.stringify(audit(),null,2));
