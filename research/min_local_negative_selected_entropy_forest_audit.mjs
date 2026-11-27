// Selected near-square-root first-cut entropy ledger: binary mixture, label and displacement shell.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=4000005,spf=new Int32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let x=p*p;x<=N;x+=p)if(!spf[x])spf[x]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity,side=0;for(let s of [-1,1])for(let q of fs(a-s)){let v=mod((s===-1?0:q+2)-n,2*q)||2*q;if(v<w||v===w&&q<p){p=q;w=v;side=s}}return {p,w,side}}
 const f=x=>x?x*Math.log(x):0,g=x=>f(1+x)-f(x),mix=(a,b)=>f(a+b)-f(a)-f(b);
 let z={roots:0,events:0,selected:0,edgeKeys:0,trafficChecks:0,entropyChecks:0,shellChecks:0,tailChecks:0,rows:[]};
 for(let R of [12000,48000,192000,480000,1000000,2000000]){
  let K=Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),T=4*K,J=Math.floor(T/5),H=Math.floor(3+T-J/2)+1,lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nr=(hi-lo)/6+1,sites=new Map(),levels=Array.from({length:H},()=>new Map()),endpoints=new Map(),gains=[],ns=0;
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,h=3,W=0,record=3,ar=[],er=[],pending=null,end=n+T;
   for(;;){let e=next(a,n),pre=h+e.w,fire=n+e.w;
    if(pending&&pre>=pending.b){er.push({...pending,c:a,D:pending.a-a});pending=null}
    if(pre>record){let cap=Math.min(pre,H);ar.push(a,record+1,cap);record=cap}
    if(fire>end)break;
    if(pre===record&&record<H){ck(!pending,"pending");pending={b:pre,a,p:e.p,s:e.side}}
    a-=e.p-1;n=fire;W+=e.w;h=pre-(e.p-1)/2;z.events++;
   }
   let G=A-a;z.roots++;
   if(G>J)continue;
   ck(record===H&&ar.at(-3)===a&&W<=9*G/4+8&&T-W>2*K,"selected cut");
   ck(er.every(e=>e.b<H),"edge cut");
   ns++;z.selected++;gains.push(G);endpoints.set(a,(endpoints.get(a)||0)+1);
   for(let i=0;i<ar.length;i+=3){let x=ar[i],v=sites.get(x)||[];v.push(ar[i+1],ar[i+2]);sites.set(x,v)}
   let sum=0;for(let e of er){let m=levels[e.b],v=m.get(e.a)||{...e,m:0};ck(v.c===e.c&&v.p===e.p&&v.s===e.s,"map");v.m++;m.set(e.a,v);sum+=e.D}ck(sum===G,"gain");
  }
  function u(a,b){let ar=sites.get(a)||[],m=0;for(let i=0;i<ar.length;i+=2)m+=+(ar[i]<=b&&b<=ar[i+1]);return m}
  let sum=0,base=0,branch=0,bin=0,bc=0,alpha=0,beta=0,globalCross=0,globalLabel=0,globalShell=0,bandRows=[],bands=new Map(),cutL=0;
  for(let b=4;b<H;b++){
   let map=levels[b],incoming=new Map(),mass=0,B=0,actualBase=0,actualBranch=0,labelMass=new Map(),shellSum=new Map(),labelActual=0,shellActual=0;
   for(let [a,e] of map){let v=incoming.get(e.c)||[];v.push(e);incoming.set(e.c,v);mass+=e.m;let k=e.p+":"+e.s;labelMass.set(k,(labelMass.get(k)||0)+e.m);shellSum.set(k,(shellSum.get(k)||0)+e.m*Math.floor(e.D/(4*e.p)));z.edgeKeys++}
   for(let a of new Set([...map.keys(),...incoming.keys()])){
    let v=incoming.get(a)||[],I=v.reduce((s,x)=>s+x.m,0),m=u(a,b),F=m+I;ck(map.has(a)?map.get(a).m===F:u(a,b+1)===F,"traffic");z.trafficChecks++;
    if(I){B+=m;actualBase+=mix(m,I);actualBranch+=f(I)-v.reduce((s,x)=>s+f(x.m),0);
     let byLabel=new Map(),keys=new Set();
     for(let e of v){let k=e.p+":"+e.s,i=Math.floor(e.D/(4*e.p)),key=k+":"+i;ck(!keys.has(key),"shell injective");keys.add(key);let l=byLabel.get(k)||[];l.push(e);byLabel.set(k,l);z.shellChecks++}
     labelActual+=f(I)-[...byLabel.values()].reduce((s,l)=>s+f(l.reduce((q,x)=>q+x.m,0)),0);
     for(let l of byLabel.values())shellActual+=f(l.reduce((s,x)=>s+x.m,0))-l.reduce((s,x)=>s+f(x.m),0)
    }
   }
   let lb=f(mass)-[...labelMass.values()].reduce((s,m)=>s+f(m),0),sb=0;for(let [k,m] of labelMass)sb+=m*g(shellSum.get(k)/m);
   ck(Math.abs(actualBranch-labelActual-shellActual)<1e-6,"decomposition");
   ck(actualBase<=mix(mass,B)+1e-6&&labelActual<=lb+1e-6&&shellActual<=sb+1e-6,"entropy bound");z.entropyChecks++;
   sum+=actualBase+actualBranch;base+=actualBase;branch+=actualBranch;bin+=labelActual;bc+=shellActual;alpha+=mass;beta+=B;globalCross+=mix(mass,B);globalLabel+=lb;globalShell+=sb;cutL=sum/ns;
   let h=2**Math.floor(Math.log2(b)),r=bands.get(h)||{h,mass:0,B:0,delta:0,cross:0,label:0,shell:0,boundCross:0,boundLabel:0,boundShell:0,collidingMass:0};
   r.mass+=mass;r.B+=B;r.delta+=actualBase+actualBranch;r.cross+=actualBase;r.label+=labelActual;r.shell+=shellActual;r.boundCross+=mix(mass,B);r.boundLabel+=lb;r.boundShell+=sb;
   for(let v of incoming.values())if(v.length>1)r.collidingMass+=v.reduce((s,e)=>s+e.m,0);
   bands.set(h,r);
   // At higher first-preheight cuts, roots with sufficiently small final gain have already arrived.
   // For a tail bound use all roots with gain above the barrier, conditional binary entropy.
   if((b+1&(b))===0||b===H-1){
    let L=0;for(let [a,m] of endpoints)L+=f(m);let cutoff=Math.max(0,Math.ceil(18*b/35-10)-1),tail=gains.filter(x=>x>cutoff).length/ns;
    // Conditional on final endpoint and no later movement, first cut is that endpoint.
    let upper=(tail? -tail*Math.log(tail):0)+(tail<1?-(1-tail)*Math.log(1-tail):0)+tail*Math.log(Math.floor(J/2)+1);
    ck(L/ns-cutL<=upper+1e-7,{b,L:L/ns,cutL,tail,upper});z.tailChecks++;
    bandRows.push({b,cutEntropy:cutL,remaining:L/ns-cutL,tail,upper});
   }
  }
  let L=[...endpoints.values()].reduce((s,m)=>s+f(m),0)/ns;ck(Math.abs(sum/ns-L)<1e-8,"global entropy");z.entropyChecks++;
  let bs=[...bands.values()].map(r=>Object.fromEntries(Object.entries(r).map(([k,v])=>[k,k==="h"?v:v/ns])));
  z.rows.push({R,K,T,J,H,nr,ns,selection:ns/nr,L,base:base/ns,branch:branch/ns,label:bin/ns,shell:bc/ns,traffic:alpha/ns,baseTraffic:beta/ns,crossUpper:globalCross/ns,labelUpper:globalLabel/ns,shellUpper:globalShell/ns,bands:bs,tail:bandRows})
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
