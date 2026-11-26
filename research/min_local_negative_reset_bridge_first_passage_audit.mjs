// First-height passage, finite reset bridges, suffix witnesses and slow reset collision factors.
function audit(){
 const ck=(b,m)=>{if(!b)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=2400000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let x=p*p;x<=N+2;x+=p)spf[x]=p;
 function fs(n){n=Math.abs(n);let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function tick(x,h){let n=h-x+1,b=h+1,e=mod(n,2)===0?-1:1,p=fs(e===-1?2*b+1:2*b-5).find(q=>mod(n-(e===-1?0:q+2),2*q)===0)||1;return {x:x-(p-1)/2,h:b-(p-1)/2,p}}
 function bridge(x,h){let xx=x,hh=h,t=0,ps=[];while(!((h===3||h===6)&&mod(x,3)===0)){let a=tick(x,h);x=a.x;h=a.h;t++;ps.push(a.p);ck(t<=11&&h<=6,"bridge");}ck(hh!==0||h===3,"minus bridge");return {x,h,t,g:2*(xx-x),ps}}
 function ev(a,v){let p=Infinity,w=Infinity,e=0,q=Infinity;for(let [d,s] of [[a+1,-1],[a-1,1]])for(let r of fs(d)){q=Math.min(q,r);let t=mod((s===-1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e,q}}
 let z={bridgeResidues:0,bridgeTicks:0,bridgeMaxTime:0,bridgeMaxGain:0,bridgeCases:{},bridgeIndependentChecks:0,roots:0,events:0,passages:0,budgetStops:0,resetChecks:0,resetBridgeChecks:0,suffixChecks:0,finiteWitnessChecks:0,cheapResetChecks:0,slowSourceChecks:0,resetMultiplicityChecks:0,collisionPairs:0,collisionFactorChecks:0,rows:[]};
 for(let h0 of [0,3])for(let x=780;x<1170;x+=2){
  let b=bridge(x,h0);ck(b.g<=22&&b.t<=11&&2*b.x%6===0,"bridge bounds");ck(h0!==0||b.g<=10&&b.t<=8,"minus bounds");ck(b.t===b.h-h0+b.g/2,"bridge invariant");
  let a=2*x,v=h0-x,ret=v+b.t;
  while(true){let y=ev(a,v);if(v+y.w>ret)break;a-=y.p-1;v+=y.w}
  ck(a===2*b.x&&ret+a/2===b.h,"independent bridge");z.bridgeIndependentChecks++;
  z.bridgeResidues++;z.bridgeTicks+=b.t;z.bridgeMaxTime=Math.max(z.bridgeMaxTime,b.t);z.bridgeMaxGain=Math.max(z.bridgeMaxGain,b.g);let k=h0+":"+b.ps.join(",");z.bridgeCases[k]=(z.bridgeCases[k]||0)+1;
 }
 for(let R of [48000,192000,480000,1000000])for(let mode of ["sqrt","near"]){
  let S=Math.sqrt(2*R+1),K=Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),H=mode==="sqrt"?Math.ceil(4*S):4*K,L=2*H,threshold=(2*H+1)/3,resetMap=new Map(),row={R,mode,H,roots:0,passages:0,budgetStops:0,resets:0,distinctResets:0,cheapResets:0,distinctCheapResets:0,meanGOverH:0,meanSuffixOverH:0,fullWitness:0,suffixWitness:0,extraWitness:0,phase6:0,slowCollisions:0};
  let cheapKeys=new Set();
  for(let A=6*Math.ceil(R/6);A<=2*R;A+=6){
   let a=A,v=3-A/2,h=3,lastSeed=A,lastPhase=3,lastTime=v,done=false,resetCount=0;
   while(true){
    ck(a>=A-L-2*H-2&&h>=0&&h<H,"height bounds");
    let x=ev(a,v),gap=H-h;
    if(x.w>gap){let n=v+gap,G=A-a,Gs=lastSeed-a,Ws=v-lastTime,Is=gap,t=n-(3-A/2);
     ck(t===H-3+G/2&&n+a/2===H,"passage invariant");
     ck(Ws<=9*Gs/4+8&&Is>=H-lastPhase-7*Gs/4-8-1e-8,"suffix inequality");
     let twin=x.q>Math.sqrt(a+1);if(!twin)ck(Is<2*S+1e-8,"non-twin wait");
     if(mode==="sqrt"&&Gs<=H/4){ck(twin,"suffix witness");row.suffixWitness++;z.finiteWitnessChecks++;if(G>H/4)row.extraWitness++}
     if(mode==="sqrt"&&G<=H/4){ck(twin,"full witness");row.fullWitness++}
     row.passages++;row.meanGOverH+=G/H;row.meanSuffixOverH+=Gs/H;z.passages++;z.suffixChecks++;done=true;break
    }
    if(A-a+x.p-1>L){row.budgetStops++;z.budgetStops++;break}
    let p=x.p,b=h+x.w,nextA=a-p+1,nextV=v+x.w,hh=b-(p-1)/2;
    ck(b<=H&&p<=2*H+1&&hh<H&&hh>=0,"preheight");
    if(p>threshold){
     ck(hh===(x.e===-1?0:3),"large reset");
     ck(nextA%4===0,"even half");
     let br=bridge(nextA/2,hh),target=2*br.x,pre=lastSeed-a;
     ck(br.g<=22&&br.t<=11&&target===nextA-br.g,"reset bridge");
     let key=a+":"+nextV,old=resetMap.get(key);
     if(old)ck(old.target===target&&old.p===p&&old.e===x.e,"same key");
     else resetMap.set(key,{a,p,e:x.e,b:nextA,target,shift:br.g,phase:br.h,slow:false});
     if(pre<=p/7){ck(x.w>=(p-1)/2-14-7*pre/4-1e-8,"cheap reset wait");z.cheapResetChecks++;row.cheapResets++;
      if(x.w>=p/8){ck(x.q>=p/16,"rough source");resetMap.get(key).slow=true;cheapKeys.add(key);z.slowSourceChecks++}
     }
     // Direct independent simulation of the finite bridge, at actual time.
     let aa=nextA,vv=nextV,ret=nextV+br.t;while(true){let y=ev(aa,vv);if(vv+y.w>ret)break;aa-=y.p-1;vv+=y.w}
     ck(aa===target&&ret+aa/2===br.h,"physical reset bridge");z.resetBridgeChecks++;
     a=target;v=ret;h=br.h;lastSeed=a;lastPhase=h;lastTime=v;row.resets++;z.resetChecks++;resetCount++;if(h===6)row.phase6++;
     // Bridge may move past budget; do not count as a low-budget passage.
     if(A-a>L){row.budgetStops++;z.budgetStops++;break}
    }else{a=nextA;v=nextV;h=hh}
    z.events++;
   }
   row.roots++;z.roots++;
  }
  row.distinctResets=resetMap.size;row.distinctCheapResets=cheapKeys.size;
  if(row.passages){row.meanGOverH/=row.passages;row.meanSuffixOverH/=row.passages}
  let by=new Map(),within=new Map();
  for(let r of resetMap.values()){
   let a=by.get(r.target)||[];a.push(r);by.set(r.target,a);
   if(r.slow){let k=[r.target,r.e,r.shift,r.phase].join(":"),b=within.get(k)||[];b.push(r);within.set(k,b)}
  }
  for(let [target,arr] of by){
   ck(arr.length<=2*2*12*Math.ceil(Math.log(2*R+30)/Math.log(threshold)),"bounded reset multiplicity");z.resetMultiplicityChecks++;
  }
  for(let arr of within.values())for(let i=0;i<arr.length;i++)for(let j=i+1;j<arr.length;j++){
   let u=arr[i],v=arr[j];ck(u.p!==v.p&&u.b===v.b&&u.e===v.e,"same-class reset collision");
   let B=u.e===-1?u.b:u.b-2,d=B/(u.p*v.p);ck(Number.isInteger(d)&&d>0,"product collision");
   ck((u.e===-1?u.a+1:u.a-1)===u.p*(d*v.p+1),"collision linear forms");
   z.collisionPairs++;z.collisionFactorChecks++;row.slowCollisions++;
  }
  z.rows.push(row)
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
