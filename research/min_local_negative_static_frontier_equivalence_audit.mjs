// Static clock spectrum, low-gain endpoint equivalence and dynamic-only frontier.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=1200000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)spf[n]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function ev(a,v){let p=Infinity,w=Infinity,e=0,q=Infinity;for(let [d,s] of [[a+1,-1],[a-1,1]])for(let r of fs(d)){q=Math.min(q,r);let t=mod((s===-1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e,q}}
 function clockHeight(a,p,e){let x=a/2,short=mod(x,2)===mod((p-1)/2,2);return ((short?1:3)*p+(e===-1?-1:5))/2}
 function staticFirst(a,h=3){let b=Infinity;for(let [d,e] of [[a+1,-1],[a-1,1]])for(let p of fs(d)){let t=clockHeight(a,p,e);while(t<=h)t+=2*p;b=Math.min(b,t)}return b}
 let z={roots:0,events:0,clockChecks:0,staticChecks:0,passages:0,cutoffs:0,smallGainChecks:0,extraChecks:0,missedClockChecks:0,roughSandwichChecks:0,twinChecks:0,shortMisses:0,longMisses:0,singleMissChecks:0,reducedHeightWitnesses:0,rows:[]};
 for(let R of [12000,48000,192000,480000]){
  let S=Math.sqrt(2*R+1),hs=[64,128,256,Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R)))*4,Math.ceil(1.5*S+3),Math.ceil(2*S),Math.ceil(4*S)].sort((a,b)=>a-b);
  let lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6);
  for(let H of [...new Set(hs)]){
   let L=Math.floor(H/4),Ls=Math.max(0,Math.floor((4/35)*(H-72))),map=new Map(),mapS=new Map(),row={R,H,L,Ls,static:0,roughLow:0,roughHigh:0,twin:0,pass:0,small:0,dynamicExtra:0,belowBarrier:0,belowBarrierExtra:0,phase6Extra:0,minExtraRatio:null,extraExamples:[]};
   for(let a=lo-6*Math.ceil(L/6);a<=hi;a+=6){
    let x=ev(a,3-a/2),b=staticFirst(a);ck(b===x.w+3,{a,b,x});z.staticChecks++;
    for(let [d,e] of [[a+1,-1],[a-1,1]])for(let p of fs(d)){let h=clockHeight(a,p,e),n=h-a/2;ck(h>0&&mod(n-(e===-1?0:p+2),2*p)===0&&h<=2*p+3,{a,p,e,h});z.clockChecks++}
    let inside=a>=lo;
    if(inside){if(b>H)row.static++;if(x.q>Math.sqrt(a+1))row.twin++;if(x.q>2*H+1){ck(b>H,"rough implies static");row.roughHigh++}if(x.q>=(2*H-5)/3)row.roughLow++;if(b>H&&H>20)ck(x.q>(2*H-5)/3,"static rough");z.roughSandwichChecks++}
   }
   for(let A=lo;A<=hi;A+=6)for(let phase of [3,6]){
    let a=A,h=phase,v=h-a/2,G=0,W=0;z.roots++;
    while(true){let x=ev(a,v);if(h+x.w>H){
     let I=H-h;ck(I>0&&I<x.w&&G<=L&&W<=9*G/4+8,"pass");
     ck(h<=14+7*G/4&&I>=H-14-7*G/4,"arrival");
     let b=staticFirst(a),extra=b<=H,inside=a>=lo;
     // roughness makes a divisible by six for H large in these controls.
     ck(a%6===0&&x.q>I/2,"rough endpoint");
     if(phase===3){row.pass++;map.set(a,Math.min(map.get(a)??Infinity,G));if(G<=Ls){row.small++;mapS.set(a,Math.min(mapS.get(a)??Infinity,G));}}
     else if(extra)row.phase6Extra++;
     z.passages++;
     if(extra){
      ck(b<=h,"missed static clock");let q0=Infinity;
      for(let [d,e] of [[a+1,-1],[a-1,1]])for(let q of fs(d))if(clockHeight(a,q,e)===b)q0=q;
      ck(Number.isFinite(q0)&&q0<=2*b+1&&H<h+2*q0&&H<5*h+2,"missed clock bound");z.missedClockChecks++;
      if(h<H/2){ck(b+2*q0>H&&h<b+2*q0,'single missed opportunity');let sh=mod(a/2,2)===mod((q0-1)/2,2);if(sh){ck(q0>(2*H-5)/5-1e-8&&q0<=2*h+1,'short range');z.shortMisses++;}else{ck(q0>(2*H-5)/7-1e-8&&q0<=(2*h+1)/3,'long range');ck(G>(12/49)*H-10-1e-8,'long gain bound');z.longMisses++;}z.singleMissChecks++;}
      ck(G>(4/35)*(H-72)-1e-8,"static barrier");z.extraChecks++;
      if(phase===3){row.minExtraRatio=Math.min(row.minExtraRatio??Infinity,G/H);if(row.extraExamples.length<3)row.extraExamples.push({A,a,G,h,b,q0});}
     }
     if(G<=Ls){ck(!extra,"small budget static");z.smallGainChecks++;if(H>=Math.ceil(1.5*S+3)){ck(x.q>Math.sqrt(a+1),'reduced-height witness');z.reducedHeightWitnesses++;}}
     if(H>=Math.ceil(4*S)&&G<=L){ck(x.q>Math.sqrt(a+1),"twin endpoint");z.twinChecks++;}
     break
    }
    if(G+x.p-1>L){z.cutoffs++;break}
    a-=x.p-1;v+=x.w;G+=x.p-1;W+=x.w;h+=x.w-(x.p-1)/2;z.events++;
    }
   }
   for(let [a,g] of map){if(staticFirst(a)<=H)row.dynamicExtra++;else if(a<lo)row.belowBarrier++;}for(let a of mapS.keys())if(staticFirst(a)<=H)row.belowBarrierExtra++;
   row.D=map.size;row.Dsmall=mapS.size;ck(row.D>=row.static&&row.Dsmall>=row.static&&row.belowBarrierExtra===0,"support inclusion");z.rows.push(row)
  }
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
