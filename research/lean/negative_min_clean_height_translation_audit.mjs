// Height translation and trial-basin-preserving repair. Finite checks, not asymptotic sieve validation.
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},mod=(x,m)=>(x%m+m)%m;
 const max=400010,sp=new Int32Array(max),pr=[];
 for(let p=2;p<max;p++)if(!sp[p]){sp[p]=p;pr.push(p);if(p*p<max)for(let j=p*p;j<max;j+=p)if(!sp[j])sp[j]=p}
 function fac(n){n=Math.abs(n);let a=[];while(n>1){let p=sp[n];ok(p>0,"factor range");a.push(p);while(n%p===0)n/=p}return a}
 function win(x,h,z=Infinity){let n=h-x/2+1,s=mod(n,2)?-1:1;for(let p of fac(x+s))if(p<=z&&mod(n,2*p)===(s===1?0:p+2))return p;return 0}
 function hw(x,h,z=Infinity){let n=h-x/2+1,s=mod(n,2)?-1:1;for(let p of fac(2*h+(s===1?3:-3)))if(p<=z&&mod(x+s,p)===0&&mod(n,2*p)===(s===1?0:p+2))return p;return 0}
 let low=[],lowStates=0,shiftPins=0,cleanBlocks=0,cleanStates=0,changedStates=0,goodStarts=0,actualChecks=0;
 for(let D of [1,2,3,5,8,12,20,32]){
  let M=D+3,z=2*M+3,fib=new Map(),maxg=0,maxt=0;
  for(let x=24000;x<=48000;x+=2){let y=x,h=3,t=0;while(h<M){let p=hw(y,h,z);ok(p===win(y,h,z),"height eligibility");if(p)y-=p-1;h+=1-(p?(p-1)/2:0);t++;lowStates++;ok(h>=0&&y>2&&t<100000,"low run")}
   let g=x-y;ok(t===D+g/2,"ledger");maxg=Math.max(maxg,g);maxt=Math.max(maxt,t);fib.set(y,(fib.get(y)||0)+1)}
  low.push({D,z,starts:12001,sinks:fib.size,maxFiber:Math.max(...fib.values()),maxGain:maxg,maxTime:maxt});
 }
 for(let D of [1,2]){
  let M=D+3,z=2*M+3,B=4*pr.filter(p=>p>2&&p<=z).reduce((a,b)=>a*b,1),Z=z+10;
  for(let a=B;a<150000&&2*(a+M)+3<max;a+=B){
   let clean=true;for(let r=0;r<M;r++)for(let s of [-1,1])if(fac(2*(a+r)+3*s).some(p=>p>z&&p<=Z))clean=false;
   if(!clean)continue;cleanBlocks++;
   let out=new Set(),good=new Set(),def=new Set();
   for(let x=48000;x<=50000;x+=2){
    let y=x,h=3,t=0,dirty=false;
    while(h<M){let p=win(y,h,z),q=hw(y,a+h,Z);ok(p===q,"translated low trial");shiftPins++;
     let actual=hw(y,a+h);ok(actual===win(y,a+h),"independent factors");cleanStates++;
     if(actual!==p){ok(actual>Z,"large discrepancy");dirty=true;def.add(y+","+(a+h))}
     if(p)y-=p-1;h+=1-(p?(p-1)/2:0);t++;ok(h>=0&&t<100000,"shifted trial")}
    out.add(y);
    if(!dirty){goodStarts++;let yy=x,hh=a+3;while(hh<a+M){let p=win(yy,hh);if(p)yy-=p-1;hh+=1-(p?(p-1)/2:0);actualChecks++;ok(hh>=a,"true shift floor")}ok(yy===y,"true transfer");good.add(y)}
   }
   ok(good.size>=out.size-def.size,"distinct defect bound");changedStates+=def.size;
  }
 }
 let repairs=[];
 for(let [R,H,z] of [[12000,42,7],[48000,74,11],[192000,129,31]]){
  let lo=R-4*H,hi=2*R,N=(hi-lo)/2+1,W=H+1,n=N*W;
  let T=new Int32Array(n),U=new Int32Array(n),C=new Uint8Array(n),P=new Uint8Array(n);
  const idx=(x,h)=>((x-lo)/2)*W+h;
  function succ(x,h,p){return p?[x-p+1,h+1-(p-1)/2]:[x,h+1]}
  function read(arr,y,k){return y<lo||y>hi||k<0||k>H?0:arr[idx(y,k)]}
  let sameDef=0,allDef=0;
  for(let x=lo;x<=hi;x+=2){let j=idx(x,H);T[j]=U[j]=x;C[j]=P[j]=1;
   for(let h=H-1;h>=0;h--){j=idx(x,h);let p=win(x,h),q=win(x,h,z),[y,k]=succ(x,h,p),[v,l]=succ(x,h,q);
    T[j]=read(T,v,l);U[j]=read(U,y,k);
    if(p!==q){allDef++;if(T[j]&&T[j]===read(T,y,k))sameDef++}
    C[j]=+(p===q&&T[j]>0&&read(C,v,l)>0);
    P[j]=+(T[j]>0&&T[j]===read(T,y,k)&&read(P,y,k)>0);
    ok(!C[j]||P[j],"common implies preserved");ok(!P[j]||T[j]===U[j],"preserved implies same sink");
   }
  }
  let tr=new Set(),common=new Set(),pres=new Set(),rejoin=new Set(),trueS=new Set();
  for(let A=Math.ceil(R/6)*6;A<=hi;A+=6){let j=idx(A,3),s=T[j],u=U[j];if(u&&A-u<=4*H)trueS.add(u);if(!s||A-s>4*H)continue;tr.add(s);if(C[j])common.add(s);if(P[j])pres.add(s);if(U[j]===s)rejoin.add(s)}
  ok(common.size<=pres.size&&pres.size<=rejoin.size&&rejoin.size<=trueS.size,"certificate hierarchy");
  repairs.push({R,H,z,trial:tr.size,common:common.size,preserved:pres.size,rejoined:rejoin.size,true:trueS.size,changedVertices:allDef,sameColorChanged:sameDef});
 }
 return {low,lowStates,shiftPins,cleanBlocks,cleanStates,changedStates,goodStarts,actualChecks,repairs}
}
console.log(JSON.stringify(audit(),null,2));
