// Future-minimum canonical target and last-upcross level audit.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.max(16,Math.floor(B/2)):Math.min(8*B,Math.floor(X/2)),a=Math.max(13,Math.ceil(B/(focus?8:2))),Q=Math.max(5,Math.ceil(B/10)),lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(x,msg)=>{if(!x)throw Error(`${X}/${focus} ${msg}`)},eq=(x,y)=>Math.abs(x-y)<=1e-7*Math.max(1,Math.abs(x),Math.abs(y)),mod=(x,y)=>(x%y+y)%y;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
 function fac(n){let f=[];while(n>1){let p=S[n];if(p>2&&p<=B)f.push(p);while(n%p===0)n/=p}return f}
 let N=0,events=0,targets=0,reached=0,fullRoots=0,completeTargets=0,positiveTargets=0,old=0,hybrid=0,future=0,hybridRem=0,futureRem=0,excess=0,recordSum=0,completeCredit=0,missing=0,recordInc=0,highRecord=0,recordLevels=0,peak=0,tickChecks=0,commonChecks=0,roughChecks=0,groups=new Map(),fullSlots=new Map();
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t0=M+2,t=t0,cut=Math.floor((7*M-1)/4),es=[],can=[{g:0,t}];
  while(C-C0<T){
   let p=0,v=Infinity,ls=fac(C-1),rs=fac(C+1),r=Math.min(...ls,...rs);
   for(let [sg,fs] of [[-1,ls],[1,rs]])for(let q of fs){let j=t+1+mod((sg===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>cut)break;
   let G=C+p-1,w=v-t,dp=2*t-C,dq=2*v-G,k=(dq-6*(v%2))/(2*p),ct=C/2+3;
   ok(w<=2*r&&w<=3*(p-1)&&dp>=0&&dq>=0&&Number.isInteger(k),"event");
   if(C%4===0&&t<=ct&&ct<v&&ct>can.at(-1).t)can.push({g:C-C0,t:ct});
   let high=p>=Q&&r>3&&2*r>p,mark=w<=.2*(p-1)||(high&&k===0&&v-can.at(-1).t>2*p);
   let z=`${C}|${p}|${v}`;fullSlots.set(z,(fullSlots.get(z)||0)+1);
   es.push({C,g:C-C0,G:G-C0,t,v,p,r,w,dp,dq,k,high,mark,z});
   events++;C=G;t=v;if(C%4===0&&2*t-C===6&&t>can.at(-1).t)can.push({g:C-C0,t});
  }
  let hit=C-C0>=T;if(hit)fullRoots++;
  const n=es.length,weights=new Float64Array(n),own=new Float64Array(n),load=new Float64Array(t-t0+1),oldLoad=new Float64Array(t-t0+1);
  let suffix=2*t-C;
  for(let i=n-1;i>=0;i--){let e=es[i];suffix=Math.min(suffix,e.dq);e.m=suffix;e.len=Math.max(0,e.m-Math.max(6,e.dp));suffix=Math.min(suffix,e.dp);ok(eq(e.len,Math.max(0,e.m-6)-Math.max(0,suffix-6)),"record level partition");recordLevels+=e.len;}
  ok(eq(es.reduce((z,e)=>z+e.len,0),Math.max(0,2*t-C-6)),"partition total");
  const add=(arr,l,h,w)=>{arr[l-t0]+=w;arr[h-t0]-=w};
  const gaps=can.filter(c=>c.g<T);let j=0,V=0,U=0,rawH=0,localEx=0,localReachedW=0;
  for(let i=0;i<gaps.length;i++){let c=gaps[i],h=gaps[i+1]?.g??T,L=h-c.g;if(L<a)continue;
   for(let x=c.g+Math.floor(L/2)+1;x<=h;x++){
    while(j<n&&es[j].G<x)j++;
    let e=es[j],R=x-c.g,rr=1/R,W=(e?.v??t)-c.t,Wh=W,Ws=W;
    targets++;V+=W*rr;
    if(e){reached++;let ts=Math.max(e.t,c.t),f=(x-e.g)/(e.G-e.g),dp=2*ts-(C0+e.g),di=(1-f)*dp+f*e.dq,dh=Math.min(di,e.dq),ds=Math.min(di,e.m);
     Wh=(R-6+dh)/2;Ws=(R-6+ds)/2;
     ok(eq(Wh,Math.min(W-(1-f)*(e.v-ts),W-(e.G-x)/2))&&Ws>=0&&Ws<=Wh+1e-9&&2*Ws>=R-6-1e-9,"future correction");
     let ex=Math.max(0,ds-6),prev=Math.max(0,Math.min(e.dp,e.m)-6),part=Math.max(0,ds-Math.max(6,e.dp));
     ok(eq(ex,prev+part)&&part<=e.len+1e-9,"target level identity");
     if(ex>1e-9)positiveTargets++;localEx+=ex*rr;weights[j]+=rr;own[j]+=part*rr;localReachedW+=rr;
     if(i+1<gaps.length||can.some(z=>z.g===T&&h===T)){completeTargets++;ok(ds<=6+1e-9,"completed gap ceiling");completeCredit+=(Wh-Ws)*rr;}
     if(Wh>0){let scale=Ws/Wh;if(2*(e.v-ts)>=e.G-e.g||f===1){add(oldLoad,c.t,ts,rr);add(oldLoad,ts,e.v,rr*f);add(load,c.t,ts,rr*scale);add(load,ts,e.v,rr*f*scale)}else{add(oldLoad,c.t,e.v,rr*Wh/W);add(load,c.t,e.v,rr*Ws/W)}}
    }else{missing+=(x-(C-C0))*rr;add(oldLoad,c.t,t,rr);add(load,c.t,t,rr);}
    rawH+=Wh*rr;U+=Ws*rr;
   }
  }
  let after=0,localRecord=0;
  for(let i=n-1;i>=0;i--){let e=es[i],charge=e.len*after+own[i];after+=weights[i];ok(charge>=-1e-9&&charge<=e.len+1e-7,"bounded level load");localRecord+=charge;
   if(charge>1e-9){recordInc++;if(e.high)highRecord++;ok(e.m>6&&e.dq>6&&e.dq-e.dp>0&&e.r>(e.p-1)/4&&charge<=2*e.w+1e-7,"positive record geometry");roughChecks++;
    let g=groups.get(e.z)||{p:e.p,k:e.k,charge:0,n:0,hit:0,maxTarget:0,maxEnd:0,suffix:[],maxHitEnd:0,C:e.C};
    let seq=es.slice(i+1).map(z=>z.z);for(let l=0;l<Math.min(g.suffix.length,seq.length);l++){ok(g.suffix[l]===seq[l],"common deterministic suffix");commonChecks++}
    if(seq.length>g.suffix.length)g.suffix=seq;g.n++;g.charge+=charge;g.maxEnd=Math.max(g.maxEnd,C);
    if(hit){g.hit++;g.maxTarget=Math.max(g.maxTarget,C0+T);g.maxHitEnd=Math.max(g.maxHitEnd,C);ok(C0+T>e.C,"target ahead of slot")}
    groups.set(e.z,g);
   }
  }
  ok(eq(localRecord,localEx),"record transpose");excess+=localEx;recordSum+=localRecord;
  let l=0,o=0,u0=0,v0=0,ur=0,vr=0;
  for(let e of es)for(let k=e.t;k<e.v;k++){l+=load[k-t0];o+=oldLoad[k-t0];ok(l>=-1e-7&&l<=o+1e-7&&o<=1+1e-7,"dominated tick weights");peak=Math.max(peak,l);u0+=l;v0+=o;if(!e.mark){ur+=l;vr+=o}tickChecks++}
  ok(eq(u0,U)&&eq(v0,rawH)&&ur<=vr+1e-7,"tick transpose");old+=V;hybrid+=rawH;future+=U;hybridRem+=vr;futureRem+=ur;
 }
 let paid=0,heavy=0,thin=0,heavyHit=0,maxForward=0,maxMass=0,partialSlots=0,maxReachedMass=0;
 for(let [z,g] of groups){ok(g.n<=fullSlots.get(z)&&g.charge<=4*g.p*g.n+1e-7,"persistent mass");if(g.n<fullSlots.get(z))partialSlots++;
  let cap=(focus ? .02 : 2)*B/(g.p*(g.k+1));maxMass=Math.max(maxMass,g.n);maxReachedMass=Math.max(maxReachedMass,g.hit);
  if(g.charge/(4*g.p)<=cap){thin++;paid+=g.charge}else{heavy++;if(g.hit){heavyHit++;ok(g.maxHitEnd>=g.maxTarget&&g.maxTarget-g.C>=4*(g.hit-1),"reached root spread");maxForward=Math.max(maxForward,g.maxHitEnd-g.C)}}
 }
 let rd=x=>+x.toFixed(6);
 return {X,focus,B,T,a,N,fullRoots,events,targets,reached,completeTargets,positiveTargets,old:rd(old),hybrid:rd(hybrid),future:rd(future),hybridRem:rd(hybridRem),futureRem:rd(futureRem),excess:rd(excess),recordSum:rd(recordSum),completeCredit:rd(completeCredit),missing:rd(missing),recordInc,highRecord,recordLevels,groups:groups.size,partialSlots,thin,heavy,heavyHit,paid:rd(paid),maxMass,maxReachedMass,maxForward,peak:rd(peak),tickChecks,commonChecks,roughChecks};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536])) console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
