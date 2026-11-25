// Recycled deficit and rough-boundary flux certificate; mixed future witnesses.
// Finite diagnostic parameters, derived from the global deep-record audit.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.max(16,Math.floor(B/2)):Math.min(8*B,Math.floor(X/2)),a=Math.max(13,Math.ceil(B/(focus?8:2))),D0=Math.max(14,Math.ceil(B/8)),Q=Math.max(5,Math.ceil(B/10)),lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(x,msg)=>{if(!x)throw Error(`${X}/${focus} ${msg}`)},eq=(x,y)=>Math.abs(x-y)<=1e-7*Math.max(1,Math.abs(x),Math.abs(y)),mod=(x,y)=>(x%y+y)%y;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
 function fac(n){let f=[];while(n>1){let p=S[n];if(p>2&&p<=B)f.push(p);while(n%p===0)n/=p}return f}
 const z0=focus?Math.max(1,Math.floor(T/2)):B;
 const nodes=new Map(),paths=[],slots=new Map();let N=0,events=0,full=0,virtual=0;
 function node(t,C){let z=t*lim+C,o=nodes.get(z);if(!o){o={t,C,d:2*t-C,next:null};nodes.set(z,o)}return o}
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[],can=[{g:0,t}],prev=node(t,C);
  while(C-C0<T){
   let ls=fac(C-1),rs=fac(C+1),r=Math.min(...ls,...rs),p=0,v=Infinity;
   for(let [sg,fs] of [[-1,ls],[1,rs]])for(let q of fs){let j=t+1+mod((sg===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>cut)break;
   let J=C+p-1,w=v-t,ct=C/2+3,k=(2*v-J-6*(v%2))/(2*p),post=node(v,J);
   ok(w<=2*r&&w<=3*(p-1)&&Number.isInteger(k)&&prev.d>=0&&post.d>=0,"event");
   if(prev.next)ok(prev.next===post,"deterministic recorded edge");else prev.next=post;
   if(C%4===0&&t<=ct&&ct<v&&ct>can.at(-1).t){can.push({g:C-C0,t:ct});if(ct>t)virtual++;}
   let z=`${C}|${p}|${v}`,s=slots.get(z)||{p,k,C,post,n:0,maxReached:0};s.n++;slots.set(z,s);
   es.push({g:C-C0,G:J-C0,p,r,w,t,v,prev,post,s});
   events++;C=J;t=v;prev=post;
   if(C%4===0&&2*t-C===6&&t>can.at(-1).t)can.push({g:C-C0,t});
  }
  let hit=C-C0>=T;if(hit){full++;for(let e of es)e.s.maxReached=Math.max(e.s.maxReached,C0+T);}
  paths.push({C0,es,can,term:prev,hit});
 }
 let sinks=0;for(let v of [...nodes.values()].sort((a,b)=>b.t-a.t)){
  if(v.next){ok(v.next.t>v.t&&v.next.m!==undefined,"topological order");v.m=Math.min(v.d,v.next.m);v.sink=v.next.sink}else{v.m=v.d;v.sink=v;sinks++}
 }
 let extended=0,lowered=0,targets=0,reached=0,strict=0,rawLocal=0,rawGlobal=0,localEx=0,globalEx=0,clippedEx=0,lowEx=0,layerTotal=0,recordTotal=0,lowLayer=0,lowPhaseCharge=0,phaseExcluded=0,recordInc=0,highInc=0,weightChecks=0,fullSuffixChecks=0,complete=0,groups=new Map();
 const P=focus?30:6,kappa=2,alpha=1/8,cstar=4,bc=new Map(),bt=new Map(),dc=new Map(),dt=new Map();
 let baseG=0,baseF=0,baseV=0,basePersist=0,basePlus=0,baseMinus=0,baseShort=0,baseRough=0,baseBad=0,baseAll=0,baseBound=0,baseHitBound=0,baseHitScore=0,late=0,routed=0,sourceN=0,suffixChecks=0,stackChecks=0,gridChecks=0,positiveChecks=0,mixedKeys=0,mixedRough=0,mixedShort=0,mixedBad=0,mixedTickChecks=0,loadK=0,loadT=0,maxZ=0;
 function put(m,k,w){m.set(k,(m.get(k)||0)+w)}
 function rec(es,l,h){
  let min=es[h].post.d,neg=0,pos=0,persist=0,tot=0,out=[];
  for(let j=h;j>=l;j--){let e=es[j],dp=e.prev.d,d=e.post.d,up=Math.max(0,d-dp),down=Math.max(0,dp-d),keep=Math.max(0,min-dp),b=up-keep;
   ok(keep<=up&&b>=0,"recycled level");out.push(b);pos+=up;neg+=down;persist+=keep;tot+=b;min=Math.min(min,dp);
  }
  ok(persist===es[h].post.d-min&&tot===neg-(es[l].prev.d-min)&&tot===pos-persist,"recycling identity");
  // Independent LIFO deficit stack, initial stock represented by one segment.
  let st=es[l].prev.d?[[-1,es[l].prev.d]]:[],lost=new Map(),initial=0;
  for(let j=l;j<=h;j++){let e=es[j],d=e.post.d-e.prev.d;if(d>0)st.push([j,d]);else if(d<0){let left=-d;while(left){ok(st.length>0,"stack underflow");let q=st[st.length-1],v=Math.min(left,q[1]);q[1]-=v;left-=v;if(q[0]<0)initial+=v;else put(lost,q[0],v);if(!q[1])st.pop()}}}
  out.reverse();ok(initial===es[l].prev.d-min,"initial stock");for(let j=l;j<=h;j++){ok(out[j-l]===(lost.get(j)||0),"independent recycled stack");stackChecks++}
  return {out,tot,pos,neg,persist,min};
 }
 function witnesses(es,l,h,limit,grid,ticks,charge,z,localK,localT){
  const re=rec(es,l,h),start=es[l].prev.C,finish=es[h].post.C;
  let F=0,all=0,short=0,rough=0,bad=0,keys=[],ts=[];
  for(let j=l;j<=h;j++){let e=es[j],A=e.prev.C,J=e.post.C,g=J-A,n=0;
   for(let K=P*Math.ceil(A/P);K<J&&K<limit;K+=P){ok(K>=start&&P%e.p!==0,"strict boundary");n++;all++;gridChecks++;
    if(e.p<kappa*P){short++;keys.push("s|"+K+"|"+A+"|"+e.p);}
    else if(e.r>=alpha*g){rough++;keys.push("r|"+K+"|"+A+"|"+e.p);}
    else bad++;
   }
   if(e.p>=kappa*P&&e.r<alpha*g)ok(P*n<=cstar*Math.max(0,e.prev.d-e.post.d)+1e-9,"cheap crossing deficit");
   let b=re.out[j-l];if(b){ok(e.r>g/4&&b<=2*e.w,"positive drift support");positiveChecks++;
    let w=cstar*b/e.w;for(let t=e.t;t<e.v;t++)ts.push([A+"|"+t+"|"+e.p,w]);
   }
  }
  F=P*keys.length;let score=F+cstar*re.tot;
  ok(P*all>=limit-start-P&&score>=limit-start-P-cstar*(es[l].prev.d-re.min)-1e-8,"flux lower bound");
  if(charge===null){for(let k of keys)put(grid,k,P);for(let [k,w] of ts)put(ticks,k,w);}
  else{
   ok(score>0,"nonzero mixed denominator");for(let k of keys)put(localK,k,charge*P/score);for(let [k,w] of ts)put(localT,k,charge*w/score);
   mixedKeys+=keys.length;mixedShort+=short;mixedRough+=rough;mixedBad+=bad;mixedTickChecks+=ts.length;
  }
  return {F,V:re.tot,score,short,rough,bad,all,pos:re.pos,neg:re.neg,persist:re.persist,min:re.min,finish};
 }
 for(let {C0,es,can,term,hit} of paths){
  let localK=new Map(),localT=new Map();
  if(es.length){let w=witnesses(es,0,es.length-1,term.C,bc,bt,null,0,null,null),G=term.C-C0;
   baseG+=G;baseF+=w.F;baseV+=w.V;basePlus+=w.pos;baseMinus+=w.neg;basePersist+=w.persist;baseShort+=w.short;baseRough+=w.rough;baseBad+=w.bad;baseAll+=w.all;baseBound+=G-P-cstar*6;
   if(hit){baseHitBound+=T-P-cstar*6;baseHitScore+=w.score;ok(w.score>=T-P-cstar*6,"reached baseline");}
  }
  if(term.next)extended++;if(term.m<term.d)lowered++;
  let n=es.length,local=term.d,weights=new Float64Array(n),own=new Float64Array(n),ownLow=new Float64Array(n);
  for(let i=n-1;i>=0;i--){let e=es[i];local=Math.min(local,e.post.d);e.local=local;local=Math.min(local,e.prev.d);
   let m=e.post.m,b=e.prev.d;e.len=Math.max(0,m-Math.max(6,b));e.clip=Math.max(0,m-Math.max(D0,b));
   ok(eq(e.len,Math.max(0,m-6)-Math.max(0,e.prev.m-6))&&e.clip<=e.len,"global layer");
  }
  let all=es.reduce((s,e)=>s+e.len,0),cl=es.reduce((s,e)=>s+e.clip,0);ok(eq(all,Math.max(0,term.m-6))&&all-cl<=D0-6+1e-9,"level partition");layerTotal+=all;lowLayer+=all-cl;
  const gaps=can.filter(c=>c.g<T);let j=0,ex=0,cx=0;
  for(let i=0;i<gaps.length;i++){let c=gaps[i],L=(gaps[i+1]?.g??T)-c.g;if(L<a)continue;
   for(let x=c.g+Math.floor(L/2)+1;x<=c.g+L;x++){
    while(j<n&&es[j].G<x)j++;let e=es[j],R=x-c.g,rr=1/R,W=(e?.v??term.t)-c.t;targets++;
    if(!e){rawLocal+=W*rr;rawGlobal+=W*rr;continue;}
    reached++;let ts=Math.max(c.t,e.t),dp=2*ts-(C0+e.g),f=(x-e.g)/(e.G-e.g),di=(1-f)*dp+f*e.post.d;
    let dl=Math.min(e.local,di),dg=Math.min(e.post.m,di),wl=(R-6+dl)/2,wg=(R-6+dg)/2;
    ok(wg>=0&&wg<=wl+1e-9&&2*wg>=R-6-1e-9&&di<=6+5*R+1e-9,"target envelope");
    if(wg<wl-1e-9)strict++;
    if(i+1<gaps.length){complete++;ok(dg<=6,"complete gap");}
    rawLocal+=wl*rr;rawGlobal+=wg*rr;localEx+=Math.max(0,dl-6)*rr;ex+=Math.max(0,dg-6)*rr;cx+=Math.max(0,dg-D0)*rr;
    weights[j]+=rr;own[j]+=Math.max(0,dg-Math.max(D0,e.prev.d))*rr;ownLow[j]+=Math.max(0,dg-Math.max(6,e.prev.d))*rr;
   }
  }
  let later=0,cr=0,ur=0,lp=0;
  for(let i=n-1;i>=0;i--){let e=es[i],c=e.clip*later+own[i],u=e.len*later+ownLow[i];later+=weights[i];
   ok(c<=u+1e-8&&u<=e.len+1e-7&&c<=e.clip+1e-7,"charge bound");cr+=c;ur+=u;
   if(e.post.d<=D0){ok(c<=1e-8,"low phase erased");lp+=u;phaseExcluded++;}
   if(c>1e-9){recordInc++;if(e.p>=Q)highInc++;
    let y=C0+T-(C0+e.g),b=Math.max(D0,e.prev.d),bound=e.clip*Math.min(1,5*y/(b-6));
    ok(c<=bound+1e-7&&e.post.m>D0&&e.r>(e.p-1)/4&&e.s.post.sink.C>=term.C,"weighted endpoint and global persistence");weightChecks++;
    if(hit){ok(e.s.post.sink.C>=C0+T,"reached continuation");fullSuffixChecks++;}
    let g=groups.get(e.s)||{charge:0,near:0,nearBound:0,n:0,farReached:0};g.charge+=c;g.n++;
    if(y<=z0){g.near+=c;g.nearBound+=bound;}else if(hit)g.farReached++;
    groups.set(e.s,g);
    let slack=e.post.d-e.post.m,z=Math.max(2*P,Math.floor(e.post.d/4),4*slack);maxZ=Math.max(maxZ,z);
    if(term.C-e.post.C<z){late+=c;}
    else{
     let h=i+1;while(h<n&&es[h].post.C<e.post.C+z)h++;
     ok(h<n&&h>i,"suffix existence");
     // In small finite cases the asymptotic z >> P+B need not hold.
     // Use actual lower bound to ensure a nonzero mixed denominator.
     let end=e.post.C+z,scoreBound=z-P-cstar*slack;
     if(scoreBound<=0){late+=c;}
     else{let w=witnesses(es,i+1,h,end,dc,dt,c,z,localK,localT);
      ok(w.min>=e.post.m&&w.score>=scoreBound,"persistent mixed flux");suffixChecks++;routed+=c;sourceN++;}
    }
   }
  }
  ok(eq(cr,cx)&&eq(ur,ex)&&ur-cr<=D0-6+1e-7&&lp<=D0-6+1e-7,"level charge transpose");
  for(let [k,w] of localK){put(dc,k,w);loadK=Math.max(loadK,w/P);}
  for(let [k,w] of localT){put(dt,k,w);loadT=Math.max(loadT,w);}
  globalEx+=ex;clippedEx+=cx;lowEx+=ur-cr;recordTotal+=cr;lowPhaseCharge+=lp;
 }
 let heavy=0,thin=0,heavyFar=0,heavyFullReach=0,nearPaid=0,maxForward=0;
 for(let [s,g] of groups){ok(g.n<=s.n&&g.near<=g.nearBound+1e-7&&g.charge<=4*s.p*g.n+1e-7,"slot accounting");nearPaid+=g.near;
  let cap=(focus?.02:1)*B/Math.max(1,s.post.d);
  if(g.charge<=4*s.p*cap)thin++;else{heavy++;if(s.maxReached){heavyFullReach++;ok(s.post.sink.C>=s.maxReached,"full slot future");maxForward=Math.max(maxForward,s.post.sink.C-s.C);}
    if(g.farReached){heavyFar++;ok(s.post.sink.C>s.C+z0,"far common suffix");}
  }
 }
 ok(eq(clippedEx,recordTotal)&&globalEx<=localEx+1e-7&&lowEx<=N*(D0-6)+1e-7,"total");
 const sum=m=>[...m.values()].reduce((a,b)=>a+b,0);
 const pay=(m,c)=>[...m.values()].filter(x=>x<=c).reduce((a,b)=>a+b,0);
 let baseScore=baseF+cstar*baseV,basePaid=pay(bc,P*2)+pay(bt,8),deepPaid=pay(dc,P)+pay(dt,1),deepRemain=routed-deepPaid;
 ok(eq(baseF,sum(bc))&&eq(cstar*baseV,sum(bt))&&baseScore>=baseBound&&baseHitScore>=baseHitBound&&eq(basePlus-basePersist,baseV),"baseline ledger");
 ok(eq(late+routed,clippedEx)&&eq(sum(dc)+sum(dt),routed)&&deepRemain>=-1e-7,"mixed ledger");
 const rd=x=>+x.toFixed(6);
 return {X,focus,B,T,a,D0,z0,N,P,kappa,alpha,cstar,baseG,baseF,baseV,basePlus,baseMinus,basePersist,baseShort,baseRough,baseBad,baseAll,baseScore,basePaid:rd(basePaid),baseRem:rd(baseScore-basePaid),baseHitBound,baseHitScore,late:rd(late),routed:rd(routed),sourceN,suffixChecks,stackChecks,gridChecks,positiveChecks,mixedKeys,mixedRough,mixedShort,mixedBad,mixedTickChecks,loadK:rd(loadK),loadT:rd(loadT),maxZ,deepBoundary:rd(sum(dc)),deepRecycle:rd(sum(dt)),deepPaid:rd(deepPaid),deepRemain:rd(deepRemain),baseBoundaryKeys:bc.size,baseTickKeys:bt.size,deepBoundaryKeys:dc.size,deepTickKeys:dt.size,events,full,nodes:nodes.size,sinks,virtual,extended,lowered,targets,reached,complete,strict,rawLocal:rd(rawLocal),rawGlobal:rd(rawGlobal),localEx:rd(localEx),globalEx:rd(globalEx),clippedEx:rd(clippedEx),lowEx:rd(lowEx),lowPhaseCharge:rd(lowPhaseCharge),phaseExcluded,layerTotal,lowLayer,recordTotal:rd(recordTotal),recordInc,highInc,weightChecks,fullSuffixChecks,groups:groups.size,thin,heavy,heavyFar,heavyFullReach,nearPaid:rd(nearPaid),maxForward};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
