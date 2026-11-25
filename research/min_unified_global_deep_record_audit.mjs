// Global recorded future minimum and deep-level weighted endpoint audit.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.max(16,Math.floor(B/2)):Math.min(8*B,Math.floor(X/2)),a=Math.max(13,Math.ceil(B/(focus?8:2))),D0=Math.max(14,Math.ceil(B/8)),Q=Math.max(5,Math.ceil(B/10)),lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(x,msg)=>{if(!x)throw Error(`${X}/${focus} ${msg}`)},eq=(x,y)=>Math.abs(x-y)<=1e-7*Math.max(1,Math.abs(x),Math.abs(y)),mod=(x,y)=>(x%y+y)%y;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
 function fac(n){let f=[];while(n>1){let p=S[n];if(p>2&&p<=B)f.push(p);while(n%p===0)n/=p}return f}
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
 for(let {C0,es,can,term,hit} of paths){
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
    if(y<=B){g.near+=c;g.nearBound+=bound;}else if(hit)g.farReached++;
    groups.set(e.s,g);
   }
  }
  ok(eq(cr,cx)&&eq(ur,ex)&&ur-cr<=D0-6+1e-7&&lp<=D0-6+1e-7,"level charge transpose");
  globalEx+=ex;clippedEx+=cx;lowEx+=ur-cr;recordTotal+=cr;lowPhaseCharge+=lp;
 }
 let heavy=0,thin=0,heavyFar=0,heavyFullReach=0,nearPaid=0,maxForward=0;
 for(let [s,g] of groups){ok(g.n<=s.n&&g.near<=g.nearBound+1e-7&&g.charge<=4*s.p*g.n+1e-7,"slot accounting");nearPaid+=g.near;
  let cap=(focus?.02:1)*B/Math.max(1,s.post.d);
  if(g.charge<=4*s.p*cap)thin++;else{heavy++;if(s.maxReached){heavyFullReach++;ok(s.post.sink.C>=s.maxReached,"full slot future");maxForward=Math.max(maxForward,s.post.sink.C-s.C);}
    if(g.farReached){heavyFar++;ok(s.post.sink.C>s.C+B,"far common suffix");}
  }
 }
 ok(eq(clippedEx,recordTotal)&&globalEx<=localEx+1e-7&&lowEx<=N*(D0-6)+1e-7,"total");
 const rd=x=>+x.toFixed(6);
 return {X,focus,B,T,a,D0,N,events,full,nodes:nodes.size,sinks,virtual,extended,lowered,targets,reached,complete,strict,rawLocal:rd(rawLocal),rawGlobal:rd(rawGlobal),localEx:rd(localEx),globalEx:rd(globalEx),clippedEx:rd(clippedEx),lowEx:rd(lowEx),lowPhaseCharge:rd(lowPhaseCharge),phaseExcluded,layerTotal,lowLayer,recordTotal:rd(recordTotal),recordInc,highInc,weightChecks,fullSuffixChecks,groups:groups.size,thin,heavy,heavyFar,heavyFullReach,nearPaid:rd(nearPaid),maxForward};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
