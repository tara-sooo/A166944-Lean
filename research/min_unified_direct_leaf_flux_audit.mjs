// Direct leaf Hall allocation, source-cell transport and boundary-only certificate.
// Independent finite diagnostic parameters inherited from 09ade6b.
function audit(X,focus=false){
const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),P=focus?30:6,kap=2,alpha=1/8,cstar=4,D=Math.max(4,Math.floor(B/8)),K=2*cstar*(1+B/D),eps=.25,lim=7*X+B+20,S=new Int32Array(lim);
const ok=(x,s)=>{if(!x)throw Error(X+" "+s)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
let N=0,events=0,hit=0,grid=0,F=0,target=0,initial=0,pairs=0,laminar=0,localChecks=0,slackChecks=0,eligible=0,demand=0,routed=0,routeEdges=0,peak=0,basePaid=0,extra=0,selected=0,propChecks=0,maxDepth=0,rawLong=0,eligibleTags=0,localInitial=0;
let paths=[],sink=new Map(),bound=new Map();
let leafDemand=0,leafRouted=0,leafEligible=0,leafSkipped=0,leafEdges=0,leafPeak=0,leafChecks=0,sourceCell=0,sourceCellPaid=0,sourceCellKeys=0,sourceCellChecks=0,firstBadSame=0,firstBadEarlier=0,disparatePaid=0,sourceCellException=0,cellPeak=0,gammaMax=0,globalGain=0,tagCapacityChecks=0,fullBound=0,fullF=0,fullGain=0,globalFBound=0;
const KLeaf=8*(5/6)*cstar*(1+2*B/D);
function add(m,key,w){m.set(key,(m.get(key)||0)+w)}
for(let M=X;M<2*X;M++)if(S[M]===M){
 N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[],ms=[],st=[[-1,6]];
 while(C-C0<T){
  let p=0,v=Infinity,r=Infinity;
  for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
  if(!p||v>cut)break;
  let J=C+p-1,w=v-t,dp=2*t-C,d=2*v-J,delta=d-dp,n=Math.ceil(J/P)-Math.ceil(C/P),cost=P*n,bad=p>=kap*P&&r<alpha*(p-1),i=es.length;
  ok(w<=2*r&&w<=3*(p-1)&&dp>=0&&d>=0&&(!n||P%p!==0),"clock/grid");
  if(bad)ok(delta<0&&cost<=cstar*(-delta),"bad");
  let e={i,C,J,t,v,p,dp,d,delta,cost,bad,key:C+"|"+p,F:bad?0:cost};es.push(e);events++;grid+=cost;F+=e.F;
  if(e.F)add(bound,e.key,e.F);
  if(delta>0)st.push([i,delta]);
  if(delta<0){let l=-delta,hi=dp,gamma=bad?cost/l:0;
   while(l){let a=st.at(-1),n=Math.min(l,a[1]),lo=hi-n;l-=n;a[1]-=n;if(!a[1])st.pop();
    if(a[0]<0)initial+=gamma*n;else if(gamma){let x={i:a[0],j:i,hi,lo,c:gamma*n,key:e.key};ms.push(x);target+=x.c;add(sink,e.key,x.c);pairs++}
    hi=lo;
   }ok(hi===d,"stack");
  }
  C=J;t=v;
 }
 if(C-C0>=T)hit++;
 paths.push({es,ms});
}
let sinkThin=new Set(),boundThin=new Set(),sinkPaid=0,boundPaid=0;
for(let [k,v] of sink){let q=+k.split("|")[1];if(v<=cstar*q*(focus?.12:2)*B/q){sinkThin.add(k);sinkPaid+=v}}
for(let [k,v] of bound){if(v<=P*(focus?1:2)){boundThin.add(k);boundPaid+=v}}
basePaid=sinkPaid+boundPaid;
for(let {es,ms} of paths){
 let dest=[];for(let e of es)if(e.F)dest.push({i:e.i,j:e.i,w:e.F,paid:boundThin.has(e.key),left:K*e.F});
 for(let m of ms){dest.push({i:m.i,j:m.j,w:m.c,paid:sinkThin.has(m.key),left:K*m.c});m.e=es[m.j].C-es[m.i].J;}
 for(let a of ms)for(let b of ms){ok(!(a.i<b.i&&b.i<a.j&&a.j<b.j),"laminar");laminar++}
 const leaves=dest.filter(x=>x.i===x.j||es[x.j].C-es[x.i].J<D).map(x=>({...x,left:KLeaf*x.w}));
 const totalGain=es.reduce((z,e)=>z+e.p-1,0),tg=ms.reduce((z,m)=>z+m.c,0),tf=es.reduce((z,e)=>z+e.F,0),gg=es.reduce((z,e)=>z+e.cost,0),ig=gg-tf-tg;
 let gm=0;for(let e of es)if(e.bad)gm=Math.max(gm,e.cost/(-e.delta));
 gammaMax=Math.max(gammaMax,gm);globalGain+=totalGain;
 const ps=new Map(),ss=new Map();
 for(let m of ms){add(ps,m.i,m.c);add(ss,m.j,m.c)}
 for(let [i,c] of ps)ok(c<=5*gm*(es[i].p-1)+1e-7&&es[i].delta>0,"source gain capacity");
 for(let [j,c] of ss)ok(c<=gm*(es[j].p-1)+1e-7&&es[j].delta<0&&!ps.has(j),"sink gain capacity");
 ok(tg<=5*gm*totalGain/6+1e-7&&tf+1e-7>=(1-5*gm/6)*totalGain-P-6*gm&&ig>=-1e-7&&ig<=6*gm+1e-7,"boundary-only inequality");
 globalFBound+=(1-5*gm/6)*totalGain-P-6*gm;tagCapacityChecks++;
 if(totalGain>=T){fullGain+=totalGain;fullF+=tf;fullBound+=(1-5*gm/6)*totalGain-P-6*gm}
 let cell=new Map(),next=new Int32Array(es.length);let k=-1;
 for(let i=es.length-1;i>=0;i--){if(es[i].cost)k=i;next[i]=k;}
 for(let m of ms){
  let a=es[m.i],b=es[m.j],h=next[m.i];ok(h>=m.i&&h<=m.j,"next crossing exists");let f=es[h];
  if(f.bad){ok(!a.cost&&f.C-a.C<=P,"bad first crossing geometry");
   if(h===m.j){ok(m.e<=P,"first bad consumption short");firstBadSame+=m.c;
    if(b.p>=3*a.p&&m.e<=b.p/3)disparatePaid+=m.c;else sourceCellException+=m.c;
   }else{ok(-f.delta<=5*P,"bad first crossing survival forces small drop");firstBadEarlier+=m.c;sourceCellException+=m.c;}
   continue;
  }
  ok(f.F>0&&f.C>=a.C&&h<m.j,"admissible source cell crossing");sourceCell+=m.c;
  let o=cell.get(h)||{w:0,by:new Map()};o.w+=m.c;add(o.by,m.i,m.c);cell.set(h,o);
  if(boundThin.has(f.key))sourceCellPaid+=m.c;
 }
 for(let [h,o] of cell){let f=es[h],n=f.F/P,first=P*Math.ceil(f.C/P),off=first-f.C,l=0,own=0;
  for(let [i,c] of o.by){let a=es[i];if(i===h){own=c;ok(c<=gm*(3*(a.p-1)+4)+1e-7,"crossing source drift");}else{ok(a.C>=first-P&&a.J<=f.C&&!a.cost,"cell prior source geometry");l+=a.p-1;}}
  ok(l<=P-off&&l+f.p-1<=(n+1)*P&&o.w<=5*gm*l+own+1e-7&&o.w<=gm*((3*n+5)*P+4)+1e-7,"source cell capacity");sourceCellChecks++;cellPeak=Math.max(cellPeak,o.w/f.F);sourceCellKeys++;
 }
 let leafSrc=[];
 for(let m of ms)if(m.e>=D){
  let W=leaves.filter(x=>m.i<x.i&&x.j<m.j),v=W.reduce((z,x)=>z+x.w,0);
  let inner=ms.filter(x=>m.i<x.i&&x.j<m.j&&x.e>=D).reduce((z,x)=>z+x.c,0);
  let nested=ms.filter(x=>m.i<=x.i&&x.j<=m.j&&x.e>=D).reduce((z,x)=>z+x.c,0);
  ok(inner<=5*gm*m.e/6+1e-7&&nested<=5*gm*(m.e+2*B)/6+1e-7,"disjoint two-endpoint packing");leafChecks++;
  if(v<m.e/8){leafSkipped+=m.c;continue}
  leafSrc.push({m,W});leafEligible++;leafDemand+=m.c;
 }
 leafSrc.sort((a,b)=>a.m.e-b.m.e);
 for(let {m,W} of leafSrc){let left=m.c;for(let x of W){let z=Math.min(left,x.left);if(z>1e-10){x.left-=z;left-=z;leafRouted+=z;leafEdges++;leafPeak=Math.max(leafPeak,(KLeaf*x.w-x.left)/x.w)}if(left<=1e-8)break}ok(left<=1e-7,"direct leaf Hall allocation");}
 let src=[],marked=[];
 for(let m of ms){let a=es[m.i],b=es[m.j],e=m.e;
  if(e<D)continue;rawLong+=m.c;
  let W=dest.filter(x=>m.i<x.i&&x.j<m.j),score=W.reduce((z,x)=>z+x.w,0),pw=W.filter(x=>x.paid).reduce((z,x)=>z+x.w,0);
  let min=a.d,localBad=0,localF=0,inner=0,ini=0,st=[[ -1,a.d]];
  for(let k=m.i+1;k<m.j;k++){
   let f=es[k];min=Math.min(min,f.d);localF+=f.F;
   if(f.delta>0)st.push([k,f.delta]);else if(f.delta<0){let l=-f.delta,g=f.bad?f.cost/l:0;localBad+=f.bad?f.cost:0;
    while(l){let x=st.at(-1),n=Math.min(l,x[1]);l-=n;x[1]-=n;if(!x[1])st.pop();if(x[0]===-1)ini+=g*n;else inner+=g*n}
   }
  }
  ok(a.d-min<=a.d-m.hi&&a.d-m.hi<=5*B&&ini<=cstar*(a.d-min)+1e-8,"birth slack");slackChecks++;localInitial+=ini;
  ok(eq(inner+localF,score)&&eq(inner+ini,localBad)&&score>=e-P-cstar*(a.d-min)-1e-8,"local exact flux");localChecks++;
  if(score<e/2)continue;
  eligible++;demand+=m.c;src.push({m,W,score});
  if(!sinkThin.has(m.key)&&pw>=eps*e){marked.push(m);extra+=m.c;selected++;}
 }
 if(src.length)eligibleTags++;
 // Innermost-first greedy allocation is valid because witness sets are laminar.
 src.sort((a,b)=>a.m.e-b.m.e);
 for(let {m,W} of src){let l=m.c;for(let x of W){let z=Math.min(l,x.left);if(z>1e-10){x.left-=z;l-=z;routed+=z;routeEdges++;peak=Math.max(peak,(K*x.w-x.left)/x.w)}if(l<=1e-8)break}ok(l<=1e-7,"Hall allocation");}
 // Maximal marked intervals have disjoint interior witness sets.
 let maximal=marked.filter(a=>!marked.some(b=>b!==a&&b.i<=a.i&&b.j>=a.j));
 let used=new Set(),sumE=0,paid=0;
 for(let m of maximal){sumE+=m.e;for(let x of dest)if(m.i<x.i&&x.j<m.j&&x.paid){ok(!used.has(x),"disjoint maximal witnesses");used.add(x);paid+=x.w}}
 let total=marked.reduce((z,m)=>z+m.c,0);
 ok(total<=cstar*(1+B/D)*sumE+1e-7&&eps*sumE<=paid+1e-7,"propagation budget");propChecks+=marked.length;
 for(let m of src)maxDepth=Math.max(maxDepth,src.filter(a=>a.m.i<=m.m.i&&a.m.j>=m.m.j).length);
}
ok(eq(F+target+initial,grid)&&eq(routed,demand)&&extra<=cstar*(1+B/D)*basePaid/eps+1e-7,"global");
ok(eq(leafDemand,leafRouted)&&eq(sourceCell+firstBadSame+firstBadEarlier,target)&&eq(disparatePaid+sourceCellException,firstBadSame+firstBadEarlier)&&sourceCellPaid<=cstar*(8+4/P)*boundPaid+1e-7&&F+1e-7>=globalFBound&&fullF+1e-7>=fullBound,"global direct bounds");
let rd=x=>+x.toFixed(6);return {X,focus,B,T,P,D,K:rd(K),KLeaf:rd(KLeaf),leafDemand:rd(leafDemand),leafRouted:rd(leafRouted),leafEligible,leafSkipped:rd(leafSkipped),leafEdges,leafPeak:rd(leafPeak),leafChecks,sourceCell:rd(sourceCell),sourceCellPaid:rd(sourceCellPaid),sourceCellKeys,sourceCellChecks,firstBadSame:rd(firstBadSame),firstBadEarlier:rd(firstBadEarlier),disparatePaid:rd(disparatePaid),sourceCellException:rd(sourceCellException),cellPeak:rd(cellPeak),gammaMax:rd(gammaMax),globalGain,tagCapacityChecks,fullGain,fullF,fullBound:rd(fullBound),globalFBound:rd(globalFBound),N,hit,events,F,target:rd(target),initial:rd(initial),pairs,laminar,localChecks,slackChecks,localInitial:rd(localInitial),rawLong:rd(rawLong),eligible,eligibleTags,demand:rd(demand),routed:rd(routed),routeEdges,peak:rd(peak),sinkKeys:sink.size,sinkThin:sinkThin.size,sinkPaid:rd(sinkPaid),boundPaid:rd(boundPaid),basePaid:rd(basePaid),extra:rd(extra),selected,propChecks,maxDepth};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
