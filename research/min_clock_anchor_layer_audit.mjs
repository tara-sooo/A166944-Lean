// Dyadic tail-layer charge from cross-anchor contacts to internal physical pair energy.
// Run node research/min_clock_anchor_layer_audit.mjs 1024 4096 16384 65536
function audit(X,mode='diagnostic'){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,ell=Math.log(Math.log(B)),S=Math.max(1,Math.log(ell)),U=7*X+2;
 const ok=(b,m)=>{if(!b)throw Error(m);};
 ok(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(U+4);
 for(let p=2;p<spf.length;p++)if(!spf[p]){
  spf[p]=p;if(p*p<spf.length)for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 }
 let L=2,y=2;for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>6*S**.25)break;L*=p;y=p;}
 const T=mode==='degree'?4:mode==='diagnostic'?6:Math.ceil(20*ell),g=Math.max(2,T*L),
  kg=mode==='analytic'?Math.floor(1.5*ell/Math.log(g)):5,
  k=mode==='analytic'?Math.floor(ell/(8*Math.log(g))):3,
  P=mode==='analytic'?Math.ceil(B/Math.log(B)**.125):Math.ceil(B/4),
  tau=mode==='analytic'?Math.log(B)**1.5:12,
  Z=mode==='analytic'?Math.log(B)**1.5:12,
  near=mode==='analytic'?Math.floor(4*Math.log(B)):Math.max(2,Math.floor(B/64));
 const A=mode==='analytic'?Math.floor(Math.log(B)**.125):Math.max(2,Math.floor(P/8)), capDiff=mode==='analytic'?Math.log(B)**3.5:256,capSame=mode==='analytic'?Math.log(B)**2.5:144;
 const lo=X,hi=7*X/2-1,len=hi+1,r=new Int32Array(len),d=new Uint8Array(len),paths=[],horizons=new Map();
 const gBound=(L/2)*Array.from({length:kg+1},(_,i)=>(T*L/2)**i).reduce((s,v)=>s+v,0),
  kBound=(L/2)*Array.from({length:k+1},(_,i)=>(T*L/2)**i).reduce((s,v)=>s+v,0)*Math.floor(2*Math.log(U)/Math.log(P));
 function fac(n,cb){while(n>1){const p=spf[n];if(p>B)break;if(p>2)cb(p);while(n%p===0)n/=p;}}
 for(let j=lo;j<=hi;j++){
  for(const x of [2*j,2*j+2])fac(x,p=>{if(p>y)d[j]++;});
  const q=Math.min(spf[2*j-1],spf[2*j+1]);if(q<=B)r[j]=q;
 }
 function hit(t,C,K){
  let u=K+1,p=0;for(const sign of [-1,1])fac(C+sign,q=>{
   const m=2*q,rs=sign===-1?0:q+2,v=t+1+(rs-(t+1)%m+m)%m;
   if(v<u||(v===u&&v<=K&&q<p)){u=v;p=q;}
  });return [u,p];
 }
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a;};
 const get=C=>{let x=horizons.get(C);if(!x){x={list:[],good:0,recent:0,groups:new Map(),physical:new Map(),regPhysical:new Map()};horizons.set(C,x);}return x;};
 let R=0,RK=0,removed=0,events=0,literal=0,finished=0,keptFinished=0,kept=0,goodVisits=0,recentVisits=0,regVisits=0,highHits=0,rootGoodVisitsMax=0,rootRecentVisitsMax=0,maxDeep=0;
 const fullW=new Float64Array(len),keptW=new Float64Array(len),anchorMap=new Map();
 for(let M=X+1;M<2*X;M+=2){
  const i=(M-X-1)/2,s=M+2,C0=2*M-2,K=Math.floor((7*M-1)/4),path=[];
  let t=s,C=C0,depth=0,inc=0,J=0,uHigh=0,qHigh=0,depHigh=-1,regular=true,lowGain=0,flag=false,cost=0,twin=false,nh=0;
  for(;;){
   const j=C/2;
   ok(C<=2*t&&C>=C0&&C-C0<=2*H+B+6,'prefix invariant');
   if(depth<=kg&&d[j]>T)flag=true;
   const recent=!!qHigh&&depth-depHigh<=k;
   const e={i,M,C,t,inc,depth,good:depth<=kg,recent,recentDepth:recent?depth-depHigh:-1,regular:recent&&regular,J:recent?J:0,q:recent?qHigh:0,anchor:qHigh?uHigh+':'+J+':'+qHigh:'',anchorJ:J,anchorT:uHigh,anchorP:qHigh,anchorDepth:qHigh?depth-depHigh:-1,w:0,cost:0,tail:0,end:0};
   path.push(e);
   if(t>=s+H)break;
   const [u,p]=hit(t,C,K);
   if(X<=1024){let uu=K+1,pp=0;for(let v=t+1;v<=K;v++){
    const z=gcd(v%2?v-2:v,v%2?C+1:C-1);
    if(z>1&&spf[z]<=B){uu=v;pp=spf[z];break;}
   }ok(uu===u&&pp===p,'literal clock');literal++;}
   if(!p){ok(!r[j]&&spf[C-1]===C-1&&spf[C+1]===C+1,'twin');finished++;twin=true;break;}
   const q=r[j],dur=Math.max(0,Math.min(u-s,H)-Math.max(t-s,a));
   ok(q>0&&q<=p&&u-t<=2*q,'wait bound');
   e.w=dur/(2*q);e.cost=dur/2;cost+=e.cost;R+=e.cost;fullW[j]+=e.w;
   t=u;C+=p-1;inc=p;events++;
   if(p>y){depth++;lowGain=0;ok(C%p===0||(C+2)%p===0,'post divisor');
    if(p>=P){qHigh=p;J=C;uHigh=t;depHigh=depth;regular=true;nh++;}
    else if(d[C/2]>T)regular=false;
   }else{lowGain+=p-1;ok(lowGain<L,'LOW barrier');}
  }
  ok(cost<=B&&nh*(P-1)<=2*H+B+6,'root budgets');
  maxDeep=Math.max(maxDeep,depth);
  if(flag){removed++;continue;}
  kept++;if(twin)keptFinished++;RK+=cost;highHits+=nh;
  let tail=0,gv=0,rv=0;
  for(let z=path.length-1;z>=0;z--){let e=path[z];tail+=e.cost;e.tail=tail;e.end=C;}
  for(const e of path){
   const x=get(e.C);x.list.push(e);
   if(e.good){gv++;goodVisits++;x.good++;}
   if(e.recent){rv++;recentVisits++;x.recent++;
    ok(e.J<=e.C&&e.q>=P&&(e.J%e.q===0||(e.J+2)%e.q===0),'recent key');
    if(e.regular){regVisits++;const key=e.J+':'+e.q;x.groups.set(key,(x.groups.get(key)||0)+1);x.regPhysical.set(e.anchor,(x.regPhysical.get(e.anchor)||0)+1);}
   }
   if(e.anchor){
    if(!anchorMap.has(e.anchor))anchorMap.set(e.anchor,{t:e.anchorT,J:e.anchorJ,p:e.anchorP,n:0,tags:[]});
    const an=anchorMap.get(e.anchor);if(e.C===e.anchorJ){an.n++;an.tags.push({M:e.M,tail:e.tail});}
    const group=x.physical.get(e.anchor)||{n:0,R:0,t:e.t,tails:[]};ok(group.t===e.t,'physical anchor deterministic replay');group.n++;group.R+=e.tail;group.tails.push(e.tail);x.physical.set(e.anchor,group);
    const p=e.anchorP,t=e.anchorT,J=e.anchorJ;ok(t%2===0?t%(2*p)===0&&J%p===0:(t-(p+2))%(2*p)===0&&(J+2)%p===0,'anchor clock residues');
    ok(2*t-J>=0&&2*t-J<=2*(H+2*B)+6,'anchor deficit strip');ok(e.t-t<=3*(e.C-J),'suffix elapsed');
   }
   keptW[e.C/2]+=e.w;
  }
  ok(gv<=(kg+1)*L/2&&rv<=nh*(k+1)*L/2,'visit caps');
  rootGoodVisitsMax=Math.max(rootGoodVisitsMax,gv);rootRecentVisitsMax=Math.max(rootRecentVisitsMax,rv);
  paths.push(path);
 }
 ok(R-RK<=B*removed,'root deletion budget');
 let maxGood=0,maxGroups=0,maxGroupMass=0,maxMass=0,S0=0,E=0,EK=0,diag=0;
 for(let j=lo;j<=hi;j++){S0+=r[j];E+=r[j]*fullW[j]**2;EK+=r[j]*keptW[j]**2;}
 for(const x of horizons.values()){
  maxGood=Math.max(maxGood,x.good);maxGroups=Math.max(maxGroups,x.groups.size);maxMass=Math.max(maxMass,x.list.length);
  for(const m of x.groups.values())maxGroupMass=Math.max(maxGroupMass,m);
  ok(x.good<=gBound&&x.groups.size<=kBound,'reverse leaf/key caps');
 }


 const thin=mode==='analytic'?Math.log(B)**1.5:4, Kimb=mode==='analytic'?Math.log(B):2,
   z=mode==='analytic'?Math.log(B)**(-.125):1/16,
   levels=1+Math.ceil(Math.log2(2*B)), xs=Array.from({length:levels},(_,i)=>2**(-i)),
   h=Math.floor((2*H+B+6)/(P-1)), Amax=2*(H+2*B)+6;
 const prof=ts=>xs.map(x=>ts.reduce((n,t)=>n+(t>=x*B-1e-9),0));
 const aa=[...anchorMap.values()];for(const v of aa){v.degree=0;v.prof=prof(v.tags.map(t=>t.tail));}
 let D=0,edges=0,actualHits=0;
 for(let i=0;i<aa.length;i++){
  actualHits+=aa[i].n;
  for(let j=0;j<i;j++)if(Math.abs(aa[i].J-aa[j].J)<=A||Math.abs(aa[i].t-aa[j].t)<=A){aa[i].degree++;aa[j].degree++;edges++;}
 }
 for(const v of aa)D=Math.max(D,v.degree);
 const Dbound=4*(2*A+1)*Math.ceil(Math.log(U)/Math.log(P))*(Math.floor(Amax/(2*P))+2);
 ok(D<=Dbound&&actualHits===highHits&&highHits<=h*kept,'anchor degree and total incidences');
 // Internal pair lower bounds computed independently at each threshold by source cells.
 const internal=xs.map((x,j)=>{
  let n2=0,cell2=0,pairs=0,mass=0,maxCells=0,weightedCells=0;
  for(const v of aa){
   const m=new Map();for(const t of v.tags)if(t.tail>=x*B-1e-9){
    const c=Math.floor((t.M-X)/(x*B));m.set(c,(m.get(c)||0)+1);
   }
   let n=0,sq=0;for(const k of m.values()){n+=k;sq+=k*k;}
   ok(n===v.prof[j],'anchor profile count');
   ok(m.size<=10/x+1e-8,'cell count');
   ok(n*n<=m.size*sq,'cell Cauchy');
   n2+=n*n;cell2+=sq;mass+=n;pairs+=(sq-n)/2;maxCells=Math.max(maxCells,m.size);weightedCells+=m.size*sq;
  }
  ok(mass<=highHits&&n2<=weightedCells+1e-8,'internal squared counts');
  return {x,n2,cell2,pairs,mass,maxCells,weightedCells};
 });
 for(const v of internal)ok(v.pairs*v.x*v.x*B/48<=h*EK+1e-6*Math.max(1,EK),'internal energy lower bound aggregate');
 const names=['prior','thinLayer','imbalance','rest'],counts=Array(4).fill(0),energy=counts.slice();
 const allCounts=[0,0,0,0],allEnergy=[0,0,0,0],per=xs.map(x=>({x,thinPairs:0,imbPairs:0,thinEnergy:0,imbEnergy:0,thinBudget:0,imbBudget:0}));
 let pairs=0,contacts=0,bothThick=0,bothThickImb=0,oldCapExtra=0,closeEnergy=0,zeroTail=0,priorEnergy=0,priorResidual=0,layerThinExtra=0,layerImbExtra=0;
 const anchorContact=new Map();
 // At most one first projected contact for a fixed pair of physical anchors.
 for(const path of paths){
  const M=path[0].M,seen=new Map();
  for(const e of path){
   const x=get(e.C),q=r[e.C/2];diag+=q*e.w**2;
   for(const b of x.list){
    if(b.M>=M)break;
    let v=seen.get(b.i);
    if(!v){
     pairs++;
     const dist=M-b.M,short=Math.min(e.tail,b.tail)<=Z,gg=e.good&&b.good,rg=(e.recent&&b.good)||(b.recent&&e.good),rr=e.recent&&b.recent;
     const pt=rr&&((e.regular&&x.regPhysical.get(e.anchor)<=tau)||(b.regular&&x.regPhysical.get(b.anchor)<=tau));
     let oldAnchor=false,layer=0,j=-1,weighted=0,raw=0;
     if(e.anchor&&b.anchor&&(Math.abs(e.anchorJ-b.anchorJ)<=A||Math.abs(e.anchorT-b.anchorT)<=A)){
      contacts++;const key=e.anchor<b.anchor?e.anchor+'|'+b.anchor:b.anchor+'|'+e.anchor;
      if(anchorContact.has(key))ok(anchorContact.get(key)===e.C,'unique first anchor contact');else anchorContact.set(key,e.C);
      const ga=x.physical.get(e.anchor),gb=x.physical.get(b.anchor);
      weighted=Math.min(ga.n*gb.R,gb.n*ga.R)/B;raw=ga.n*gb.n;
      oldAnchor=weighted<=(e.anchorP===b.anchorP?capSame:capDiff);
      const tail=Math.min(e.tail,b.tail);
      if(tail<=0){zeroTail++;layer=3;}
      else{
       j=Math.max(0,Math.ceil(Math.log2(B/tail)-1e-12));
       ok(j<levels&&xs[j]*B<=tail+1e-8&&tail<=2*xs[j]*B+1e-8,'dyadic tail bracket');
       if(!ga.prof)ga.prof=prof(ga.tails);if(!gb.prof)gb.prof=prof(gb.tails);
       const na=ga.prof[j],nb=gb.prof[j],mn=Math.min(na,nb),mx=Math.max(na,nb);
       ok(mn>=1&&na<=anchorMap.get(e.anchor).prof[j]&&nb<=anchorMap.get(b.anchor).prof[j],'contact profiles bounded by earlier anchor');
       layer=mn<=thin?1:xs[j]>=z/2&&mn*Kimb<=mx?2:3;
       if(ga.n>tau&&gb.n>tau){bothThick++;if(layer===2)bothThickImb++;}
       if(layer===1||layer===2){
        if(!oldAnchor)oldCapExtra++;
        const p=per[j];if(layer===1){p.thinPairs++;p.thinBudget+=4*B*xs[j];}
        else{p.imbPairs++;p.imbBudget+=4*B*xs[j];}
       }
      }
     }
     const prior=dist<=near||short||gg||rg||pt||oldAnchor;
     const cls=prior?0:layer===1?1:layer===2?2:3;
     if(cls===1)layerThinExtra++;if(cls===2)layerImbExtra++;
     counts[cls]++;allCounts[layer]++;v={cls,layer,j,w:0,cap:2*Math.min(e.tail,b.tail),close:layer!==0};seen.set(b.i,v);
    }
    const w=2*q*e.w*b.w;v.w+=w;energy[v.cls]+=w;allEnergy[v.layer]+=w;
    if(v.close)closeEnergy+=w;
    if(v.layer===1)per[v.j].thinEnergy+=w;if(v.layer===2)per[v.j].imbEnergy+=w;
    ok(v.w<=v.cap+1e-7*Math.max(1,v.cap),'pair tail bound');
   }
  }
 }
 let thinBudget=0,imbBudget=0,thinTheory=0,imbTheory=0;
 for(let j=0;j<levels;j++){
  const p=per[j],v=internal[j];
  const thinBound=4*B*p.x*thin*D*v.mass,imbBound=4*B*p.x*D*v.n2/Kimb;
  ok(p.thinBudget<=thinBound+1e-7*Math.max(1,thinBound),'thin layer adjacency bound');
  ok(p.imbBudget<=imbBound+1e-7*Math.max(1,imbBound),'imbalance layer adjacency bound');
  ok(p.thinEnergy<=p.thinBudget+1e-7*Math.max(1,EK)&&p.imbEnergy<=p.imbBudget+1e-7*Math.max(1,EK),'layer energy budgets');
  thinBudget+=p.thinBudget;imbBudget+=p.imbBudget;thinTheory+=thinBound;
  if(p.x>=z/2)imbTheory+=imbBound;
 }
 ok(Math.abs(EK-diag-energy.reduce((s,v)=>s+v,0))<=1e-7*Math.max(1,EK),'exact energy partition');
 ok(pairs===counts.reduce((s,v)=>s+v,0),'pair partition');
 return {X,B,mode,P,A,thin,Kimb,z,h,D,Dbound,anchors:aa.length,edges,highHits,removed,kept,events,literal,E,EK,RK,diag,pairs,contacts,uniqueContacts:anchorContact.size,zeroTail,bothThick,bothThickImb,oldCapExtra,layerThinExtra,layerImbExtra,closeEnergy,counts,energy,allCounts,allEnergy,thinBudget,imbBudget,thinTheory,imbTheory,per:per.filter(p=>p.thinPairs||p.imbPairs),internal:internal.slice(0,5)};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','degree'])console.log(JSON.stringify(audit(X,mode)));
