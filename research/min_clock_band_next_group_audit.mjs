// Scale-sensitive next-event groups and two-sided same-band propagation.
// Run node research/min_clock_band_next_group_audit.mjs 1024 4096 16384 65536
function audit(X,mode='diagnostic'){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,ell=Math.log(Math.log(B)),S=Math.max(1,Math.log(ell)),U=7*X+2;
 const ok=(b,m)=>{if(!b)throw Error(m);};
 ok(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(U+4);
 for(let p=2;p<spf.length;p++)if(!spf[p]){
  spf[p]=p;if(p*p<spf.length)for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 }
 let L=2,y=2;for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>6*S**.25)break;L*=p;y=p;}
 const T=mode==='degree'?4:(mode==='diagnostic'||(mode==='wide'||mode==='clock'))?6:Math.ceil(20*ell),g=Math.max(2,T*L),
  kg=mode==='analytic'?Math.floor(1.5*ell/Math.log(g)):5,
  k=mode==='analytic'?Math.floor(ell/(8*Math.log(g))):3,
  P=mode==='analytic'?Math.ceil(B/Math.log(B)**.125):Math.ceil(B/((mode==='wide'||mode==='clock')?8:4)),
  tau=mode==='analytic'?Math.log(B)**1.5:12,
  Z=mode==='analytic'?Math.log(B)**1.5:12,
  near=mode==='analytic'?Math.floor(4*Math.log(B)):Math.max(2,Math.floor(B/64));
 const A=mode==='analytic'?Math.floor(Math.log(B)**.125):Math.max(2,Math.floor(P/((mode==='wide'||mode==='clock')?2:8))), capDiff=mode==='analytic'?Math.log(B)**3.5:256,capSame=mode==='analytic'?Math.log(B)**2.5:144;
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
 const get=C=>{let x=horizons.get(C);if(!x){x={list:[],good:0,recent:0,groups:new Map(),physical:new Map(),regPhysical:new Map(),occupation:new Map()};horizons.set(C,x);}return x;};
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
  const past=[];for(let ix=0;ix<path.length;ix++){
   const e=path[ix];e.ix=ix;if(e.anchor&&e.C===e.anchorJ)past.push(e.anchor);
   const x=get(e.C);if(e.w)for(const id of past)x.occupation.set(id,(x.occupation.get(id)||0)+e.w);x.list.push(e);
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





 const u=Math.log(B),Y=mode==='analytic'?2**Math.floor(Math.log2(Math.max(4,Math.log(u)))):4,
 Q=mode==='analytic'?2**Math.floor(Math.log2(B/u**.25)):2**Math.floor(Math.log2(B/(mode==='wide'?8:4))),
 band=p=>2**Math.floor(Math.log2(p)), bands=new Map(),groups=new Map(),primeCounts=new Map();
 const getBand=P=>{let v=bands.get(P);if(!v){const l=Math.log(2+P);
  v={P,high:P>=Q,k:mode==='analytic'?Math.floor(l**.125):mode==='wide'?2:1,
   tau:mode==='analytic'?Math.floor(P>=Q?u**2.75:l**1.5):mode==='wide'?3:2,
   width:mode==='analytic'?B/l**.125:mode==='wide'?B/4:B/2,
   input:0,weight:0,R:0,cheap:0,cheapR:0,seed:0,seedW:0,seedR:0,end:0,endW:0,endR:0,halo:0,haloW:0,haloR:0,kept:0,keptW:0,keptR:0,groups:0,thinGroups:0,candidates:0,arithKeys:0,arithW:0,arithCellW:0,maxMass:0,neighborChecks:0};
  bands.set(P,v);}return v;};
 const G=2*H+B+6,maxDelta=2*(H+2*B)+6;
 const byI=new Map(paths.map(p=>[p[0].i,p]));
 let selected=0,cheap=0,seed=0,end=0,halo=0,keptCost=0,low=0,lowWeight=0,fullCost=0,lowCost=0,marks=0;
 // Build full-prefix selected-event ledger (including unoccupied events), not just slab hits.
 for(const path of paths){const seq=new Map();
  for(let i=0;i+1<path.length;i++){
   const e=path[i],v=path[i+1],p=v.inc,q=r[e.C/2];
   ok(p>=3&&v.C-e.C===p-1&&v.t>e.t&&v.t-e.t<=2*q,'event identity');
   e.selected=p;selected+=p;fullCost+=e.cost;
   if(p<Y){low++;lowWeight+=p;lowCost+=e.cost;e.cls='low';continue;}
   const P0=band(p),b=getBand(P0);b.input++;b.weight+=p;b.R+=e.cost;
   const ratio=mode==='analytic'?Math.log(2+p)**.125:2;
   if(q<p/ratio){e.cls='cheap';cheap++;b.cheap+=p;b.cheapR+=e.cost;continue;}
   e.band=P0;const c=Math.floor((e.M-X)/b.width),id=v.t+':'+v.C+':'+p+':'+c;
   e.group=id;let gr=groups.get(id);if(!gr){gr={id,p,P:P0,t:v.t,J:v.C,C:e.C,c,list:[],mass:0};groups.set(id,gr);b.groups++;}
   ok(gr.C===e.C&&gr.J===v.C&&gr.t===v.t,'group physical event');
   gr.list.push(e);gr.mass++;const list=seq.get(P0)||[];list.push(e);seq.set(P0,list);
  }
  path.bands=seq;
 }
 for(const gr of groups.values()){const b=getBand(gr.P);b.maxMass=Math.max(b.maxMass,gr.mass);if(gr.mass<=b.tau)b.thinGroups++;}
 // Exact relaxed arithmetic key envelope with candidate source cells at each C.
 for(let C=2*X;C<7*X;C+=2){const rr=r[C/2];if(!rr)continue;
  for(const s of [-1,1])fac(C+s,p=>{
   if(p<Y)return;const ratio=mode==='analytic'?Math.log(2+p)**.125:2;if(rr<p/ratio||rr>p)return;
   const b=getBand(band(p)),J=C+p-1,side=s===-1?0:1;
   const residue=side?p+2:0,m=2*p,t0=Math.ceil(J/2),t1=Math.floor((J+maxDelta)/2);
   const nt=Math.max(0,Math.floor((t1-residue)/m)-Math.ceil((t0-residue)/m)+1);
   // C0=2M-2, C-C0<=G for every actual tag.
   const m0=Math.max(X+1,Math.ceil((C-G+2)/2)),m1=Math.min(2*X-1,Math.floor((C+2)/2));
   const nc=m1>=m0?Math.floor((m1-X)/b.width)-Math.floor((m0-X)/b.width)+1:0;
   b.candidates++;b.arithKeys+=nt;b.arithW+=p*nt;b.arithCellW+=p*nt*nc;
  });
 }
 for(const gr of groups.values()){
  const b=getBand(gr.P),p=gr.p,side=gr.t%2,m=2*p,res=side?p+2:0;
  ok((gr.t-res)%m===0&&(gr.J+2*side)%p===0,'clock congruences');
  ok(gr.t>=gr.J/2&&2*gr.t-gr.J<=maxDelta,'post deficit');
  for(const e of gr.list)ok(Math.floor((e.M-X)/b.width)===gr.c&&e.C===gr.C,'cell membership');
 }
 let pairLower=0,maxActualSpread=0,postMassChecks=0;
 for(const gr of groups.values()){
  const b=getBand(gr.P);if(gr.mass<=b.tau)continue;
  const ids=new Set(gr.list.map(e=>e.i));ok(ids.size===gr.mass,'distinct source tags');
  const minM=gr.list[0].M,maxM=gr.list[gr.list.length-1].M;
  ok(maxM-minM<b.width+1e-8,'source span');
  const next=get(gr.J).list.filter(e=>e.t===gr.t);ok(next.length>=gr.mass,'actual post mass');
  postMassChecks++;pairLower+=gr.mass*(gr.mass-1)/2;maxActualSpread=Math.max(maxActualSpread,maxM-minM);
 }
 for(const path of paths)for(const [P0,list] of path.bands){const b=getBand(P0),k=b.high?0:b.k;
  const thin=list.map(e=>groups.get(e.group).mass<=b.tau),pref=[0];for(const v of thin)pref.push(pref[pref.length-1]+ +v);
  for(let i=0;i<list.length;i++){const e=list[i],p=e.selected;
   const l=Math.max(0,i-k),j=Math.min(list.length-1,i+k),neighbor=pref[j+1]-pref[l]>0;
   if(thin[i]){e.cls='seed';seed++;b.seed++;b.seedW+=p;b.seedR+=e.cost;}
   else if(neighbor){e.cls='halo';halo++;b.halo++;b.haloW+=p;b.haloR+=e.cost;}
   else if(!b.high&&(i<k||i+k>=list.length)){e.cls='end';end++;b.end++;b.endW+=p;b.endR+=e.cost;}
   else{e.cls='kept';b.kept++;b.keptW+=p;b.keptR+=e.cost;keptCost+=e.cost;
    for(let t=i-k;t<=i+k;t++){ok(t>=0&&t<list.length&&groups.get(list[t].group).mass>b.tau,'two-sided frozen thick group');b.neighborChecks++;}
   }
  }
 }
 // Verify common companions from the earliest frozen band event, not merely per-event thickness.
 let interior=0,interiorCost=0,companionChecks=0,companionStateChecks=0,minCompanions=Infinity,maxCompanions=0,trimLost=0,commonEnergyLower=0;
 const margin=Math.ceil(Math.max(0,...[...bands.values()].map(b=>b.width)));
 for(const path of paths)for(const [P0,list] of path.bands){const b=getBand(P0);if(b.high)continue;
  for(let i=0;i<list.length;i++){const e=list[i];if(e.cls!=='kept'||!e.cost)continue;
   const s=e.M+2,v=path[e.ix+1],l=Math.max(e.t,s+a+margin),u0=Math.min(v.t,s+H-margin),dur=Math.max(0,u0-l);
   trimLost+=e.cost-dur/2;if(!dur)continue;
   interior++;interiorCost+=dur/2;
   const early=list[i-b.k],gr=groups.get(early.group),q=r[e.C/2];ok(gr.mass>b.tau,'earliest group thick');
   minCompanions=Math.min(minCompanions,gr.mass);maxCompanions=Math.max(maxCompanions,gr.mass);
   let sum=0;
   for(const other of gr.list){const p=byI.get(other.i),idx=other.ix+1,central=p.findIndex(v=>v.C===e.C);
    ok(Math.abs(other.M-e.M)<b.width+1e-8&&central>=idx,'companion root proximity and earlier common anchor');
    ok(p[central].t===e.t&&central+1<p.length&&p[central+1].t===v.t&&p[central+1].C===v.C,'companion shares center event');
    const cs=other.M+2;ok(l>=cs+a&&u0<=cs+H,'trimmed common slab');
    ok(p[central].w+1e-8>=dur/(2*q),'companion occupied weight');sum+=p[central].w;companionChecks++;
    for(let j=i-b.k+1;j<=i;j++){const c=list[j],ix=p.findIndex(w=>w.C===c.C);ok(ix>=idx&&p[ix].t===c.t,'same companions across prior band states');companionStateChecks++;}
   }
   ok(sum+1e-7>=gr.mass*dur/(2*q),'common group weight');
   commonEnergyLower+=q*dur/(2*q)*sum;
  }
 }
 ok(trimLost<=kept*margin+1e-6*Math.max(1,RK),'two-sided trim cost');

 // Stronger two-sided common-history core: remove large gain span, trim boundary.
 const spanGate=mode==='analytic'?B/u**(1/16):B/8;
 const futureMargin=Math.ceil(margin+3*spanGate);
 let spanDeleted=0,spanWeight=0,spanCost=0,coreTrimLost=0,coreCost=0,coreEvents=0,coreCompanions=0,coreStateChecks=0,coreMaxSpan=0,coreMinGroup=Infinity,coreMaxGroup=0;
 const spanSum=new Map(),spanWeightByBand=new Map();
 for(const path of paths)for(const [P0,list] of path.bands){const b=getBand(P0);if(b.high)continue;
  for(let i=b.k;i+b.k<list.length;i++){
   const e=list[i],early=list[i-b.k],late=list[i+b.k],last=path[late.ix+1],span=last.C-early.C;
   spanSum.set(P0,(spanSum.get(P0)||0)+span);
   if(e.cls!=='kept')continue;
   if(span>spanGate){spanDeleted++;spanWeight+=e.selected;spanCost+=e.cost;spanWeightByBand.set(P0,(spanWeightByBand.get(P0)||0)+e.selected);continue;}
   const v=path[e.ix+1],s=e.M+2,l=Math.max(e.t,s+a+margin),u0=Math.min(v.t,s+H-futureMargin),dur=Math.max(0,u0-l);
   coreTrimLost+=e.cost-dur/2;if(!dur)continue;
   coreEvents++;coreCost+=dur/2;coreMaxSpan=Math.max(coreMaxSpan,span);
   const gr=groups.get(early.group);coreMinGroup=Math.min(coreMinGroup,gr.mass);coreMaxGroup=Math.max(coreMaxGroup,gr.mass);
   ok(last.t-e.t<=3*span,'future span time');
   for(const other of gr.list){const p=byI.get(other.i),idx=other.ix+1;coreCompanions++;
    ok(last.t<(other.M+2+H),'future common endpoint before cutoff');
    for(let j=i-b.k+1;j<=i+b.k;j++){
     const c=list[j],post=path[c.ix+1],ix=p.findIndex(w=>w.C===c.C);
     ok(ix>=idx&&p[ix].t===c.t&&ix+1<p.length&&p[ix+1].C===post.C&&p[ix+1].t===post.t,'two-sided common physical history');
     coreStateChecks++;
    }
   }
  }
 }
 for(const [P0,ss] of spanSum){const b=getBand(P0);ok(ss<=(2*b.k+1)*kept*G,'sum of band spans');ok((spanWeightByBand.get(P0)||0)<=2*P0*ss/spanGate+1e-7,'span deletion weight');}
 ok(coreTrimLost<=kept*(margin+futureMargin)/2+1e-6*Math.max(1,RK),'future trim clock bound');
 let total={input:0,weight:0,R:0,cheap:0,cheapR:0,seed:0,seedW:0,seedR:0,halo:0,haloW:0,haloR:0,end:0,endW:0,endR:0,kept:0,keptW:0,keptR:0,groups:0,thinGroups:0,candidates:0,arithKeys:0,arithW:0,arithCellW:0,neighborChecks:0};
 for(const b of bands.values()){
  ok(b.groups<=b.arithKeys*(Math.ceil(G/(2*b.width))+2),'group count arithmetic bound');
  ok(b.seedW<=b.tau*b.arithCellW,'thin selected weight envelope');
  ok(b.haloW+b.seedW<=2*(2*(b.high?0:b.k)+1)*b.seedW,'same-band halo weight bound');
  ok(b.endW<=4*b.k*b.P*kept,'end weight bound');
  ok(b.weight===b.cheap+b.seedW+b.haloW+b.endW+b.keptW,'band selected weight identity');
  ok(Math.abs(b.R-b.cheapR-b.seedR-b.haloR-b.endR-b.keptR)<1e-6*Math.max(1,b.R),'band linear clock identity');
  for(const key of Object.keys(total))total[key]+=b[key];
 }
 ok(selected===lowWeight+total.weight&&Math.abs(fullCost-lowCost-total.R)<=1e-6*Math.max(1,fullCost)&&Math.abs(fullCost-RK)<=1e-6*Math.max(1,RK),'global selected/clock budget');
 ok(Math.abs(coreCost+spanCost+coreTrimLost-[...bands.values()].filter(b=>!b.high).reduce((s,b)=>s+b.keptR,0))<=1e-6*Math.max(1,RK),'stronger medium budget partition');
 const W=new Float64Array(len);for(const path of paths)for(const e of path)if(e.cls==='kept'||e.cls==='low')W[e.C/2]+=e.w;
 let E2=0,R2=0;for(let j=lo;j<=hi;j++){E2+=r[j]*W[j]**2;R2+=r[j]*W[j];}
 ok(Math.abs(R2-keptCost-lowCost)<=1e-6*Math.max(1,R2)&&E2<=EK+1e-6*Math.max(1,EK),'retained energy oracle');
 return {X,B,mode,Y,Q,spanGate,futureMargin,spanDeleted,spanWeight,spanCost,coreTrimLost,coreCost,coreEvents,coreCompanions,coreStateChecks,coreMaxSpan,coreMinGroup:Number.isFinite(coreMinGroup)?coreMinGroup:null,coreMaxGroup,margin,interior,interiorCost,trimLost,companionChecks,companionStateChecks,minCompanions:Number.isFinite(minCompanions)?minCompanions:null,maxCompanions,commonEnergyLower,kept,removed,events,literal,RK,EK,R2,E2,low,lowCost,lowWeight,selected,postMassChecks,pairLower,maxActualSpread,total,bands:[...bands.values()].sort((a,b)=>a.P-b.P)};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','wide'])console.log(JSON.stringify(audit(X,mode)));
