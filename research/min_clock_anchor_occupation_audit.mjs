// Pointwise anchor occupation and prefix-filtered absorption, projected and physical.
// Run node research/min_clock_anchor_occupation_audit.mjs 1024 4096 16384 65536
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



 const thin=mode==='analytic'?Math.log(B)**1.5:4,
  Kimb=mode==='analytic'?Math.log(B)**.5:2,z=mode==='analytic'?Math.log(B)**(-.125):1/16,
  h=Math.floor((2*H+B+6)/(P-1)), Amax=2*(H+2*B)+6;
 const close=(e,b)=>e.anchor&&b.anchor&&e.anchor!==b.anchor&&(Math.abs(e.anchorJ-b.anchorJ)<=A||Math.abs(e.anchorT-b.anchorT)<=A);
 const aa=[...anchorMap.entries()];let D=0,edges=0;
 for(let i=0;i<aa.length;i++){const v=aa[i][1];v.degree=0;
  for(let j=0;j<aa.length;j++)if(i!==j&&(Math.abs(v.J-aa[j][1].J)<=A||Math.abs(v.t-aa[j][1].t)<=A))v.degree++;
  D=Math.max(D,v.degree);edges+=v.degree;
 }
 edges/=2;
 const Dbound=4*(2*A+1)*Math.ceil(Math.log(U)/Math.log(P))*(Math.floor(Amax/(2*P))+2);
 ok(D<=Dbound&&highHits<=kept*h,'degree and hit bounds');
 let occupationR=0,occupationE=0,maxActualH=0;
 for(const [C,x] of horizons){let s=0,sq=0;const W=keptW[C/2],rr=r[C/2];
  for(const w of x.occupation.values()){ok(w<=W+1e-8,'anchor occupation subset');s+=w;sq+=w*w;}
  ok(s<=h*W+1e-7*Math.max(1,W)&&sq<=h*W*W+1e-7*Math.max(1,W*W),'pointwise multiplicity');
  occupationR+=rr*s;occupationE+=rr*sq;if(W)maxActualH=Math.max(maxActualH,s/W);
 }
 ok(occupationR<=h*RK+1e-6*Math.max(1,RK)&&occupationE<=h*EK+1e-6*Math.max(1,EK),'global occupation norm');
 const byI=new Map(paths.map(p=>[p[0].i,p]));
 const maps=[new Map(),new Map()]; // projected first contact, first physical meeting
 const pairKey=(a,b)=>a<b?a+'|'+b:b+'|'+a;
 const stateKey=(rec,phys)=>phys?rec.t+':'+rec.C:rec.C;
 function makeEdge(e,b,phys){
  if(!close(e,b))return null;
  const id=pairKey(e.anchor,b.anchor),m=maps[+phys],old=m.get(id);
  if(old){ok(old.C===e.C&&(!phys||old.t===e.t),'unique first contact of anchor pair');return old;}
  const [a0,b0]=e.anchor<b.anchor?[e,b]:[b,e];
  const x=get(e.C);
  const group=(u)=>x.list.filter(v=>v.anchor===u.anchor&&(!phys||v.t===u.t));
  const ga=group(a0),gb=group(b0);
  const suffix=(u)=>new Set(byI.get(u.i).slice(0,u.ix).filter(v=>v.C>=u.anchorJ).map(v=>stateKey(v,phys)));
  const sa=suffix(a0),sb=suffix(b0);
  const filter=(gs,S)=>gs.filter(v=>!byI.get(v.i).slice(0,v.ix).some(w=>S.has(stateKey(w,phys))));
  const fa=filter(ga,sb),fb=filter(gb,sa);
  const rec={id,C:e.C,t:e.t,keys:[a0.anchor,b0.anchor],groups:[ga.length,gb.length],filtered:[fa.length,fb.length],sets:[new Set(fa.map(v=>v.i)),new Set(fb.map(v=>v.i))],cells:new Map(),pairs:0,energy:0};
  for(const [side,fs] of [fa,fb].entries())for(const v of fs){
   const path=byI.get(v.i);
   for(let j=v.ix;j<path.length;j++){const w=path[j];if(!w.w)continue;
    const row=rec.cells.get(w.C)||[0,0,0];row[side]+=w.w;rec.cells.set(w.C,row);
   }
  }
  m.set(id,rec);return rec;
 }
 function cellClass(rec,C){
  if(!rec)return 0;
  const row=rec.cells.get(C);if(!row)return 0;
  const [f,g]=row,xx=get(C),u=xx.occupation.get(rec.keys[0])||0,v=xx.occupation.get(rec.keys[1])||0;
  ok(f<=u+1e-7&&g<=v+1e-7,'filtered occupation subset');
  if(Math.min(f,g)<=thin)return 1;
  if(Math.min(u,v)*Kimb<=Math.max(u,v))return 2;
  if(Math.min(f,g)*Kimb<=Math.max(u,v))return 3;
  return 4;
 }
 function confirm(rec,e,b){
  if(!rec)return;
  const [a0,b0]=e.anchor<b.anchor?[e,b]:[b,e];
  ok(rec.sets[0].has(a0.i)&&rec.sets[1].has(b0.i),'first contact pair survives both prefix filters');rec.pairs++;
 }
 function oldPriority(e,b,x){
  const dist=e.M-b.M,short=Math.min(e.tail,b.tail)<=Z,gg=e.good&&b.good,rg=(e.recent&&b.good)||(b.recent&&e.good),rr=e.recent&&b.recent;
  const pt=rr&&((e.regular&&x.regPhysical.get(e.anchor)<=tau)||(b.regular&&x.regPhysical.get(b.anchor)<=tau));
  let ac=false,layer=false;
  if(close(e,b)){
   const ga=x.physical.get(e.anchor),gb=x.physical.get(b.anchor);
   ac=Math.min(ga.n*gb.R,gb.n*ga.R)/B<=(e.anchorP===b.anchorP?capSame:capDiff);
   const tail=Math.min(e.tail,b.tail);
   if(tail>0){const x0=2**(-Math.max(0,Math.ceil(Math.log2(B/tail)-1e-12)));
    const ca=ga.tails.filter(t=>t>=x0*B-1e-9).length,cb=gb.tails.filter(t=>t>=x0*B-1e-9).length;
    const oldI=mode==='analytic'?Math.log(B):2;
    layer=Math.min(ca,cb)<=thin||(x0>=z/2&&Math.min(ca,cb)*oldI<=Math.max(ca,cb));
   }
  }
  return dist<=near||short||gg||rg||pt||ac||layer;
 }

 const Y=mode==='clock'?B:mode==='analytic'?Math.log(B)**.125:(mode==='wide'||mode==='clock')?Math.ceil(P/4):12;
 const merges=new Map();
 function makeMerge(e,b){
  if(!e.anchor||e.anchor!==b.anchor)return null;
  ok(e.C===e.anchorJ&&e.t===e.anchorT&&e.C===b.anchorJ&&e.inc===e.anchorP&&b.inc===b.anchorP,'same anchor first physical meeting at high event');
  const alpha=e.anchor,x=get(e.C);
  let rec=merges.get(alpha);
  if(!rec){
   const group=x.list.filter(v=>v.anchor===alpha);
   const D0=e.C-e.anchorP+1,rr=r[D0/2],groups=new Map(),cells=new Map(),tags=new Map();
   ok(rr>0,'same anchor pre horizon active');
   for(const v of group){
    const path=byI.get(v.i),pre=path[v.ix-1];ok(pre.C===D0&&v.t-pre.t<=2*rr&&v.t>pre.t,'same label predecessor interval');
    const key=pre.t;let meta=groups.get(key);if(!meta){meta={n:0,reg:0,good:0};groups.set(key,meta);}
    meta.n++;meta.reg+=+pre.regular;meta.good+=+pre.good;tags.set(v.i,{key,reg:pre.regular,good:pre.good});
    for(let j=v.ix;j<path.length;j++){const w=path[j];if(!w.w)continue;
     let c=cells.get(w.C);if(!c){c={g:new Map(),actual:0};cells.set(w.C,c);}
     let a=c.g.get(key);if(!a){a={w:0,reg:0,good:0};c.g.set(key,a);}
     a.w+=w.w;if(pre.regular)a.reg+=w.w;if(pre.good)a.good+=w.w;
    }
   }
   const nr=[...groups.values()].filter(v=>v.reg).length,ng=[...groups.values()].reduce((n,v)=>n+v.good,0);
   ok(groups.size<=2*rr&&nr<=kBound*2*(Math.floor(Amax/(4*P))+2)&&ng<=gBound,'same anchor incoming group caps');
   rec={alpha,C:e.C,rr,groups,cells,tags,n:group.length,nr,ng,pairs:0};merges.set(alpha,rec);
  }
  const a=rec.tags.get(e.i),c=rec.tags.get(b.i);ok(a&&c&&a.key!==c.key,'different predecessors at first meeting');rec.pairs++;
  return {rec,a,b:c};
 }
 function mergeClass(v,C,w){
  if(!v)return 0;
  const {rec,a,b}=v,c=rec.cells.get(C);ok(c,'same anchor cell');
  const u=c.g.get(a.key),z=c.g.get(b.key);ok(u&&z,'same anchor predecessor weights');
  c.actual+=w;
  if(a.good||b.good)return 1;
  if((a.reg&&u.reg<=thin)||(b.reg&&z.reg<=thin))return 2;
  if(rec.rr<=Y){
   if(Math.min(u.w,z.w)<=thin)return 3;
   if(Math.min(u.w,z.w)*Kimb<=Math.max(u.w,z.w))return 4;
  }
  return 5;
 }
 const names=['prior','projThin','projImb','projFilter','physThin','physImb','physFilter','sameGood','sameRegThin','sameClockThin','sameClockImb','rest'];
 const energy=Array(names.length).fill(0),visits=energy.slice();
 const typeEnergy=[Array(5).fill(0),Array(5).fill(0)],typeVisits=[Array(5).fill(0),Array(5).fill(0)];
 const mergeEnergy=Array(6).fill(0),mergeVisits=mergeEnergy.slice();
 let pairs=0,physPairs=0,physicalNew=0,positive=0,physicalSameAnchor=0,filterPositive=0,filterRawBalanced=0,filterImproved=0,physicalOldNoEdge=0;
 for(const path of paths){const seen=new Map();
  for(const e of path){const x=get(e.C),q=r[e.C/2];diag+=q*e.w**2;
   for(const b of x.list){if(b.M>=e.M)break;
    let v=seen.get(b.i);
    if(!v){pairs++;const rec=makeEdge(e,b,false);confirm(rec,e,b);v={prior:oldPriority(e,b,x),projected:rec,physical:null,merge:null,met:false};seen.set(b.i,v);}
    if(!v.met&&e.t===b.t){v.met=true;physPairs++;
     if(e.anchor&&e.anchor===b.anchor)physicalSameAnchor++;
     v.physical=makeEdge(e,b,true);confirm(v.physical,e,b);v.merge=makeMerge(e,b);
     if(v.physical&&!v.projected)physicalOldNoEdge++;
    }
    const w=2*q*e.w*b.w;if(!w)continue;positive++;
    const pc=cellClass(v.projected,e.C),sc=e.t===b.t?cellClass(v.physical,e.C):0;
    for(const [i,rec,cl] of [[0,v.projected,pc],[1,e.t===b.t?v.physical:null,sc]]){
     if(!rec)continue;const row=rec.cells.get(e.C);ok(row,'positive pair belongs to filtered occupation');
     row[2]+=w;rec.energy+=w;typeEnergy[i][cl]+=w;typeVisits[i][cl]++;
     if(cl===3){filterPositive++;filterRawBalanced++;}
    }
    const mc=e.t===b.t?mergeClass(v.merge,e.C,w):0;
    if(mc){mergeEnergy[mc]+=w;mergeVisits[mc]++;}
    let cls=v.prior?0:pc>=1&&pc<=3?pc:sc>=1&&sc<=3?3+sc:mc>=1&&mc<=4?6+mc:11;
    if(cls>=4&&cls<=6)physicalNew++;
    if(cls===3||cls===6)filterImproved++;
    energy[cls]+=w;visits[cls]++;
   }
  }
 }
 let mergePairs=0,mergeActual=0,mergeDirect=0,mergeMaxDegree=0,mergeMaxRegular=0,mergeShort=0,mergeShortMass=0,mergeRegularMass=0,mergeGoodMass=0;
 for(const rec of merges.values()){
  mergePairs+=rec.pairs;mergeMaxDegree=Math.max(mergeMaxDegree,rec.groups.size);mergeMaxRegular=Math.max(mergeMaxRegular,rec.nr);if(rec.rr<=Y)mergeShort++;
  for(const [C,c] of rec.cells){let s=0,sq=0;for(const a of c.g.values()){s+=a.w;sq+=a.w*a.w;}const rr=r[C/2],expected=rr*(s*s-sq);
   ok(Math.abs(c.actual-expected)<=1e-7*Math.max(1,expected),'same high anchor exact cross predecessor energy');mergeActual+=c.actual;mergeDirect+=expected;
   mergeRegularMass+=rr*s*rec.nr;mergeGoodMass+=rr*s*rec.ng;if(rec.rr<=Y)mergeShortMass+=rr*s*rec.groups.size;
  }
 }
 ok(mergePairs===physicalSameAnchor&&Math.abs(mergeActual-mergeEnergy.reduce((s,v)=>s+v,0))<=1e-7*Math.max(1,EK),'same anchor pair identity');
 ok(mergeEnergy[1]<=2*mergeGoodMass+1e-6*Math.max(1,EK)&&mergeEnergy[2]<=2*thin*mergeRegularMass+1e-6*Math.max(1,EK)&&mergeEnergy[3]<=2*thin*mergeShortMass+1e-6*Math.max(1,EK),'same anchor thin bounds');
 ok(mergeEnergy[4]<=4*Y*occupationE/Kimb+1e-6*Math.max(1,EK),'same anchor imbalance bound');
 const reports=[];
 for(let i=0;i<2;i++){
  let removedA=0,rawA=0,edgeMass=0,filterEdges=0,positiveEdges=0,thinBudget=0,imbBudget=0,filterBudget=0,filterOnlyBudget=0,maxRatio=0;
  for(const rec of maps[i].values()){
   const raw=rec.groups[0]+rec.groups[1],filtered=rec.filtered[0]+rec.filtered[1];
   rawA+=raw;removedA+=raw-filtered;if(raw>filtered)filterEdges++;if(rec.energy)positiveEdges++;
   for(const [C,row] of rec.cells){const q=r[C/2],bound=2*q*row[0]*row[1];ok(row[2]<=bound+1e-7*Math.max(1,bound),'actual assigned edge cell energy');
    const cl=cellClass(rec,C);
    if(cl===1)thinBudget+=bound;if(cl===2)imbBudget+=bound;if(cl===3){filterBudget+=bound;filterOnlyBudget+=row[2];}
    edgeMass+=bound;
   }
  }
  ok(typeEnergy[i][1]<=thinBudget+1e-6*Math.max(1,EK)&&typeEnergy[i][2]+typeEnergy[i][3]<=imbBudget+filterBudget+1e-6*Math.max(1,EK),'actual type bounds');
  ok(thinBudget<=2*thin*D*occupationR+1e-6*Math.max(1,EK),'thin graph norm');
  ok(imbBudget+filterBudget<=2*D*occupationE/Kimb+1e-6*Math.max(1,EK),'absorption graph norm');
  reports.push({edges:maps[i].size,rawA,removedA,filterEdges,positiveEdges,edgeMass,thinBudget,imbBudget,filterBudget,filterOnlyBudget,typeEnergy:typeEnergy[i],typeVisits:typeVisits[i]});
 }
 ok(Math.abs(EK-diag-energy.reduce((s,v)=>s+v,0))<=1e-7*Math.max(1,EK),'energy partition');
 return {X,B,mode,P,A,D,h,Y,merge:{anchors:merges.size,pairs:mergePairs,actual:mergeActual,direct:mergeDirect,maxDegree:mergeMaxDegree,maxRegular:mergeMaxRegular,short:mergeShort,energy:mergeEnergy,visits:mergeVisits},anchors:aa.length,edges,removed,kept,events,literal,RK,EK,diag,occupationR,occupationE,maxActualH,pairs,physPairs,physicalSameAnchor,physicalOldNoEdge,positive,physicalNew,filterImproved,energy:Object.fromEntries(names.map((n,i)=>[n,energy[i]])),visits:Object.fromEntries(names.map((n,i)=>[n,visits[i]])),reports};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','degree','wide','clock'])console.log(JSON.stringify(audit(X,mode)));
