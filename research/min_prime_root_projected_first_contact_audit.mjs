// Reproduce: node research/min_prime_root_projected_first_contact_audit.mjs
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),T=mode==="four"?4*B:mode==="gain"?Math.floor(X/Math.log(B)**.25):B,D=Math.max(1,Math.floor(T/8)),Q=Math.ceil(B/Math.log(B)),P=mode==="gain"?Math.ceil(B/Math.log(B)**.25):Math.max(5,Math.ceil(B/4)),y=3,L=6,tauBig=mode==="gain"?Math.max(1,Math.floor(B/Math.sqrt(Math.log(B)))):128,tauSmall=mode==="gain"?Math.max(1,Math.floor(Math.log(B)**.25)):12,tauThin=tauSmall,d=mode==="gain"?Math.floor(B*Math.log(B)**1.5):Math.max(0,Math.floor(B/64));
 const lim=7*X+5,spf=new Int32Array(lim+1);for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)if(!spf[j])spf[j]=n;}
 const fs=n=>{let a=[];while(n>1){const p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;},mod=(a,m)=>((a%m)+m)%m,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c;}return a;},ok=(b,msg)=>{if(!b)throw Error(msg);};
 const horizons=new Map(),cap=Math.max(tauBig,tauSmall)+1,bc=new Map();
 function candidates(J){if(!bc.has(J))bc.set(J,[...new Set([...fs(J),...fs(J+2)])].filter(p=>p>y).length);return bc.get(J);}
 function add(e){if(!horizons.has(e.C))horizons.set(e.C,[]);horizons.get(e.C).push(e);}
 let N=0,events=0,visits=0,R=0,G=0,cross=0,twins=0,literal=0,goodVisits=0,recentVisits=0,highArrivals=0,rootGood=0,maxGood=0,maxSmall=0,maxGroups=0,maxMass=0,keptR=0,diag=0;
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){
   N++;let t=M+2,C=2*M-2,cut=Math.floor((7*M-1)/4),kappa=Math.min(cap,L),incoming=0,J=0,qRecent=0,lowGain=0,by=new Map(),a=[],all=[],gVisits=0,rv=0,ha=0,nNonlow=0;
   while(true){
     const g=C-(2*M-2),e={M,C,t,g,incoming,J,qRecent,kappa,keep:false,p:0,r:0};add(e);all.push(e);visits++;
     if(kappa<=tauBig){goodVisits++;gVisits++;}
     if(qRecent){recentVisits++;rv++;ok(C-J===lowGain&&lowGain<L,"recent LOW span");ok(J%qRecent===0||(J+2)%qRecent===0,"recent post divisor");}
     if(g>=T){cross++;break;}
     let tt=Infinity,p=Infinity;
     const sgns=[-1,1];for(const sg of sgns)for(const q of fs(C+sg)){let tick=t+1+mod((sg===-1?0:q+2)-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;}}
     if(X<=1024){let lt=Infinity,lp=Infinity;for(let u=t+1;u<=cut;u++){const f=fs(gcd(u%2?u-2:u,C+(u%2?1:-1)));if(f.length){lt=u;lp=f[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal clock");literal++;}
     if(tt>cut){if(spf[C-1]===C-1&&spf[C+1]===C+1)twins++;break;}
     const r=Math.min(...fs(C-1),...fs(C+1));ok(r<=p&&tt-t<=2*r,"clock");e.p=p;e.r=r;a.push(e);R+=r;events++;
     t=tt;C+=p-1;incoming=p;ok(C<=2*t&&((C%p===0&&t%(2*p)===0)||((C+2)%p===0&&mod(t,2*p)===mod(p+2,2*p))),"post-event congruence");
     if(p>y){const dd=candidates(C);ok(dd>=1,"reverse label");kappa=Math.min(cap,kappa*L*dd);lowGain=0;nNonlow++;if(p>=P){J=C;qRecent=p;highArrivals++;ha++;}else{J=0;qRecent=0;}}
     else{lowGain+=p-1;ok(lowGain<L,"LOW barrier");}
   }
   const gain=C-(2*M-2);for(const e of all)e.end=C;G+=gain;ok(gain<T+B,"gain cap");ok(rv<=ha*(L/2+1),"recent visit count");ok(ha*(P-1)<=gain,"large arrival gain");ok(gVisits<= (L/2+1)*(1+Math.max(0,Math.floor(Math.log(Math.max(1,tauBig/L))/Math.log(L)))),"good prefix visit count");
   if(L<=tauBig)rootGood++;
   for(const e of a)if(e.p>=7&&e.g>=D&&gain-(e.g+e.p-1)>=D&&e.r>e.p/2){
     let j=Math.floor(Math.log2(Math.log(e.p)));if(!by.has(j))by.set(j,new Map());let m=by.get(j);if(!m.has(e.p))m.set(e.p,[]);m.get(e.p).push(e);
   }
   for(const m of by.values()){let items=[...m].sort((a,b)=>b[0]*b[1].length-a[0]*a[1].length||a[0]-b[0]);for(const [p,es] of items.slice(1))if(p>=Q)for(const e of es){e.keep=true;keptR+=e.r;}}
 }
 const names=["near","bothGood","recentSmall","recentThin","rootRecent","remaining"],first=Array(6).fill(0),energy=Array(6).fill(0),fullEnergy=Array(6).fill(0),remainingBudget=Array(6).fill(0),independent={gg:0,rs:0,rt:0,root:0},seen=new Map();let pairs=0,asyncFirst=0,physicalFirst=0,mixed=0,rootMeet=0,recentBoth=0,retainedPairVisits=0,oracle=0,firstWithBothRecentSame=0,predecessorCheck=0,allPhysicalFirst=0,latePhysicalFirst=0,lateSameIncoming=0,distinctPhysicalFirst=0,resetPhysicalFirst=0,largeProductGate=0,fullDiag=0,fullOracle=0;
 for(const C of [...horizons.keys()].sort((a,b)=>a-b)){
   const es=horizons.get(C),groups=new Map();let good=0,small=0,high=0;
   maxMass=Math.max(maxMass,es.length);for(const e of es){if(e.kappa<=tauBig)good++;if(e.kappa<=tauSmall)small++;if(e.qRecent){high++;let k=e.J+":"+e.qRecent;groups.set(k,(groups.get(k)||0)+1);}}
   maxGood=Math.max(maxGood,good);maxSmall=Math.max(maxSmall,small);maxGroups=Math.max(maxGroups,groups.size);ok(good<=tauBig&&small<=tauSmall,"Kraft cap");ok(groups.size<=(L/2)*Math.floor(2*Math.log(7*X+2)/Math.log(P)),"recent group count");
   const full=es.filter(e=>e.p>=Q);
   if(full.length){const r=full[0].r;ok(full.every(e=>e.r===r),"full common r");fullDiag+=r*full.length;fullOracle+=r*full.length**2;}
   const keep=es.filter(e=>e.keep);if(keep.length){const r=keep[0].r;ok(keep.every(e=>e.r===r),"common r");diag+=r*keep.length;oracle+=r*keep.length**2;}
   for(let i=0;i<es.length;i++)for(let j=i+1;j<es.length;j++){
     const a=es[i],b=es[j],key=a.M<b.M?(a.M-X)*X+(b.M-X):(b.M-X)*X+(a.M-X);let v=seen.get(key);
     if(!v){
       pairs++;ok(a.M!==b.M&&Math.abs(a.M-b.M)<(T+B)/2,"first pair support");
       if(!a.incoming||!b.incoming){ok(!(a.incoming===0&&b.incoming===0),"distinct roots");rootMeet++;}
       else{ok(a.incoming!==b.incoming,"first common mixed incoming");mixed++;predecessorCheck++;}
       if(a.t===b.t)physicalFirst++;else asyncFirst++;
       const gg=a.kappa<=tauBig&&b.kappa<=tauBig,rs=(a.qRecent&&b.kappa<=tauSmall)||(b.qRecent&&a.kappa<=tauSmall),rr=a.qRecent&&b.qRecent;
       let rt=false;if(rr){recentBoth++;const ka=a.J+":"+a.qRecent,kb=b.J+":"+b.qRecent;ok(ka!==kb,"first contact cannot share recent high group");rt=groups.get(ka)<=tauThin||groups.get(kb)<=tauThin;}
       const root=(!a.incoming&&b.qRecent)||(!b.incoming&&a.qRecent);
       if(gg)independent.gg++;if(rs)independent.rs++;if(rt)independent.rt++;if(root)independent.root++;
       const cls=Math.abs(a.M-b.M)<=d?0:gg?1:rs?2:rt?3:root?4:5;
       first[cls]++;const budget=3*Math.min(a.end-C,b.end-C);remainingBudget[cls]+=budget;v={cls,w:0,full:0,budget,phys:false,firstC:C};seen.set(key,v);
     }
     if(a.t===b.t&&!v.phys){
       v.phys=true;allPhysicalFirst++;if(v.firstC<C){latePhysicalFirst++;if(a.incoming===b.incoming)lateSameIncoming++;}
       ok(a.incoming&&b.incoming,"no incoming prime-root physical injection");
       if(a.incoming!==b.incoming){distinctPhysicalFirst++;const delta=2*a.t-C,eps=a.t%2?6:0;ok(delta>=0&&delta<=6+5*(T+B)&&delta%2===0,"physical deficit");ok(mod(delta-eps,2*a.incoming*b.incoming)===0,"two incoming deficit product");if(delta===eps)resetPhysicalFirst++;if(2*a.incoming*b.incoming>6+5*(T+B)){largeProductGate++;ok(delta===eps,"large-product reset");}}
     }
     if(a.p>=Q&&b.p>=Q){v.full+=a.r;fullEnergy[v.cls]+=2*a.r;ok(2*v.full<=v.budget,"full pair remaining gain bound");}
     if(a.keep&&b.keep){v.w+=a.r;energy[v.cls]+=2*a.r;retainedPairVisits++;ok(2*v.w<=v.budget&&v.w<=v.full,"pair remaining gain budget");}
   }
 }
 ok(pairs===first.reduce((s,n)=>s+n,0)&&mixed+rootMeet===pairs&&asyncFirst+physicalFirst===pairs,"pair partition");
 ok(2*independent.gg<=goodVisits*Math.max(0,tauBig-1),"good-good count bound");ok(independent.rs<=tauSmall*recentVisits,"recent-small bound");ok(independent.rt<=maxGroups*tauThin*recentVisits,"thin recent bound");ok(independent.root<=recentVisits,"root recent bound");ok(recentVisits<=(L/2+1)*highArrivals,"recent bound");ok(highArrivals*(P-1)<=G,"arrival bound");
 ok(energy.every((v,i)=>v<=fullEnergy[i]&&fullEnergy[i]<=remainingBudget[i]&&remainingBudget[i]<=3*(T+B)*first[i]),"per-class remaining gain bound");ok(allPhysicalFirst===physicalFirst+latePhysicalFirst,"physical synchronization partition");ok(fullOracle===fullDiag+fullEnergy.reduce((s,n)=>s+n,0),"full high energy partition");ok(diag===keptR&&oracle===diag+energy.reduce((s,n)=>s+n,0),"exact energy decomposition");ok(Number.isSafeInteger(oracle),"exact integer energy");
 return {mode,X,B,T,P,Q,d,L,tauBig,tauSmall,N,events,visits,R,G,cross,twins,literal,goodVisits,recentVisits,highArrivals,maxGood,maxSmall,maxGroups,maxMass,pairs,asyncFirst,physicalFirst,mixed,rootMeet,recentBoth,independent,first:Object.fromEntries(names.map((n,i)=>[n,first[i]])),energy:Object.fromEntries(names.map((n,i)=>[n,energy[i]])),keptR,oracle,retainedPairVisits,allPhysicalFirst,latePhysicalFirst,lateSameIncoming,distinctPhysicalFirst,resetPhysicalFirst,largeProductGate,fullDiag,fullOracle,fullEnergy:Object.fromEntries(names.map((n,i)=>[n,fullEnergy[i]])),remainingBudget:Object.fromEntries(names.map((n,i)=>[n,remainingBudget[i]]))};
}
const xs=process.argv.slice(2).map(Number);for(const mode of ['short','four','gain'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
