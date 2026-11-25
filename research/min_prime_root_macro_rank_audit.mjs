// Macroblock density and original descending-rank stable common ancestry audit.
function audit(X,mode="diagnostic",P0=30,j0=2){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),analytic=mode==="analytic",wide=mode==="wide"||mode==="wideRaw",raw=mode==="raw"||mode==="wideRaw",lim=7*X+5;
 const spf=new Int32Array(lim+1);
 const ok=(x,s)=>{if(!x)throw Error(`X=${X},${mode}: ${s}`);};
 const mod=(a,b)=>((a%b)+b)%b, gcd=(a,b)=>{while(b){const t=a%b;a=b;b=t;}return a;},choose=n=>n*(n-1)/2;
 for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n*n<=lim)for(let k=n*n;k<=lim;k+=n)if(!spf[k])spf[k]=n;}
 let P=2,z=2;
 for(let p=3;p<=B;p+=2)if(spf[p]===p){
   if(analytic&&P*p>B*u**1.5)break;
   if(wide&&P>B)break;
   if(!analytic&&!wide&&P*p>P0)break;
   P*=p;z=p;
 }
 if(!analytic&&!wide)ok(P===P0,"diagnostic P must be an even primorial");
 if(wide)ok(P>B,"wide grid");
 const baseP=P,T=analytic?Math.floor(X/u**.25):wide?Math.max(4*B,4*P):4*B,H=T+B;
 if(analytic)P=baseP*Math.max(1,Math.floor(T/(baseP*u**1.5)));
 const j=analytic?1:j0,D=j*P,delta=analytic?u**(-1/8):raw?.5:.25;
 const Q=Math.max(5,Math.ceil(B/(analytic?u:8))),m=analytic?Math.floor(B*u**(13/8)):8,c=P*(analytic?B*u**1.5:3/16);
 const fs=n=>{const a=[];while(n>1){const p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const roots=new Map(),hits=new Map(),groups=new Map();
 const v=Math.max(1,Math.log(u)),eps=raw?0:analytic?u**(-1/8):.15,eta=raw?0:analytic?u**(-1/8):.25;
 const minLen=analytic?Math.ceil(B**1.5):Math.max(2,Math.floor(P/4));
 const rank=raw?0:analytic?Math.max(1,Math.floor(u**1.5)):1;
 let rawHighR=0,rawHighTime=0,cheapTime=0,cheapProxy=0,rankTime=0,rankProxy=0,sparseTime=0,sparseProxy=0,keepTime=0,blocks=0,nonempty=0,keepBlocks=0,rankLabels=0,quotientChecks=0,quotientCandidates=0,witnesses=0,coverIntervals=0,coverLen=0,coverTime=0,unionGain=0,bruteIntervals=0,bruteBlocks=0,liveIntervals=0,minLiveLabels=Infinity,maxLiveLabels=0,uniformSequenceChecks=0,fullBlockDenseChecks=0;
 function localFilter(es,postC){
   blocks++;const n=es.length,points=es.map(e=>e.C).concat(postC),g=postC-points[0];
   ok(g<=P+B,"block gain cap");
   const buckets=new Map();for(const e of es)if(e.h){let a=buckets.get(e.p);if(!a){a=[];buckets.set(e.p,a);}a.push(e);}
   if(!buckets.size)return "";
   nonempty++;
   const stats=[];
   for(const [p,a] of buckets){
     const seen=new Set(),lo=Math.floor((points[0]-2)/(2*p))-1,hi=Math.ceil((postC+2)/(2*p))+1;
     let candidates=0;for(let k=lo;k<=hi;k++)if(k>=0){
       let good=false;
       for(const s of [-1,1]){const C=p*(2*k+1)-s;if(C<points[0]||C>=postC||C+1>lim||C<4)continue;
         const r=Math.min(...fs(C-1),...fs(C+1));
         if(r>p/(analytic?Math.sqrt(Math.log(p)):2))good=true;
       }
       if(good)candidates++;quotientCandidates++;
     }
     let weight=0;
     for(const e of a){
       const sig=(e.C-1)%p===0?-1:1,k=((e.C+sig)/p-1)/2;
       ok(Number.isInteger(k)&&k>=lo&&k<=hi&&!seen.has(k),"distinct same-label quotient");seen.add(k);weight+=2*e.h;quotientChecks++;
     }
     ok(a.length<=candidates&&weight<=2*p*candidates,"literal local quotient capacity");
     stats.push({p,a,weight});
   }
   stats.sort((a,b)=>b.weight-a.weight||a.p-b.p);
   for(const x of stats.slice(0,rank)){
     rankLabels++;for(const e of x.a){rankTime+=e.wait;rankProxy+=2*e.h;e.h=0;}
   }
   const prefix=[0],score=[0],mx=[0];
   for(let i=0;i<n;i++){prefix.push(prefix[i]+(es[i].h?es[i].wait:0));score.push(prefix[i+1]-eta*(points[i+1]-points[0]));mx.push(Math.max(mx[i],score[i+1]));}
   const intervals=[],diff=new Int32Array(n+1);
   for(let b=1;b<=n;b++){
     let lo=0,hi=b;while(lo<hi){let mid=(lo+hi)>>1;if(mx[mid]+1e-8>=score[b])hi=mid;else lo=mid+1;}
     const a=lo;if(a>=b||points[b]-points[a]<minLen)continue;
     ok(prefix[b]-prefix[a]<=eta*(points[b]-points[a])+1e-7,"actual sparse witness");
     intervals.push([a,b]);diff[a]++;diff[b]--;witnesses++;
   }
   const mark=[];let depth=0,ug=0,um=0;
   for(let i=0;i<n;i++){depth+=diff[i];mark.push(depth>0);if(depth){ug+=points[i+1]-points[i];um+=prefix[i+1]-prefix[i];}}
   unionGain+=ug;
   // Earliest-start interval for each endpoint; union cover has depth at most two.
   intervals.sort((a,b)=>a[0]-b[0]||b[1]-a[1]);
   const chosen=[];let i=0,reach=-1;
   while(i<intervals.length){if(intervals[i][0]>reach)reach=intervals[i][0];let best=null;while(i<intervals.length&&intervals[i][0]<=reach){const x=intervals[i++];if(!best||x[1]>best[1])best=x;}if(best&&best[1]>reach){chosen.push(best);reach=best[1];}}
   let sl=0,sm=0;const cd=new Int32Array(n+1);
   for(const [a,b] of chosen){sl+=points[b]-points[a];sm+=prefix[b]-prefix[a];cd[a]++;cd[b]--;coverIntervals++;}
   depth=0;for(let k=0;k<n;k++){depth+=cd[k];ok(depth<=2&&(depth>0)===mark[k],"depth-two exact interval union");}
   ok(sl<=2*ug&&um<=sm&&sm<=eta*sl+1e-6,"local actual sparse payment");coverLen+=sl;coverTime+=sm;
   // Literal all intervals on every small-X block and on a bounded sample of larger blocks.
   if(X<=4096||(bruteBlocks<128&&n<=100)){
     bruteBlocks++;const oracle=new Uint8Array(n);
     for(let a=0;a<n;a++){const labels=new Set();for(let b=a+1;b<=n;b++){
       if(es[b-1].h)labels.add(es[b-1].p);
       if(points[b]-points[a]<minLen)continue;
       bruteIntervals++;
       if(prefix[b]-prefix[a]<=eta*(points[b]-points[a])+1e-8){for(let k=a;k<b;k++)oracle[k]=1;}
       else if(es.slice(a,b).some((e,k)=>e.h&&!mark[a+k])){
         liveIntervals++;minLiveLabels=Math.min(minLiveLabels,labels.size);maxLiveLabels=Math.max(maxLiveLabels,labels.size);
       }
     }}
     for(let k=0;k<n;k++)ok(Boolean(oracle[k])===mark[k],"literal all-interval union oracle");
   }
   let keep=0;const signature=[];
   for(let k=0;k<n;k++){const e=es[k];if(e.h&&mark[k]){sparseTime+=e.wait;sparseProxy+=2*e.h;e.h=0;}if(e.h){keep+=e.wait;keepTime+=e.wait;signature.push(e.C+":"+e.p+":"+e.h);}}
   if(keep){keepBlocks++;if(g>=minLen){ok(prefix[n]>eta*g-1e-8,"surviving block has high actual density before sparse mask");fullBlockDenseChecks++;}}
   return signature.join("|");
 }
 let N=0,G=0,R=0,highR=0,events=0,highHits=0,literal=0,gridCount=0,edgeGridChecks=0,wideEdges=0,blockMassChecks=0,tagMass=0,throughTags=0,maxN=0,thickGroups=0;
 const block=C=>P*Math.floor((C-1)/P);
 const ceilDiv=(a,b)=>Math.ceil(a/b);
 const key=(K,e)=>`${K}:${e.C}:${e.t}`;
 const same=(a,b)=>a.C===b.C&&a.t===b.t;
 function crossing(a,K){
   if(K<a[0].C||K>=a.at(-1).C)return null;
   let lo=0,hi=a.length-1;while(lo+1<hi){const mid=(lo+hi)>>1;if(a[mid].C<=K)lo=mid;else hi=mid;}
   const e=a[lo];ok(e.p>z&&e.C<=K&&K<a[lo+1].C,"strict crossing");return e;
 }
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){
   N++;const a=[],byC=new Map(),mass=new Map(),blockLists=new Map(),signatures=new Map();let C=2*M-2,t=M+2,cut=Math.floor((7*M-1)/4),gc=0;
   while(true){
     const e={M,C,t,p:0,r:0,h:0,i:a.length};a.push(e);byC.set(C,e);
     if(C-(2*M-2)>=T)break;
     let tt=Infinity,p=Infinity;
     const f1=fs(C-1),f2=fs(C+1);
     for(const [s,f] of [[-1,f1],[1,f2]])for(const q of f){
       const tick=t+1+mod((s===-1?0:q+2)-(t+1),2*q);
       if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;}
     }
     if(X<=1024){
       let lt=Infinity,lp=Infinity;
       for(let k=t+1;k<=cut;k++){const f=fs(gcd(k%2?k-2:k,C+(k%2?1:-1)));if(f.length){lt=k;lp=f[0];break;}}
       ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"independent literal clock");literal++;
     }
     if(tt>cut)break;
     const r=Math.min(...f1,...f2),J=C+p-1;
     ok(r<=p&&tt-t<=2*r&&tt>t&&J<=2*tt,"clock");
     e.p=p;e.r=r;e.wait=tt-t;R+=r;events++; const K=block(C);if(!blockLists.has(K))blockLists.set(K,[]);blockLists.get(K).push(e);
     if(p>=Q&&r>p/(analytic?Math.sqrt(Math.log(p)):2)){
       rawHighR+=r;rawHighTime+=e.wait;
       if(e.wait<=eps*(p-1)){cheapTime+=e.wait;cheapProxy+=2*r;}else e.h=r;
     }
     const ng=ceilDiv(J,P)-ceilDiv(C,P);gc+=ng;edgeGridChecks++;
     if(ng){ok(p>z,"small prime strict crossing");if(P>B){ok(ng===1,"wide edge crosses at most one boundary");wideEdges++;}}
     t=tt;C=J;
   }
   const gain=C-(2*M-2);G+=gain;ok(gain<T+B&&gc===ceilDiv(C,P)-ceilDiv(a[0].C,P)&&gc<=gain/P+1,"root crossing ledger");gridCount+=gc;
   for(const [K,es] of blockLists){
     const last=es.at(-1);signatures.set(K,localFilter(es,a[last.i+1].C));
     for(const e of es)if(e.h){highR+=e.h;highHits++;const hk=e.C+":"+e.t;mass.set(K,(mass.get(K)||0)+2*e.h);if(!hits.has(hk))hits.set(hk,[]);hits.get(hk).push(e);}
   }
   roots.set(M,{a,byC,end:C,mass});
   for(const [K,A] of mass){
     ok(A<=3*(P+B),"natural block occupation");
     const past=crossing(a,K-D),future=crossing(a,K+D);
     if(!past||!future)continue;
     const middle=crossing(a,K);ok(middle,"middle crossing");
     const id=key(K,past);let g=groups.get(id);
     if(!g){g={K,past,middle,future,A,signature:signatures.get(K),tags:new Set(),loads:new Map(),masked:new Map(),actual:0,maskedTotal:0};groups.set(id,g);}
     ok(g.A===A&&g.signature===signatures.get(K)&&same(g.middle,middle)&&same(g.future,future)&&!g.tags.has(M),"persistent common occupation");
     uniformSequenceChecks++;g.tags.add(M);tagMass+=A;throughTags++;blockMassChecks++;
     // All tags of this group actually complete every strict grid crossing across the span.
     let lastCross=null;for(let L=K-D;L<=K+D;L+=baseP){const ce=crossing(a,L);ok(ce,"full persistent span");if(baseP>B&&lastCross)ok(ce.i>lastCross.i,"distinct base-grid crossing");lastCross=ce;}
   }
 }
 ok(gridCount<=G/P+N+1e-8&&throughTags<=gridCount&&tagMass<=2*highR&&2*R<=3*G,"global membership/occupation");
 ok(rawHighTime===cheapTime+rankTime+sparseTime+keepTime&&2*rawHighR===cheapProxy+rankProxy+sparseProxy+2*highR,"disjoint actual and proxy partitions");
 ok(cheapTime<=eps*G+1e-6&&sparseTime<=coverTime+1e-6&&coverTime<=2*eta*G+1e-6&&coverLen<=2*unionGain&&unionGain<=G,"global actual deletions");
 let full=0,short=0,late=0,through=0,pairHits=0,shortPairs=0,latePairs=0,birthChecks=0,maskMass=0;
 const pairs=new Map();
 for(const a of hits.values()){
   a.sort((a,b)=>a.M-b.M);
   full+=2*a[0].h*choose(a.length);
   for(let i=0;i<a.length;i++)for(let k=i+1;k<a.length;k++){
     const e=a[i],f=a[k],A=roots.get(e.M),B1=roots.get(f.M),C=e.C,K=block(C),w=2*e.h,id=`${e.M}:${f.M}`;
     ok(e.h===f.h&&e.t===f.t&&f.M-e.M<T/2&&A.end<=B1.end,"shared natural hit and stop order");pairHits++;
     let pr=pairs.get(id);
     if(!pr){
       let lo=0,hi=e.i;
       while(lo<hi){const mid=(lo+hi)>>1,x=A.a[mid],y=B1.byC.get(x.C);if(y&&same(x,y))hi=mid;else lo=mid+1;}
       const x=A.a[lo],y=B1.byC.get(x.C);ok(y&&same(x,y),"birth membership");
       if(lo){const prev=A.a[lo-1],yp=B1.byC.get(prev.C);ok(!yp||!same(prev,yp),"first physical birth");}
       if(X<=4096){const literalBirth=A.a.slice(0,e.i+1).find(x=>{const y=B1.byC.get(x.C);return y&&same(x,y);});ok(literalBirth.C===x.C,"linear birth oracle");}
       pr={birth:x.C,short:0,late:0};pairs.set(id,pr);birthChecks++;
     }
     if(pr.birth>K-D){short+=w;pr.short+=w;ok(C-pr.birth<D+P,"short shared age");continue;}
     if(A.end<=K+D){late+=w;pr.late+=w;ok(A.end-C<D,"terminal age");continue;}
     const p=crossing(A.a,K-D),q=crossing(B1.a,K-D);
     ok(p&&q&&same(p,q),"actual old shared strict crossing");
     const g=groups.get(key(K,p));ok(g&&g.tags.has(e.M)&&g.tags.has(f.M),"through group membership");
     through+=w;g.actual+=w;g.loads.set(id,(g.loads.get(id)||0)+w);
     const masked=((e.M+3*f.M+C+e.t)%5===0)?0:((e.M+f.M+C)%3===0?w/2:w);
     g.maskedTotal+=masked;g.masked.set(id,(g.masked.get(id)||0)+masked);maskMass+=masked;
   }
 }
 for(const pr of pairs.values()){
   if(pr.short){shortPairs++;ok(pr.short<=3*(D+P+B),"pair short bound");}
   if(pr.late){latePairs++;ok(pr.late<=3*D,"pair terminal bound");}
 }
 ok(full===short+late+through,"exact natural pair partition");
 let groupEnergy=0,thin=0,heavy=0,excess=0,heavyExcess=0,positive=0,maskedExcessSmall=0,maskedChecks=0,subsetChecks=0,uniformChecks=0,maxA=0,groupPairs=0;
 for(const g of groups.values()){
   const tags=[...g.tags].sort((a,b)=>a-b),n=tags.length,A=g.A,E=A*choose(n);
   groupEnergy+=E;groupPairs+=choose(n);maxN=Math.max(maxN,n);maxA=Math.max(maxA,A);
   ok(g.actual===E&&g.loads.size===choose(n),"exact uniform complete through graph");
   for(let i=0;i<n;i++)for(let k=i+1;k<n;k++){
     const id=`${tags[i]}:${tags[k]}`;
     ok(g.loads.get(id)===A&&(g.masked.get(id)||0)<=A,"literal natural pair load");uniformChecks++;
   }
   const h=Math.max(0,E-c*n);
   let cardinalityMax=0;for(let k=0;k<=n;k++)cardinalityMax=Math.max(cardinalityMax,A*choose(k)-c*k);
   ok(Math.abs(h-cardinalityMax)<1e-7,"convex Hall envelope");
   excess+=h;if(h>0)positive++;
   if(n<=m)thin+=E;else{thickGroups++;heavy+=E;heavyExcess+=h;}
   // Exhaust every subset on small groups with genuinely nonuniform retained weights.
   if(n>=2&&n<=10){
     let maxMasked=0,maxNatural=0;
     for(let S=0;S<(1<<n);S++){
       let k=0,W=0;for(let i=0;i<n;i++)if(S&(1<<i)){k++;for(let l=i+1;l<n;l++)if(S&(1<<l))W+=g.masked.get(`${tags[i]}:${tags[l]}`)||0;}
       maxMasked=Math.max(maxMasked,W-c*k);maxNatural=Math.max(maxNatural,A*choose(k)-c*k);subsetChecks++;
     }
     ok(Math.abs(maxNatural-h)<1e-7&&maxMasked<=h+1e-7,"subset Hall oracle");maskedExcessSmall+=maxMasked;maskedChecks++;
   }
 }
 ok(groupEnergy===through&&thin+heavy===through&&thin<=(m-1)*tagMass/2+1e-7&&throughTags<=gridCount&&maskMass<=through,"global complete graph and thin bound");
 // Full original descending rank: larger roots persist until the smaller's stop.
 const phys=e=>e.C+":"+e.t, visits=new Map(),cont=new Map(),bin=r=>Math.floor(Math.log(r)/Math.log1p(delta)+1e-12);
 let rankChecks=0,rankThresholds=0,rankCrossChecks=0,maxRank=0,maxBin=0;
 for(const [M,root] of [...roots.entries()].reverse()){
   let prev=0,prevBin=0,lastRise=root.a[0].C;
   for(const e of root.a){
     const id=phys(e),r=(visits.get(id)||0)+1;visits.set(id,r);e.dr=r;e.rb=bin(r);
     ok(r>=prev&&e.rb>=prevBin,"descending rank monotone");rankChecks++;
     if(e.rb>prevBin){rankThresholds+=e.rb-prevBin;lastRise=e.C;}
     e.lastRise=lastRise;prev=r;prevBin=e.rb;maxRank=Math.max(maxRank,r);maxBin=Math.max(maxBin,e.rb);
     if(e.p)cont.set(id,(cont.get(id)||0)+1);
   }
 }
 ok(rankThresholds<=N*bin(Math.max(1,N)),"rank threshold budget");
 let rankOrigin=0,rankTerminal=0,rankDeleted=0,dominantDeleted=0,rankOriginActual=0,rankTerminalActual=0,rankDeletedActual=0,dominantActual=0;
 let keptProxy=0,keptActual=0,preDominant=0,preRecentPairs=0,preOldPairs=0,postPairs=0,postEnergy=0,postFibres=0,domNonzero=0,maxForeign=0,oldPartnerChecks=0,eligible=0,dominantChecks=0,rankGateChecks=0,rootGateChecks=0;
 const perRoot=new Map(),newGroupPairs=new Map();
 for(const [id,ar] of hits){
   const C=ar[0].C,K=block(C),n=cont.get(id),surv=[];
   ok(n>=ar.length,"full completed mass");
   for(const e of ar){
     const root=roots.get(e.M),a=root.a,w=e.h,wait=e.wait;
     let budget=perRoot.get(e.M);if(!budget){budget={origin:0,late:0,rank:0};perRoot.set(e.M,budget);}
     const past=crossing(a,K-D),future=crossing(a,K+D);
     if(!past){ok(C-a[0].C<D+P,"origin age");rankOrigin+=w;rankOriginActual+=wait;budget.origin+=w;continue;}
     if(!future){ok(root.end-C<D,"terminal age");rankTerminal+=w;rankTerminalActual+=wait;budget.late+=w;continue;}
     ok(past.dr<=e.dr&&past.rb<=e.rb,"prior rank");rankGateChecks++;
     if(past.rb!==e.rb){
       ok(e.lastRise>past.C&&e.lastRise<=C&&C-e.lastRise<D+P+B,"actual rank threshold witness");
       rankCrossChecks++;rankDeleted+=w;rankDeletedActual+=wait;budget.rank+=w;continue;
     }
     ok(e.dr-past.dr<delta*past.dr+1e-7,"same-bin rank growth");
     surv.push({e,past,k:key(K,past)});eligible++;preDominant+=w;
   }
   if(!surv.length)continue;
   surv.sort((a,b)=>a.e.M-b.e.M);
   const first=surv[0],good=[],bad=[];
   for(const x of surv){
     const y=roots.get(x.e.M).byC.get(first.past.C);
     const old=!!(y&&same(y,first.past));
     ok(old===(x.k===first.k),"literal earlier membership");
     oldPartnerChecks++;
     if(old)good.push(x);else bad.push(x);
   }
   const growth=first.e.dr-first.past.dr;
   ok(bad.length<=growth&&growth<delta*n+1e-7,"dominant cohort foreign bound");
   dominantChecks++;if(bad.length)domNonzero++;maxForeign=Math.max(maxForeign,bad.length);
   const gc=new Map();for(const x of surv)gc.set(x.k,(gc.get(x.k)||0)+1);
   const oldPairs=[...gc.values()].reduce((s,k)=>s+choose(k),0);
   preOldPairs+=oldPairs;preRecentPairs+=choose(surv.length)-oldPairs;
   for(const x of bad){dominantDeleted+=x.e.h;dominantActual+=x.e.wait;}
   const g=groups.get(first.k);ok(g,"actual natural through group");
   for(const x of good){
     ok(x.k===first.k&&g.tags.has(x.e.M),"retained pair through membership");
     keptProxy+=x.e.h;keptActual+=x.e.wait;
   }
   postFibres++;postPairs+=choose(good.length);postEnergy+=2*first.e.h*choose(good.length);
   for(let i=0;i<good.length;i++)for(let k=i+1;k<good.length;k++){
     const pair=good[i].e.M+":"+good[k].e.M,ky=first.k+"|"+pair;
     const old=newGroupPairs.get(ky)||0;newGroupPairs.set(ky,old+2*first.e.h);
     ok(g.loads.has(pair)&&old+2*first.e.h<=g.loads.get(pair),"retained natural pair envelope");
   }
 }
 for(const [M,b] of perRoot){
   const root=roots.get(M),last=root.a.at(-1);
   ok(b.origin<=1.5*(D+P+B)&&b.late<=1.5*D,"root endpoint linear bounds");
   ok(b.rank<=1.5*last.rb*(D+P+2*B),"root rank window bound");rootGateChecks++;
 }
 ok(rankOrigin+rankTerminal+rankDeleted+dominantDeleted+keptProxy===highR,"macro proxy priority ledger");
 ok(rankOriginActual+rankTerminalActual+rankDeletedActual+dominantActual+keptActual===keepTime,"macro actual priority ledger");
 ok(dominantDeleted<=delta*R+1e-6&&postPairs<=preOldPairs&&postEnergy<=through,"global dominant linear and long energy");
 return {X,mode,B,baseP,P,z,j,D,T,N,G,R,eps,eta,minLen,rank,delta,rankChecks,rankThresholds,rankCrossChecks,maxRank,maxBin,rankGateChecks,rootGateChecks,rankOrigin,rankTerminal,rankDeleted,dominantDeleted,rankOriginActual,rankTerminalActual,rankDeletedActual,dominantActual,keptProxy,keptActual,preDominant,preRecentPairs,preOldPairs,postPairs,postEnergy,postFibres,domNonzero,maxForeign,oldPartnerChecks,eligible,dominantChecks,retainedPairKeys:newGroupPairs.size,rawHighR,rawHighTime,cheapTime,cheapProxy,rankTime,rankProxy,sparseTime,sparseProxy,keepTime,highR,events,highHits,literal,blocks,nonempty,keepBlocks,rankLabels,quotientChecks,quotientCandidates,witnesses,coverIntervals,coverLen,coverTime,unionGain,bruteIntervals,bruteBlocks,liveIntervals,minLiveLabels:Number.isFinite(minLiveLabels)?minLiveLabels:0,maxLiveLabels,uniformSequenceChecks,fullBlockDenseChecks,gridCount,edgeGridChecks,wideEdges,groups:groups.size,throughTags,tagMass,maxN,maxA,thickGroups,full,short,late,through,pairHits,shortPairs,latePairs,birthChecks,blockMassChecks,groupPairs,uniformChecks,thin,heavy,excess,heavyExcess,positive,maskMass,maskedChecks,subsetChecks,maskedExcessSmall};
}

const argv=process.argv.slice(2); const mode=argv[0]||'diagnostic'; const P=Number(argv[1]||30), j=Number(argv[2]||2); const xs=argv.slice(3).map(Number); for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144])) console.log(JSON.stringify(audit(X,mode,P,j)));
