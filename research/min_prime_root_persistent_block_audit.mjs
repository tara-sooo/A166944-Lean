// Independent persistent-block MIN audit; see adjacent research note.
function audit(X,mode="diagnostic",P0=30,j0=2){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),analytic=mode==="analytic",lim=7*X+5;
 const spf=new Int32Array(lim+1);
 const ok=(x,s)=>{if(!x)throw Error(`X=${X},${mode}: ${s}`);};
 const mod=(a,b)=>((a%b)+b)%b, gcd=(a,b)=>{while(b){const t=a%b;a=b;b=t;}return a;},choose=n=>n*(n-1)/2;
 for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n*n<=lim)for(let k=n*n;k<=lim;k+=n)if(!spf[k])spf[k]=n;}
 let P=2,z=2;
 for(let p=3;p<=B;p+=2)if(spf[p]===p){
   if(analytic&&P*p>B*u**1.5)break;
   if(mode==="wide"&&P>B)break;
   if(mode==="diagnostic"&&P*p>P0)break;
   P*=p;z=p;
 }
 if(mode==="diagnostic")ok(P===P0,"diagnostic P must be an even primorial");
 if(mode==="wide")ok(P>B,"wide grid");
 const j=analytic?Math.max(1,Math.floor(B*u**2.5/P)):j0,D=j*P;
 const T=analytic?Math.floor(X/u**.25):mode==="wide"?Math.max(4*B,4*P):4*B,H=T+B;
 const Q=Math.max(5,Math.ceil(B/(analytic?u:8))),m=analytic?Math.floor(B*u**(13/8)):8,c=P*(analytic?B*u**1.5:3/16);
 const fs=n=>{const a=[];while(n>1){const p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const roots=new Map(),hits=new Map(),groups=new Map();
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
   N++;const a=[],byC=new Map(),mass=new Map();let C=2*M-2,t=M+2,cut=Math.floor((7*M-1)/4),gc=0;
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
     e.p=p;e.r=r;R+=r;events++;
     if(p>=Q&&r>p/(analytic?Math.sqrt(Math.log(p)):2)){
       e.h=r;highR+=r;highHits++;
       const K=block(C),hk=`${C}:${t}`;mass.set(K,(mass.get(K)||0)+2*r);
       if(!hits.has(hk))hits.set(hk,[]);hits.get(hk).push(e);
     }
     const ng=ceilDiv(J,P)-ceilDiv(C,P);gc+=ng;edgeGridChecks++;
     if(ng){ok(p>z,"small prime strict crossing");if(P>B){ok(ng===1,"wide edge crosses at most one boundary");wideEdges++;}}
     t=tt;C=J;
   }
   const gain=C-(2*M-2);G+=gain;ok(gain<T+B&&gc===ceilDiv(C,P)-ceilDiv(a[0].C,P)&&gc<=gain/P+1,"root crossing ledger");gridCount+=gc;
   roots.set(M,{a,byC,end:C,mass});
   for(const [K,A] of mass){
     ok(A<=3*(P+B),"natural block occupation");
     const past=crossing(a,K-D),future=crossing(a,K+D);
     if(!past||!future)continue;
     const middle=crossing(a,K);ok(middle,"middle crossing");
     const id=key(K,past);let g=groups.get(id);
     if(!g){g={K,past,middle,future,A,tags:new Set(),loads:new Map(),masked:new Map(),actual:0,maskedTotal:0};groups.set(id,g);}
     ok(g.A===A&&same(g.middle,middle)&&same(g.future,future)&&!g.tags.has(M),"persistent common occupation");
     g.tags.add(M);tagMass+=A;throughTags++;blockMassChecks++;
     // All tags of this group actually complete every strict grid crossing across the span.
     for(let L=K-D;L<=K+D;L+=P)ok(crossing(a,L),"full persistent span");
   }
 }
 ok(gridCount<=G/P+N+1e-8&&throughTags<=gridCount&&tagMass<=2*highR&&2*R<=3*G,"global membership/occupation");
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
 return {X,mode,B,P,z,j,D,T,N,G,R,highR,events,highHits,literal,gridCount,edgeGridChecks,wideEdges,groups:groups.size,throughTags,tagMass,maxN,maxA,thickGroups,full,short,late,through,pairHits,shortPairs,latePairs,birthChecks,blockMassChecks,groupPairs,uniformChecks,thin,heavy,excess,heavyExcess,positive,maskMass,maskedChecks,subsetChecks,maskedExcessSmall};
}

const argv=process.argv.slice(2); const mode=argv[0]||'diagnostic'; const P=Number(argv[1]||30), j=Number(argv[2]||2); const xs=argv.slice(3).map(Number); for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144])) console.log(JSON.stringify(audit(X,mode,P,j)));
