// Reproduce: node research/min_prime_root_projected_anchor_tail_audit.mjs
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),l=Math.log(u),analytic=mode==="gain",T=analytic?Math.floor(X/u**.25):mode==="short"?B:4*B,Qh=Math.ceil(B/u),Q=analytic?Math.max(5,Qh):Math.max(5,Math.ceil(B/4)),V=analytic?Math.max(5,Math.ceil(B*Math.exp(-Math.sqrt(u)))):Math.max(5,Math.ceil(B/8)),A=analytic?Math.max(2,Math.floor(B**.25)):Math.max(2,Math.floor(B/8)),Kd=analytic?B*u**1.25/A:mode==="tight"?8:64,Ka=analytic?B*u**.75/A:mode==="tight"?4:32,Ks=analytic?B*Math.sqrt(u):mode==="tight"?8:64;
 const low=2*X-2,hi=7*X,lim=hi+5,ok=(b,m)=>{if(!b)throw Error(m);},mod=(a,m)=>((a%m)+m)%m,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c;}return a;};
 const spf=new Int32Array(lim+1);for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)if(!spf[j])spf[j]=n;}
 const fs=n=>{let a=[];while(n>1){let p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const horizons=new Map(),anchors=new Map(),roots=new Map(),key=(D,p)=>D+":"+p;
 let N=0,R=0,G=0,events=0,visits=0,literal=0,cross=0,twins=0,anchorHits=0;
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){
   N++;let C=2*M-2,t=M+2,cut=Math.floor((7*M-1)/4),a=[],last=null,cost=0;
   while(true){
     const e={M,C,t,last,p:0,r:0};a.push(e);if(!horizons.has(C))horizons.set(C,[]);horizons.get(C).push(e);visits++;
     if(C-(2*M-2)>=T){cross++;break;}
     let tt=Infinity,p=Infinity;
     for(const sg of [-1,1])for(const q of fs(C+sg)){let tick=t+1+mod((sg===-1?0:q+2)-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;}}
     if(X<=1024){let lt=Infinity,lp=Infinity;for(let s=t+1;s<=cut;s++){const f=fs(gcd(s%2?s-2:s,C+(s%2?1:-1)));if(f.length){lt=s;lp=f[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal");literal++;}
     if(tt>cut){if(spf[C-1]===C-1&&spf[C+1]===C+1)twins++;break;}
     const r=Math.min(...fs(C-1),...fs(C+1));ok(r<=p&&tt-t<=2*r,"clock");e.p=p;e.r=r;cost+=r;events++;t=tt;C+=p-1;ok(C<=2*t,"horizon");
     if(p>=V){const k=key(C,p);if(!anchors.has(k))anchors.set(k,{D:C,p,ms:[]});last=anchors.get(k);last.ms.push(M);anchorHits++;ok(C%p===0||(C+2)%p===0,"post divisor");}
   }
   const gain=C-(2*M-2);R+=cost;G+=gain;ok(gain<T+B&&2*cost<=3*gain,"gain budget");
   let tail=0;for(let i=a.length-1;i>=0;i--){if(a[i].p>=Qh)tail+=a[i].r;a[i].tail=tail;}
   roots.set(M,{a,end:C,vis:new Set(a.map(e=>e.C))});
 }
 function tail(M,C){let a=roots.get(M).a,lo=0,hi=a.length;while(lo<hi){let m=(lo+hi)>>1;if(a[m].C<C)lo=m+1;else hi=m;}return lo<a.length?a[lo].tail:0;}
 const groups=new Map();let groupChecks=0,filterReduction=0,tailReduction=0,capNew=0,largestProduct=0;
 function group(a,b){
   if(a.D>b.D||(a.D===b.D&&a.p>b.p))[a,b]=[b,a];const id=key(a.D,a.p)+"|"+key(b.D,b.p);if(groups.has(id))return groups.get(id);
   const cls=a.p===b.p?2:a.p>=Q&&b.p>=Q?0:1,cap=[Kd,Ka,Ks][cls],J=b.D;
   const aa=a.ms.filter(M=>roots.get(M).end>=J),bb=b.ms.filter(M=>a.D===b.D||!roots.get(M).vis.has(a.D));
   const sa=aa.reduce((s,M)=>s+tail(M,J),0),sb=bb.reduce((s,M)=>s+tail(M,J),0),raw=a.ms.length*b.ms.length,filtered=aa.length*bb.length,ub=2*Math.min(bb.length*sa,aa.length*sb);
   ok(ub<=3*(T+B)*filtered&&filtered<=raw,"tail cap");if(a.p===b.p&&a.p>A+2)ok(Math.abs(a.D-b.D)===2,"same shifted");
   if(filtered<raw)filterReduction++;if(ub<3*(T+B)*filtered)tailReduction++;
   const eligible=ub<=3*(T+B)*cap;if(eligible&&raw>cap)capNew++;largestProduct=Math.max(largestProduct,raw);
   const v={a,b,aa:new Set(aa),bb:new Set(bb),cls,cap,raw,filtered,ub,eligible,energy:0,n:0,rawNew:0};groups.set(id,v);groupChecks++;return v;
 }
 // Independent finite arithmetic envelope: each (D,p) is deduplicated, count unordered close projected keys.
 const cand=[];for(let D=low;D<=hi;D+=2){for(const p of [...fs(D),...fs(D+2)])if(p>=V)cand.push({D,p});}
 let envelope=[0,0,0];for(let i=0;i<cand.length;i++)for(let j=i+1;j<cand.length&&cand[j].D-cand[i].D<=A;j++){let a=cand[i],b=cand[j];if(Math.max(a.p,b.p)<Q)continue;envelope[a.p===b.p?2:a.p>=Q&&b.p>=Q?0:1]++;}
 const seen=new Map(),first=[0,0,0,0,0,0,0],energy=[0,0,0,0,0,0,0],eligibleGroups=[0,0,0],allGroups=[0,0,0];let E=0,diag=0,pairs=0,closePairs=0,deepClose=0,sameLag=0,rawNewPairs=0,rawNewEnergy=0,bothThick=0,bothThickEnergy=0,unfilteredBound=0,filteredBound=0,tailBound=0;
 for(const C of [...horizons.keys()].sort((a,b)=>a-b)){
   const es=horizons.get(C),full=es.filter(e=>e.p>=Qh);if(full.length){const r=full[0].r;ok(full.every(e=>e.r===r),"r common");diag+=r*full.length;E+=r*full.length**2;}
   for(let i=0;i<es.length;i++)for(let j=i+1;j<es.length;j++){
     const a=es[i],b=es[j],id=(Math.min(a.M,b.M)-X)*X+Math.max(a.M,b.M)-X;let v=seen.get(id);
     if(!v){pairs++;let g=null,cl=6,rawNew=false,thick=false;if(a.last&&b.last){ok(a.last!==b.last,"distinct projected keys");if(Math.max(a.last.p,b.last.p)>=Q&&Math.abs(a.last.D-b.last.D)<=A){
       closePairs++;g=group(a.last,b.last);let ma=a.last===g.a?a.M:b.M,mb=a.last===g.a?b.M:a.M;ok(g.aa.has(ma)&&g.bb.has(mb),"first contact prefix exclusion");g.n++;if(C-Math.max(a.last.D,b.last.D)>B)deepClose++;cl=g.cls+(g.eligible?0:3);rawNew=g.eligible&&g.raw>g.cap;thick=g.eligible&&Math.min(g.a.ms.length,g.b.ms.length)>4;if(rawNew){rawNewPairs++;g.rawNew++;}if(thick)bothThick++;}}
       v={g,cl,w:0,rawNew,thick,budget:3*Math.min(roots.get(a.M).end-C,roots.get(b.M).end-C)};seen.set(id,v);first[cl]++;
     }
     if(a.p>=Qh&&b.p>=Qh){const n=2*a.r;v.w+=n;energy[v.cl]+=n;ok(v.w<=v.budget,"whole pair budget");if(v.g){v.g.energy+=n;ok(v.g.energy<=v.g.ub,"aggregate anchor group tail budget");}if(v.rawNew)rawNewEnergy+=n;if(v.thick)bothThickEnergy+=n;}
   }
 }
 for(const v of groups.values()){allGroups[v.cls]++;if(v.eligible)eligibleGroups[v.cls]++;ok(v.n<=v.filtered&&v.energy<=v.ub,"aggregate product and energy");unfilteredBound+=3*(T+B)*v.raw;filteredBound+=3*(T+B)*v.filtered;tailBound+=v.ub;}
 ok(allGroups.every((n,i)=>n<=envelope[i])&&first.reduce((s,n)=>s+n,0)===pairs&&E===diag+energy.reduce((s,n)=>s+n,0),"arithmetic envelope and pair oracle");
 return {mode,X,B,T,Qh,Q,V,A,Kd,Ka,Ks,N,R,G,events,visits,literal,cross,twins,anchorHits,anchors:anchors.size,envelope,allGroups,eligibleGroups,groupChecks,filterReduction,tailReduction,capNew,largestProduct,closePairs,deepClose,rawNewPairs,rawNewEnergy,bothThick,bothThickEnergy,unfilteredBound,filteredBound,tailBound,pairs,first,energy,E,diag};
}
const xs=process.argv.slice(2).map(Number);for(const mode of ['short','four','gain','tight'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
