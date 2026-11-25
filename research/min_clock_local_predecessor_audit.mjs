// Nested clock-cell potential and multiscale light-branch graph for same-label physical mergers.
// Run node research/min_clock_local_predecessor_audit.mjs 1024 4096 16384 65536
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,G=2*H+B+6,U=7*X+4,W=16*B,u=Math.log(B),ell=Math.log(u);
 const ok=(b,m)=>{if(!b)throw Error(m);};
 ok(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(U);
 for(let p=2;p<U;p++)if(!spf[p]){spf[p]=p;if(p*p<U)for(let j=p*p;j<U;j+=p)if(!spf[j])spf[j]=p;}
 let z=2,L=2;
 if(mode==='analytic'){for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>B**(1/16))break;L*=p;z=p;}}
 else {z=3;L=6;}
 const T=mode==='analytic'?Math.max(z+1,Math.ceil(B**.25)):Math.ceil(Math.sqrt(B));
 const mH=mode==='analytic'?Math.max(1,Math.floor(u**2.75)):mode==='diagnostic'||mode==='stress'?8:16;
 const mM=mode==='analytic'?Math.max(1,Math.floor(B**.625)):mode==='diagnostic'||mode==='stress'?12:24;
 const D0=mode==='analytic'?Math.ceil(40*ell)+1:4;
 const lo=X,hi=7*X/2-1,len=hi+1,r=new Int32Array(len),degrees=new Uint8Array(len);
 function fac(n,cb){while(n>1){const p=spf[n];if(p>B)break;if(p>2)cb(p);while(n%p===0)n/=p;}}
 let rare=0,maxDegree=0;
 for(let j=lo;j<=hi;j++){const q=Math.min(spf[2*j-1],spf[2*j+1]);if(q<=B)r[j]=q;for(const C of [2*j,2*j+2])fac(C,()=>degrees[j]++);maxDegree=Math.max(maxDegree,degrees[j]+1);rare+=+(degrees[j]+1>D0);}
 function hit(t,C,K){let v=K+1,p=0;for(const side of [-1,1])fac(C+side,q=>{const m=2*q,res=side===-1?0:q+2,w=t+1+(res-(t+1)%m+m)%m;if(w<v||(w===v&&w<=K&&q<p)){v=w;p=q;}});return [v,p];}
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a;};
 const paths=[],at=new Map(),W0=new Float64Array(len),WM=new Float64Array(len),WH=new Float64Array(len);
 let R=0,RM=0,RH=0,events=0,literal=0,twins=0;
 for(let i=0;i<N;i++){const M=X+1+2*i,s=M+2,K=Math.floor((7*M-1)/4),path=[];let t=s,C=2*M-2,inc=0,rr=0;
  for(;;){const e={i,M,C,t,inc,p:0,w:0};path.push(e);let row=at.get(C);if(!row){row=[];at.set(C,row);}row.push(e);
   ok(C<=2*t&&C-(2*M-2)<=G,'prefix gain');
   if(t>=s+H)break;
   const [v,p]=hit(t,C,K);
   if(X===1024){let vv=K+1,pp=0;for(let j=t+1;j<=K;j++){const n=gcd(j%2?j-2:j,j%2?C+1:C-1);if(n>1&&spf[n]<=B){vv=j;pp=spf[n];break;}}ok(v===vv&&p===pp,'literal');literal++;}
   if(!p){ok(!r[C/2]&&spf[C-1]===C-1&&spf[C+1]===C+1,'twin');twins++;break;}
   const q=r[C/2],cost=Math.max(0,Math.min(v,s+H)-Math.max(t,s+a))/2;
   ok(v-t<=2*q&&q<=p,'wait');e.p=p;e.w=cost/q;rr+=cost;R+=cost;W0[C/2]+=e.w;
   if(p>z&&p<=T){RM+=cost;WM[C/2]+=e.w;}if(p>T){RH+=cost;WH[C/2]+=e.w;}
   t=v;C+=p-1;inc=p;events++;
  }
  ok(rr<=B,'root cost');paths.push(path);
 }

 const results=[];
 for(const sector of [0,1]){
  const m=sector===0?mM:mH,mLL=sector===1&&mode==='analytic'?Math.floor(u**2):m,accept=e=>sector===0?e.p>z&&e.p<=T:e.p>T;
  const levels=mode==='analytic'?(sector===0?Math.floor(Math.log2(B)/8):Math.floor(Math.log2(u)/4)):2;
  const scales=Array.from({length:levels+1},(_,j)=>Math.max(1,Math.floor(B/2**j)));
  const schemes=[{name:'global',type:'global'},...scales.flatMap(d=>scales.map(D=>({name:'local '+d+'/'+D,type:'local',d,D}))),...scales.map(d=>({name:'incoming '+d,type:'incoming',d}))];
  let clockExtra=0,graphExtra=0,clockRaw=0,graphRaw=0,eligibleRaw=0,eligibleRestBefore=0,eligibleRestAfter=0,clockChecks=0,graphChecks=0,potentialChecks=0,sourceChecks=0,certificateChecks=0,maxLag=0,maxArity=0,maxClockRatio=0,oldRest=0;const newScale=[];
  let E=0,R1=0,diag=0,prior=0,priorProj=0,priorPhys=0,priorOverlap=0,globalExtra=0,localExtra=0,incomingExtra=0,reverseExtra=0,rest=0,lightLightAfter=0,residualInc=0,rankCertificate=0,asyncRest=0,syncRest=0,rawPairInc=0,physPairInc=0,prefixChecks=0,cohorts=0,maxMass=0,maxResidualPairRank=0,projectedEarlier=0,lightHeavyBefore=0,lightHeavyAfter=0,heavyHeavyBefore=0,heavyHeavyAfter=0;
  const info=schemes.map(s=>({...s,projEnergy:0,physEnergy:0,unionEnergy:0,projBudget:0,physBudget:0,maxUsed:0,partial:0,projPairs:0,physPairs:0}));
  for(const [C,row] of at){
   const q=r[C/2],tags=row.filter(e=>e.w>0&&accept(e)),n=tags.length;if(!n)continue;
   const w=tags.map(e=>e.w),U0=w.reduce((a,b)=>a+b,0),ds=w.reduce((a,b)=>a+b*b,0);
   E+=q*U0*U0;R1+=q*U0;diag+=q*ds;cohorts++;maxMass=Math.max(maxMass,U0);if(n<2)continue;
   const idx=(i,j)=>Math.min(i,j)*n+Math.max(i,j);
   const pairs=[],lists=Array.from({length:n},()=>[]),physLists=Array.from({length:n},()=>[]);
   // Independently intersect literal original prefix paths. Record first direct
   // projected and physical contact, even if neither tag was occupied there.
   for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
    const a0=paths[tags[i].i],b0=paths[tags[j].i];let a=0,b=0,J=-1,F=-1,pi=0,pj=0,fi=0,fj=0,ft=0,ti=0,tj=0;
    while(a<a0.length&&b<b0.length&&a0[a].C<=C&&b0[b].C<=C){
     const x=a0[a],y=b0[b];prefixChecks++;
     if(x.C<y.C){a++;continue;}if(y.C<x.C){b++;continue;}
     if(J<0){J=x.C;pi=x.inc;pj=y.inc;ok(pi!==pj,'first direct projected incoming labels differ');}
     if(x.t===y.t&&F<0){F=x.C;ft=x.t;fi=x.inc;fj=y.inc;ti=a>0?a0[a-1].t:0;tj=b>0?b0[b-1].t:0;}
     if(J>=0&&(F>=0||tags[i].t!==tags[j].t))break;
     a++;b++;
    }
    ok(J>=0&&J<=C,'direct cohort contact');const sync=tags[i].t===tags[j].t;
    ok(!sync||F>=J&&F<=C,'physical first meeting');
    // Unsynchronized tags cannot have a previous physical meeting, by determinism
    // through the shared final C; scan entire common prefix in the independent
    // physical forest below as well.
    const e=2*q*w[i]*w[j],id=idx(i,j),p={i,j,id,J,F,ft,pi,pj,fi,fj,ti,tj,sync,e};
    pairs.push(p);rawPairInc++;if(sync){physPairInc++;if(J<F)projectedEarlier++;}
    lists[i].push({j,id,J,p:pi});lists[j].push({j:i,id,J,p:pj});
    if(sync){physLists[i].push({j,id,J:F,p:fi});physLists[j].push({j:i,id,J:F,p:fj});}
   }
   const prevP=new Uint8Array(n*n),prevS=new Uint8Array(n*n),form=new Uint8Array(n*n);
   // Previous destination cohort light/light and physical small-total/small-label
   // classifications, independently from direct-contact pair order.
   for(const phys of [false,true]){
    const par=Array.from({length:n},(_,i)=>i),mass=w.slice(),members=Array.from({length:n},(_,i)=>[i]),hs=new Map();
    for(let i=0;i<n;i++)for(const v of paths[tags[i].i]){if(v.C>C)break;const key=phys?v.C*U+v.t:v.C;let h=hs.get(key);if(!h){h={C:v.C,t:v.t,list:[]};hs.set(key,h);}h.list.push([i,v.inc]);}
    const order=[...hs.values()].sort((a,b)=>a.C-b.C||a.t-b.t);
    function find(i){let k=i;while(par[k]!==k)k=par[k];while(par[i]!==i){const j=par[i];par[i]=k;i=j;}return k;}
    for(const h of order){
     const cs=new Map();for(const [i,p] of h.list){const k=find(i);if(!cs.has(k))cs.set(k,p);else if(phys)ok(cs.get(k)===p,'physical predecessor label');}
     if(cs.size<2)continue;
     const a=[...cs.keys()],s=a.reduce((x,k)=>x+mass[k],0),label=new Map();
     if(phys)for(const k of a)label.set(cs.get(k),(label.get(cs.get(k))||0)+mass[k]);
     for(let i=0;i<a.length;i++)for(let j=i+1;j<a.length;j++){
      const b=a[i],c=a[j],ll=mass[b]<m&&mass[c]<m;
      for(const x of members[b])for(const y of members[c]){
       const id=idx(x,y);if(!phys){ok(form[id]===0,'unique projected allocation');form[id]=ll?1:mass[b]>=m&&mass[c]>=m?3:2;if(s<=m||mass[b]<mLL&&mass[c]<mLL)prevP[id]=1;}
       else{ok(tags[x].t===tags[y].t,'physical common final time');if(s<=m||cs.get(b)===cs.get(c)&&label.get(cs.get(b))<=m)prevS[id]=1;}
      }
     }
     const k=a.reduce((x,y)=>mass[x]>=mass[y]?x:y);for(const j of a)if(j!==k){par[j]=k;members[k].push(...members[j]);}mass[k]=s;
    }
   }
   const coverage=new Float64Array(n*n),beforeCertificate=new Uint16Array(n*n),afterCertificate=new Uint16Array(n*n);
   for(const p of pairs){ok(form[p.id]>0,'projected forest covers pair');if(prevP[p.id])priorProj+=p.e;if(prevS[p.id])priorPhys+=p.e;if(prevP[p.id]&&prevS[p.id])priorOverlap+=p.e;if(prevP[p.id]||prevS[p.id]){coverage[p.id]=1;prior+=p.e;}if(form[p.id]===2)lightHeavyBefore+=p.e;if(form[p.id]===3)heavyHeavyBefore+=p.e;}
   for(const reverse of [false,true])for(const [ix,scheme] of schemes.entries()){
    const stat=info[ix],local=scheme.type==='local',incoming=scheme.type==='incoming';
    const pc=new Float64Array(n*n),sc=new Float64Array(n*n);
    for(const phys of [false,true]){
     const ls=phys?physLists:lists,cover=phys?sc:pc;
     for(let i=0;i<n;i++){
      const order=ls[i].sort((a,b)=>(reverse?-1:1)*(a.J-b.J||tags[a.j].M-tags[b.j].M)),used=new Map(),limits=new Map();
      let s=0;
      for(const v of order){
       const cell=scheme.d?Math.floor((tags[v.j].M-X)/scheme.d):0;
       const key=local?cell+':'+Math.floor((v.J-2*X)/scheme.D):incoming?cell+':'+v.J:'all';
       const cap=local?m*scheme.d*scheme.D/(B*B):incoming?m*scheme.d*Math.max(1,v.p-1)/(B*B):m;
       if(limits.has(key))ok(limits.get(key)===cap,'same quota key');else limits.set(key,cap);
       const before=used.get(key)||0,part=Math.min(w[v.j],Math.max(0,cap-before)),f=part/w[v.j];
       used.set(key,before+w[v.j]);s+=part;cover[v.id]=Math.max(cover[v.id],f);
       if(part>1e-12&&f<1-1e-12)stat.partial++;
       ok(f>=0&&f<=1+1e-8,'fractional quota');
      }
      const capSum=[...limits.values()].reduce((a,b)=>a+b,0);
      let bound=m;if(local)bound=m*scheme.d*scheme.D/(B*B)*(Math.ceil(G/(2*scheme.d))+2)*(Math.ceil(G/scheme.D)+2);
      if(incoming)bound=m*scheme.d*(G+1)/(B*B)*(Math.ceil(G/(2*scheme.d))+2);
      ok(s<=capSum+1e-7*Math.max(1,capSum)&&capSum<=bound+1e-7*Math.max(1,bound),'per-leaf gain and cell budget');
      stat.maxUsed=Math.max(stat.maxUsed,s);if(phys)stat.physBudget+=2*q*w[i]*s;else stat.projBudget+=2*q*w[i]*s;
     }
    }
    for(const p of pairs){
     const fp=pc[p.id],fs=sc[p.id],f=Math.max(fp,fs),before=coverage[p.id],extra=Math.max(0,f-before)*p.e;
     stat.projEnergy+=fp*p.e;stat.physEnergy+=fs*p.e;stat.unionEnergy+=f*p.e;stat.projPairs+=+(fp>0);stat.physPairs+=+(fs>0);
     if(reverse)reverseExtra+=extra;else if(scheme.type==='global')globalExtra+=extra;else if(local)localExtra+=extra;else incomingExtra+=extra;
     if(f<1-1e-10)(reverse?afterCertificate:beforeCertificate)[p.id]++;
     coverage[p.id]=Math.max(before,f);
    }
   }

   // Full physical prefix lookup. Group weights at each vertex by selected incoming label
   // and predecessor time, then by original source cell. Only same-label first pairs
   // are marked; other physical and asynchronous terms remain.
   const hs=new Map(),same=pairs.filter(p=>p.sync&&p.fi===p.fj&&p.fi>0);
   for(const p of same){const D=p.F-p.fi+1,h=Math.abs(p.ti-p.tj);
    ok(h>0&&h<2*r[D/2]&&p.ft-p.ti<=2*r[D/2]&&p.ft-p.tj<=2*r[D/2],'same-label arrival interval');
    maxLag=Math.max(maxLag,h);eligibleRaw+=p.e;eligibleRestBefore+=(1-coverage[p.id])*p.e;
    const key=p.ft+':'+p.F+':'+p.fi;if(!hs.has(key))hs.set(key,{F:p.F,t:p.ft,p:p.fi,list:[],members:[]});hs.get(key).list.push(p);
   }
   if(hs.size)for(let i=0;i<n;i++)for(let k=1;k<paths[tags[i].i].length;k++){
    const v=paths[tags[i].i][k];if(v.C>C)break;const row=hs.get(v.t+':'+v.C+':'+v.inc);if(row)row.members.push({i,t:paths[tags[i].i][k-1].t});
   }
   const beforeNew=coverage.slice(),cf=new Uint8Array(n*n),gf=new Uint8Array(n*n);
   const f=(x,m)=>x<=m?x*x:2*m*x-m*m;
   const M0=mode==='analytic'?(sector===0?B**.625*u*u:u**3/(1+ell)):mode==='stress'?64:mode==='wide'?24:12;
   for(let j=0;j<scales.length;j++){
    const d=scales[j],md=mode==='analytic'?M0*d/B/(j+1)**2:M0*d/B;
    const byCell=new Map();for(let i=0;i<n;i++){const c=Math.floor((tags[i].M-X)/d);if(!byCell.has(c))byCell.set(c,[]);byCell.get(c).push(i);}
    const K=byCell.size;ok(K<=Math.ceil(G/(2*d))+2,'source cell count');
    if(!newScale[j])newScale[j]={d,md,clockRaw:0,graphRaw:0,clockExtra:0,graphExtra:0,potential:0,clockBound:0,graphBound:0,graphPotentialBound:0,groups:0};
    const st=newScale[j];let potSum=0,clockSum=0,graphSum=0;const gp=new Map(),ge=new Map();
    // Each unordered pair of source cells gets its own restricted cohort; same-cell
    // pairs use the singleton cell. A tag belongs to exactly K such cohorts.
    for(const row of hs.values()){
     const grouped=new Map();
     for(const p of row.list){const a=Math.floor((tags[p.i].M-X)/d),b=Math.floor((tags[p.j].M-X)/d),key=Math.min(a,b)+':'+Math.max(a,b);
      if(!grouped.has(key))grouped.set(key,{a,b,ps:[]});grouped.get(key).ps.push(p);}
     for(const {a,b,ps} of grouped.values()){
      const times=new Map();for(const v of row.members){const c=Math.floor((tags[v.i].M-X)/d);if(c===a||c===b)times.set(v.t,(times.get(v.t)||0)+w[v.i]);}
      const ts=[...times.keys()].sort((a,b)=>a-b),total=[...times.values()].reduce((a,b)=>a+b,0);
      const potential=f(total,md)-[...times.values()].reduce((a,b)=>a+f(b,md),0);
      ok(potential>=-1e-7,'label restricted potential');potSum+=potential;st.groups++;maxArity=Math.max(maxArity,ts.length);
      // For each grid, compute all within-label cross-time products in the smallest
      // shared ternary interval, including pairs not assigned to this cell pair.
      let fullClock=0;
      for(const shift of [0,.5]){
       let paid=0;
       for(let x=0;x<ts.length;x++)for(let y=x+1;y<ts.length;y++){
        let W=1;while(Math.floor(ts[x]/W-shift)!==Math.floor(ts[y]/W-shift))W*=3;
        const k=Math.floor(ts[x]/W-shift);let mass=0;for(const t of ts)if(Math.floor(t/W-shift)===k)mass+=times.get(t);
        if(mass<=md+1e-10)paid+=2*times.get(ts[x])*times.get(ts[y]);
       }
       ok(paid<=potential+1e-7*Math.max(1,potential),'nested clock potential');fullClock+=paid;potentialChecks++;
      }
      let assignedClock=0,assignedGraph=0;
      for(const p of ps){
       const h=Math.abs(p.ti-p.tj),wi=times.get(p.ti),wj=times.get(p.tj);
       ok(wi>=w[p.i]-1e-9&&wj>=w[p.j]-1e-9,'actual branch masses');sourceChecks++;
       let best=Infinity,minWidth=Infinity;
       for(const shift of [0,.5]){
        let W=1;while(Math.floor(p.ti/W-shift)!==Math.floor(p.tj/W-shift))W*=3;
        minWidth=Math.min(minWidth,W);const k=Math.floor(p.ti/W-shift);let mass=0;for(const t of ts)if(Math.floor(t/W-shift)===k)mass+=times.get(t);
        best=Math.min(best,mass);if(mass<=md+1e-10){cf[p.id]=1;}
       }
       ok(minWidth<=6*h+1e-8,'two grid covering width');maxClockRatio=Math.max(maxClockRatio,minWidth/h);clockChecks++;
       if(cf[p.id]&&best<=md+1e-10){assignedClock+=p.e/q;st.clockRaw+=p.e;}
       const k=Math.ceil(Math.log2(h)),Hk=2**k,mu=mode==='analytic'?md/(Hk*(k+1)**2):md/Hk;
       if(wi<=mu+1e-10&&wj<=mu+1e-10){gf[p.id]=1;assignedGraph+=p.e/q;st.graphRaw+=p.e;}
       graphChecks++;
       if(best>md+1e-10&&Math.max(wi,wj)>mu+1e-10)certificateChecks++;
      }
      ok(assignedClock<=fullClock+1e-7*Math.max(1,fullClock),'assigned clock bound');clockSum+=assignedClock;graphSum+=assignedGraph;
      // Independent graph inequality for all dyadic lag bands.
      for(let k=0;2**k<=4*r[(row.F-row.p+1)/2];k++){
       const Hk=2**k,mu=mode==='analytic'?md/(Hk*(k+1)**2):md/Hk;let edges=0,degree=0;
       const ds=new Map();
       for(let x=0;x<ts.length;x++)for(let y=x+1;y<ts.length;y++)if(Math.ceil(Math.log2(ts[y]-ts[x]))===k&&times.get(ts[x])<=mu+1e-10&&times.get(ts[y])<=mu+1e-10){edges+=2*times.get(ts[x])*times.get(ts[y]);ds.set(ts[x],(ds.get(ts[x])||0)+1);ds.set(ts[y],(ds.get(ts[y])||0)+1);}
       degree=Math.max(0,...ds.values());ok(degree<=2*Hk,'lag degree');
       const dp=f(total,mu)-[...times.values()].reduce((a,b)=>a+f(b,mu),0);
       ok(edges<=2*Math.max(0,2*degree-1)*dp+1e-7*Math.max(1,edges),'light graph potential');gp.set(k,(gp.get(k)||0)+dp);ge.set(k,(ge.get(k)||0)+edges);potentialChecks++;
      }
     }
    }
    // Restricted physical forests telescope; only same-label nodes with assigned
    // pairs were included, so their potential is no greater than the full forest.
    ok(potSum<=2*md*K*U0+1e-7*Math.max(1,potSum),'restricted potential summed');
    ok(clockSum<=2*potSum+1e-7*Math.max(1,clockSum),'two grids');
    let gb=0,geSum=0;for(const [k,dp] of gp){const Hk=2**k,mu=mode==='analytic'?md/(Hk*(k+1)**2):md/Hk;ok(dp<=2*mu*K*U0+1e-7*Math.max(1,dp),'restricted graph potential summed');const es=ge.get(k)||0;ok(es<=8*Hk*dp+1e-7*Math.max(1,es),'lag graph summed');gb+=16*Hk*mu*K*U0;geSum+=es;}ok(graphSum<=geSum+1e-7*Math.max(1,geSum),'assigned graph bound');st.graphPotentialBound+=q*gb;st.potential+=q*potSum;st.clockBound+=4*q*md*K*U0;st.graphBound+=q*graphSum;
   }
   for(const p of pairs){
    oldRest+=(1-beforeNew[p.id])*p.e;
    if(cf[p.id]){clockRaw+=p.e;clockExtra+=(1-coverage[p.id])*p.e;coverage[p.id]=1;}
    if(gf[p.id]){graphRaw+=p.e;graphExtra+=(1-coverage[p.id])*p.e;coverage[p.id]=1;}
   }
   for(const p of same)eligibleRestAfter+=(1-coverage[p.id])*p.e;
   for(const p of pairs){const v=(1-coverage[p.id])*p.e;rest+=v;if(v>1e-8){residualInc++;ok(beforeCertificate[p.id]===schemes.length&&afterCertificate[p.id]===schemes.length,'both orders all schemes residual certificate');rankCertificate+=2*schemes.length;}if(form[p.id]===1)lightLightAfter+=v;if(p.sync)syncRest+=v;else asyncRest+=v;if(form[p.id]===2)lightHeavyAfter+=v;if(form[p.id]===3)heavyHeavyAfter+=v;}
  }
  const eps=1e-6*Math.max(1,E);
  for(const s of info)ok(s.projEnergy<=s.projBudget+eps&&s.physEnergy<=s.physBudget+eps&&s.unionEnergy<=s.projEnergy+s.physEnergy+eps,'direct quota energy');
  ok(Math.abs(E-diag-prior-globalExtra-localExtra-incomingExtra-reverseExtra-clockExtra-graphExtra-rest)<=eps,'disjoint energy identity');
  ok(Math.abs(rest-syncRest-asyncRest)<=eps&&Math.abs(rest-lightLightAfter-lightHeavyAfter-heavyHeavyAfter)<=eps,'residual types');
  ok(Math.abs(oldRest-clockExtra-graphExtra-rest)<=eps&&Math.abs(eligibleRestBefore-clockExtra-graphExtra-eligibleRestAfter)<=eps,'new disjoint ledger');
  results.push({sector,m,mLL,scales,oldRest,clockExtra,graphExtra,clockRaw,graphRaw,eligibleRaw,eligibleRestBefore,eligibleRestAfter,clockChecks,graphChecks,potentialChecks,sourceChecks,certificateChecks,maxLag,maxArity,maxClockRatio,newScale,E,R:R1,diag,prior,priorProj,priorPhys,priorOverlap,globalExtra,localExtra,incomingExtra,reverseExtra,rest,residualInc,rankCertificate,lightLightAfter,syncRest,asyncRest,rawPairInc,physPairInc,prefixChecks,cohorts,maxMass,projectedEarlier,lightHeavyBefore,lightHeavyAfter,heavyHeavyBefore,heavyHeavyAfter,info});
 }
 return {X,B,mode,z,L,T,mH,mM,N,events,literal,twins,R,RM,RH,results};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','wide','stress'])console.log(JSON.stringify(audit(X,mode)));
