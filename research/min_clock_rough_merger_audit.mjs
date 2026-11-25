// Rough mixed-high reset and same-high two-step merger caps after direct quotas.
// Run node research/min_clock_rough_merger_audit.mjs 1024 4096 16384 65536
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


 const P=Math.ceil(B/(mode==='analytic'?u**.125:mode==='stress'?32:mode==='wide'?8:4)),ratio=mode==='analytic'?u**.125:mode==='stress'?4:2,
 caps=mode==='analytic'?[u**4.75,u**6.75,u**7.75,u**5.75]:mode==='wide'?[4,8,16,12]:[2,4,8,6];
 const exp=(J,p)=>r[(J-p+1)/2]>=p/ratio;
 const envelope=Array.from({length:4},()=>new Set()),stateKey=(t,J)=>t+':'+J;
 let residueTests=0,mixedLabelPairs=0,oneExpPairs=0,bothExpPairs=0,prevHorizonCount=0,sameCandidateKeys=0;
 for(let J=2*X;J<7*X;J+=2)for(const side of [0,1]){
  const n=J+2*side,t=(J+6*side)/2;if(t%2!==side)continue;
  const ps=[];fac(n,p=>{if(p>=P)ps.push(p);});
  for(let i=0;i<ps.length;i++)for(let j=i+1;j<ps.length;j++){
   const p=ps[i],q=ps[j],k=n/(p*q),eps=side?-2:2;
   ok(Number.isInteger(k)&&k>0&&k<= (7*X+2)/(P*P),'reset cofactor');
   const e=exp(J,p),f=exp(J,q),cl=e&&f?2:e||f?1:0;
   // Independent arithmetic envelope sets are nested, for the three upper bounds.
   envelope[0].add(stateKey(t,J));mixedLabelPairs++;
   if(e||f){envelope[1].add(stateKey(t,J));oneExpPairs++;}
   if(e&&f){envelope[2].add(stateKey(t,J));bothExpPairs++;}
   for(const [a,b] of [[p,q],[q,p]])if(exp(J,a)){
    const D=J-a+1;
    ok(a*(k*b-1)===D+(side?1:-1)&&a*(k*b-1)+eps===D+(side?-1:1),'three forms');
    if(exp(J,b))ok((k*a-1)*b+eps===(J-b+1)+(side?-1:1),'fourth form');
    for(const l of [5,7,11,13,17,19,23,29,31,37,41,43]){
     if(l>=Math.min(a,b,a/ratio)||k%l===0||a%l===0||(a-eps)%l===0)continue;
     const forms=x=>[x,k*x-1,a*(k*x-1)+eps];
     let n3=0,n4=0;
     for(let x=0;x<l;x++){const fs=forms(x);if(fs.some(v=>v%l===0))n3++;if([...fs,(k*a-1)*x+eps].some(v=>v%l===0))n4++;}
     ok(n3===3,'three residue roots');residueTests++;
     if(exp(J,b)&& (k*a-1)%l!==0&&(k*a-1+eps*k)%l!==0&&(k*a*a+eps-a)%l!==0){ok(n4===4,'four residue roots');residueTests++;}
    }
   }
  }
 }
 for(let D=2*X;D<7*X;D+=2){
  let has=false;for(const n of [D,D+2])fac(n,q=>{if(q>=P)has=true;});
  if(!has)continue;prevHorizonCount++;
  for(const side of [0,1])fac(D+(side?1:-1),p=>{
   if(p<P||r[D/2]<p/ratio)return;
   const J=D+p-1;if(J>=7*X)return;
   const res=side?p+2:0,mod=2*p,t0=Math.ceil(J/2),t1=Math.floor((J+12*B+6)/2);
   for(let t=t0+(res-t0%mod+mod)%mod;t<=t1;t+=mod){envelope[3].add(stateKey(t,J));sameCandidateKeys++;}
  });
 }
 const results=[];
 for(const sector of [0,1]){
  const m=sector===0?mM:mH,mLL=sector===1&&mode==='analytic'?Math.floor(u**2):m,accept=e=>sector===0?e.p>z&&e.p<=T:e.p>T;
  const levels=mode==='analytic'?(sector===0?Math.floor(Math.log2(B)/8):Math.floor(Math.log2(u)/4)):2;
  const scales=Array.from({length:levels+1},(_,j)=>Math.max(1,Math.floor(B/2**j)));
  const schemes=[{name:'global',type:'global'},...scales.flatMap(d=>scales.map(D=>({name:'local '+d+'/'+D,type:'local',d,D}))),...scales.map(d=>({name:'incoming '+d,type:'incoming',d}))];
  const arith=Array.from({length:4},(_,i)=>({cap:caps[i],raw:0,rawCapEnergy:0,rawCapRest:0,maxRawProduct:0,residualBefore:0,extra:0,rest:0,incidences:0,residualInc:0,vertices:new Set(),suffix:new Map(),maxProduct:0}));let nonreset=0,nonresetResidual=0,arithExtra=0,priorQuotaRest=0;
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
    const a0=paths[tags[i].i],b0=paths[tags[j].i];let a=0,b=0,J=-1,F=-1,pi=0,pj=0,fi=0,fj=0,ft=0,ai=0,bi=0;
    while(a<a0.length&&b<b0.length&&a0[a].C<=C&&b0[b].C<=C){
     const x=a0[a],y=b0[b];prefixChecks++;
     if(x.C<y.C){a++;continue;}if(y.C<x.C){b++;continue;}
     if(J<0){J=x.C;pi=x.inc;pj=y.inc;ok(pi!==pj,'first direct projected incoming labels differ');}
     if(x.t===y.t&&F<0){F=x.C;ft=x.t;fi=x.inc;fj=y.inc;ai=a>0?a0[a-1].inc:0;bi=b>0?b0[b-1].inc:0;}
     if(J>=0&&(F>=0||tags[i].t!==tags[j].t))break;
     a++;b++;
    }
    ok(J>=0&&J<=C,'direct cohort contact');const sync=tags[i].t===tags[j].t;
    ok(!sync||F>=J&&F<=C,'physical first meeting');
    // Unsynchronized tags cannot have a previous physical meeting, by determinism
    // through the shared final C; scan entire common prefix in the independent
    // physical forest below as well.
    const e=2*q*w[i]*w[j],id=idx(i,j),p={i,j,id,J,F,ft,pi,pj,fi,fj,ai,bi,sync,e};
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

   const batches=new Map();
   for(const p of pairs){
    priorQuotaRest+=(1-coverage[p.id])*p.e;
    if(!p.sync||p.fi<P||p.fj<P)continue;
    let cl=-1;
    if(p.fi!==p.fj){
     const side=p.ft%2,delta=2*p.ft-p.F,eps=6*side;
     ok(delta>=0&&delta<=12*B+6&&(delta-eps)%(2*p.fi*p.fj)===0,'mixed incoming phase');
     if(delta!==eps){nonreset++;nonresetResidual+=(1-coverage[p.id])*p.e;continue;}
     cl=exp(p.F,p.fi)&&exp(p.F,p.fj)?2:exp(p.F,p.fi)||exp(p.F,p.fj)?1:0;
    }else if(exp(p.F,p.fi)&&(p.ai>=P||p.bi>=P)){
     cl=3;const D=p.F-p.fi+1;
     ok((p.ai>=P&&(D%p.ai===0||(D+2)%p.ai===0))||(p.bi>=P&&(D%p.bi===0||(D+2)%p.bi===0)),'previous high divides predecessor');
    }
    if(cl<0)continue;const key=stateKey(p.ft,p.F);
    ok(envelope[cl].has(key),'actual merger in independent arithmetic envelope');
    const a=arith[cl];a.raw+=p.e;a.incidences++;a.vertices.add(key);
    const id=cl+':'+key;let row=batches.get(id);if(!row){row={cl,key,list:[],mass:0,rawMass:0};batches.set(id,row);}
    row.list.push(p);row.rawMass+=p.e/q;row.mass+=(1-coverage[p.id])*p.e/q;
   }
   for(const row of batches.values()){
    const a=arith[row.cl];a.maxProduct=Math.max(a.maxProduct,row.mass);a.maxRawProduct=Math.max(a.maxRawProduct,row.rawMass);a.rawCapEnergy+=q*Math.min(a.cap,row.rawMass);a.rawCapRest+=q*Math.max(0,row.rawMass-a.cap);
    a.residualBefore+=q*row.mass;
    const old=a.suffix.get(row.key)||0;a.suffix.set(row.key,old+q);
    const frac=row.mass>0?Math.min(1,a.cap/row.mass):0;
    let paid=0;
    for(const p of row.list){const rem=1-coverage[p.id],extra=rem*frac*p.e;paid+=extra;coverage[p.id]+=rem*frac;
     const left=(1-coverage[p.id])*p.e;a.rest+=left;a.residualInc+=+(left>1e-8);}
    ok(paid<=q*a.cap+1e-6*Math.max(1,paid),'pointwise rare vertex cap');a.extra+=paid;arithExtra+=paid;
   }
   for(const p of pairs){const v=(1-coverage[p.id])*p.e;rest+=v;if(v>1e-8){residualInc++;ok(beforeCertificate[p.id]===schemes.length&&afterCertificate[p.id]===schemes.length,'both orders all schemes residual certificate');rankCertificate+=2*schemes.length;}if(form[p.id]===1)lightLightAfter+=v;if(p.sync)syncRest+=v;else asyncRest+=v;if(form[p.id]===2)lightHeavyAfter+=v;if(form[p.id]===3)heavyHeavyAfter+=v;}
  }
  const eps=1e-6*Math.max(1,E);
  for(const s of info)ok(s.projEnergy<=s.projBudget+eps&&s.physEnergy<=s.physBudget+eps&&s.unionEnergy<=s.projEnergy+s.physEnergy+eps,'direct quota energy');
  ok(Math.abs(E-diag-prior-globalExtra-localExtra-incomingExtra-reverseExtra-arithExtra-rest)<=eps,'disjoint energy identity');
  ok(Math.abs(rest-syncRest-asyncRest)<=eps&&Math.abs(rest-lightLightAfter-lightHeavyAfter-heavyHeavyAfter)<=eps,'residual types');
  for(const a of arith){for(const s of a.suffix.values())ok(s<=1.5*G,'physical suffix sum r bound');ok(a.extra<=a.cap*[...a.suffix.values()].reduce((x,y)=>x+y,0)+eps&&a.rawCapEnergy<=a.cap*[...a.suffix.values()].reduce((x,y)=>x+y,0)+eps,'arithmetic vertex cap');ok(Math.abs(a.raw-a.rawCapEnergy-a.rawCapRest)<=eps,'independent raw cap partition');}
  ok(Math.abs(priorQuotaRest-arithExtra-rest)<=eps,'additional rare merger partition');
  results.push({sector,m,mLL,scales,priorQuotaRest,arithExtra,nonreset,nonresetResidual,arith:arith.map(({vertices,suffix,...a})=>({...a,vertices:vertices.size,maxSuffix:Math.max(0,...suffix.values())})),E,R:R1,diag,prior,priorProj,priorPhys,priorOverlap,globalExtra,localExtra,incomingExtra,reverseExtra,rest,residualInc,rankCertificate,lightLightAfter,syncRest,asyncRest,rawPairInc,physPairInc,prefixChecks,cohorts,maxMass,projectedEarlier,lightHeavyBefore,lightHeavyAfter,heavyHeavyBefore,heavyHeavyAfter,info});
 }
 return {X,B,mode,z,L,T,mH,mM,P,ratio,caps,envelope:envelope.map(x=>x.size),residueTests,mixedLabelPairs,oneExpPairs,bothExpPairs,prevHorizonCount,sameCandidateKeys,N,events,literal,twins,R,RM,RH,results};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','wide','stress'])console.log(JSON.stringify(audit(X,mode)));
