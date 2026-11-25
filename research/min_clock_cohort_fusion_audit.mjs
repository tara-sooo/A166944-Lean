// Destination-weighted cohort fusion, independent projected and physical histories.
// Run node research/min_clock_cohort_fusion_audit.mjs 1024 4096 16384 65536
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
 const mH=mode==='analytic'?Math.max(1,Math.floor(u**2.75)):mode==='diagnostic'?8:16;
 const mM=mode==='analytic'?Math.max(1,Math.floor(B**.625)):mode==='diagnostic'?12:24;
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

 const bySector=[e=>e.p>z&&e.p<=T,e=>e.p>T,e=>e.p>0],ms=[mM,mH,mH],results=[];
 const ff=(n,m)=>n<=m?n*n:2*m*n-m*m;
 for(let sector=0;sector<3;sector++){
  const m=ms[sector],accept=bySector[sector];
  let E=0,R1=0,diag=0,cohorts=0,cohortTags=0,maxMass=0,visits=0,heavy=0;
  const reports=[];
  for(const phys of [false,true]){
   const stat={physical:phys,merges:0,lightSmall:0,lightExtra:0,lightHeavy:0,heavyHeavy:0,smallLabel:0,potential:0,heavyBirths:0,heavyBranch:0,lightAttach:0,largestArity:0,rawArity:0,energy:0,rawPairs:0,rawSync:0,weightedRoots:0,weightedHeavyRoots:0,rawHighMerges:0,exceptional:0,nontrivialCohorts:0};
   let localMax=0;
   for(const [C,row] of at){
    const q=r[C/2],tags=row.filter(e=>e.w>0&&accept(e));if(!tags.length)continue;
    const n=tags.length,weights=tags.map(e=>e.w),mass=weights.reduce((a,b)=>a+b,0),sq=weights.reduce((a,b)=>a+b*b,0);
    if(!phys){E+=q*mass*mass;R1+=q*mass;diag+=q*sq;cohorts++;cohortTags+=n;maxMass=Math.max(maxMass,mass);heavy+=+(mass>=m);}
    if(n<2)continue;stat.nontrivialCohorts++;
    const par=Array.from({length:n},(_,i)=>i),ws=weights.slice(),ns=Array(n).fill(1);
    const hs=new Map();
    for(let j=0;j<n;j++){const e=tags[j];for(const v of paths[e.i]){
     if(v.C>C)break;const key=phys?v.C*U+v.t:v.C;let h=hs.get(key);if(!h){h={C:v.C,t:phys?v.t:0,list:[]};hs.set(key,h);}h.list.push([j,v.inc]);if(!phys)visits++;
    }}
    const order=[...hs.values()].sort((a,b)=>a.C-b.C||a.t-b.t);
    function find(i){let j=i;while(par[j]!==j)j=par[j];while(par[i]!==i){const k=par[i];par[i]=j;i=k;}return j;}
    let eSmall=0,eExtra=0,eLH=0,eHH=0,pot=0,newHeavy=0,hBranch=0,attach=0,allLight=0,allPairs=0,diagFormation=0,smallLabel=0;
    for(const h of order){
     const cs=new Map(),ls=new Map();
     for(const [i,p] of h.list){const j=find(i);if(!phys){if(ls.has(p))ok(ls.get(p)===j,'projected cohort witness label');else ls.set(p,j);}
      if(!cs.has(j))cs.set(j,p);
      else if(phys)ok(cs.get(j)===p,'physical component unique predecessor label at merge');
     }
     if(cs.size<2)continue;
     stat.merges++;stat.largestArity=Math.max(stat.largestArity,cs.size);stat.exceptional+=+(degrees[h.C/2]+1>D0);
     if(!phys)ok(cs.size<=degrees[h.C/2]+1,'cohort arity');
     const roots=[...cs.keys()],s=roots.reduce((a,j)=>a+ws[j],0),s2=roots.reduce((a,j)=>a+ws[j]**2,0),l=roots.filter(j=>ws[j]<m),sl=l.reduce((a,j)=>a+ws[j],0),sl2=l.reduce((a,j)=>a+ws[j]**2,0),sh=s-sl,sh2=s2-sl2,nh=roots.length-l.length;
     const ll=Math.max(0,sl*sl-sl2),lh=2*sl*sh,hh=Math.max(0,sh*sh-sh2);
     allPairs+=s*s-s2;pot+=ff(s,m)-roots.reduce((a,j)=>a+ff(ws[j],m),0);
     if(s<m){eSmall+=ll;}else{eExtra+=ll;allLight+=sl;if(!nh)newHeavy++;else{hBranch+=nh-1;attach+=sl;}}
     eLH+=lh;eHH+=hh;
     // Physical label hierarchy: total mass in each incoming label, no double counting
     // with small total. At physical merges the component already has a common prefix suffix.
     if(phys&&s>=m){const pmap=new Map();for(const j of roots){const p=cs.get(j),v=pmap.get(p)||[0,0];v[0]+=ws[j];v[1]+=ws[j]**2;pmap.set(p,v);}
      for(const [b,c] of pmap.values())if(b<m)smallLabel+=Math.max(0,b*b-c);
     }
     const j=roots.reduce((a,b)=>ws[a]>=ws[b]?a:b);for(const k of roots)if(k!==j)par[k]=j;ws[j]=s;ns[j]=roots.reduce((a,k)=>a+ns[k],0);
    }
    const roots=[];for(let i=0;i<n;i++)if(find(i)===i)roots.push(i);
    const final=roots.reduce((a,j)=>a+ws[j]**2,0)-sq;
    ok(Math.abs(allPairs-final)<=1e-7*Math.max(1,final),'weighted forest exact energy');
    if(!phys)ok(roots.length===1,'all projected cohort members connect by C');
    else{const gr=new Map();for(const e of tags)gr.set(e.t,(gr.get(e.t)||0)+e.w);const expected=[...gr.values()].reduce((a,b)=>a+b*b,0)-sq;ok(Math.abs(final-expected)<=1e-7*Math.max(1,final),'physical energy oracle');}
    ok(Math.abs(eSmall+eExtra+eLH+eHH-final)<=1e-7*Math.max(1,final),'weighted class partition');
    ok(Math.abs(pot-(roots.reduce((a,j)=>a+ff(ws[j],m),0)-weights.reduce((a,w)=>a+ff(w,m),0)))<=1e-7*Math.max(1,pot),'weighted potential');
    ok(eSmall+smallLabel<=pot+1e-7*Math.max(1,pot)&&pot<=2*m*mass+1e-7*Math.max(1,pot),'small total and physical label potential');
    ok(allLight<=mass+1e-7&&newHeavy<=mass/m+1e-7&&hBranch<=newHeavy&&attach<=mass+1e-7,'weighted threshold crossing');
    if(!phys)ok(eExtra<=maxDegree*m*mass+1e-7*Math.max(1,eExtra),'projected extra light-light bound');
    stat.lightSmall+=q*eSmall;stat.lightExtra+=q*eExtra;stat.lightHeavy+=q*eLH;stat.heavyHeavy+=q*eHH;stat.smallLabel+=q*smallLabel;stat.potential+=q*pot;stat.energy+=q*final;
    stat.heavyBirths+=q*newHeavy;stat.heavyBranch+=q*hBranch;stat.lightAttach+=q*attach;stat.weightedRoots+=q*mass;stat.weightedHeavyRoots+=q*allLight;
    localMax=Math.max(localMax,roots.length);
   }
   ok(stat.lightSmall+stat.smallLabel<=2*m*R1+1e-5*Math.max(1,E),'summed weighted bound');
   if(!phys){ok(Math.abs(stat.energy+diag-E)<=1e-7*Math.max(1,E),'projected full energy');ok(stat.lightExtra<=maxDegree*m*R1+1e-5*Math.max(1,E),'extra projected bound');}
   reports.push({...stat,maxFinalComponents:localMax});
  }
  results.push({sector,m,E,R:R1,diag,cohorts,cohortTags,maxMass,heavy,visits,reports});
 }
 return {X,B,mode,z,L,T,mH,mM,maxDegree,N,events,literal,twins,R,RM,RH,results};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','wide'])console.log(JSON.stringify(audit(X,mode)));
