// Projected first-connectivity forest (two overlapping root block partitions).
// Run node research/min_clock_projected_union_forest_audit.mjs 1024 4096 16384 65536
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
 const block=(i,shift)=>Math.floor((1+2*i+shift*W/2)/W);
 const horizons=[...at.keys()].sort((a,b)=>a-b);
 const forest=[];
 for(let shift=0;shift<2;shift++){
  const par=Array.from({length:N},(_,i)=>i),node=Array.from({length:N},(_,i)=>i),size=Array(N).fill(1);
  const up=Array(N).fill(-1),ns=Array(N).fill(1),birth=paths.map(p=>p[0].C),child=Array(N).fill(null);
  function find(i){let j=i;while(par[j]!==j)j=par[j];while(par[i]!==i){const k=par[i];par[i]=j;i=k;}return j;}
  const stat=[mH,mM].map(m=>({m,smallPairs:0,normalLight:0,rareLight:0,largeLightTags:0,heavyBirths:0,heavyBranch:0,lightAttach:0,allPairs:0,heavyLight:0,heavyHeavy:0,potential:0}));
  const ff=(n,m)=>n<=m?n*n:2*m*n-m*m;
  let merges=0,rootMerges=0,labelsChecked=0,maxArity=0,rareMerges=0,indirectWitness=0;
  for(const C of horizons){const by=new Map();for(const e of at.get(C)){const b=block(e.i,shift);let a=by.get(b);if(!a){a=[];by.set(b,a);}a.push(e);}
   ok(by.size<=2,'horizon root block support');
   for(const es of by.values()){
    const cs=new Map(),ls=new Map();
    for(const e of es){const j=find(e.i);if(ls.has(e.inc))ok(ls.get(e.inc)===j,'same incoming label already connected');else ls.set(e.inc,j);if(!cs.has(j))cs.set(j,e);labelsChecked++;}
    if(cs.size<2)continue;
    const roots=[...cs.keys()],ch=roots.map(j=>node[j]),s=roots.reduce((a,j)=>a+size[j],0),ss=roots.reduce((a,j)=>a+size[j]**2,0);
    ok(cs.size<=degrees[C/2]+1,'distinct component incoming witness labels');
    maxArity=Math.max(maxArity,cs.size);merges++;rareMerges+=+(degrees[C/2]+1>D0);rootMerges+=+ls.has(0);indirectWitness+=s-es.length>0?1:0;
    for(const v of stat){const m=v.m,light=roots.filter(j=>size[j]<m),l=light.reduce((a,j)=>a+size[j],0),l2=light.reduce((a,j)=>a+size[j]**2,0),h=s-l,h2=ss-l2,nh=roots.length-light.length;
     const ll=(l*l-l2)/2,lh=l*h,hh=(h*h-h2)/2;
     v.allPairs+=(s*s-ss)/2;v.heavyLight+=lh;v.heavyHeavy+=hh;v.potential+=ff(s,m)-roots.reduce((a,j)=>a+ff(size[j],m),0);
     if(s<m)v.smallPairs+=ll;
     else{v.largeLightTags+=l;if(degrees[C/2]+1>D0)v.rareLight+=ll;else v.normalLight+=ll;if(!nh)v.heavyBirths++;else{v.heavyBranch+=nh-1;v.lightAttach+=l;}}
    }
    const nd=ns.length;ns.push(s);birth.push(C);child.push(ch);up.push(-1);for(const n of ch){ok(up[n]===-1,'forest child');up[n]=nd;}
    const j=roots.reduce((a,b)=>size[a]>=size[b]?a:b);for(const k of roots)if(k!==j)par[k]=j;size[j]=s;node[j]=nd;
   }
  }
  const depth=new Int32Array(ns.length);for(let j=ns.length-1;j>=0;j--)if(up[j]>=0)depth[j]=depth[up[j]]+1;
  const lift=[Int32Array.from(up)];for(let b=1;(1<<b)<=ns.length;b++){const prev=lift[b-1];lift.push(Int32Array.from(prev,x=>x<0?-1:prev[x]));}
  function climb(j,d){for(let b=0;d;b++,d>>=1)if(d&1)j=lift[b][j];return j;}
  function pair(i,j){
   ok(find(i)===find(j),'contact pair connected');
   let a=i,b=j;if(depth[a]>depth[b])a=climb(a,depth[a]-depth[b]);else if(depth[b]>depth[a])b=climb(b,depth[b]-depth[a]);
   // Leaves cannot be ancestors of each other, but aligned nodes can coincide.
   let l;
   if(a===b)l=a;else{for(let k=lift.length-1;k>=0;k--)if(lift[k][a]!==lift[k][b]){a=lift[k][a];b=lift[k][b];}l=up[a];}
   ok(l>=N,'distinct leaves LCA');
   const ca=climb(i,depth[i]-depth[l]-1),cb=climb(j,depth[j]-depth[l]-1);ok(ca!==cb&&up[ca]===l&&up[cb]===l,'LCA immediate children');
   return {C:birth[l],a:ns[ca],b:ns[cb],n:ns[l]};
  }
  const allRoots=[];for(let i=0;i<N;i++)if(find(i)===i)allRoots.push(node[i]);
  for(const v of stat){const m=v.m;
   ok(v.allPairs===allRoots.reduce((s,j)=>s+ns[j]*(ns[j]-1)/2,0),'all pair formation');
   ok(v.allPairs===v.smallPairs+v.normalLight+v.rareLight+v.heavyLight+v.heavyHeavy,'tree pair partition');
   ok(v.smallPairs<=N*m/2&&v.largeLightTags<=N&&v.normalLight<=D0*m*N/2,'light pair budget');
   ok(v.rareLight<=rareMerges*(maxDegree*m)**2/2,'rare light bound');
   ok(v.heavyBirths<=N/m&&v.heavyBranch<=v.heavyBirths&&v.lightAttach<=N,'heavy formation budget');
   ok(v.potential===allRoots.reduce((s,j)=>s+ff(ns[j],m),0)-N&&v.potential<=2*m*N,'potential telescoping');
  }
  forest.push({shift,merges,rootMerges,labelsChecked,maxArity,rareMerges,indirectWitness,nodes:ns.length,components:allRoots.length,stat,pair});
 }
 let E=0,EM=0,EH=0,diag=0,diagM=0,diagH=0,allPairs=0,earlier=0,indirectEnergy=0,sync=0,async=0,shift1=0;
 const energyM=[0,0,0],energyH=[0,0,0],energyAll=[0,0,0],countsM=[0,0,0],countsH=[0,0,0],countsAll=[0,0,0];
 const cls=(p,m)=>p.a<m&&p.b<m?0:p.a>=m&&p.b>=m?2:1;
 for(let j=lo;j<=hi;j++){E+=r[j]*W0[j]**2;EM+=r[j]*WM[j]**2;EH+=r[j]*WH[j]**2;}
 for(const path of paths){const seen=new Map();for(const e of path){
   const q=r[e.C/2];diag+=q*e.w**2;if(e.p>z&&e.p<=T)diagM+=q*e.w**2;if(e.p>T)diagH+=q*e.w**2;
   for(const b of at.get(e.C)){if(b.i>=e.i)break;let v=seen.get(b.i);
    if(!v){const sh=block(e.i,0)===block(b.i,0)?0:1;ok(block(e.i,sh)===block(b.i,sh),'two block cover');const p=forest[sh].pair(e.i,b.i);
     ok(p.C<=e.C,'first connectivity no later than direct contact');
     v={p,cm:cls(p,mM),ch:cls(p,mH),first:e.C,m:false,h:false,w:0};seen.set(b.i,v);allPairs++;earlier+=+(p.C<e.C);shift1+=sh;countsAll[v.ch]++;
    }
    const w=2*q*e.w*b.w;v.w+=w;ok(v.w<=2*B+1e-6,'whole pair cost');
    energyAll[v.ch]+=w;if(v.p.C<v.first)indirectEnergy+=w;if(e.t===b.t)sync+=w;else async+=w;
    if(e.p>z&&e.p<=T&&b.p>z&&b.p<=T){energyM[v.cm]+=w;if(!v.m){countsM[v.cm]++;v.m=true;}}
    if(e.p>T&&b.p>T){energyH[v.ch]+=w;if(!v.h){countsH[v.ch]++;v.h=true;}}
   }
  }}
 const tol=1e-7*Math.max(1,E);
 ok(Math.abs(E-diag-energyAll.reduce((a,b)=>a+b,0))<=tol&&Math.abs(E-diag-sync-async)<=tol,'whole energy oracle');
 ok(Math.abs(EM-diagM-energyM.reduce((a,b)=>a+b,0))<=tol&&Math.abs(EH-diagH-energyH.reduce((a,b)=>a+b,0))<=tol,'sector energy oracle');
 for(const [i,c,e] of [[0,countsH,energyH],[1,countsM,energyM],[0,countsAll,energyAll]]){const bound=forest.reduce((s,f)=>s+f.stat[i].smallPairs+f.stat[i].normalLight+f.stat[i].rareLight,0);ok(c[0]<=bound&&e[0]<=2*B*bound+tol,'sector whole light-light bound');}
 return {X,B,mode,z,L,T,mH,mM,D0,rare,maxDegree,N,events,literal,twins,R,RM,RH,E,EM,EH,diag,diagM,diagH,allPairs,earlier,indirectEnergy,sync,async,shift1,countsAll,countsM,countsH,energyAll,energyM,energyH,forest:forest.map(({pair,...f})=>f)};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','wide'])console.log(JSON.stringify(audit(X,mode)));
