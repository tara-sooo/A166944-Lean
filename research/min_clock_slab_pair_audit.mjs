// Canonical MIN short-slab middle-pair categories, fast-high/LOW removal.
// Run: node research/min_clock_slab_pair_audit.mjs 1024 4096 16384 65536 262144
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)), H=4*B,a=2*B,N=X/2,d=Math.floor(4*Math.log(B));
 const z=Math.max(1,Math.floor(Math.sqrt(Math.log(B)))),z2=Math.floor(Math.log(B)**1.5),Q=Math.ceil(B/Math.sqrt(Math.log(B)));
 const check=(x,m)=>{if(!x)throw Error(m)};
 const spf=new Int32Array(7*X+4);
 for(let p=2;p<spf.length;p++)if(!spf[p]){
  spf[p]=p;if(p*p<spf.length)for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 }
 let L=2,y=2;
 for(let p=3;p<=B;p+=2)if(spf[p]===p){
  if(L*p>6*Math.sqrt(Math.log(B)))break;L*=p;y=p;
 }
 check(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix cutoff gate');
 const r=new Int32Array(7*X/2+1),lists=new Map(),paths=X<=4096?new Map():null;
 let S0=0;
 for(let C=2*X;C<7*X;C+=2){const q=Math.min(spf[C-1],spf[C+1]);if(q<=B){r[C/2]=q;S0+=q;}}
 function hit(t,C,K){
  let T=K+1,P=0;
  for(const side of [-1,1]){
   let v=C+side;while(v>1){const p=spf[v];if(p>B)break;
    const m=2*p,res=side===-1?0:p+2,u=t+1+(res-(t+1)%m+m)%m;
    if(p>2&&(u<T||(u===T&&u<=K&&p<P))){T=u;P=p;}
    while(v%p===0)v/=p;
   }
  }return [T,P];
 }
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a};
 let R=0,removedR=0,fastR=0,lowR=0,events=0,slabRecords=0,literal=0,maxBig=0,finished=0,lowBlocks=0;
 const rootCap=Math.floor((H+3)/2)+1;
 for(let M=X+1;M<2*X;M+=2){
  const s=M+2,C0=2*M-2,K=Math.floor((7*M-1)/4),path=[];
  let t=s,C=C0,big=0,rc=0,fc=0,lc=0;
  while(t<s+H){
   const [u,p]=hit(t,C,K),q=r[C/2];
   if(X<=1024){
    let aa=K+1,bb=0;for(let j=t+1;j<=K;j++){const g=gcd(j%2?j-2:j,j%2?C+1:C-1);
     if(g>1&&spf[g]<=B){aa=j;bb=spf[g];break;}}
    check(aa===u&&bb===p,'literal MIN');literal++;
   }
   if(!p){check(!q&&spf[C-1]===C-1&&spf[C+1]===C+1,'terminal twin');finished++;break;}
   check(q>0&&u-t<=2*q&&C<=2*t&&C-C0<=2*H+6,'clock support');
   const dur=Math.max(0,Math.min(u-s,H)-Math.max(t-s,a)),w=dur/(2*q);
   const rec={M,C,t,u,p,q,dur,w,del:false,idx:path.length};
   path.push(rec);events++;if(p>=Q)big++;
   t=u;C+=p-1;
  }
  check(C-C0<=2*H+B+6,'prefix gain');
  check(big*(Q-1)<=2*H+B+6,'large-count bound');maxBig=Math.max(maxBig,big);
  for(const rec of path)if(rec.p>=Q&&rec.dur<=2*z){rec.del=true;rec.fast=true;fc+=rec.dur/2;}
  let nb=0;
  for(let i=0;i<path.length;){
   if(path[i].p>y){i++;continue}
   let j=i+1;while(j<path.length&&path[j].p<=y)j++;
   const gain=path[j-1].C+path[j-1].p-1-path[i].C;
   check(gain<L,'LOW barrier');
   const flag=i===0||j===path.length||path[i-1].p>=Q||path[j].p>=Q;
   if(flag){nb++;lowBlocks++;for(let k=i;k<j;k++){check(!path[k].del,'disjoint removal');path[k].del=true;lc+=path[k].dur/2;}}
   i=j;
  }
  check(nb<=2*big+2&&fc<=z*big+1e-8&&lc<=1.5*L*nb+1e-8,'linear removal bound');
  fastR+=fc;lowR+=lc;removedR+=fc+lc;
  for(const rec of path)if(rec.dur){
   R+=rec.dur/2;rc+=rec.dur/2;slabRecords++;
   if(!lists.has(rec.C))lists.set(rec.C,[]);
   lists.get(rec.C).push(rec);
  }
  check(rc<=B,'slab duration');
  if(paths)paths.set(M,path);
 }
 const names=['same','merge','parallel','change','different'];
 function categories(trim){
  let E=0,diag=0,near=0,middle=0,shortMerge=0,maxU=0;
  const sums=Object.fromEntries(names.map(n=>[n,0]));
  for(const [C,arr0] of lists){
   const arr=trim?arr0.filter(v=>!v.del):arr0;
   const q=r[C/2];let U=0,old=0,k=0;
   const tmap=new Map(),umap=new Map(),pmap=new Map(),waitmap=new Map(),longt=new Map(),longu=new Map();
   const add=(m,k,w)=>m.set(k,(m.get(k)||0)+w),get=(m,k)=>m.get(k)||0;
   for(let i=0;i<arr.length;i++){
    const v=arr[i];
    while(k<i&&arr[k].M<v.M-d){
     const b=arr[k++];old+=b.w;
     add(tmap,b.t,b.w);add(umap,b.u,b.w);add(pmap,b.p,b.w);
     add(waitmap,b.p+':'+(b.u-b.t),b.w);
     if(b.dur>2*z2){add(longt,b.t,b.w);add(longu,b.u,b.w);}
    }
    const same=get(tmap,v.t),merge=get(umap,v.u)-same,parallel=get(waitmap,v.p+':'+(v.u-v.t))-same;
    const change=get(pmap,v.p)-same-merge-parallel,diff=old-get(pmap,v.p);
    const values=[same,merge,parallel,change,diff];
    check(values.every(x=>x>=-1e-7),'category nonnegative');
    for(let j=0;j<names.length;j++)sums[names[j]]+=2*q*v.w*values[j];
    const longMerge=v.dur>2*z2?get(longu,v.u)-get(longt,v.t):0;
    shortMerge+=2*q*v.w*(merge-longMerge);
    middle+=2*q*v.w*old;
    near+=q*(v.w*v.w+2*v.w*(U-old));diag+=q*v.w*v.w;
    U+=v.w;
   }
   E+=q*U*U;maxU=Math.max(maxU,U);
  }
  check(Math.abs(E-near-middle)<=1e-7*Math.max(1,E),'energy split');
  check(Math.abs(Object.values(sums).reduce((x,y)=>x+y,0)-middle)<=1e-7*Math.max(1,middle),'five categories');
  return {E,diag,near,middle,shortMerge,maxU,sums};
 }
 const full=categories(false),trim=categories(true);
 check(full.E-trim.E<=2*rootCap*removedR+1e-7*Math.max(1,full.E),'removed energy bound');
 check(full.shortMerge<=z2*N*(2*Math.floor((H+3)/2))+1e-7*Math.max(1,full.E),'short merger bound');
 let oracle=null;
 if(paths){
  const sums=Object.fromEntries(names.map(n=>[n,0]));
  let lateShared=0,shortMerge=0,boundedLagPremerge=0,mergers=0,nonresetBig=0,constantRuns=0;
  const seen=new Set();
  for(const [C,arr] of lists)for(let i=0;i<arr.length;i++)for(let j=0;j<i;j++){
   const v=arr[i],b=arr[j];if(v.M-b.M<=d)continue;
   check(v.M-b.M<=H+3,'pair support');
   const w=2*v.q*v.w*b.w,lag=Math.abs(v.t-b.t),nl=Math.abs(v.u-b.u);
   const type=!lag?'same':!nl?'merge':v.p!==b.p?'different':lag===nl?'parallel':'change';
   sums[type]+=w;
   if(v.p===b.p&&lag){
    check(nl===2*v.p*Math.floor(lag/(2*v.p))||nl===2*v.p*Math.ceil(lag/(2*v.p)),'lag rounding');
    check(Math.abs(nl-lag)<=2*v.q-1,'lag displacement');
   }
   const P=paths.get(v.M),A=paths.get(b.M);
   if(type==='same'){
    let k=v.idx,l=b.idx;
    while(k>0&&l>0&&P[k-1].C===A[l-1].C&&P[k-1].t===A[l-1].t){k--;l--;}
    if(P[k].t-(b.M+2)>=H-2*z2)lateShared+=w;
   }
   if(type==='merge'){
    const key=b.M+':'+v.M;check(!seen.has(key),'one first merge');seen.add(key);mergers++;
    if(Math.min(v.dur,b.dur)<=2*z2)shortMerge+=w;
    let k=v.idx,l=b.idx,gain=0,pw=0;
    while(k>0&&l>0&&Math.abs(P[k].t-A[l].t)>0&&Math.abs(P[k].t-A[l].t)<=2*y&&P[k-1].C===A[l-1].C){
     const vv=P[k-1],bb=A[l-1];
     check(vv.p===bb.p&&vv.p<=y,'bounded output lag label');
     gain+=vv.p-1;pw+=2*vv.q*vv.w*bb.w;k--;l--;
    }
    check(gain<L&&pw<=3*L,'bounded-lag LOW suffix');
    boundedLagPremerge+=pw;
   }
  }
  for(const n of names)check(Math.abs(sums[n]-full.sums[n])<=1e-7*Math.max(1,sums[n]),'oracle '+n);
  check(Math.abs(shortMerge-full.shortMerge)<=1e-7*Math.max(1,shortMerge),'short merge oracle');
  check(lateShared<=z2*N*(2*Math.floor((H+3)/2))+1e-7*Math.max(1,lateShared),'late shared bound');
  check(boundedLagPremerge<=1.5*L*N*(2*Math.floor((H+3)/2))+1e-7*Math.max(1,boundedLagPremerge),'bounded-lag total');
  oracle={lateShared,shortMerge,boundedLagPremerge,mergers};
 }
 return {X,B,H,d,Q,y,L,z,z2,events,slabRecords,literal,finished,maxBig,lowBlocks,R,fastR,lowR,removedR,S0,full,trim,oracle};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536,262144])console.log(JSON.stringify(audit(X)));
