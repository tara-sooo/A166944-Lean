// Exact lower quadrature for both orientations of the pinned least-prime count, with ordered source P2..P6 boxes and unrestricted two-prime short variables.
function audit(){
 const E=1000000, S=10n**22n, slack=100, a=160000, b=400000, step=2000, Q=208000;
 const B=BigInt, assert=(v,m)=>{if(!v)throw Error(m)}, fl=(x,y)=>x/y, ce=(x,y)=>(x+y-1n)/y;
 const dec=x=>(x/S)+"."+((x%S)/(10n**10n)).toString().padStart(12,"0");
 const cache=new Map();
 function log(p,q){p=B(p);q=B(q);assert(p>=q&&q>0n,"positive log");const k=p+"/"+q;if(cache.has(k))return cache.get(k);const a=p-q,b=p+q,a2=a*a,b2=b*b;let x=a,y=b,lo=0n;for(let i=0;i<32;i++){lo+=fl(2n*S*x,y*B(2*i+1));x*=a2;y*=b2;}cache.set(k,lo);return lo;}
 const n=(b-a)/step,m=(Q-a)/step, M=Array.from({length:n},()=>Array(m).fill(0n)), basic=Array.from({length:n},()=>Array(m).fill(0n));
 const sums=Array(7).fill(0n), old=Array(7).fill(0n), count=Array(7).fill(0);
 let pins=0, q3=0, q2=0, subsetWins=0, capChecks=0;
 function res(l,r,q){
  if(l<=slack||r>=E/2)return [0,0];
  const x=l-slack,y=Math.min(E-2*r,Math.floor((2*E-2*r)/5))-slack;
  let d=0,k=0;
  if(y>=0&&Math.max(x,y)>=q&&x+y>q){assert(2*r+y<E&&2*r+5*y<2*E&&x<l,"two-factor");d=x+y-q;k=1;capChecks++;}
  const z=Math.min(Math.floor((E-2*r-q)/2),Math.floor((2*E-2*r-5*q)/2))-slack;
  if(z>=0&&x+z>d){assert(2*r+q+2*z<E&&2*r+5*q+2*z<2*E,"Q2 pin");d=x+z;k=2;capChecks++;}
  const w=Math.min(E-2*r-2*q,Math.floor((2*E-2*r-2*q)/5))-slack;
  if(w>=0&&x+w>d){assert(2*r+w+2*q<E&&2*r+5*w+2*q<2*E,"Q3 pin");d=x+w;k=3;capChecks++;}
  return [d,k];
 }
 const coeffCache=new Map();
 function L(d,q,j){
  if(d<=2*q)return 0n;assert(d<4*q,"first lower region");
  const key=d+"/"+q;if(coeffCache.has(key))return coeffCache.get(key);
  const x=fl(2n*B(E)*log(d-q,q),B(d));
  const v=fl(x*log(q,q-step),S);coeffCache.set(key,v);return v;
 }
 function add(i,box,mass){
  const k=box.length;count[k]++;
  const choices=box.map(([l,r])=>[l,r,1]);
  for(let j=0;j<k;j++)for(let h=j+1;h<k;h++)choices.push([box[j][0]+box[h][0],box[j][1]+box[h][1],2]);
  for(let j=0;j<m;j++){
   const q=a+(j+1)*step;let d=0,kind=0,group=0,dSingle=0;
   for(const [l,r,g] of choices){const [v,w]=res(l,r,q);if(g===1)dSingle=Math.max(dSingle,v);if(v>d){d=v;kind=w;group=g;}}
   if(d<=2*q)continue;
   const val=fl(mass*L(d,q,j),S),v0=fl(mass*L(dSingle,q,j),S);
   M[i][j]+=val;basic[i][j]+=v0;sums[k]+=val;old[k]+=v0;pins++;
   if(kind===3)q3++;if(kind===2)q2++;if(group===2&&d>dSingle)subsetWins++;
  }
 }
 for(let i=0;i<n;i++){
  const l=a+i*step,r=l+step;
  const mass=log(B(r)*B(E-l),B(l)*B(E-r));
  add(i,[[l,r],[E-r,E-l]],mass);
 }
 // Source simplex boxes: t0 on shared least-factor grid, all other
 // variables except the final one on fixed-width inner rectangles.
 const widths={3:2000,4:4000,5:5000,6:4000};
 for(let k=3;k<=6;k++)for(let i=0;i<n;i++){
  const l=a+i*step,r=Math.min(l+step,Math.floor(E/k));if(r<=l)continue;
  function dfs(box,sumLo,sumHi,vol){
   const idx=box.length;
   if(idx===k-1){
    const lo=E-sumHi,hi=E-sumLo;
    if(lo<box.at(-1)[1]||hi>=E)return;
    const full=[...box,[lo,hi]];const den=full.reduce((v,box)=>v*B(box[1]),1n);
    const mass=fl(S*B(E)*vol,den); // E * product cell widths / product upper exponents
    add(i,full,mass);return;
   }
   const lim=Math.floor((E-sumHi)/(k-idx)),w=widths[k];
   for(let l=box.at(-1)[1];l<lim;){const r=Math.min(l+w,lim);if(r<=l)break;dfs([...box,[l,r]],sumLo+l,sumHi+r,vol*B(r-l));l=r;}
  }
  dfs([[l,r]],l,r,B(r-l));
 }
 function total(A){let one=0n,large=0n,small=0n,gain=0n;for(let i=0;i<n;i++)for(let j=0;j<m;j++)one+=A[i][j];for(let i=m;i<n;i++)for(let j=0;j<m;j++)large+=2n*A[i][j];for(let i=0;i<m;i++){small+=A[i][i];for(let j=i+1;j<m;j++){const x=A[i][j],y=A[j][i];small+=2n*(x>=y?x:y);gain+=x>=y?x-y:y-x;}}return{one:dec(one),largeBothOrientations:dec(large),smallOptimal:dec(small),smallDirectionGain:dec(gain),total:dec(large+small),raw:large+small};}
 const result=total(M),ref=total(basic);
 assert(result.raw>85n*S/100n,"joint lower .85 "+JSON.stringify({...result,raw:""}));
 assert(subsetWins>0&&q3>0&&q2>0&&count[4]>0,"nonvacuity");
 return {a:a/E,b:b/E,qmax:Q/E,sourceCounts:count.slice(2),sourceCoeffs:sums.slice(2).map(dec),sourceSingleCoeffs:old.slice(2).map(dec),all:{...result,raw:undefined},single:{...ref,raw:undefined},pins,q3,q2,subsetWins,capChecks,logCache:cache.size,coeffCache:coeffCache.size};
}
console.log(JSON.stringify(audit(),null,2));
