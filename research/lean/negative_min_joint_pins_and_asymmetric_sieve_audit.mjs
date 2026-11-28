// Exact integer exponent capacities, outward-rounded logarithm/integral bounds, and direct vs pinned finite determinant counts. Numeric coefficients are not asymptotic proofs.
function audit(){
 const E=1000000,S=10n**22n,slack=100,D0=571328,DU=599900;
 const B=BigInt,fl=(a,b)=>a/b,ce=(a,b)=>(a+b-1n)/b,assert=(v,m)=>{if(!v)throw Error(m)};
 const dec=x=>{const s=x<0n?"-":"";x=x<0n?-x:x;return s+(x/S)+"."+((x%S)/(10n**10n)).toString().padStart(12,"0");};
 const cache=new Map();
 function log(p,q){p=B(p);q=B(q);assert(p>0n&&q>0n,"log domain");if(p<q){const v=log(q,p);return[-v[1],-v[0]];}const k=p+"/"+q;if(cache.has(k))return cache.get(k);const a=p-q,b=p+q,a2=a*a,b2=b*b;let x=a,y=b,lo=0n;const N=36;for(let i=0;i<N;i++){lo+=fl(2n*S*x,y*B(2*i+1));x*=a2;y*=b2;}const hi=lo+B(N)+ce(2n*S*x*b2,y*B(2*N+1)*(b2-a2));const ans=[lo,hi];cache.set(k,ans);return ans;}
 function cuts(l,r,h){if(l>=r)return[l];const a=[l];while(a.at(-1)<r)a.push(Math.min(r,a.at(-1)+h));return a;}
 function upper2(r){return Math.min(E-2*r,Math.floor((2*E-2*r)/5))-slack;}
 function cap2(l,r){return l-slack+upper2(r);}
 function L(d,u){if(d<=2*u)return 0n;assert(d<4*u,"first lower range");return fl(2n*B(E)*log(d-u,u)[0],B(d));}
 function mass2(l,r){return log(B(r)*B(E-l),B(l)*B(E-r))[0];}
 function trmass(l,r,u,v){return fl(S*B(E)*B(r-l)*B(v-u),B(r)*B(v)*B(E-l-u));}
 let capacityChecks=0, q3Wins=0,q2Wins=0;
 function res(l,r,q,allow3){
  if(l<=slack||r>=E/2)return {d:0,kind:0};
  const x=l-slack,y=upper2(r);
  let d=0,kind=0;
  if(y>=0&&Math.max(x,y)>=q&&x+y>q){d=x+y-q;kind=1;assert(x<l&&2*r+y<E&&2*r+5*y<2*E,"two factor");capacityChecks++;}
  if(allow3){
   const z=Math.min(Math.floor((E-2*r-q)/2),Math.floor((2*E-2*r-5*q)/2))-slack;
   if(z>=0&&x+z>d){assert(2*r+q+2*z<E&&2*r+5*q+2*z<2*E,"Q2 pin");d=x+z;kind=2;capacityChecks++;}
   const w=Math.min(E-2*r-2*q,Math.floor((2*E-2*r-2*q)/5))-slack;
   if(w>=0&&x+w>d){assert(2*r+w+2*q<E&&2*r+5*w+2*q<2*E,"Q3 pin");d=x+w;kind=3;capacityChecks++;}
  }
  return {d,kind};
 }
 function row(xs,qs,allow3,needSurplus){
  let ans=0n,extra=0n;
  const base=Math.max(DU,...xs.map(([l,r])=>cap2(l,r)));
  for(let j=1;j<qs.length;j++){
   const q=qs[j],prev=qs[j-1];let best={d:0,kind:0};for(const [l,r] of xs){const t=res(l,r,q,allow3);if(t.d>best.d)best=t;}
   const c=L(best.d,q);if(c===0n)continue;
   const a=fl(c*log(q,prev)[0],S);ans+=a;
   if(best.kind===3)q3Wins++;if(best.kind===2)q2Wins++;
   if(needSurplus&&3*prev>=base+slack)extra+=a;
  }
  return [ans,extra];
 }
 function integrate(a,b,step,qstep){
  const qs=cuts(a,208300,qstep);let p2=0n,p3=0n,old2=0n,old3=0n,extra=0n,rows=0;
  const ts=cuts(a,b,step);for(let i=1;i<ts.length;i++){
   const l=ts[i-1],r=ts[i],m=mass2(l,r);
   const xs=[[l,r],[E-r,E-l]];
   const [v,e]=row(xs,qs,true,true);const [o]=row(xs,qs,false,false);
   p2+=fl(m*v,S);old2+=fl(m*o,S);extra+=fl(m*e,S);rows++;
  }
  const us=cuts(a,333333,step);for(let i=1;i<us.length;i++){
   const l=us[i-1],r=us[i];const end=Math.floor((E-r)/2);if(end<=r)continue;
   const vs=cuts(r,end,step);for(let j=1;j<vs.length;j++){
    const u=vs[j-1],v=vs[j],lo=E-r-v,hi=E-l-u;assert(l>=a&&r<=u&&v<=lo,"triple ordered box");
    const xs=[[l,r],[u,v],[lo,hi]],m=trmass(l,r,u,v);
    const [w,e]=row(xs,qs,true,true);const [o]=row(xs,qs,false,false);
    p3+=fl(m*w,S);old3+=fl(m*o,S);extra+=fl(m*e,S);rows++;
   }
  }
  return {a:a/E,b:b/E,p2:dec(p2),p3:dec(p3),total:dec(p2+p3),ordinary:dec(old2+old3),plateauSurplus:dec(extra),raw:p2+p3,rawExtra:extra,rows};
 }
 const rows=[integrate(160000,400000,2000,1000),integrate(200000,365000,1000,500),integrate(206000,400000,500,250)];
 const explicit=fl(mass2(169000,171000)*row([[169000,171000]], [202000,203000],true,true)[1],S);
 function m2(c,upper=false){return S+log(E-c,c)[upper?1:0];}
 function tripleUpper(a){let s=0n;const xs=cuts(a,333334,100);for(let i=1;i<xs.length;i++){const l=xs[i-1],r=xs[i];if(l*3>=E)continue;const w=log(E-2*l,l)[1];s+=ce(B(r-l)*B(E)*w,B(l)*B(E-l));}return s;}
 function massUpper(a){if(a<250000)return ce(S*561522n,B(a));return m2(a,true)+tripleUpper(a);}
 function sieve(d,a){assert(d>2*a&&d<4*a,"sieve lower");return L(d,a);}
 function positive(b,a){let s=sieve(D0,a);if(b===500000)return s;const xs=cuts(b,500000,500);for(let i=1;i<xs.length;i++){const l=xs[i-1],r=xs[i];s+=fl(mass2(l,r)*sieve(Math.max(D0,cap2(l,r)),a),S);}return s;}
 function triSaving(a){
  let s=0n;const xs=cuts(a,333333,500);for(let i=1;i<xs.length;i++){
   const l=xs[i-1],r=xs[i],end=Math.floor((E-r)/2);if(end<=r)continue;
   const ys=cuts(r,end,500);for(let j=1;j<ys.length;j++){
    const u=ys[j-1],v=ys[j],d=Math.max(DU,cap2(l,r),cap2(u,v),cap2(E-r-v,E-l-u));
    if(d>DU)s+=fl(trmass(l,r,u,v)*2n*B(E)*B(d-DU),B(DU)*B(d));
   }
  }return s;
 }
 const asym=[];
 for(const [a,b,c] of [[228000,400000,295000],[245000,450000,280000],[276000,500000,276700]]){
  const p=positive(b,a),up=ce((massUpper(a)-m2(c))*2n*B(E),B(DU)),s=triSaving(a),net=p-up+s;
  asym.push({a:a/E,b:b/E,c:c/E,positive:dec(p),upper:dec(up),saving:dec(s),net:dec(net),raw:net});
 }
 const finite=[];let finiteChecks=0;
 for(const R of [12000,48000,192000]){
  const f=new Int32Array(2*R+4);for(let p=2;p<f.length;p++)if(!f[p]){f[p]=p;if(p*p<f.length)for(let n=p*p;n<f.length;n+=p)if(!f[n])f[n]=p;}
  const fac=n=>{const a=[];while(n>1){a.push(f[n]);n/=f[n];}return a;};
  const lo=Math.ceil(R**.16),hi=Math.floor(R**.4),qhi=Math.floor(R**.28);
  const source=n=>{if(n%2===0)return false;const a=fac(n);return (a.length===2||a.length===3)&&a[0]>=lo&&a[0]<hi;};
  const dir=new Set(),pin=new Set();let square=0,det=0;
  for(let n=R-1;n<=2*R-1;n++)if(source(n)){
   const q=f[n+2];if(q>=lo&&q<=qhi){if((n+2)%(q*q)===0){square++;continue;}dir.add(n);}
  }
  for(let q=Math.max(3,lo);q<=qhi;q++)if(f[q]===q){
   let n=R-1+((q-((R+1)%q))%q);
   for(;n<=2*R-1;n+=q)if(source(n)){
    const v=(n+2)/q;assert(Number.isInteger(v),"pin");if(f[v]<=q)continue;
    const p=f[n],u=n/p;assert(p*u-q*v===-2&&p!==q,"determinant");det++;
    assert(!pin.has(n),"least prime unique");pin.add(n);
   }
  }
  assert(dir.size===pin.size&&[...dir].every(n=>pin.has(n)),"pinned count exact");
  finiteChecks+=det;finite.push({R,lo,hi,qhi,direct:dir.size,pinned:pin.size,deletedSquares:square,determinants:det});
 }
 assert(finiteChecks>0,"finite nonvacuity");
 const result={rows:rows.map(({raw,rawExtra,...r})=>r),explicitQ3:dec(explicit),asym:asym.map(({raw,...r})=>r),capacityChecks,q3Wins,q2Wins,finiteChecks,finite,logCache:cache.size};
 // These explicit rational margins are independent of displayed decimal truncation.
 assert(rows[0].raw>35n*S/100n,".16 joint lower "+JSON.stringify(result.rows[0]));
 assert(rows[1].raw>100n*S/1000000n,".2 joint lower "+JSON.stringify(result.rows[1]));
 assert(rows[2].raw>5n*S/1000000n,".206 joint lower "+JSON.stringify(result.rows[2]));
 assert(explicit>10n*S/1000000n,"explicit Q3 plateau surplus "+result.explicitQ3);
 assert(asym[0].raw>40n*S/1000n,"asym .4 "+JSON.stringify(result.asym[0]));
 assert(asym[1].raw>20n*S/1000n,"asym .45 "+JSON.stringify(result.asym[1]));
 assert(asym[2].raw>0n,"prime P2 "+JSON.stringify(result.asym[2]));
 return result;
}
console.log(JSON.stringify(audit(),null,2));
