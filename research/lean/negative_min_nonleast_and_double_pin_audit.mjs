// Exact fixed-point certificates for independent roughness cutoff and one/two target prime pins, including conditional anatomy model bounds. Finite broad proxy checks are not asymptotic tests.
function audit(){
 const E=100000000,S=10n**25n,N=20000,B=BigInt,assert=(v,m)=>{if(!v)throw Error(m)},ce=(a,b)=>(a+b-1n)/b;
 const cache=new Map();
 function log(p,q){p=B(p);q=B(q);assert(p>=q&&q>0n,"log domain");const key=p+"/"+q;if(cache.has(key))return cache.get(key);const a=p-q,b=p+q,a2=a*a,b2=b*b;let x=a,y=b,l=0n;for(let j=0;j<64;j++){l+=2n*S*x/(y*B(2*j+1));x*=a2;y*=b2;}const r=[l,l+64n+ce(2n*S*x*b2,y*129n*(b2-a2))];cache.set(key,r);return r;}
 const dec=v=>Number(v)/Number(S);
 function cap(l,r,slack){const x=l-slack,y=Math.min(E-2*r,Math.floor((2*E-2*r)/5))-slack;assert(x<l&&2*r+y<E&&2*r+5*y<2*E,"Pascadi capacity");return [x,y];}
 function cell(l,r,qs,z,slack){
  const [x,y]=cap(l,r,slack);let c1=x,c2=y;
  for(let i=0;i<qs.length;i++){const [a,b]=qs[i];assert(a>z&&a<b&&(i===0||qs[i-1][1]<=a),"disjoint high pins");if(i===0)c1-=b;else c2-=b;}
  assert(c1>0&&c2>0,"remaining two factors");const d=c1+c2;assert(d>2*z&&d<4*z,"positive lower range");
  const coeff=2n*B(E)*log(d-z,z)[0]/B(d);
  let bare=log(B(r)*B(E-l),B(l)*B(E-r))[0];for(const [a,b] of qs)bare=bare*log(b,a)[0]/S;
  const incidence=bare*coeff/S;
  // At most four distinct prime divisors in the union of all chosen q bands;
  // one-pin multiplicity <=4, two disjoint band multiplicity <=2*2=4.
  assert(5*qs[0][0]>E,"multiplicity 4");
  return {source:[l/E,r/E],pins:qs.map(([a,b])=>[a/E,b/E]),z:z/E,capacity:[x/E,y/E],residual:d/E,remaining:[c1/E,c2/E],coefficient:dec(coeff),bare:dec(bare),incidence:dec(incidence),distinct:dec(incidence/4n),raw:incidence/4n,rawCoeff:coeff,rawBare:bare};
 }
 const rows=[
  cell(37495000,37505000,[[23000000,23020000]],18500000,500),
  cell(37495000,37505000,[[23000000,23020000]],19400000,500),
  cell(37495000,37505000,[[23000000,23020000]],19700000,500),
  cell(37499000,37501000,[[20833400,20835000]],20830100,100),
  cell(37490000,37510000,[[23000000,23100000],[24000000,24100000]],7500000,1000),
  cell(37450000,37550000,[[20850000,20900000],[20950000,21000000]],10200000,10000)
 ];
 // Buchstab bound on cofactor ratio for conditional least r<.23 and q .23-.2302.
 const lo=[],hi=[];
 for(let i=0;i<=6*N;i++){
  if(i<N){lo[i]=hi[i]=0n;continue;}
  if(i<=2*N){lo[i]=hi[i]=S;continue;}
  lo[i]=lo[i-1]+lo[i-1-N]/B(i-N);
  hi[i]=hi[i-1]+ce(hi[i-N],B(i-1-N));
 }
 const ylo=Math.floor(N*(E-23020000-23000000)/23000000);
 const yhi=Math.ceil(N*(E-23000000-18500000)/18500000);
 let maxOm=0n;
 for(let i=ylo;i<yhi;i++){const u=ce(hi[i+1]*B(N),B(i));if(u>maxOm)maxOm=u;}
 assert(maxOm<58n*S/100n,"omega .58");
 function invDiff(l,r){return ce(S*B(E)*B(r-l),B(l)*B(r));}
 const natural=ce(58n*invDiff(18500000,23000000),100n);
 assert(rows[0].rawCoeff>natural+S/100n,"rank-one suppression gap");
 // Model 2 upper for z=.194: previous g0 > .4779, hence 1-g0 < .5221.
 const ubands=[[19400000,Math.ceil(E*5/24),5221],[Math.floor(E*5/24),22000000,2500],[22000000,23000000,1000]];
 let upper=0n;for(const [l,r,w] of ubands)upper+=ce(58n*B(w)*invDiff(l,r),100n*10000n);
 assert(rows[1].rawCoeff>upper+S/100n,"model2 excluded at .194");
 assert(rows[0].raw>5n*S/100000000n,".185 distinct");
 assert(rows[1].raw>1n*S/100000000n,".194 distinct");
 assert(rows[2].raw>1n*S/1000000000n,".197 distinct lower");
 assert(rows[3].raw>5n*S/10000000000000n,"high complement distinct lower");
 assert(rows[4].raw>1n*S/1000000000n,"two target .23 pins");
 assert(rows[5].raw>1n*S/10000000000n,"two target .208 pins");
 // Conditional alternative: incidence >= .632 K Pi after errors.
 // Either high distinct >= .002 K Pi or low incidence >= .624 K Pi > bare .614 K Pi.
 assert(rows[0].rawCoeff>632n*S/1000n&&natural<614n*S/1000n,"alternative margins");
 assert(2n*rows[0].rawBare/1000n>7n*S/10000000000n,"high alternative coefficient");
 assert(23000000+4*19700000>E&&23020000+23000000<E,"P3/P4 if low .197");
 assert(rows[3].z>.2083&&rows[3].pins[0][0]>5/24,"disjoint new high strip");
 // Two-pin coefficient bounds and odd CRT, finite broad proxy.
 const R=100000,spf=new Int32Array(2*R+4);for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i;}
 const fac=n=>{let f=[];while(n>1){f.push(spf[n]);n/=spf[n];}return f;};
 let source=0,inc=0,distinct=0,same=0,low=0,high=0;
 for(let n=R-1;n<=2*R-1;n+=2){const fs=fac(n);if(fs.length!==2||fs[0]<30||fs[0]>100)continue;source++;const fm=fac(n+2);if(fm[0]<5)continue;const a=[...new Set(fm.filter(x=>x>=7&&x<=29))],b=[...new Set(fm.filter(x=>x>=31&&x<=97))];
  if(a.length){distinct++;inc+=a.length;for(const q of a){assert((n+2)%q===0,"first pin");if(fm[0]<q)low++;else high++;}}
  for(const p of a)for(const q of b){assert((n+2)%(p*q)===0&&p!==q,"double pin");same++;}
 }
 assert(low>0&&high>0&&same>0,"nonvacuous finite controls");
 return {rows:rows.map(({raw,rawCoeff,rawBare,...r})=>r),omega:{interval:[ylo/N,yhi/N],maxUpper:dec(maxOm),cells:yhi-ylo},naturalUpper:dec(natural),suppressionGap:dec(rows[0].rawCoeff-natural),model2Upper194:dec(upper),model2Gap194:dec(rows[1].rawCoeff-upper),finite:{R,source,inc,distinct,same,low,high},logCache:cache.size};
}
console.log(JSON.stringify(audit(),null,2));
