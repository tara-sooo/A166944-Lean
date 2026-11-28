// Rational fixed-point outward bounds for bilateral sieve coefficients and the continuous marginal-envelope countermodel. Numerical assertions use BigInt; printed decimals truncate toward zero, use explicit margins in the note.
function audit(){
 const E=2100000,S=10n**25n,slack=210,D0=1199790,DU=1259790;
 const assert=(v,m)=>{if(!v)throw Error(m)};
 const B=BigInt,fl=(a,b)=>a/b,ce=(a,b)=>(a+b-1n)/b;
 const dec=(v)=>{const sign=v<0n?"-":"";v=v<0n?-v:v;return sign+(v/S).toString()+"."+((v%S)/(10n**15n)).toString().padStart(10,"0");};
 const cache=new Map();
 function log(p,q){
   p=B(p);q=B(q);assert(p>0n&&q>0n,"log domain");
   if(p<q){const [l,h]=log(q,p);return [-h,-l];}
   const key=p+"/"+q;if(cache.has(key))return cache.get(key);
   const a=p-q,b=p+q,a2=a*a,b2=b*b;
   let x=a,y=b,lo=0n;const N=64;
   for(let j=0;j<N;j++){lo+=2n*fl(S*x,y*B(2*j+1));x*=a2;y*=b2;}
   const tail=ce(2n*S*x*b2,y*B(2*N+1)*(b2-a2));
   const ans=[lo,lo+2n*B(N)+tail];cache.set(key,ans);return ans;
 }
 function cuts(a,b,step=210){assert(Number.isInteger(a)&&Number.isInteger(b)&&a<=b,"integer cuts");const v=[a];while(v.at(-1)<b)v.push(Math.min(b,v.at(-1)+step));return v;}
 function min2(l,r){return Math.min(Number(fl(B(2*E+3*l),5n)),E-r)-slack;}
 function wuf(t){if(t<=E/4)return Number(fl(B(3*E+2*t),6n));if(t<=2*E/7)return Number(fl(B(2*E-t),3n));if(t<=2*E/5)return Number(fl(B(2*E+t),4n));return E-t;}
 function wul(l,r){let d=Math.min(wuf(l),wuf(r));for(const t of [E/4,2*E/7,2*E/5])if(l<t&&t<r)d=Math.min(d,wuf(t));return d-slack;}
 function level(l,r,phase){return Math.max(min2(l,r),phase?wul(l,r):D0);}
 function lower(d,a,upper=false){assert(2*a<d&&d<4*a,"first lower formula");const [l,h]=log(d-a,a);return upper?ce(2n*B(E)*h,B(d)):fl(2n*B(E)*l,B(d));}
 function mass(l,r){return log(B(r)*B(E-l),B(l)*B(E-r));}
 function m2(z,upper=false){return S+log(E-z,z)[upper?1:0];}
 function m3cell(l,r){return fl(B(r-l)*B(E)*log(E-2*r,r)[0],B(r)*B(E-r));}
 function trMass(z){let s=0n;const a=cuts(z,E/3);for(let i=1;i<a.length;i++)s+=m3cell(a[i-1],a[i]);return s;}
 function m3(z){return m2(z)+trMass(z);}
 function semilower(l,r,a,phase){let s=0n;const v=cuts(l,r);for(let i=1;i<v.length;i++)s+=fl(mass(v[i-1],v[i])[0]*lower(level(v[i-1],v[i],phase),a),S);return s;}
 function trilower(l,a){let s=0n;const v=cuts(l,E/3);for(let i=1;i<v.length;i++)s+=fl(m3cell(v[i-1],v[i])*lower(level(v[i-1],v[i],true),a),S);return s;}
 function semiSaving(l,r,cap=E){if(l>=r)return 0n;let s=0n;const v=cuts(l,r);for(let i=1;i<v.length;i++){const d=Math.min(cap,min2(v[i-1],v[i]));if(d>DU)s+=fl(mass(v[i-1],v[i])[0]*2n*B(E)*B(d-DU),B(d)*B(DU));}return s;}
 function triSaving(a,lim,cap=E){let s=0n,cells=0;const step=1050,ts=cuts(a,Math.min(lim,E/3),step);for(let i=1;i<ts.length;i++){const l=ts[i-1],r=ts[i];const end=Math.floor((E-r)/2);if(end<=r)continue;const us=cuts(r,end,step);for(let j=1;j<us.length;j++){const u=us[j-1],v=us[j],low=E-r-v,high=E-l-u;assert(l>=a&&u>=r&&v<=low,"ordered cell");const d=Math.min(cap,Math.max(DU,min2(l,r),min2(u,v),min2(low,high)));if(d<=DU)continue;
 s+=fl(S*2n*B(E)**2n*B(r-l)*B(v-u)*B(d-DU),B(DU)*B(d)*B(r)*B(v)*B(high));cells++;}}
 return {s,cells};}
 const om=561522n;
 function maUpper(a){return ce(S*om*B(E),1000000n*B(a));}
 function upperBaseline(a,m){return ce((maUpper(a)-m)*2n*B(E),B(DU));}
 const a=432600; // .206
 const results=[];
 function record(type,params,p,base,ts,ss,min){
  const net=p-base+ts.s+ss;assert(net>B(min)*S/1000000n,"positive certificate "+JSON.stringify(params));
  results.push({type,...params,positiveLower:dec(p),upperBaselineUpper:dec(base),tripleSavingLower:dec(ts.s),semiprimeSavingLower:dec(ss),cells:ts.cells,netLower:dec(net),usableCoefficient:min/1000000});
 }
 for(const [c,min] of [[630000,980000],[656250,590000],[672000,375000],[680400,270000],[701400,15000],[702450,4000],[702660,2000]]){
  const mt=c<E/3?m3(c):m2(c);
  const tr=c<E/3?fl(trMass(c)*lower(D0,a),S):0n;
  const p=lower(D0,a)+semilower(c,E/2,a,false)+tr,base=upperBaseline(a,mt),ts=triSaving(a,c),ss=semiSaving(E/3,c);
  record("static",{a:a/E,c:c/E},p,base,ts,ss,min);
 }
 for(const [ell,b,min] of [[588000,840000,70000],[594300,840000,20000],[596400,840000,2000],[672000,735000,4000],[630000,787500,10000]]){
  const p=lower(D0,a)+semilower(b,E/2,a,false)+fl(semilower(ell,b,a,true)+trilower(ell,a),2n);
  const m=fl(m3(ell)+m2(b),2n),base=upperBaseline(a,m),ts=triSaving(a,ell),ss=fl(semiSaving(E/3,b),2n);
  record("phase",{ell:ell/E,b:b/E},p,base,ts,ss,min);
 }
 const aold=433020,cold=701400;
 const old=lower(D0,aold)+semilower(cold,E/2,aold,false)-upperBaseline(aold,m2(cold))
 -ce(mass(E/3,cold)[1]*2n*B(E)*B(DU-D0),B(D0)*B(DU));
 assert(old>5n*S/1000n,"old lower reconstruction");
 const c=766500,d=1312500,lo=367500,hi=656250;
 const mh=m2(c,true),ml=m2(c);
 assert(2n*mh<fl(2n*B(E)*S,B(d)),"row upper plateau");
 const mlo=m3(lo),mhi=maUpper(E/5);
 assert(mlo>2n*mh&&mhi<2n*ml,"split exists");
 const zz=cuts(lo,hi);zz.push(...cuts(hi,E/3).slice(1));
 const tail=new Array(zz.length).fill(0n);
 for(let i=zz.length-2;i>=0;i--)tail[i]=tail[i+1]+m3cell(zz[i],zz[i+1]);
 let min=100n*S,ncells=0;
 for(let i=1;zz[i]<=hi;i++){
  const l=zz[i-1],r=zz[i];const low=m2(r)+tail[i];const lv=2n*(low-mh)-lower(d,l,true);
  if(lv<min)min=lv;ncells++;
 }
 assert(min>35n*S/1000n,"all interval inequalities");
 const model={c:c/E,d:d/E,b0Bracket:[lo/E,.2],M3LowerAtLo:dec(mlo),MUpperAtHi:dec(mhi),twiceMUpper:dec(2n*mh),minMargin:dec(min),ncells};
 const twins=[];
 for(const [th,seed,surviveNum,surviveDen] of [[1008000,980000,2,3],[1037400,270000,2,3],[1049370,15000,2,3]]){
  const u=ce(4n*B(E)*mass(th,E/2)[1],B(D0));
  assert(u*B(surviveDen)<B(seed)*S*B(surviveNum)/1000000n,"strict survival margin");
  twins.push({theta:th/E,nonTwinUpper:dec(u),seed:seed/1000000,survival:surviveNum+"/"+surviveDen});
 }
 const b=840000,cap=3*a-slack;
 const pc=lower(D0,a)+semilower(b,E/2,a,false);
 const vc=upperBaseline(a,m2(b))-triSaving(a,b,cap).s-semiSaving(E/3,b,cap);
 const gap=vc-pc;
 assert(gap<1560n*S/1000n,"correction gap .206: "+dec(gap));
 const a2=336000;assert(3*a2<DU&&DU<4*a2,"upper second plateau");
 let fU=S;const cut=cuts(3*a2,DU,210);
 for(let i=1;i<cut.length;i++){const l=cut[i-1],r=cut[i];fU+=ce(B(r-l)*log(r-2*a2,a2)[1],B(r-a2));}
 const upper2=ce(ce(2n*B(E)*fU,B(DU))*(maUpper(a2)-m2(b)),S);
 const p2=lower(D0,a2)+semilower(b,E/2,a2,false);const gap2=upper2-p2;
 assert(gap2<3030n*S/1000n,"correction gap .16: "+dec(gap2));
 return {results,old334Lower:dec(old),model,twins,correction:[{a:.206,gapUpperTruncated:dec(gap),sufficient:1.56},{a:.16,gapUpperTruncated:dec(gap2),sufficient:3.03}],logCache:cache.size};
}
console.log(JSON.stringify(audit(),null,2));
