// Exact outward coefficient bounds. The BC theorem application and vector sieve are paper deductions; this script checks powers and numeric inequalities.
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
 function cuts(a,b,step=105){assert(Number.isInteger(a)&&Number.isInteger(b)&&a<=b,"integer cuts");const v=[a];while(v.at(-1)<b)v.push(Math.min(b,v.at(-1)+step));return v;}
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
 function triSaving(a,lim,cap=E){let s=0n,cells=0;const step=525,ts=cuts(a,Math.min(lim,E/3),step);for(let i=1;i<ts.length;i++){const l=ts[i-1],r=ts[i];const end=Math.floor((E-r)/2);if(end<=r)continue;const us=cuts(r,end,step);for(let j=1;j<us.length;j++){const u=us[j-1],v=us[j],low=E-r-v,high=E-l-u;assert(l>=a&&u>=r&&v<=low,"ordered cell");const d=Math.min(cap,Math.max(DU,min2(l,r),min2(u,v),min2(low,high)));if(d<=DU)continue;
 s+=fl(S*2n*B(E)**2n*B(r-l)*B(v-u)*B(d-DU),B(DU)*B(d)*B(r)*B(v)*B(high));cells++;}}
 return {s,cells};}
 const om=561522n;
 function maUpper(a){return ce(S*om*B(E),1000000n*B(a));}
 function upperBaseline(a,m){return ce((maUpper(a)-m)*2n*B(E),B(DU));}

 const a=432600,c=702870,b=840000;
 const staticNet=lower(D0,a)+semilower(c,E/2,a,false)-upperBaseline(a,m2(c))+triSaving(a,c).s+semiSaving(E/3,c);
 const staticOk=staticNet>8n*S/10000n;
 const phase=[];
 for(const [a,c,b] of [[436800,438900,840000],[432600,434700,840000],[443100,609000,735000],[462000,525000,787500]]){
   const m=fl(m2(c)+m2(b),2n);
   const p=lower(D0,a)+semilower(b,E/2,a,false);
   const save=triSaving(a,E/3).s+fl(semiSaving(E/3,b),2n);
   const net=p-upperBaseline(a,m)+save;
   assert(net>0n,"phase net "+dec(net));phase.push({a:a/E,c:c/E,b:b/E,net:dec(net)});
 }
 const a2=436800,cap=3*a2-slack;
 const gap=upperBaseline(a2,m2(b))-triSaving(a2,b,cap).s-semiSaving(E/3,b,cap)-(lower(D0,a2)+semilower(b,E/2,a2,false));
 assert(gap<1545n*S/1000n,"residual gap "+dec(gap));
 // Strictly above the old .208 low-pin cutoff; disjoint q cells.
 let hi=0n,positiveCells=0,capacities=0;
 const ts=cuts(783300,789600,42),qs=cuts(436800,437430,21); // .373..376, .208..2083
 for(let i=1;i<ts.length;i++){const l=ts[i-1],r=ts[i],x=l-21,y=Math.min(E-2*r,Number(fl(B(2*E-2*r),5n)))-21;
  assert(x<l&&2*r+y<E&&2*r+5*y<2*E,"pin strict caps");
  for(let j=1;j<qs.length;j++){const q=qs[j],p=qs[j-1];if(q>x)continue;const d=x+y-q;capacities++;if(d<=2*q)continue;
    const k=fl(fl(mass(l,r)[0]*log(q,p)[0],S)*lower(d,q),S);
    hi+=k;positiveCells++;
  }}
 assert(hi>S/100000000n,"high sector lower "+dec(hi));
 // BC exponent and vector sieve coefficient: p,q in [.2085,.211], residual d=.3, z exponent .11.
 const maxMod=1075200;assert(17*2*maxMod+5*maxMod<20*E,"BC .512 exponent"); // .85 sum+.25 max
 const d=630000,z=231000;
 const ratio=2n*log(d-z,z)[0]-S;
 assert(ratio>0n,"vector positivity");
 const k=fl(4n*B(E)**2n*ratio,B(d)**2n);
 const pm=log(443100,437850)[0];
 const coeff=fl(fl(fl(k*pm,S)*pm,S)*9n,160n);
 assert(coeff>3n*S/100000n,"distinct vector lower "+dec(coeff));
 return {static3347:dec(staticNet),staticOk,phase,gap208:dec(gap),highSector:dec(hi),positiveCells,capacities,BC:{modulusCap:.512,errorExponent:.9984,ratioLower:dec(ratio),distinctCoefficient:dec(coeff)},logCache:cache.size};
}

console.log(JSON.stringify(audit(),null,2));
