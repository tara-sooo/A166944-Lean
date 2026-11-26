// Run: node research/infinite-orbit/clock_direction_audit.mjs
function audit(){
const max=4*65536+4096,spf=new Int32Array(max+1);for(let p=2;p*p<=max;p++)if(!spf[p])for(let n=p*p;n<=max;n+=p)spf[n]=p;
function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
function prime(n){return Number.isInteger(n)&&n>=2&&n<=max&&!spf[n]}
function mod(a,b){return (a%b+b)%b}
function gcd(a,b){a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a}
function inv(a,b){let x=1,y=0,u=mod(a,b),v=b;while(v){let k=Math.floor(u/v);[u,v]=[v,u-k*v];[x,y]=[y,x-k*y]}if(u!==1)throw Error("inverse");return mod(x,b)}
function elig(H){let B=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=B),fac(H+1).filter(p=>p<=B)]}
function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let z=1+mod((i?q+2:0)-t-1,2*q);if(z<w||(z===w&&q<p)){p=q;w=z;s=i}}return {p,w,s}}
function gap(n,p,f){let W=2*p;for(let i=0;i<2;i++)for(let q of f[i])if(q!==p){let z=mod(n-(i?q+2:0),2*q);if(!z&&q<p)return 0;W=Math.min(W,z||2*q)}return W}
function ok(v,m){if(!v)throw Error(m)}
let totals={roots:0,targeted:0,events:0,stops:0,exits:0,cap:0,high:0,triples:0,distinct:0,aligned:0,alignedShort:0,alignedLargeGap:0,alignedCanonical:0,alignedFast:0,zero:0,nonparallel:0,coupled:0,zeroAffine:0,shortTriple:0,shortNonparallel:0,shortZero:0,literal:0,censuses:0,shiftConfigs:0,candidates:0,alignedActualCandidates:0},results=[],examples={aligned:null,alignedShort:null,largeGap:null,nonparallel:null,zero:null};
for(let X of [4096,16384,65536]){
let Y=4*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(Y+1)),before={...totals};
function clock(p,s){return s?p+2:0}
function coord(a,b){let E=b.H-a.J,V=b.n-a.n,D=E-1+2*(b.s-a.s),d=V-2*(b.s-a.s),A=a.q+1,C=(a.n-2*a.s)/a.p,A1=b.q+1,C1=(b.n-2*b.s)/b.p,m=(D*C-d*A)/b.p;
ok(E>=0&&E%2===0&&mod(D,2)===1&&d!==0&&Number.isInteger(C)&&Number.isInteger(C1),"coordinates");
ok(b.p*(A1-1)===a.p*A+D&&b.p*C1===a.p*C+d,"shift rows");
if(a.p!==b.p)ok(Number.isInteger(m)&&D*C1-d*A1===a.p*m-d,"pair determinant");
return {E,V,D,d,A,C,A1,C1,m}}
function inspect(a,b,c,can){
totals.triples++;
if(new Set([a.p,b.p,c.p]).size!==3)return;
totals.distinct++;
let x=coord(a,b),y=coord(b,c),Q=x.D*y.d-y.D*x.d,short=x.E+y.E<=16&&x.V+y.V<=16;
if(short)totals.shortTriple++;
ok(Q*x.C1===y.d*(a.p*x.m-x.d)-x.d*c.p*y.m&&Q*x.A1===y.D*(a.p*x.m-x.d)-x.D*c.p*y.m,"middle Cramer");
ok(mod(b.p*(c.p*y.m+y.d)+Q,a.p)===0||x.d%a.p===0,"first coupled");
ok(mod(b.p*(a.p*x.m-x.d)+Q,c.p)===0||y.d%c.p===0,"second coupled");
if(x.d%a.p!==0&&y.d%c.p!==0)totals.coupled++;
if(Q===0){totals.aligned++;
let g=gcd(x.D,x.d),D=x.D/g,d=x.d/g;if(D<0){D=-D;d=-d}
let m0=(D*x.C-d*x.A)/b.p,m1=(D*y.C-d*y.A)/c.p;
ok(Number.isInteger(m0)&&Number.isInteger(m1)&&m1*c.p===m0*a.p-d,"aligned recurrence");
if(Math.abs(d)<T)ok(m0!==0&&m1!==0&&m0*m1>0,"nonzero aligned");
let data={X,can,a,b,c,x,y,Q,D,d,m0,m1};if(!examples.aligned)examples.aligned=data;
if(short){totals.alignedShort++;if(!examples.alignedShort)examples.alignedShort=data;}
if(short&&Math.abs(a.p-c.p)>=T/2){totals.alignedLargeGap++;if(!examples.largeGap)examples.largeGap=data;}
if(can)totals.alignedCanonical++;
if(4*b.w<=b.p-1&&4*c.w<=c.p-1)totals.alignedFast++;
}else{totals.nonparallel++;if(short)totals.shortNonparallel++;
if(!examples.nonparallel&&short)examples.nonparallel={X,can,a,b,c,x,y,Q};
if(x.m===0||y.m===0){totals.zero++;if(short)totals.shortZero++;
if(x.m===0&&y.d%c.p!==0){ok((Q-b.p*x.d)%c.p===0,"zero first affine");totals.zeroAffine++;}
if(y.m===0&&x.d%a.p!==0){ok((Q+b.p*y.d)%a.p===0,"zero second affine");totals.zeroAffine++;}
if(!examples.zero&&short)examples.zero={X,can,a,b,c,x,y,Q};
}}
}
function scan(H,t,can){
let list=[];
for(let it=0;it<2000&&H<Y;it++){
let z=first(t,elig(H));if(!z.p){totals.stops++;break}let {p,w,s}=z,e=1-2*s,q=(H-e)/p,J=H+p-1,n=t+w;let v={H,t,p,w,s,e,q,J,n};totals.events++;
if(totals.events%9973===0){let found=null;for(let w0=1;w0<=2*Math.floor(Math.sqrt(H+1));w0++){let n0=t+w0,d=gcd(n0%2?n0-2:n0,n0%2?H+1:H-1),p0=fac(d).find(f=>f<=Math.floor(Math.sqrt(H+1)));if(p0){found=[p0,w0];break}}ok(found&&found[0]===p&&found[1]===w,"literal");totals.literal++;}
if(p>=T){list.push(v);totals.high++;if(list.length>=3)inspect(...list.slice(-3),can);}
H=J;t=n;if(it===1999&&H<Y)totals.cap++;}if(H>=Y)totals.exits++;
}
for(let H=X;H<Y;H+=4){scan(H,(H+6)/2,true);totals.roots++}
let seen=new Set();for(let H=X;H<Y;H+=Math.max(2,2*Math.floor(Math.sqrt(X)/8))){let f=elig(H);for(let s=0;s<2;s++)for(let p of f[s]){if(p<T)continue;let r=clock(p,s),lo=H/2+1,hi=3*H+3+2*p;for(let frac of [1,3,5]){let base=Math.floor(lo+(hi-lo)*frac/6),n=base+mod(r-base,2*p);if(n>hi)continue;let W=gap(n,p,f),l=Math.max(1,n-(3*H+3)),u=Math.min(W,n-H/2);if(l>u)continue;for(let w of new Set([l,u])){let t=n-w,key=H+","+t;if(seen.has(key))continue;seen.add(key);let a=first(t,f);ok(a.p===p&&a.w===w,"target");scan(H,t,false);totals.targeted++;}}}}
// Independent aligned product-clock candidate sets. Source arrival necessary, not necessarily exact MIN.
let counts=[],ps=[];for(let p=T;p<=B;p++)if(prime(p))ps.push(p);
let Nlo=X/2+1,Nhi=3*Y+3+2*B;
function hf(n){return fac(n).filter(p=>p>=T&&p<=B)}
function horizon(p,r,v,n,E,F,V,W,s,t,u,D,d,m0,m1,out){
let e=1-2*s,f=1-2*t,g=1-2*u,base=e+p;
let h0=base+2*p*mod((f-p+1-E-base)*inv(2*p,r),r),period=2*p*r;
for(let H=X+mod(h0-X,period);H<Y;H+=period){
let H1=H+p-1+E,H2=H1+r-1+F;if(H1>=Y||H2>=Y||(H2-g)%v||p*p>H+1||r*r>H1+1||v*v>H2+1||n<H/2+1||n>3*H+3+2*p)continue;
let a=(H-e)/p+1,b=(H1-f)/r+1,c=(n-2*s)/p,k=(n+V-2*t)/r;
if(!Number.isInteger(a)||!Number.isInteger(b)||!Number.isInteger(c)||!Number.isInteger(k))throw Error("candidate coords");
let l0=(D*c-d*a)/r,l1=(D*k-d*b)/v;
ok(Number.isInteger(l0)&&Number.isInteger(l1)&&l1*v===l0*p-d,"candidate alignment");
if(m0!==null&&(l0!==m0||l1!==m1))continue;
out.add([H,p,r,v,n,E,F,V,W,s,t,u].join(","));
}
}
for(let [L,Wmax] of [[0,4],[2,6],[4,8]]){
let brute=new Set(),affine=new Set(),configs=0;
for(let E=0;E<=L;E+=2)for(let F=0;F<=L-E;F+=2)for(let s of [0,1])for(let t of [0,1])for(let u of [0,1])for(let V=1;V<Wmax;V++)for(let W=1;W<=Wmax-V;W++){
if(mod(V,2)!==mod(t-s,2)||mod(W,2)!==mod(u-t,2))continue;
let D1=E-1+2*(t-s),d1=V-2*(t-s),D2=F-1+2*(u-t),d2=W-2*(u-t);if(D1*d2!==D2*d1)continue;
let gg=gcd(D1,d1),D=D1/gg,d=d1/gg;if(D<0){D=-D;d=-d}configs++;totals.shiftConfigs++;
for(let p of ps)for(let n=Nlo+mod(clock(p,s)-Nlo,2*p);n<=Nhi;n+=2*p){
for(let r of hf(n+V-2*t)){if(r===p)continue;for(let v of hf(n+V+W-2*u)){if(v===r||v===p)continue;horizon(p,r,v,n,E,F,V,W,s,t,u,D,d,null,null,brute);}}}
let cap=Math.ceil((Math.abs(D)*(3*Y+3+2*B)/T+Math.abs(d)*(Y+B+2)/T)/T);
for(let p of ps)for(let m0=-cap;m0<=cap;m0++){
if(!m0)continue;let prod=m0*p-d;if(!prod)continue;
for(let v of ps){if(v===p||prod%v)continue;let m1=prod/v;if(!m1||Math.abs(m1)>cap)continue;
let base=clock(p,s),n0=base+2*p*mod((2*u-V-W-base)*inv(2*p,v),v),period=2*p*v;
for(let n=Nlo+mod(n0-Nlo,period);n<=Nhi;n+=period)for(let r of hf(n+V-2*t)){if(r===p||r===v)continue;horizon(p,r,v,n,E,F,V,W,s,t,u,D,d,m0,m1,affine);}
}}
}
ok(brute.size===affine.size&&[...brute].every(k=>affine.has(k)),"aligned exact census");
totals.censuses++;totals.candidates+=brute.size;
let real=0;for(let key of brute){let [H,p,r,v,n,E,F,V,W,s,t,u]=key.split(",").map(Number),ff=elig(H),l=Math.max(1,n-(3*H+3)),hi=Math.min(gap(n,p,ff),n-H/2);if(l>hi)continue;let aa=first(n-l,ff);if(aa.p!==p||aa.w!==l||aa.s!==s)continue;
let h=H+p-1,nn=n,got=[];for(let it=0;it<Wmax&&nn<n+V+W&&h<Y;it++){let z=first(nn,elig(h));if(!z.p||nn+z.w>n+V+W)break;nn+=z.w;if(z.p>=T)got.push([h,z.p,nn,z.s]);h+=z.p-1;if(got.length===2)break;}
let H1=H+p-1+E,H2=H1+r-1+F;if(got.length===2&&got[0].join(",")===[H1,r,n+V,t].join(",")&&got[1].join(",")===[H2,v,n+V+W,u].join(",")){real++;totals.alignedActualCandidates++}
}
counts.push({L,W:Wmax,configs,candidates:brute.size,real});
}
results.push({X,T,B,counts,totals:Object.fromEntries(Object.keys(totals).map(k=>[k,totals[k]-before[k]]))});
}
return {totals,results,examples}
}
console.log(JSON.stringify(audit(),null,2));
