// Run: node research/infinite-orbit/middle_projection_audit.mjs
function audit(){
const max=12*65536+4096,spf=new Int32Array(max+1);for(let p=2;p*p<=max;p++)if(!spf[p])for(let n=p*p;n<=max;n+=p)spf[n]=p;
function fac(n){if(!Number.isInteger(n)||n<1||n>max)throw Error('factor domain '+n);let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
function prime(n){return Number.isInteger(n)&&n>=2&&n<=max&&!spf[n]}
function mod(a,b){return (a%b+b)%b}
function gcd(a,b){a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a}
function inv(a,b){let x=1,y=0,u=mod(a,b),v=b;while(v){let k=Math.floor(u/v);[u,v]=[v,u-k*v];[x,y]=[y,x-k*y]}if(u!==1)throw Error("inverse");return mod(x,b)}
function elig(H){let B=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=B),fac(H+1).filter(p=>p<=B)]}
function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let z=1+mod((i?q+2:0)-t-1,2*q);if(z<w||(z===w&&q<p)){p=q;w=z;s=i}}return {p,w,s}}
function gap(n,p,f){let W=2*p;for(let i=0;i<2;i++)for(let q of f[i])if(q!==p){let z=mod(n-(i?q+2:0),2*q);if(!z&&q<p)return 0;W=Math.min(W,z||2*q)}return W}
function ok(v,m){if(!v)throw Error(m)}
let totals={roots:0,targeted:0,events:0,stops:0,exits:0,cap:0,high:0,triples:0,distinct:0,nonparallel:0,inverse:0,uniqueR:0,projection:0,smallStrip:0,nonzeroStrip:0,smallCoefficients:0,nonproportional:0,degenerate:0,wide:0,deficit:0,literal:0,censuses:0,configs:0,necessary:0,local:0,localWide:0,localPrimeSource:0,allProjectionSmall:0,degenerateCandidates:0,degenerateLocal:0,evenDenominator:0},results=[],examples={small:null,wide:null,local:null,localWide:null};
const ratios=[[1,2],[1,1],[2,1],[3,2],[2,3]];
for(let X of [4096,16384,65536]){
let Y=4*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(Y+1)),before={...totals};
function clock(p,s){return s?p+2:0}
function A(x){return x.q+1}
function C(x){return (x.n-2*x.s)/x.p}
function shift(a,b){let E=b.H-a.J,V=b.n-a.n,s=b.s-a.s,D=E-1+2*s,d=V-2*s,m=(D*C(a)-d*A(a))/b.p;return {E,V,D,d,m}}
function inspect(a,b,c,can){
totals.triples++;let p=a.p,r=b.p,v=c.p;if(new Set([p,r,v]).size!==3)return;totals.distinct++;
let x=shift(a,b),y=shift(b,c),Q=x.D*y.d-y.D*x.d;
ok(Number.isInteger(x.m)&&Number.isInteger(y.m),"integer determinant");
if(Q){
totals.nonparallel++;let aa=(y.D*(p*x.m-x.d)-x.D*v*y.m)/Q,cc=(y.d*(p*x.m-x.d)-x.d*v*y.m)/Q;
ok(aa===A(b)&&cc===C(b),"middle inverse");
ok((r*(aa-1)-x.D)/p===A(a)&&(r*cc-x.d)/p===C(a)&&(r*aa+y.D)/v+1===A(c)&&(r*cc+y.d)/v===C(c),"outer inverse");
totals.inverse++;
if(mod(Q,p)&&mod(Q,v)&&mod(x.d,p)&&mod(y.d,v)){
let rp=mod(-Q*inv(v*y.m+y.d,p),p),rv=mod(-Q*inv(p*x.m-x.d,v),v);
let rr=rp+p*mod((rv-rp)*inv(p,v),v);
ok(rr===r,"unique middle CRT");totals.uniqueR++;
}}
for(let [M,N] of ratios){
let h0=N*C(a)-M*A(a),h=N*C(b)-M*A(b),h2=N*C(c)-M*A(c),w1=N*x.d-M*x.D,w2=N*y.d-M*y.D;
ok(r*(h+M)===p*h0+w1&&v*(h2+M)===r*h+w2,"projection");totals.projection++;
if(M===1&&N===2){ok(r*h===2*b.n-b.J-6*b.s,"deficit");totals.deficit++}
if(Math.abs(h)>16||x.E+y.E>16||x.V+y.V>16)continue;totals.smallStrip++;
if(Math.abs(w1)<T&&Math.abs(w2)<T&&Math.abs(h)<T&&Math.abs(h+M)<T&&Math.abs(h0)<T&&Math.abs(h2+M)<T){
totals.smallCoefficients++;totals.allProjectionSmall++;
if(N%2===0){ok(w1&&w2&&h&&h+M,'even denominator no degeneracy');totals.evenDenominator++;}
if(h===0)ok(w2===0&&h2===-M&&!y.m&&w1!==0,'zero middle projection');
if(h===-M)ok(w1===0&&h0===0&&!x.m&&w2!==0,'negative middle projection');
if(x.m&&y.m){ok(h&&h+M&&h0&&h2+M&&w1&&w2,"nonzero projection");totals.nonzeroStrip++;
ok((r*(h+M)-w1)/h0===p&&(r*h+w2)/(h2+M)===v,"affine reconstruction");
let det=(h+M)*w2+h*w1;
// If proportional, p/v=small coefficient ratio; distinct primes rule it out for small coefficients.
ok(det!==0,"three nonproportional forms");totals.nonproportional++;
let data={X,can,a,b,c,M,N,h0,h,h2,w1,w2,x,y,Q,det};if(!examples.small)examples.small=data;
if(Math.min(Math.abs(p-r),Math.abs(r-v),Math.abs(p-v))>=T/4){totals.wide++;if(!examples.wide)examples.wide=data;}
}else{totals.degenerate++;if(!w1)ok(h0===0&&h===-M&&!x.m,"first zero");if(!w2)ok(h===0&&h2===-M&&!y.m,"second zero");}
}
}
}
function scan(H,t,can){let list=[];for(let it=0;it<2000&&H<Y;it++){let z=first(t,elig(H));if(!z.p){totals.stops++;break}let {p,w,s}=z,e=1-2*s,q=(H-e)/p,J=H+p-1,n=t+w;let z0={H,t,p,w,s,e,q,J,n};totals.events++;
if(totals.events%9973===0){let found=null;for(let w0=1;w0<=2*Math.floor(Math.sqrt(H+1));w0++){let n0=t+w0,d=gcd(n0%2?n0-2:n0,n0%2?H+1:H-1),p0=fac(d).find(f=>f<=Math.floor(Math.sqrt(H+1)));if(p0){found=[p0,w0];break}}ok(found&&found[0]===p&&found[1]===w,"literal");totals.literal++;}
if(p>=T){list.push(z0);totals.high++;if(list.length>=3)inspect(...list.slice(-3),can);}
H=J;t=n;if(it===1999&&H<Y)totals.cap++;}if(H>=Y)totals.exits++;}
for(let H=X;H<Y;H+=4){scan(H,(H+6)/2,true);totals.roots++}
let seen=new Set();for(let H=X;H<Y;H+=Math.max(2,2*Math.floor(Math.sqrt(X)/8))){let f=elig(H);for(let s=0;s<2;s++)for(let p of f[s]){if(p<T)continue;let r=clock(p,s),lo=H/2+1,hi=3*H+3+2*p;for(let frac of [1,3,5]){let base=Math.floor(lo+(hi-lo)*frac/6),n=base+mod(r-base,2*p);if(n>hi)continue;let W=gap(n,p,f),l=Math.max(1,n-(3*H+3)),u=Math.min(W,n-H/2);if(l>u)continue;for(let w of new Set([l,u])){let t=n-w,key=H+","+t;if(seen.has(key))continue;seen.add(key);let a=first(t,f);ok(a.p===p&&a.w===w,"target");scan(H,t,false);totals.targeted++;}}}}
let ps=[];for(let p=T;p<=B;p++)if(prime(p))ps.push(p);
function highFac(n){return fac(n).filter(p=>p>=T&&p<=B)}
function horizons(p,r,v,E,F,s,t,u){
let e=1-2*s,f=1-2*t,g=1-2*u,base=e+p,period=2*p*r,H0=base+2*p*mod((f-p+1-E-base)*inv(2*p,r),r),out=[];
for(let H=X+mod(H0-X,period);H<Y;H+=period){let H1=H+p-1+E,H2=H1+r-1+F;if(H1>=Y||H2>=Y||mod(H2-g,v)||p*p>H+1||r*r>H1+1||v*v>H2+1)continue;out.push([H,H1,H2]);}return out;
}
function add(out,H,H1,H2,p,r,v,n,E,F,V,W,s,t,u,M,N,cap){
if(n<H/2+1||n>3*H+3+2*p||mod(n-clock(p,s),2*p)||mod(n+V-clock(r,t),2*r)||mod(n+V+W-clock(v,u),2*v))return;
let a0=(H-(1-2*s))/p+1,a1=(H1-(1-2*t))/r+1,a2=(H2-(1-2*u))/v+1,c0=(n-2*s)/p,c1=(n+V-2*t)/r,c2=(n+V+W-2*u)/v;
let D1=E-1+2*(t-s),d1=V-2*(t-s),D2=F-1+2*(u-t),d2=W-2*(u-t),l1=(D1*c0-d1*a0)/r,l2=(D2*c1-d2*a1)/v;
ok(Number.isInteger(l1)&&Number.isInteger(l2),"census det");
let h=N*c1-M*a1,h0=N*c0-M*a0,h2=N*c2-M*a2,w1=N*d1-M*D1,w2=N*d2-M*D2;
if(Math.abs(h)>cap)return;
// Explicit finite sufficient conditions used by the theorem's nondegenerate affine class.
if(Math.max(Math.abs(h),Math.abs(h+M),Math.abs(h0),Math.abs(h2+M),Math.abs(w1),Math.abs(w2))>=T)return;
if(h!==0&&h!==-M)ok(h0&&h2+M&&w1&&w2&&(h+M)*w2+h*w1!==0,"census nondegenerate");else if(h===0)ok(w2===0&&h2===-M&&!l2&&w1!==0&&h0!==0,"census zero middle");else ok(w1===0&&h0===0&&!l1&&w2!==0&&h2+M!==0,"census negative middle");
if(N%2===0)ok(h!==0&&h!==-M,"even denominator census");
out.add([H,p,r,v,n,E,F,V,W,s,t,u].join(","));
}
let counts=[];
for(let [L,Wmax,cap,M,N] of [[0,4,4,1,2],[0,4,4,1,1],[2,6,8,1,2],[2,6,8,1,1]]){
if(X===65536&&L>0)continue;
let brute=new Set(),proj=new Set();
for(let E=0;E<=L;E+=2)for(let F=0;F<=L-E;F+=2)for(let s of [0,1])for(let t of [0,1])for(let u of [0,1])for(let V=1;V<Wmax;V++)for(let W=1;W<=Wmax-V;W++){
if(mod(V,2)!==mod(t-s,2)||mod(W,2)!==mod(u-t,2))continue;
totals.configs++;let w1=N*(V-2*(t-s))-M*(E-1+2*(t-s)),w2=N*(W-2*(u-t))-M*(F-1+2*(u-t));
for(let p of ps)for(let n=X/2+1+mod(clock(p,s)-(X/2+1),2*p);n<=3*Y+3+2*B;n+=2*p){
for(let r of highFac(n+V-2*t)){if(r===p||mod(n+V-clock(r,t),2*r))continue;for(let v of highFac(n+V+W-2*u)){if(v===p||v===r||mod(n+V+W-clock(v,u),2*v))continue;
for(let [H,H1,H2] of horizons(p,r,v,E,F,s,t,u))add(brute,H,H1,H2,p,r,v,n,E,F,V,W,s,t,u,M,N,cap);
}}}
if(Math.abs(w1)>=T||Math.abs(w2)>=T)continue;
// Degenerate cases: recover the nondegenerate neighboring prime pair, then factor the other corrected clock.
if(w2===0&&w1!==0){for(let r of ps){let Z1=r*M-w1;if(!Z1)continue;for(let p of highFac(Math.abs(Z1))){if(p===r||Math.abs(Z1/p)>=T)continue;
let base=clock(p,s),n0=base+2*p*mod((2*t-V-base)*inv(2*p,r),r),per=2*p*r;
for(let n=X/2+1+mod(n0-(X/2+1),per);n<=3*Y+3+2*B;n+=per)for(let v of highFac(n+V+W-2*u)){if(v===p||v===r)continue;for(let [H,H1,H2] of horizons(p,r,v,E,F,s,t,u)){let h=N*(n+V-2*t)/r-M*((H1-(1-2*t))/r+1);if(h===0)add(proj,H,H1,H2,p,r,v,n,E,F,V,W,s,t,u,M,N,cap);}}
}}}
if(w1===0&&w2!==0&&M<=cap){for(let r of ps){let Z2=-r*M+w2;if(!Z2)continue;for(let v of highFac(Math.abs(Z2))){if(v===r||Math.abs(Z2/v)>=T)continue;
let base=clock(r,t),n1=base+2*r*mod((2*u-W-base)*inv(2*r,v),v),per=2*r*v;
for(let mid=X/2+1+V+mod(n1-(X/2+1+V),per);mid<=3*Y+3+2*B+V;mid+=per){let n=mid-V;for(let p of highFac(n-2*s)){if(p===r||p===v)continue;for(let [H,H1,H2] of horizons(p,r,v,E,F,s,t,u)){let h=N*(mid-2*t)/r-M*((H1-(1-2*t))/r+1);if(h===-M)add(proj,H,H1,H2,p,r,v,n,E,F,V,W,s,t,u,M,N,cap);}}}
}}}
if(!w1||!w2)continue;
for(let r of ps)for(let h=-cap;h<=cap;h++){if(!h||h===-M||Math.abs(h+M)>=T)continue;
let Z1=r*(h+M)-w1,Z2=r*h+w2;if(!Z1||!Z2)continue;
for(let p of highFac(Math.abs(Z1))){if(p===r||Math.abs(Z1/p)>=T)continue;for(let v of highFac(Math.abs(Z2))){if(v===p||v===r||Math.abs(Z2/v)>=T)continue;
for(let [H,H1,H2] of horizons(p,r,v,E,F,s,t,u)){let n=(M*(H1-(1-2*t))+(M+h)*r)/N+2*t-V;if(!Number.isInteger(n))continue;add(proj,H,H1,H2,p,r,v,n,E,F,V,W,s,t,u,M,N,cap);}
}}}
}
ok(brute.size===proj.size&&[...brute].every(k=>proj.has(k)),"projection census equality");
totals.censuses++;totals.necessary+=brute.size;let real=0,deg=0,degReal=0;
for(let key of brute){let [H,p,r,v,n,E,F,V,W,s,t,u]=key.split(",").map(Number),hh=N*(n+V-2*t)/r-M*((H+p-1+E-(1-2*t))/r+1),isDeg=(hh===0||hh===-M);if(isDeg){deg++;totals.degenerateCandidates++;}let ff=elig(H),l=Math.max(1,n-(3*H+3)),hi=Math.min(gap(n,p,ff),n-H/2);if(l>hi)continue;let aa=first(n-l,ff);if(aa.p!==p||aa.w!==l||aa.s!==s)continue;
let H1=H+p-1+E,H2=H1+r-1+F,h=H+p-1,nn=n,got=[];for(let it=0;it<Wmax&&nn<n+V+W&&h<Y;it++){let z=first(nn,elig(h));if(!z.p||nn+z.w>n+V+W)break;nn+=z.w;if(z.p>=T)got.push([h,z.p,nn,z.s]);h+=z.p-1;if(got.length===2)break;}
if(got.length===2&&got[0].join(",")===[H1,r,n+V,t].join(",")&&got[1].join(",")===[H2,v,n+V+W,u].join(",")){
real++;totals.local++;if(isDeg){degReal++;totals.degenerateLocal++;}if(prime((H-(1-2*s))/p))totals.localPrimeSource++;
let a1=(H1-(1-2*t))/r+1,c1=(n+V-2*t)/r,hv=N*c1-M*a1,info={X,H,H1,H2,p,r,v,n,E,F,V,W,s,t,u,M,N,h:hv,sourceWait:l,q0:(H-(1-2*s))/p,q1:a1-1,q2:(H2-(1-2*u))/v};
if(!examples.local)examples.local=info;if(Math.min(Math.abs(p-r),Math.abs(r-v),Math.abs(p-v))>=T/4){totals.localWide++;if(!examples.localWide)examples.localWide=info;}
}
}
counts.push({L,W:Wmax,A:cap,M,N,necessary:brute.size,real,deg,degReal});
}
results.push({X,T,B,counts,totals:Object.fromEntries(Object.keys(totals).map(k=>[k,totals[k]-before[k]]))});
}
return {totals,results,examples}
}
console.log(JSON.stringify(audit(),null,2));
