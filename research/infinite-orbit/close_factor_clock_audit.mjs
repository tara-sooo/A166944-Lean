// Run: node research/infinite-orbit/close_factor_clock_audit.mjs
function audit(){
const max=4*65536+4096,spf=new Int32Array(max+1);
for(let p=2;p*p<=max;p++)if(!spf[p])for(let n=p*p;n<=max;n+=p)if(!spf[n])spf[n]=p;
function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
function prime(n){return Number.isInteger(n)&&n>=2&&n<=max&&!spf[n]}
function gcd(a,b){a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a}
function mod(a,b){return (a%b+b)%b}
function elig(H){let B=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=B),fac(H+1).filter(p=>p<=B)]}
function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let z=1+mod((i?q+2:0)-t-1,2*q);if(z<w||(z===w&&q<p)){p=q;w=z;s=i}}return {p,w,s}}
function gap(n,p,f){let W=2*p;for(let i=0;i<2;i++)for(let q of f[i])if(q!==p){let z=mod(n-(i?q+2:0),2*q);if(!z&&q<p)return 0;W=Math.min(W,z||2*q)}return W}
function ok(v,m){if(!v)throw Error(m)}
let totals={roots:0,targeted:0,events:0,stops:0,exits:0,caps:0,high:0,pairs:0,distinct:0,close:0,three:0,four:0,compositeTarget:0,determinants:0,clock:0,fastClose:0,zeroClockDet:0,literal:0,census:0,threeCandidates:0,fourCandidates:0,localized:0},results=[],examples={three:null,four:null,fastComposite:null,zero:null};
for(let X of [4096,16384,65536]){
const Y=4*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(Y+1)),Q=Math.floor((Y+1)/T);
let roots=0,targeted=0,events=0,high=0,pairs=0,close=0,three=0,four=0,comp=0,fastClose=0;
function scan(H,t,can){
let last=null;
for(let i=0;i<2000&&H<Y;i++){
let z=first(t,elig(H));if(!z.p){totals.stops++;break}let {p,w,s}=z,e=1-2*s,q=(H-e)/p,J=H+p-1,n=t+w,a=q+1,c=(n-2*s)/p;
ok(Number.isInteger(q)&&Number.isInteger(c)&&q>=p,"coords");let v={H,t,p,w,s,e,q,J,n,a,c};events++;totals.events++;
if(totals.events%9973===0){let found=null;for(let w0=1;w0<=2*Math.floor(Math.sqrt(H+1));w0++){let n0=t+w0,d=gcd(n0%2?n0-2:n0,n0%2?H+1:H-1),p0=fac(d).find(f=>f<=Math.floor(Math.sqrt(H+1)));if(p0){found=[p0,w0];break}}ok(found&&found[0]===p&&found[1]===w,"literal");totals.literal++}
if(p>=T){high++;totals.high++;
if(last){pairs++;totals.pairs++;let d=p-last.p,j=q-last.q,k=c-last.c,E=H-last.J,V=n-last.n,D=E-1+2*(s-last.s),R=V-2*(s-last.s);
ok(E>=0&&E%2===0&&V>=1&&V<=3*E+w,"relay");ok(d*last.a+(j-1)*p===D&&d*last.c+k*p===R,"joint equation");ok(d*((j-1)*last.c-k*last.a)===(j-1)*R-k*D,"clock elimination");totals.clock++;
if(d!==0){totals.distinct++;ok(j%2===0&&D%2!==0,"parity");let A=1-j,C=D-d*j;
ok(d*last.q===A*last.p+C&&d*q===A*last.p+D,"affine factor");ok(A!==0&&C!==0&&D-d!==0&&D!==0&&D-d*A!==0,"nondegenerate three determinants");totals.determinants++;
if(Math.abs(d)<=16&&E<=16){close++;totals.close++;ok(Math.abs(j)<=1+(Math.abs(d)*(Q+1)+E+3)/T,"j bound");
if(prime(last.q)){three++;totals.three++;let data={X,can,prev:last,next:v,d,j,k,E,V,D,R,clockDet:(j-1)*last.c-k*last.a};if(prime(q)){four++;totals.four++;ok(j!==0,"no common cofactor cheap");if(!examples.four)examples.four=data}else{comp++;totals.compositeTarget++;if(!examples.three)examples.three=data;if(4*w<=p-1&&!examples.fastComposite)examples.fastComposite=data}}
if(4*w<=p-1){fastClose++;totals.fastClose++}
if((j-1)*last.c-k*last.a===0){totals.zeroClockDet++;if(!examples.zero)examples.zero={X,can,prev:last,next:v,d,j,k,E,V,D,R}}
}
}else ok(E>=last.p-1,"same label relay");
}
last=v;
}
H=J;t=n;if(i===1999&&H<Y)totals.caps++;
}
if(H>=Y)totals.exits++;
}
for(let H=X;H<Y;H+=4){scan(H,(H+6)/2,true);roots++;totals.roots++}
let seen=new Set();
for(let H=X;H<Y;H+=Math.max(2,2*Math.floor(Math.sqrt(X)/8))){
let f=elig(H);for(let s=0;s<2;s++)for(let p of f[s]){if(p<T)continue;let r=s?p+2:0,lo=H/2+1,hi=3*H+3+2*p;
for(let frac of [1,3,5]){let base=Math.floor(lo+(hi-lo)*frac/6),n=base+mod(r-base,2*p);if(n>hi)continue;let W=gap(n,p,f),l=Math.max(1,n-(3*H+3)),u=Math.min(W,n-H/2);if(l>u)continue;for(let w of new Set([l,u])){let t=n-w,key=H+","+t;if(seen.has(key))continue;seen.add(key);let a=first(t,f);ok(a.p===p&&a.w===w,"target");scan(H,t,false);targeted++;totals.targeted++}}
}}
let rows=[];
for(let K of [2,4,8,16])for(let L of [0,4,16]){
// independent product enumeration with source prime cofactor, target cofactor arbitrary, both labels prime.
let expected=new Set(),fourExpected=new Set(),got=new Set(),fourGot=new Set();
for(let p=T;p<=B;p++)if(prime(p))for(let q=p;q<=Q;q++)if(prime(q))for(let e of [-1,1]){
let H=p*q+e;if(H<X||H>=Y||p*p>H+1)continue;
for(let E=0;E<=L;E+=2){let H2=H+p-1+E;if(H2>=Y)continue;for(let f of [-1,1])for(let r of fac(H2-f)){if(r<T||r>B||r===p||Math.abs(r-p)>K||r*r>H2+1)continue;let u=(H2-f)/r;if(u<r)continue;let key=[p,q,e,r,u,f,E].join(",");expected.add(key);if(prime(u))fourExpected.add(key)}}}
for(let d=-K;d<=K;d+=2){if(!d)continue;for(let j=-2*Math.ceil(1+(Math.abs(d)*(Q+1)+L+3)/T);j<=2*Math.ceil(1+(Math.abs(d)*(Q+1)+L+3)/T);j+=2)for(let E=0;E<=L;E+=2)for(let e of [-1,1])for(let f of [-1,1]){
let D=E-1+e-f,A=1-j,C=D-d*j,g=gcd(A,d);if(C%g)continue;let step=Math.abs(d)/g,base=0;while(mod(A*base+C,Math.abs(d))!==0)base++;
for(let p=T+mod(base-T,step);p<=B;p+=step){let r=p+d,q=(A*p+C)/d,u=q+j;if(!prime(p)||!prime(r)||r<T||r>B||!prime(q)||q<p||u<r||u%2!==1)continue;let H=p*q+e,H2=r*u+f;if(H<X||H>=Y||H2<X||H2>=Y||H2!==H+p-1+E||p*p>H+1||r*r>H2+1)continue;let key=[p,q,e,r,u,f,E].join(",");ok(!got.has(key),"duplicate");got.add(key);if(prime(u))fourGot.add(key)}
}}
ok(got.size===expected.size&&[...got].every(k=>expected.has(k)),"three census");ok(fourGot.size===fourExpected.size&&[...fourGot].every(k=>fourExpected.has(k)),"four census");totals.census++;totals.threeCandidates+=got.size;totals.fourCandidates+=fourGot.size;
let D=Math.ceil(X**.75);for(let off of [0,Math.floor(D/3)]){let m=new Map(),n=new Map();for(let key of expected){let [p,q,e]=key.split(",").map(Number),b=Math.floor((p*q+e-off)/D);m.set(b,(m.get(b)||0)+1)}for(let key of got){let [p,q,e]=key.split(",").map(Number),b=Math.floor((p*q+e-off)/D);n.set(b,(n.get(b)||0)+1)}ok(m.size===n.size&&[...m].every(([b,v])=>n.get(b)===v),"localized");totals.localized++}
rows.push({K,L,three:got.size,four:fourGot.size});
}
results.push({X,T,B,roots,targeted,events,high,pairs,close,three,four,comp,fastClose,rows});
}
return {totals,results,examples}
}
console.log(JSON.stringify(audit(),null,2));
