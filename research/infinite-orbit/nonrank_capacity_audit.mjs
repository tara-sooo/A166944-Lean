// Run: node research/infinite-orbit/nonrank_capacity_audit.mjs
function audit(){
const max=4*65536+4096,spf=new Int32Array(max+1);
for(let p=2;p*p<=max;p++)if(!spf[p])for(let x=p*p;x<=max;x+=p)if(!spf[x])spf[x]=p;
function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
function prime(n){return Number.isInteger(n)&&n>=2&&n<=max&&!spf[n]}
function gcd(a,b){a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a}
function mod(a,b){return (a%b+b)%b}
function elig(H){let B=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=B),fac(H+1).filter(p=>p<=B)]}
function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let z=1+mod((i?q+2:0)-t-1,2*q);if(z<w||(z===w&&q<p)){p=q;w=z;s=i}}return {p,w,s}}
function gap(n,p,f){let W=2*p;for(let i=0;i<2;i++)for(let q of f[i])if(q!==p){let z=mod(n-(i?q+2:0),2*q);if(!z&&q<p)return 0;W=Math.min(W,z||2*q)}return W}
function ok(v,m){if(!v)throw Error(m)}
let totals={roots:0,targeted:0,events:0,stops:0,exits:0,cap:0,high:0,triples:0,nonrank:0,rank:0,cramer:0,compositeSource:0,words:0,localWitness:0,literal:0,censuses:0,primeCandidates:0,compositeCandidates:0,latticeTuples:0,latticeBounds:0},results=[],examples={prime:null,composite:null};
for(let X of [4096,16384,65536]){
let Y=4*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(Y+1)),Q=Math.floor((Y+1)/T),before={...totals};
function triple(a,b,c,can){
let d=b.p-a.p,f=c.p-a.p,j=b.q-a.q-1,k=c.q-a.q-2,E1=b.H-a.H-a.p+1,E2=c.H-a.H-a.p-b.p+2,R1=-1+E1+a.e-b.e-d*(1+j),R2=d-2+E2+a.e-c.e-f*(2+k),det=d*k-f*j;
ok(d*a.q+j*a.p===R1&&f*a.q+k*a.p===R2,"row");totals.triples++;
if(det){ok(det%2===0&&(d*R2-f*R1)/det===a.p&&(R1*k-R2*j)/det===a.q,"Cramer");totals.nonrank++;totals.cramer++;if(!prime(a.q)){totals.compositeSource++;if(!examples.composite)examples.composite={X,can,a,b,c,E1,E2,det,d,f,j,k,R1,R2};}else if(!examples.prime)examples.prime={X,can,a,b,c,E1,E2,det,d,f,j,k,R1,R2};}else totals.rank++;
return det;
}
function scan(H,t,can){
let list=[],dets=[];
for(let it=0;it<2000&&H<Y;it++){
let a=first(t,elig(H));if(!a.p){totals.stops++;break}let {p,w,s}=a,e=1-2*s,q=(H-e)/p,J=H+p-1,n=t+w;let v={H,t,p,w,s,e,q,J,n};totals.events++;
if(totals.events%9973===0){let found=null;for(let w0=1;w0<=2*Math.floor(Math.sqrt(H+1));w0++){let n0=t+w0,d=gcd(n0%2?n0-2:n0,n0%2?H+1:H-1),p0=fac(d).find(f=>f<=Math.floor(Math.sqrt(H+1)));if(p0){found=[p0,w0];break}}ok(found&&found[0]===p&&found[1]===w,"literal");totals.literal++;}
if(p>=T){list.push(v);totals.high++;let m=list.length;if(m>=3)dets.push(triple(...list.slice(-3),can));for(let k=3;k<=Math.min(5,m);k++){let l=list.slice(-k);if(l.slice(1).some((v,i)=>v.p===l[i].p))continue;let a=l[0],b=l[1],d=b.p-a.p,j=b.q-a.q-1,rank=l.every((v,i)=>d*(v.q-a.q-i)===(v.p-a.p)*j);ok(rank===dets.slice(-(k-2)).every(x=>x===0),"local rank equivalence");totals.words++;if(!rank)totals.localWitness++;}}
H=J;t=n;if(it===1999&&H<Y)totals.cap++;
}if(H>=Y)totals.exits++;
}
for(let H=X;H<Y;H+=4){scan(H,(H+6)/2,true);totals.roots++}
let seen=new Set();for(let H=X;H<Y;H+=Math.max(2,2*Math.floor(Math.sqrt(X)/8))){let f=elig(H);for(let s=0;s<2;s++)for(let p of f[s]){if(p<T)continue;let r=s?p+2:0,lo=H/2+1,hi=3*H+3+2*p;for(let frac of [1,3,5]){let base=Math.floor(lo+(hi-lo)*frac/6),n=base+mod(r-base,2*p);if(n>hi)continue;let W=gap(n,p,f),l=Math.max(1,n-(3*H+3)),u=Math.min(W,n-H/2);if(l>u)continue;for(let w of new Set([l,u])){let t=n-w,key=H+","+t;if(seen.has(key))continue;seen.add(key);let a=first(t,f);ok(a.p===p&&a.w===w,"target");scan(H,t,false);totals.targeted++;}}}}
let counts=[];
for(let [K,L] of [[4,0],[8,0],[8,4],[16,0]]){
let expected=new Set(),got=new Set();
for(let p=T;p<=B;p++)if(prime(p))for(let q=p;q<=Q;q+=2)for(let e of [-1,1]){
let H=p*q+e;if(H<X||H>=Y||p*p>H+1)continue;
for(let E1=0;E1<=L;E1+=2){let H1=H+p-1+E1;if(H1>=Y)continue;
for(let f of [-1,1])for(let r of fac(H1-f)){if(r<T||r>B||r===p||Math.abs(r-p)>K||r*r>H1+1)continue;let u=(H1-f)/r,a=r-p,j=u-q-1;
for(let E2=E1;E2<=L;E2+=2){let H2=H+p+r-2+E2;if(H2>=Y)continue;
for(let h of [-1,1])for(let v of fac(H2-h)){if(v<T||v>B||v===r||Math.abs(v-p)>K||v*v>H2+1)continue;let z=(H2-h)/v,b=v-p,k=z-q-2;if(a*k!==b*j)expected.add([p,q,e,r,u,f,v,z,h,E1,E2].join(","));}
}
}}
}
let Jmax=Math.ceil((K*(Q+2)+2*(K+1)+L+2)/T),Rbound=2*(K+1)+L+2+K*(2+Jmax),M=Math.floor(2*K*Rbound/T);
for(let a=-K;a<=K;a+=2){if(!a)continue;for(let b=-K;b<=K;b+=2){if(b===a)continue;
let gg=gcd(a,b),Ja=Math.ceil((Math.abs(a)*(Q+2)+2*(K+1)+L+2)/T),Jb=Math.ceil((Math.abs(b)*(Q+2)+2*(K+1)+L+2)/T),lattice=0;
for(let j=-Ja;j<=Ja;j++){if(mod(j,2)!==1)continue;
for(let k=-Jb;k<=Jb;k++){if(k%2)continue;let det=a*k-b*j;if(!det||Math.abs(det)>M)continue;lattice++;totals.latticeTuples++;
for(let E1=0;E1<=L;E1+=2)for(let E2=E1;E2<=L;E2+=2)for(let e of [-1,1])for(let f of [-1,1])for(let h of [-1,1]){
let R1=-1+E1+e-f-a*(1+j),R2=a-2+E2+e-h-b*(2+k),p=(a*R2-b*R1)/det,q=(R1*k-R2*j)/det,r=p+a,u=q+1+j,v=p+b,z=q+2+k;
if(!prime(p)||!prime(r)||!prime(v)||p<T||p>B||r<T||r>B||v<T||v>B||!Number.isInteger(q)||q<p||q%2!==1||u<r||z<v||u%2!==1||z%2!==1)continue;
let H=p*q+e,H1=r*u+f,H2=v*z+h;if(H<X||H>=Y||H1>=Y||H2>=Y||H1!==H+p-1+E1||H2!==H+p+r-2+E2||p*p>H+1||r*r>H1+1||v*v>H2+1)continue;
got.add([p,q,e,r,u,f,v,z,h,E1,E2].join(","));
}}}ok(lattice<=2*Math.floor(M/gg)*(1+Math.floor(2*Ja*gg/Math.abs(a))),"lattice bound");totals.latticeBounds++;
}}
ok(got.size===expected.size&&[...got].every(k=>expected.has(k)),"nonrank exact census");
let primeN=[...got].filter(k=>prime(Number(k.split(",")[1]))).length;totals.censuses++;totals.primeCandidates+=primeN;totals.compositeCandidates+=got.size-primeN;counts.push({K,L,prime:primeN,composite:got.size-primeN});
}
results.push({X,T,B,counts,totals:Object.fromEntries(Object.keys(totals).map(k=>[k,totals[k]-before[k]]))});
}
return {totals,results,examples}
}
console.log(JSON.stringify(audit(),null,2));
