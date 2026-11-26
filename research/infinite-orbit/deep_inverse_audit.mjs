// Run: node research/infinite-orbit/deep_inverse_audit.mjs
function audit(){
const max=4*65536+4096,spf=new Int32Array(max+1);for(let p=2;p*p<=max;p++)if(!spf[p])for(let n=p*p;n<=max;n+=p)if(!spf[n])spf[n]=p;
function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
function prime(n){return n>=2&&!spf[n]}
function mod(a,b){return (a%b+b)%b}
function gcd(a,b){while(b){[a,b]=[b,a%b]}return Math.abs(a)}
function elig(H){let B=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=B),fac(H+1).filter(p=>p<=B)]}
function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let z=1+mod((i?q+2:0)-t-1,2*q);if(z<w||(z===w&&q<p)){p=q;w=z;s=i}}return {p,w,s}}
function gap(n,p,s,f){let W=2*p;for(let i=0;i<2;i++)for(let q of f[i])if(q!==p){let z=mod(n-(i?q+2:0),2*q);if(!z&&q<p)return 0;W=Math.min(W,z||2*q)}return W}
function ok(x,m){if(!x)throw Error(m)}
const R=7,K=210,ps=[3,5,7],M=34;
let offsets=new Set();for(let h=0;h<K;h+=2)for(let t=0;t<K;t++){let H=h,u=t;while(true){let a=first(u,[ps.filter(p=>mod(H-1,p)===0),ps.filter(p=>mod(H+1,p)===0)]);if(!a.p)break;H+=a.p-1;u+=a.w}offsets.add(`${H-h},${u-t}`)}
let relays=[...offsets].map(s=>s.split(",").map(Number)),results=[],literalChecks=0,reverseChecks=0,reverseEdges=0,relayChecks=0;
function literal(H,t){let B=Math.floor(Math.sqrt(H+1));for(let w=1;w<=2*B;w++){let n=t+w,g=gcd(n%2?n-2:n,n%2?H+1:H-1),p=fac(g).find(q=>q<=B);if(p)return {p,w,s:n%2}}return {p:0,w:Infinity,s:0}}
for(let X of [4096,16384,65536]){
let Y=4*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(Y+1)),candidate=0,arrivals=0,feasible=0,deep=0,ambiguity=new Map(),seenPairs=new Set(),maxIncoming=0,primePairChecks=0,collisionExamples=[],gcdChecks=0,possibleRational=0,cofactorExceptions=0;
function inverse(H2,n){let s=n%2,A=H2+2*s,C=n-2*s,G=gcd(A,C),out=[];
for(let p of fac(A)){if(p<T||p>B||C%p)continue;let H=H2-p+1;if(H<X||H>=Y||p*p>H+1)continue;let f=elig(H);if(!f[s].includes(p))continue;
let W=gap(n,p,s,f),l=Math.max(p-2,n-(3*H+3)),u=Math.min(W,n-H/2);
if(l<=u)out.push({H,p,s,l,u});
}return out}
function backMixed(H2,n){let result=new Set();
for(let cur of inverse(H2,n)){let H=cur.H;
for(let [E,C] of relays){let J=H-E;if(J<X)continue;
for(let s=0;s<2;s++)for(let p of fac(J+2*s)){if(p<T||p>B)continue;
let r=s?p+2:0,L=n-cur.u-C,U=n-cur.l-C;
for(let t=L+mod(r-L,2*p);t<=U;t+=2*p){
let prev=inverse(J,t).find(a=>a.p===p);if(!prev)continue;
let h=J,u=t,valid=true;while(h<H){let a=first(u,elig(h));if(!a.p||a.p>R){valid=false;break}h+=a.p-1;u+=a.w}
if(!valid||h!==H||u!==t+C)continue;
let a=first(u,elig(h));if(a.p!==cur.p||a.w<cur.p-2||u+a.w!==n)continue;
result.add(`${J},${t}`);relayChecks++;
}}}}
ok(result.size<=8*relays.length*(1+Math.floor(B/T)),"bounded reverse degree");return result}
let prevExamples=[],sampled=0,maxBack=0,backAmbiguous=0;
for(let H=X;H<Y;H+=2){let f=elig(H);for(let s=0;s<2;s++)for(let p of f[s]){if(p<T||p>B)continue;candidate++;
let H2=H+p-1,lo=H/2+p-2,hi=3*H+3+2*p,r=s?p+2:0;
for(let n=lo+mod(r-lo,2*p);n<=hi;n+=2*p){arrivals++;let W=gap(n,p,s,f),l=Math.max(p-2,n-(3*H+3)),u=Math.min(W,n-H/2);if(l>u)continue;
feasible++;let d=2*n-H2,h=(d-6*s)/(2*p);ok(h>=1&&Number.isInteger(h),"high adjusted");if(d>=X/4)deep++;
let A=H2+2*s,C=n-2*s,G=gcd(A,C);ok(G%p===0,"gcd");gcdChecks++;let factors=fac(A).filter(q=>q>=T&&q<=B&&C%q===0);ok(factors.length<=2,"high inverse degree");
if(factors.length>1){possibleRational++;let key=`${H2},${n}`;if(!ambiguity.has(key))ambiguity.set(key,new Set());ambiguity.get(key).add(p)}
if(feasible%997===0){let v=inverse(H2,n);ok(v.some(a=>a.p===p&&a.l===l&&a.u===u),"exact inverse");let a=literal(H,n-l);ok(a.p===p&&a.w===l,"literal");literalChecks++;
let bk=backMixed(H2,n);maxBack=Math.max(maxBack,bk.size);if(bk.size>1)backAmbiguous++;reverseChecks++;
for(let key of bk){let [J,t]=key.split(",").map(Number);let vv=inverse(J,t);ok(vv.length>0,"prior valid");reverseEdges++}
}
// Generate actual adjacent mixed pair from a sparse arrival sample; check reverse inclusion.
if(feasible%193===0){let hh=H2,tt=n;for(let j=0;j<=M/2+1&&hh<Y;j++){let a=first(tt,elig(hh));if(!a.p)break;if(a.p<=R){hh+=a.p-1;tt+=a.w;continue}if(a.p>=T&&a.w>=a.p-2){let end=hh+a.p-1,nt=tt+a.w,bk=backMixed(end,nt);ok(bk.has(`${H2},${n}`),"reverse includes actual predecessor");sampled++;maxBack=Math.max(maxBack,bk.size);if(prevExamples.length<2)prevExamples.push([H2,n,end,nt,bk.size]);}break}}
}
}}
let collided=0,deepCollided=0,ambiguousLabelIncidences=0;
for(let [key,labels] of ambiguity){let [H2,n]=key.split(",").map(Number);let v=inverse(H2,n);ok(v.length===labels.size,"inverse collision enumeration");maxIncoming=Math.max(maxIncoming,v.length);
if(v.length<2)continue;collided++;ambiguousLabelIncidences+=v.length;if(2*n-H2>=X/4)deepCollided++;
let s=n%2,[p,r]=v.map(x=>x.p),a=(H2+2*s)/(p*r),c=(n-2*s)/(p*r);
ok(Number.isInteger(a)&&a%2===0&&Number.isInteger(c),"resonance");ok(a<= (Y+B+2)/(T*T)&&c<= (3*Y+3+2*B)/(T*T),"bounded coefficients");
let e=1-2*s,q1=a*r-1,q2=a*p-1;ok(v[0].H===p*q1+e&&v[1].H===r*q2+e,"cofactor forms");
if(prime(q1)&&prime(q2))primePairChecks++;else cofactorExceptions++;
seenPairs.add([Math.min(p,r),Math.max(p,r),a].join(","));
if(collisionExamples.length<4)collisionExamples.push({H2,n,p,r,a,c,d:2*n-H2,h:v.map(z=>(2*n-H2-6*s)/(2*z.p)),cofactors:[q1,q2],waits:v.map(z=>[z.l,z.u])});
}
results.push({X,T,B,candidate,arrivals,feasible,deep,gcdChecks,possibleRational,collided,deepCollided,ambiguousLabelIncidences,maxIncoming,primePairChecks,cofactorExceptions,distinctPairs:seenPairs.size,collisionExamples,sampled,maxBack,backAmbiguous,prevExamples})
}
return {relayOffsets:relays.length,literalChecks,reverseChecks,reverseEdges,relayChecks,results}
}
console.log(JSON.stringify(audit(),null,2));
