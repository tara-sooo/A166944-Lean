// Run: node research/infinite-orbit/asymmetric_repeat_audit.mjs
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
let totals={roots:0,targeted:0,events:0,stops:0,exits:0,cap:0,high:0,triples:0,distinct:0,nonrank:0,detIdentities:0,detBound:0,repeats:0,repeatNonrank:0,shortRepeat:0,shortRepeatNonrank:0,repeatForms:0,primeFormChecks:0,fastRepeat:0,phaseSets:0,phaseCandidates:0,actualPhaseChecks:0,phaseReal:0,phaseNecessaryOnly:0,repeatCensuses:0,repeatCandidates:0,repeatPrimeSources:0,repeatNonrankCandidates:0,literal:0},results=[],examples={repeat:null,nonrankRepeat:null,shortNonrankRepeat:null,asymmetric:null,phase:null};
for(let X of [4096,16384,65536]){
let Y=4*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(Y+1)),Q=Math.floor((Y+1)/T),before={...totals},C=Q/T+3+4*B/T;
function clock(p,s){return s?p+2:0}
function phases(a,b,c,W){
let p=a.p,r=b.p,v=c.p,lo=a.H/2+1,hi=3*a.H+3+2*p,brute=new Set(),crt=new Set();
for(let n=lo+mod(clock(p,a.s)-lo,2*p);n<=hi;n+=2*p){
for(let V1=1+mod(clock(r,b.s)-n-1,2*r);V1<W;V1+=2*r){
for(let V2=V1+1+mod(clock(v,c.s)-n-V1-1,2*v);V2<=W;V2+=2*v)brute.add([n,V1,V2].join(","));
}}
let i=inv(p,r);
for(let V1=1;V1<W;V1++){
if(mod(V1,2)!==mod(b.s-a.s,2))continue;
let z=mod((2*b.s-V1-clock(p,a.s))*inv(2,r)*i,r),n0=clock(p,a.s)+2*p*z,P=2*p*r;
for(let n=lo+mod(n0-lo,P);n<=hi;n+=P){
let V2=V1+1+mod(clock(v,c.s)-n-V1-1,2*v);if(V2<=W)crt.add([n,V1,V2].join(","));
}}
ok(brute.size===crt.size&&[...brute].every(x=>crt.has(x)),"phase CRT equality");
ok(crt.size<=(W-1)*(1+Math.floor((hi-lo)/(2*p*r))),"phase bound");
totals.phaseSets++;totals.phaseCandidates+=crt.size;
let V1=b.n-a.n,V2=c.n-a.n;if(V2<=W){ok(crt.has([a.n,V1,V2].join(",")),"actual phase");totals.actualPhaseChecks++}
for(let key of crt){
let [n,v1,v2]=key.split(",").map(Number),f=elig(a.H),u=gap(n,p,f),l=Math.max(1,n-(3*a.H+3));u=Math.min(u,n-a.H/2);let real=false;
if(l<=u){let st=first(n-l,f);if(st.p===p&&st.w===l&&st.s===a.s){let H=a.H+p-1,t=n,got=[];for(let it=0;it<W&&t<n+W&&H<Y;it++){let z=first(t,elig(H));if(!z.p||t+z.w>n+W)break;t+=z.w;if(z.p>=T)got.push([H,z.p,z.s,t]);H+=z.p-1;if(got.length===2)break;}
real=got.length===2&&got[0].join(",")===[b.H,r,b.s,n+v1].join(",")&&got[1].join(",")===[c.H,v,c.s,n+v2].join(",");}}
if(real)totals.phaseReal++;else totals.phaseNecessaryOnly++;
if(!examples.phase&&real)examples.phase={X,p,r,v,H:a.H,n,V1:v1,V2:v2,W};
}
}
function inspect(a,b,c,can){
let p=a.p,r=b.p,v=c.p,q=a.q,u=b.q,z=c.q,A=r-p,D=v-p,j=u-q-1,k=z-q-2,E1=b.H-a.J,E2=c.H-b.J+E1,C1=E1-1+a.e-b.e,C2=E2-2+a.e-c.e,det=A*k-D*j;
ok(E1>=0&&E2>=E1&&E1%2===0&&E2%2===0,"relay");totals.triples++;
let R1=C1-A*(1+j),R2=A+C2-D*(2+k);ok(A*q+j*p===R1&&D*q+k*p===R2,"rows");
let rhs=A*(D-A)*(D*(q+1)-(p+A))+A*C2*(p+A)-D*C1*(p+D);
ok(det*r*v===rhs,"curvature identity");totals.detIdentities++;
if(det)totals.nonrank++;
if(new Set([p,r,v]).size===3){
totals.distinct++;let K=Math.max(Math.abs(A),Math.abs(D),2),min=Math.min(Math.abs(A),Math.abs(D),Math.abs(D-A));
ok(Math.abs(det)*T<=C*(Math.abs(A*D*(D-A))+K*(E2+1)),"asymmetric determinant bound");totals.detBound++;
if(!examples.asymmetric&&det&&min<=4&&E2<=4)examples.asymmetric={X,can,a,b,c,A,D,j,k,E1,E2,det,min};
}
if(v===p&&r!==p){totals.repeats++;let m=(z-q)/2,h=2-E2-a.e+c.e,M=2*m-1;
ok(Number.isInteger(m)&&m>=1&&r===M*p+h&&h!==0&&h%2===0,"repeat affine");ok(det===A*2*(m-1),"repeat rank");
let l=q+1-M*u;ok(l%2!==0&&h*(q+1)===M*C1+l*r&&h*u===l*p+C1,"repeat cofactor forms");totals.repeatForms++;
if(det){totals.repeatNonrank++;ok(r>=3*p-E2,"repeat large ratio");if(!examples.nonrankRepeat)examples.nonrankRepeat={X,can,a,b,c,m,M,h,l,E1,E2,det};}
if(!examples.repeat)examples.repeat={X,can,a,b,c,m,M,h,l,E1,E2,det};
if(E2<T-1){totals.shortRepeat++;if(det){totals.shortRepeatNonrank++;if(!examples.shortNonrankRepeat)examples.shortNonrankRepeat={X,can,a,b,c,m,M,h,l,E1,E2,det};}
let forms=[[1,0,p],[M,h,r]]; // multiply by h for cofactors to avoid fractions
if(prime(q))forms.push([M*l,l*h+M*C1-h,q]);
if(prime(u))forms.push([l,C1,u]);
if(prime(z))forms.push([M*l,l*h+M*C1+(2*m-1)*h,z]);
for(let i=0;i<forms.length;i++)for(let j=i+1;j<forms.length;j++){ok(forms[i][0]*forms[j][1]-forms[j][0]*forms[i][1]!==0,"repeat prime determinants");totals.primeFormChecks++}
}
if(c.n-a.n<p-2){totals.fastRepeat++;throw Error("too fast repeat");}
}
if(p!==r&&totals.phaseSets<500&&((totals.triples%17===0)||(c.n-a.n<=Math.min(T,64))))phases(a,b,c,Math.min(T,64));
}
function scan(H,t,can){let list=[];for(let it=0;it<2000&&H<Y;it++){let a=first(t,elig(H));if(!a.p){totals.stops++;break}let {p,w,s}=a,e=1-2*s,q=(H-e)/p,J=H+p-1,n=t+w;let v={H,t,p,w,s,e,q,J,n};totals.events++;
if(totals.events%9973===0){let found=null;for(let w0=1;w0<=2*Math.floor(Math.sqrt(H+1));w0++){let n0=t+w0,d=gcd(n0%2?n0-2:n0,n0%2?H+1:H-1),p0=fac(d).find(f=>f<=Math.floor(Math.sqrt(H+1)));if(p0){found=[p0,w0];break}}ok(found&&found[0]===p&&found[1]===w,"literal");totals.literal++;}
if(p>=T){list.push(v);totals.high++;if(list.length>=3)inspect(...list.slice(-3),can);}
H=J;t=n;if(it===1999&&H<Y)totals.cap++;}if(H>=Y)totals.exits++;}
for(let H=X;H<Y;H+=4){scan(H,(H+6)/2,true);totals.roots++}
let seen=new Set();for(let H=X;H<Y;H+=Math.max(2,2*Math.floor(Math.sqrt(X)/8))){let f=elig(H);for(let s=0;s<2;s++)for(let p of f[s]){if(p<T)continue;let r=clock(p,s),lo=H/2+1,hi=3*H+3+2*p;for(let frac of [1,3,5]){let base=Math.floor(lo+(hi-lo)*frac/6),n=base+mod(r-base,2*p);if(n>hi)continue;let W=gap(n,p,f),l=Math.max(1,n-(3*H+3)),u=Math.min(W,n-H/2);if(l>u)continue;for(let w of new Set([l,u])){let t=n-w,key=H+","+t;if(seen.has(key))continue;seen.add(key);let a=first(t,f);ok(a.p===p&&a.w===w,"target");scan(H,t,false);totals.targeted++;}}}}
let rows=[];
for(let L of [0,4,8,16]){
if(L>=T-1)continue;
let expected=new Set(),got=new Set();
for(let p=T;p<=B;p++)if(prime(p))for(let q=p;q<=Q;q+=2)for(let e of [-1,1]){let H=p*q+e;if(H<X||H>=Y||p*p>H+1)continue;
for(let E1=0;E1<=L;E1+=2){let H1=H+p-1+E1;if(H1>=Y)continue;
for(let f of [-1,1])for(let r of fac(H1-f)){if(r<T||r>B||r===p||r*r>H1+1)continue;let u=(H1-f)/r;
for(let E2=E1;E2<=L;E2+=2){let H2=H+p+r-2+E2;if(H2>=Y)continue;for(let g of [-1,1]){if((H2-g)%p||p*p>H2+1)continue;let z=(H2-g)/p;if(z<p||z%2!==1)continue;expected.add([p,q,e,r,u,f,p,z,g,E1,E2].join(","));}}}}}
for(let E2=0;E2<=L;E2+=2)for(let E1=0;E1<=E2;E1+=2)for(let e of [-1,1])for(let f of [-1,1])for(let g of [-1,1]){
let h=2-E2-e+g,C1=E1-1+e-f;if(!h)continue;
for(let M=1;M<=Math.ceil((B+L+4)/T);M+=2){
let cap=Math.ceil((Math.abs(h)*(Q+1)+M*Math.abs(C1))/T);
for(let l=-cap;l<=cap;l++){if(mod(l,2)!==1)continue;let gg=gcd(h,l);if(C1%gg)continue;let step=Math.abs(h)/gg,base=0;while(mod(l*base+C1,Math.abs(h))!==0)base++;
for(let p=T+mod(base-T,step);p<=B;p+=step){let r=M*p+h,u=(l*p+C1)/h,q=M*u+l-1,z=q+M+1;if(!prime(p)||!prime(r)||r===p||r<T||r>B||!Number.isInteger(q)||!Number.isInteger(u)||q<p||u<r||q%2!==1||u%2!==1)continue;
let H=p*q+e,H1=r*u+f,H2=p*z+g;if(H<X||H>=Y||H1>=Y||H2>=Y||p*p>H+1||r*r>H1+1||p*p>H2+1||H1!==H+p-1+E1||H2!==H+p+r-2+E2)continue;
got.add([p,q,e,r,u,f,p,z,g,E1,E2].join(","));}
}}}
ok(got.size===expected.size&&[...got].every(k=>expected.has(k)),"repeat census equality");let nprime=0,nn=0;for(let key of got){let [p,q,e,r,u,f,v,z]=key.split(",").map(Number);if(prime(q))nprime++;if(z-q>2)nn++;}
totals.repeatCensuses++;totals.repeatCandidates+=got.size;totals.repeatPrimeSources+=nprime;totals.repeatNonrankCandidates+=nn;rows.push({L,all:got.size,sourcePrime:nprime,nonrank:nn});
}
results.push({X,T,B,rows,totals:Object.fromEntries(Object.keys(totals).map(k=>[k,totals[k]-before[k]]))});
}
return {totals,results,examples}
}
console.log(JSON.stringify(audit(),null,2));
