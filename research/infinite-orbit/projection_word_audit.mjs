// Run: node research/infinite-orbit/projection_word_audit.mjs
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
const totals={roots:0,targeted:0,events:0,stops:0,exits:0,cap:0,high:0,literal:0,words:0,identities:0,spanChecks:0,short:0,shortDistinct:0,shortAnchor:0,affineWords:0,affineChecks:0,residence:0,oddCut:0,smallDeficit:0,censuses:0,necessary:0,local:0,latticeChecks:0,latticeCandidates:0,localStarts:0,localShortWords:0,localShortAnchor:0,localEvents:0,endpointChecks:0,stripReturnChecks:0,divisorChecks:0};let results=[],examples={actual:null,local:null,localShort:null};
const slopes=[[1,2],[1,1],[3,2],[2,3]];
function clock(p,s){return s?p+2:0}
function state(H,t,z){let {p,w,s}=z;return {H,t,p,w,s,e:1-2*s,q:(H-1+2*s)/p,J:H+p-1,n:t+w}}
function proj(a,M,N){return N*(a.n-2*a.s)/a.p-M*(a.q+1)}
function shifts(a,b,M,N){let E=b.H-a.J,V=b.n-a.n,s=b.s-a.s,D=E-1+2*s,d=V-2*s;return {E,V,b:N*d-M*D}}
function gcdB(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b)[a,b]=[b,a%b];return a}
function modB(a,b){return (a%b+b)%b}
function invB(a,b){let x=1n,y=0n,u=modB(a,b),v=b;while(v){let k=u/v;[u,v]=[v,u-k*v];[x,y]=[y,x-k*y]}ok(u===1n,"big inverse");return modB(x,b)}
// Each parameter t has p0=u0+k*t, all prior labels integer-affine.
// Extend by solving the next label integrality exactly.
function extend(st,h,d,b){
let H=BigInt(h),D=BigInt(d),B=BigInt(b);ok(H!==0n&&D!==0n,"nondegenerate extension");
let A=H*st.a,C=H*st.c+B,dd=D<0n?-D:D,g=gcdB(A,dd);if(C%g)return null;
let l=dd/g,t0=l===1n?0n:modB((-C/g)*invB(A/g,l),l);
return {u:st.u+st.k*t0,k:st.k*l,a:A*l/D,c:(A*t0+C)/D,step:l};
}
for(let X of [4096,16384,65536]){
let Y=4*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(Y+1)),base={...totals},patterns=new Map();
function inspect(list,can){
let m=list.length,L=list.slice(1).reduce((s,b,i)=>s+b.H-list[i].J,0),W=list[m-1].n-list[0].n;totals.words++;
let short=W<T-2&&L<T/4,distinct=new Set(list.map(x=>x.p)).size===m;
if(short){totals.short++;ok(distinct,"short word repeats");totals.shortDistinct++;}
for(let [M,N] of slopes){
let hs=list.map(x=>proj(x,M,N)),bs=list.slice(1).map((x,i)=>shifts(list[i],x,M,N).b),xs=hs.map((h,i)=>h*list[i].p),sum=0,gain=0;
for(let i=1;i<m;i++){ok(list[i].p*(hs[i]+M)===list[i-1].p*hs[i-1]+bs[i-1],"projection row");sum+=bs[i-1];gain+=list[i].p;ok(xs[i]-xs[0]===sum-M*gain,"telescoping");totals.identities++;}
for(let i=0;i<m;i++)for(let j=i+1;j<m;j++){
let V=list[j].n-list[i].n,G=list[j].J-list[i].J,ds=list[j].s-list[i].s;
ok(xs[j]-xs[i]===N*V-M*G-2*(N+M)*ds,"physical endpoint identity");totals.endpointChecks++;
let A=Math.max(Math.abs(hs[i]),Math.abs(hs[j]));ok(N*V>=M*G-2*B*A-2*(N+M),"strip return clock toll");totals.stripReturnChecks++;
}
let anchor=Math.min(...hs.map(Math.abs));ok(hs.every(h=>Math.abs(h)*T<=B*(anchor+M*(m-1))+bs.reduce((s,x)=>s+Math.abs(x),0)),"anchor spread");totals.spanChecks++;
if(bs.every(b=>2*b<M*T)){let z=0;for(let i=1;i<m;i++){ok(2*(xs[i-1]-xs[i])>=M*T,"monotone");if(hs[i-1]===0&&hs[i]===-M)z++;}ok(z<=1,"single cut");totals.oddCut++;
ok(M*T*(m-1)<=2*(xs[0]-xs[m-1]),"residence");totals.residence++;
if(M===1&&N===2){ok(hs.every(h=>h>=0),"nonnegative deficit");ok(M*T*(m-1)<=2*xs[0],"deficit residence");totals.smallDeficit++;}}
if(!short||anchor>16||bs.some(b=>Math.abs(b)>=T)||hs.some(h=>Math.abs(h)>=T||Math.abs(h+M)>=T))continue;
totals.shortAnchor++;
let deg=0;for(let i=1;i<m;i++){if(!hs[i-1]||hs[i]===-M||!bs[i-1]){ok(hs[i-1]===0&&hs[i]===-M&&bs[i-1]===0,"degenerate edge");deg++;}}
if(N%2===0)ok(!deg,"even denominator");
if(deg)continue;
let st={u:0n,k:1n,a:1n,c:0n},p0=BigInt(list[0].p);
for(let i=1;i<m;i++){let prev=st;st=extend(st,hs[i-1],hs[i]+M,bs[i-1]);ok(st&&modB(p0-st.u,st.k)===0n,"actual progression");ok(st.a*((p0-st.u)/st.k)+st.c===BigInt(list[i].p),"actual affine");ok(st.k===prev.k*st.step,"modulus growth");totals.affineChecks++;}
totals.affineWords++;
if(!examples.actual)examples.actual={X,can,M,N,list,hs,bs,L,W,modulus:String(st.k)};
if(N%2===0&&patterns.size<8){let E=list.slice(1).map((b,i)=>b.H-list[i].J),V=list.slice(1).map((b,i)=>b.n-list[i].n),s=list.map(x=>x.s),A=Math.max(2,anchor),idx=hs.findIndex(x=>Math.abs(x)===anchor),key=JSON.stringify({E,V,s,M,N,A,idx});patterns.set(key,{E,V,s,M,N,A,idx});}
}
}
function scan(H,t,can){
let list=[];
for(let it=0;it<2000&&H<Y;it++){
let z=first(t,elig(H));if(!z.p){totals.stops++;break}let v=state(H,t,z);totals.events++;
if(totals.events%9973===0){let found=null;for(let w0=1;w0<=2*Math.floor(Math.sqrt(H+1));w0++){let n0=t+w0,d=gcd(n0%2?n0-2:n0,n0%2?H+1:H-1),p0=fac(d).find(f=>f<=Math.floor(Math.sqrt(H+1)));if(p0){found=[p0,w0];break}}ok(found&&found[0]===v.p&&found[1]===v.w,"literal");totals.literal++;}
if(v.p>=T){list.push(v);totals.high++;for(let m=4;m<=Math.min(6,list.length);m++)inspect(list.slice(-m),can);}
H=v.J;t=v.n;if(it===1999&&H<Y)totals.cap++;
}if(H>=Y)totals.exits++;
}
for(let H=X;H<Y;H+=4){scan(H,(H+6)/2,true);totals.roots++}
let seen=new Set();for(let H=X;H<Y;H+=Math.max(2,2*Math.floor(Math.sqrt(X)/8))){let f=elig(H);for(let s=0;s<2;s++)for(let p of f[s]){if(p<T)continue;let r=clock(p,s),lo=H/2+1,hi=3*H+3+2*p;for(let frac of [1,3,5]){let n=Math.floor(lo+(hi-lo)*frac/6);n+=mod(r-n,2*p);if(n>hi)continue;let W=gap(n,p,f),l=Math.max(1,n-(3*H+3)),u=Math.min(W,n-H/2);if(l>u)continue;for(let w of new Set([l,u])){let t=n-w,key=H+","+t;if(seen.has(key))continue;seen.add(key);let a=first(t,f);ok(a.p===p&&a.w===w,"target");scan(H,t,false);totals.targeted++;}}}}
// Target additional exact intermediate states in narrow even-denominator strips.
if(X<=16384){
let seenLocal=new Set();
for(let H=X;H<Y;H+=2){let f=elig(H);for(let side=0;side<2;side++)for(let p of f[side]){if(p<T)continue;let a=(H-1+2*side)/p+1;
for(let M of [1,3,5])for(let hv=-16;hv<=16;hv+=2){let c=(M*a+hv)/2,n=p*c+2*side;if(mod(n-clock(p,side),2*p)||n<H/2+1||n>3*H+3+2*p)continue;let key=H+","+n+","+p;if(seenLocal.has(key))continue;seenLocal.add(key);
let l=Math.max(1,n-(3*H+3)),u=Math.min(gap(n,p,f),n-H/2);if(l>u)continue;let z=first(n-l,f);if(z.p!==p||z.s!==side||z.w!==l)continue;totals.localStarts++;
let list=[state(H,n-l,z)],t=n,J=H+p-1,Etotal=0;
for(let it=0;it<T&&J<Y&&t<n+T-3;it++){let z=first(t,elig(J));if(!z.p||t+z.w>n+T-3)break;let v=state(J,t,z);totals.localEvents++;if(v.p<T)Etotal+=v.p-1;else{list.push(v);if(list.length>=4){totals.localShortWords++;let pre=totals.shortAnchor;inspect(list,false);totals.localShortAnchor+=totals.shortAnchor-pre;if(!examples.localShort)examples.localShort={X,M,hv,list:[...list],Etotal,W:v.n-n};}if(list.length>=6)break;}if(Etotal>=T/4)break;J=v.J;t=v.n;}
}
}}
}
// Fixed shift patterns independently chosen, plus actual short observed patterns.
for(let m of [4,5,6])for(let M of [1,3])for(let alt of [false,true]){
let s=Array.from({length:m},(_,i)=>alt?i%2:0),E=Array(m-1).fill(0),V=Array(m-1).fill(alt?1:2),N=2,A=8,idx=Math.floor(m/2);
let data={E,V,s,M,N,A,idx};patterns.set(JSON.stringify(data),data);
}
let ps=[];for(let p=T;p<=B;p++)if(prime(p))ps.push(p);
function hf(n){if(!n)return [];return fac(Math.abs(n)).filter(p=>p>=T&&p<=B);}
function horizons(labels,E,s){let [p,r]=labels,e=1-2*s[0],f=1-2*s[1],a=e+p,per=2*p*r,H0=a+2*p*mod((f-p+1-E[0]-a)*inv(2*p,r),r),out=[];
for(let H=X+mod(H0-X,per);H<Y;H+=per){let Hs=[H];for(let i=1;i<labels.length;i++)Hs.push(Hs[i-1]+labels[i-1]-1+E[i-1]);if(Hs.every((h,i)=>h<Y&&mod(h-1+2*s[i],labels[i])===0&&labels[i]*labels[i]<=h+1))out.push(Hs);}return out;}
function verifyCandidate(out,labels,Hs,n,pattern){
let {E,V,s,M,N,A,idx}=pattern,m=labels.length,ns=[n];for(let v of V)ns.push(ns[ns.length-1]+v);
if(n<Hs[0]/2+1||n>3*Hs[0]+3+2*labels[0]||ns.some((n,i)=>mod(n-clock(labels[i],s[i]),2*labels[i])))return;
let h=labels.map((p,i)=>N*(ns[i]-2*s[i])/p-M*((Hs[i]-1+2*s[i])/p+1));
if(Math.abs(h[idx])>A)return;
out.add([Hs[0],n,...labels].join(","));
}
let counts=[];
for(let pat of patterns.values()){
let {E,V,s,M,N,A,idx}=pat,m=s.length,elapsed=V.reduce((a,b)=>a+b,0),bs=V.map((v,i)=>N*(v-2*(s[i+1]-s[i]))-M*(E[i]-1+2*(s[i+1]-s[i])));
if(elapsed>=T-2||bs.some(b=>Math.abs(b)>=T))continue;
let brute=new Set(),recon=new Set(),sumV=[0];for(let v of V)sumV.push(sumV[sumV.length-1]+v);
function byClock(labels,n){let i=labels.length;if(i===m){for(let Hs of horizons(labels,E,s))verifyCandidate(brute,labels,Hs,n,pat);return;}
for(let p of hf(n+sumV[i]-2*s[i]))if(!labels.includes(p)&&mod(n+sumV[i]-clock(p,s[i]),2*p)===0)byClock([...labels,p],n);}
for(let p of ps)for(let n=X/2+1+mod(clock(p,s[0])-(X/2+1),2*p);n<=3*Y+3+2*B;n+=2*p)byClock([p],n);
let cap=Math.floor((B*(A+M*(m-1))+bs.reduce((s,b)=>s+Math.abs(b),0))/T);
function byProjection(labels,hs){
let i=labels.length;if(i===m){if(Math.abs(hs[idx])>A)return;for(let Hs of horizons(labels,E,s)){let p=labels[0],a=(Hs[0]-1+2*s[0])/p+1,c=(M*a+hs[0])/N,n=p*c+2*s[0];if(!Number.isInteger(c))continue;verifyCandidate(recon,labels,Hs,n,pat);}return;}
let num=labels[i-1]*hs[i-1]+bs[i-1];if(!num)return;
for(let p of hf(num))if(!labels.includes(p))byProjection([...labels,p],[...hs,num/p-M]);
}
for(let p of ps)for(let h=-cap;h<=cap;h++)byProjection([p],[h]);
ok(brute.size===recon.size&&[...brute].every(k=>recon.has(k)),"word census equality");totals.censuses++;totals.necessary+=brute.size;let local=0;
for(let key of brute){let [H,n,...labels]=key.split(",").map(Number),f=elig(H),l=Math.max(1,n-(3*H+3)),u=Math.min(gap(n,labels[0],f),n-H/2);if(l>u)continue;let zz=first(n-l,f);if(zz.p!==labels[0]||zz.s!==s[0]||zz.w!==l)continue;
let h=H+labels[0]-1,t=n,got=[],Hs=[H];for(let i=1;i<m;i++)Hs.push(Hs[i-1]+labels[i-1]-1+E[i-1]);for(let it=0;it<elapsed&&t<n+elapsed&&h<Y;it++){let z=first(t,elig(h));if(!z.p||t+z.w>n+elapsed)break;t+=z.w;if(z.p>=T)got.push([h,z.p,t,z.s]);h+=z.p-1;if(got.length===m-1)break;}
if(got.length===m-1&&got.every((v,i)=>v.join(",")===[Hs[i+1],labels[i+1],n+sumV[i+1],s[i+1]].join(","))){local++;totals.local++;if(!examples.local)examples.local={X,pat,H,n,labels,Hs,sourceWait:l};}}
counts.push({m,M,N,A,idx,E,V,s,necessary:brute.size,local});
}
results.push({X,T,B,counts,totals:Object.fromEntries(Object.keys(totals).map(k=>[k,totals[k]-base[k]]))});
}
// Independent exact lattice test with signed projection data, not assumed MIN.
// Compare the recursive progression for all integer anchors in [1,96] to literal division.
let seed=1717;function rand(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n;}
for(let test=0;test<12000;test++){let m=3+rand(5),M=1+rand(3),hs=Array.from({length:m},()=>{let h;do{h=rand(21)-10;}while(!h||h===-M);return h}),bs=Array.from({length:m-1},()=>rand(17)-8),st={u:0n,k:1n,a:1n,c:0n};
for(let i=1;i<m&&st;i++)st=extend(st,hs[i-1],hs[i]+M,bs[i-1]);
for(let p=1;p<=96;p++){let q=BigInt(p),real=true;for(let i=1;i<m;i++){let n=BigInt(hs[i-1])*q+BigInt(bs[i-1]),d=BigInt(hs[i]+M);if(n%d){real=false;break}q=n/d;}let got=!!st&&modB(BigInt(p)-st.u,st.k)===0n;ok(real===got,"lattice exact");if(got){ok(st.a*((BigInt(p)-st.u)/st.k)+st.c===q,"lattice endpoint");totals.latticeCandidates++;}totals.latticeChecks++;}
}
for(let a=1;a<=512;a++)for(let H of [1,4,16,64,128]){let s=0,tau=0,harm=0;for(let d=1;d<=H;d++){s+=gcd(a,d)/d;harm+=1/d;}for(let d=1;d<=a;d++)if(a%d===0)tau++;ok(s<=tau*harm+1e-9,"divisor weighted extension");totals.divisorChecks++;}
return {totals,results,examples};
}
console.log(JSON.stringify(audit(),null,2));
