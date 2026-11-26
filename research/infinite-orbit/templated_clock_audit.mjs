// Run: node research/infinite-orbit/templated_clock_audit.mjs
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
const totals={roots:0,targeted:0,events:0,stops:0,exits:0,cap:0,high:0,literal:0,words:0,rows:0,composition:0,repeat:0,repeatToll:0,zeroSource:0,zeroToll:0,finiteEscape:0,affine:0,nonprop:0,smallTemplateWords:0,longTemplateWords:0,censuses:0,candidates:0,local:0};
let results=[],examples={long:null,repeat:null,census:null};
for(let X of [4096,16384,65536]){
let Y=4*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(Y+1)),before={...totals},patterns=new Map();
function inspect(list,can){
let m=list.length;totals.words++;
for(let M of [1,3])for(let d of [1,3]){
let N=2,hs=list.map(x=>proj(x,M,N)),rows=[],L=0,R=0,hasLong=false;
for(let j=1;j<m;j++){let u=list[j-1],v=list[j],E=v.H-u.J,V=v.n-u.n,s=v.s-u.s,a=Math.max(0,Math.min(2*d,Math.round(d*V/v.p))),tau=d*V-a*v.p,A=d*hs[j-1],C=d*(hs[j]+M)-N*a,b=N*(tau-2*d*s)-M*d*(E-1+2*s);
ok(mod(A,2)===0&&mod(C,2)===1&&mod(b,2)===1&&C*v.p===A*u.p+b,"template transport");totals.rows++;
if(!A){ok(Math.abs(b)>=v.p,"zero projection toll");totals.zeroSource++;totals.zeroToll++;}
L+=E;R+=Math.abs(tau);if(2*V>=v.p)hasLong=true;rows.push({A,C,b,E,V,a,tau});
}
for(let i=0;i<m-1;i++){
let A=1n,C=1n,F=0n,H=1n,R=0n;
for(let j=i;j<m-1;j++){let z=rows[j],a=BigInt(z.A),c=BigInt(z.C),b=BigInt(z.b);
F=a*F+b*C;A=a*A;C=c*C;let h=BigInt(Math.max(Math.abs(z.A),Math.abs(z.C),1));if(h>H)H=h;let r=b<0n?-b:b;if(r>R)R=r;
ok(C*BigInt(list[j+1].p)===A*BigInt(list[i].p)+F&&A%2n===0n&&C%2n!==0n&&F%2n!==0n,"composition parity");totals.composition++;
let bound=BigInt(j-i+1)*R*H**BigInt(j-i),absF=F<0n?-F:F;ok(absF<=bound,"composition bound");
if(list[j+1].p===list[i].p){totals.repeat++;ok(absF>=BigInt(list[i].p)&&bound>=BigInt(T),"repeat toll");totals.repeatToll++;if(!examples.repeat)examples.repeat={X,can,M,d,labels:list.map(v=>v.p),hs,rows,i,j:j+1,F:String(F),bound:String(bound)};}
if(bound<BigInt(T)){ok(list[j+1].p!==list[i].p,"finite escape");totals.finiteEscape++;}
}}
if(rows.every(z=>z.A!==0)){
let st={u:0n,k:1n,a:1n,c:0n},p0=BigInt(list[0].p),forms=[{a:1n,b:0n,c:1n}];
for(let j=0;j<rows.length;j++){let z=rows[j],prev=forms[j];forms.push({a:BigInt(z.A)*prev.a,b:BigInt(z.A)*prev.b+BigInt(z.b)*prev.c,c:BigInt(z.C)*prev.c});
st=extend(st,z.A,z.C,z.b);ok(st&&modB(p0-st.u,st.k)===0n&&st.a*((p0-st.u)/st.k)+st.c===BigInt(list[j+1].p),"affine exact");totals.affine++;}
for(let i=0;i<m;i++)for(let j=i+1;j<m;j++){let a=forms[i],b=forms[j];ok(a.a*b.c!==b.a*a.c,"distinct slopes by parity");ok(a.a*b.b!==b.a*a.b,"nonproportional affine forms by odd composed intercept");totals.nonprop++;}
if(L<=24&&R<=24&&Math.min(...hs.map(Math.abs))<=16){
totals.smallTemplateWords++;if(hasLong){totals.longTemplateWords++;let data={X,can,M,N,d,list,hs,rows,L,R,modulus:String(st.k)};if(!examples.long)examples.long=data;
if(patterns.size<6){let p={M,N,d,h0:hs[0],s:list.map(v=>v.s),E:rows.map(z=>z.E),a:rows.map(z=>z.a),tau:rows.map(z=>z.tau)};patterns.set(JSON.stringify(p),p);}
}}
}
}}
function scan(H,t,can){let list=[];for(let it=0;it<2000&&H<Y;it++){let z=first(t,elig(H));if(!z.p){totals.stops++;break}let v=state(H,t,z);totals.events++;
if(totals.events%9973===0){let found=null;for(let w0=1;w0<=2*Math.floor(Math.sqrt(H+1));w0++){let n0=t+w0,d=gcd(n0%2?n0-2:n0,n0%2?H+1:H-1),p0=fac(d).find(f=>f<=Math.floor(Math.sqrt(H+1)));if(p0){found=[p0,w0];break}}ok(found&&found[0]===v.p&&found[1]===v.w,"literal");totals.literal++;}
if(v.p>=T){list.push(v);totals.high++;for(let m=3;m<=Math.min(5,list.length);m++)inspect(list.slice(-m),can);}
H=v.J;t=v.n;if(it===1999&&H<Y)totals.cap++;}if(H>=Y)totals.exits++;}
for(let H=X;H<Y;H+=4){scan(H,(H+6)/2,true);totals.roots++}
let seen=new Set();for(let H=X;H<Y;H+=Math.max(2,2*Math.floor(Math.sqrt(X)/8))){let f=elig(H);for(let s=0;s<2;s++)for(let p of f[s]){if(p<T)continue;let r=clock(p,s),lo=H/2+1,hi=3*H+3+2*p;for(let frac of [1,3,5]){let n=Math.floor(lo+(hi-lo)*frac/6);n+=mod(r-n,2*p);if(n>hi)continue;let W=gap(n,p,f),l=Math.max(1,n-(3*H+3)),u=Math.min(W,n-H/2);if(l>u)continue;for(let w of new Set([l,u])){let t=n-w,key=H+","+t;if(seen.has(key))continue;seen.add(key);let z=first(t,f);ok(z.p===p&&z.w===w,"target");scan(H,t,false);totals.targeted++;}}}}
let ps=[];for(let p=T;p<=B;p++)if(prime(p))ps.push(p);
let counts=[];
for(let pat of patterns.values()){
let {M,N,d,h0,s,E,a,tau}=pat,m=s.length,brute=new Set(),recon=new Set();
function origin(H,p){let c=(M*((H-1+2*s[0])/p+1)+h0)/N,n=p*c+2*s[0];return Number.isInteger(c)&&mod(n-clock(p,s[0]),2*p)===0&&n>=H/2+1&&n<=3*H+3+2*p?n:null;}
function walk(H,n,labels,h0start,n0,out){
let j=labels.length;if(j===m){out.add([h0start,n0,...labels].join(","));return;}
let prev=labels[j-1],J=H+prev-1+E[j-1];if(J>=Y)return;
for(let p of fac(J-1+2*s[j])){if(p<T||p>B||p*p>J+1)continue;let V=(a[j-1]*p+tau[j-1])/d;if(!Number.isInteger(V)||V<=0||mod(n+V-clock(p,s[j]),2*p))continue;walk(J,n+V,[...labels,p],h0start,n0,out);}
}
for(let p of ps)for(let H=X+mod(1-2*s[0]+p-X,2*p);H<Y;H+=2*p){if(p*p>H+1)continue;let n=origin(H,p);if(n!==null)walk(H,n,[p],H,n,brute);}
function check(labels){
let p=labels[0],r=labels[1];if(p===r){ // repeated first label: use the exact single source progression
for(let H=X+mod(1-2*s[0]+p-X,2*p);H<Y;H+=2*p)finish(H,labels);return;}
let base=1-2*s[0]+p,per=2*p*r,H0=base+2*p*mod((1-2*s[1]-p+1-E[0]-base)*inv(2*p,r),r);for(let H=X+mod(H0-X,per);H<Y;H+=per)finish(H,labels);
}
function finish(H,labels){let n=origin(H,labels[0]);if(n===null)return;let H0=H,n0=n;for(let j=0;j<m;j++){let p=labels[j];if(H>=Y||mod(H-1+2*s[j],p)||p*p>H+1||mod(n-clock(p,s[j]),2*p))return;if(j+1<m){let V=(a[j]*labels[j+1]+tau[j])/d;if(!Number.isInteger(V)||V<=0)return;H+=p-1+E[j];n+=V;}}recon.add([H0,n0,...labels].join(","));}
function byProj(labels,h){let j=labels.length;if(j===m){check(labels);return;}let sigma=s[j]-s[j-1],b=N*(tau[j-1]-2*d*sigma)-M*d*(E[j-1]-1+2*sigma),num=d*h*labels[j-1]+b;if(!num)return;
for(let p of fac(Math.abs(num))){if(p<T||p>B)continue;let c=num/p,hh=(c+N*a[j-1])/d-M;if(!Number.isInteger(hh))continue;byProj([...labels,p],hh);}}
for(let p of ps)byProj([p],h0);
ok(brute.size===recon.size&&[...brute].every(k=>recon.has(k)),"template census");totals.censuses++;totals.candidates+=brute.size;let local=0;
for(let key of brute){let [H,n,...labels]=key.split(",").map(Number),f=elig(H),l=Math.max(1,n-(3*H+3)),u=Math.min(gap(n,labels[0],f),n-H/2);if(l>u)continue;let z=first(n-l,f);if(z.p!==labels[0]||z.s!==s[0]||z.w!==l)continue;
let Hs=[H],ns=[n];for(let i=1;i<m;i++){Hs.push(Hs[i-1]+labels[i-1]-1+E[i-1]);ns.push(ns[i-1]+(a[i-1]*labels[i]+tau[i-1])/d);}
let h=H+labels[0]-1,t=n,got=[];for(let it=0;it<ns[m-1]-n&&t<ns[m-1]&&h<Y;it++){let z=first(t,elig(h));if(!z.p||t+z.w>ns[m-1])break;t+=z.w;if(z.p>=T)got.push([h,z.p,t,z.s]);h+=z.p-1;if(got.length===m-1)break;}
if(got.length===m-1&&got.every((v,i)=>v.join(",")===[Hs[i+1],labels[i+1],ns[i+1],s[i+1]].join(","))){local++;totals.local++;if(!examples.census)examples.census={X,pat,H,n,labels,Hs,ns,sourceWait:l};}}
ok(local>=1,"observed pattern local");counts.push({pat,candidates:brute.size,local});}
results.push({X,T,B,counts,totals:Object.fromEntries(Object.keys(totals).map(k=>[k,totals[k]-before[k]]))});
}
return {totals,results,examples};
}
console.log(JSON.stringify(audit(),null,2));
