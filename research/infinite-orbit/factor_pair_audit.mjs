// Run: node research/infinite-orbit/factor_pair_audit.mjs
function audit(){
const max=4*65536+4096,spf=new Int32Array(max+1);
for(let p=2;p*p<=max;p++)if(!spf[p])for(let n=p*p;n<=max;n+=p)if(!spf[n])spf[n]=p;
function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
function gcd(a,b){while(b)[a,b]=[b,a%b];return Math.abs(a)}
function mod(a,b){return (a%b+b)%b}
function prime(n){return n>=2&&!spf[n]}
function elig(H){let B=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=B),fac(H+1).filter(p=>p<=B)]}
function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let z=1+mod((i?q+2:0)-t-1,2*q);if(z<w||(z===w&&q<p)){p=q;w=z;s=i}}return {p,w,s}}
function gap(n,p,f){let W=2*p;for(let i=0;i<2;i++)for(let q of f[i])if(q!==p){let z=mod(n-(i?q+2:0),2*q);if(!z&&q<p)return 0;W=Math.min(W,z||2*q)}return W}
function ok(v,m){if(!v)throw Error(m)}
const ratios=[[1,1],[3,2],[2,1],[5,3],[3,1],[4,3]],Ks=[0,2,8,32];
let totals={roots:0,targeted:0,events:0,stops:0,exits:0,caps:0,high:0,positive:0,semiprime:0,positiveSemi:0,cube:0,rough:0,literal:0,lists:0,pairs:0,shared:0,roleSwitch:0,globalRepeat:0,globalSwitch:0,square:0,toll:0,tollAgg:0,stripChecks:0,localCensus:0,latticeCandidates:0,independentCandidates:0},results=[],examples={shared:null,switch:null,canonicalShared:null,shortDisjoint:null},ratioCounts=[];
for(let X of [4096,16384,65536]){
let Y=4*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(Y+1)),Qmax=Math.floor((Y+1)/T);
let configs=[{name:"all semiprime",test:e=>true},{name:"positive semiprime",test:e=>2*e.w>e.g},{name:"narrow semiprime",test:e=>e.p<=Math.floor(1.5*T)}].map(z=>({...z,lists:0,events:0,pairs:0,shared:0,switch:0,maxK:0,sharedGain:0,U:0,paid:0,canonicalPairs:0,canonicalShared:0}));
let roots=0,targeted=0,events=0;
function scan(H0,t0,can){
let H=H0,t=t0,ev=[];
for(let j=0;j<2000&&H<Y;j++){let a=first(t,elig(H));if(!a.p){totals.stops++;break}
let e=1-2*a.s,q=(H-e)/a.p,g=a.p-1,J=H+g,n=t+a.w;
ok(Number.isInteger(q)&&q>=a.p,"cofactor");
let x={H,t,p:a.p,q,w:a.w,s:a.s,e,g,J,n};
ev.push(x);H=J;t=n;events++;totals.events++;
if(totals.events%9973===0){let found=null;for(let w=1;w<=2*Math.floor(Math.sqrt(x.H+1));w++){let n=x.t+w,d=gcd(n%2?n-2:n,n%2?x.H+1:x.H-1),p=fac(d).find(q=>q<=Math.floor(Math.sqrt(x.H+1)));if(p){found=[p,w];break}}ok(found&&found[0]===x.p&&found[1]===x.w,"literal");totals.literal++}
if(j===1999&&H<Y)totals.caps++;
}
if(H>=Y)totals.exits++;
let high=ev.filter(e=>e.p>=T),semi=high.filter(e=>prime(e.q));totals.high+=high.length;totals.semiprime+=semi.length;
for(let e of high)if(2*e.w>e.g){totals.positive++;for(let r of fac(e.H-1).concat(fac(e.H+1))){ok(4*r>=e.g,"roughness");totals.rough++}if(e.p*(e.g/4)**2>e.H+1){ok(prime(e.q),"cube");totals.cube++}}
totals.positiveSemi+=semi.filter(e=>2*e.w>e.g).length;
totals.square+=semi.filter(e=>e.p===e.q).length;
let G=ev.reduce((a,e)=>a+e.g,0);
for(let z of configs){
let list=semi.filter(z.test);if(!list.length)continue;
z.lists++;totals.lists++;z.events+=list.length;z.maxK=Math.max(z.maxK,list.length);
let F=list.reduce((a,e)=>a+e.g,0),U=G-F,paid=0,shareGain=0;z.U+=U;
let last=new Map(),used=new Set(),prodSeen=new Set();
for(let i=0;i<list.length;i++){
let a=list[i],product=a.p*a.q;ok(!prodSeen.has(product),"distinct product");prodSeen.add(product);
ok(!used.has(a.q),"no later cofactor after prior label");
for(let v of new Set([a.p,a.q])){let b=last.get(v);if(b){ok(a.H-b.H>=2*v-2&&product-b.p*b.q>=2*v,"factor gap");totals.globalRepeat++;if(b.q===v&&a.p===v&&b.p<v){ok(a.H-b.H>=v*(v-b.p)-2,"role threshold");totals.globalSwitch++;}}last.set(v,a)}
used.add(a.p);
if(i===0)continue;
let b=list[i-1],E=a.H-b.J,common=[...new Set([b.p,b.q])].filter(v=>v===a.p||v===a.q);
ok(E>=0&&E%2===0,"relay");totals.pairs++;z.pairs++;if(can)z.canonicalPairs++;
if(common.length){ok(common.length===1,"distinct factor pairs");let v=common[0],lb=2*v-b.p-1;ok(E>=lb&&lb>=b.g,"shared toll");paid+=lb;shareGain+=b.g;totals.shared++;totals.toll++;z.shared++;if(can)z.canonicalShared++;if(!examples.shared)examples.shared={X,can,prev:b,next:a,E,v,lb};if(can&&!examples.canonicalShared)examples.canonicalShared={X,can,prev:b,next:a,E,v,lb};
if(b.q===a.p&&b.p<b.q){let stronger=v*(v-b.p)-b.p-1;ok(E>=stronger,"switch toll");totals.roleSwitch++;z.switch++;if(!examples.switch)examples.switch={X,can,prev:b,next:a,E,v,lb,stronger}}
}else if(E<=4&&!examples.shortDisjoint)examples.shortDisjoint={X,can,prev:b,next:a,E};
}
ok(shareGain<=paid&&paid<=U,"aggregate toll");totals.tollAgg++;z.paid+=paid;z.sharedGain+=shareGain;
}
}
// Canonical all roots and targeted full MIN arrivals at sampled horizons.
for(let H=X;H<Y;H+=4){scan(H,(H+6)/2,true);roots++;totals.roots++}
let seen=new Set();
for(let H=X;H<Y;H+=Math.max(2,2*Math.floor(Math.sqrt(X)/8))){
let f=elig(H);for(let s=0;s<2;s++)for(let p of f[s]){if(p<T)continue;
let r=s?p+2:0,lo=H/2+1,hi=3*H+3+2*p;
for(let frac of [1,3,5]){let base=Math.floor(lo+(hi-lo)*frac/6),n=base+mod(r-base,2*p);if(n>hi)continue;
let W=gap(n,p,f),l=Math.max(1,n-(3*H+3)),u=Math.min(W,n-H/2);if(l>u)continue;
for(let w of new Set([l,u])){let t=n-w,key=H+","+t;if(seen.has(key))continue;seen.add(key);let a=first(t,f);ok(a.p===p&&a.w===w,"target exact");scan(H,t,false);targeted++;totals.targeted++}
}
}}
let ps=[];for(let p=T;p<=B;p++)if(prime(p))ps.push(p);
let qs=[];for(let q=T;q<=Qmax;q++)if(prime(q))qs.push(q);
let all=[];
for(let p of ps)for(let q of qs){if(q<p)continue;let P=p*q;if(P-1>=Y)break;for(let e of [-1,1])if(P+e>=X&&P+e<Y)all.push([p,q,e,P+e])}
let rows=[];
for(let [u,v] of ratios)for(let K of Ks){
let independent=all.filter(([p,q])=>Math.abs(v*q-u*p)<=K),keys=new Set(),zero=0;
for(let m=-K;m<=K;m++){
// gcd(u,v)=1; unique p residue mod v. Enumerate p and reconstruct q.
let r=0;while(mod(u*r+m,v)!==0)r++;for(let p=T+mod(r-T,v);p<=B;p+=v){
let q=(u*p+m)/v;if(!prime(p)||q<p||q>Qmax||!prime(q))continue;
for(let e of [-1,1]){let H=p*q+e;if(H<X||H>=Y)continue;let key=[p,q,e].join(",");ok(!keys.has(key),"unique lattice");keys.add(key);if(m===0){ok(u===1&&v===1&&p===q,"zero exception");zero++}
}
}}
ok(keys.size===independent.length&&independent.every(([p,q,e])=>keys.has([p,q,e].join(","))),"lattice versus product census");
totals.localCensus++;totals.latticeCandidates+=keys.size;totals.independentCandidates+=independent.length;
// independent localization into translated physical bins; exact candidate count only.
let D=Math.ceil(X**.75);
for(let off of [0,Math.floor(D/3),Math.floor(D/2)]){
let map=new Map(),other=new Map();for(let [p,q,e,H] of independent){let b=Math.floor((H-off)/D);map.set(b,(map.get(b)||0)+1)}for(let key of keys){let [p,q,e]=key.split(",").map(Number),b=Math.floor((p*q+e-off)/D);other.set(b,(other.get(b)||0)+1)}
ok(map.size===other.size&&[...map].every(([b,n])=>other.get(b)===n),"translated bin");totals.stripChecks++;
}
rows.push({u,v,K,candidates:keys.size,zero});
}
ratioCounts.push({X,all:all.length,rows});
results.push({X,T,B,roots,targeted,events,configs:configs.map(({test,...z})=>z)});
}
return {totals,results,examples,ratioCounts}
}
console.log(JSON.stringify(audit(),null,2));
