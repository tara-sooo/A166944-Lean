// Run: node research/infinite-orbit/cofactor_support_audit.mjs
function audit(){
const max=4*65536+4096,spf=new Int32Array(max+1);
for(let p=2;p*p<=max;p++)if(!spf[p])for(let n=p*p;n<=max;n+=p)if(!spf[n])spf[n]=p;
function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
function gcd(a,b){while(b)[a,b]=[b,a%b];return Math.abs(a)}
function mod(a,b){return (a%b+b)%b}
function prime(n){return n>=2&&!spf[n]}
function elig(H){let B=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=B),fac(H+1).filter(p=>p<=B)]}
function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let v=1+mod((i?q+2:0)-t-1,2*q);if(v<w||(v===w&&q<p)){p=q;w=v;s=i}}return {p,w,s}}
function gap(n,p,s,f){let W=2*p;for(let i=0;i<2;i++)for(let q of f[i])if(q!==p){let z=mod(n-(i?q+2:0),2*q);if(!z&&q<p)return 0;W=Math.min(W,z||2*q)}return W}
function ok(a,m){if(!a)throw Error(m)}
let totals={roots:0,targeted:0,events:0,stops:0,exits:0,cap:0,high:0,positive:0,primeCofactor:0,roughChecks:0,largeDenom:0,deep:0,pairs:0,sameCofactor:0,narrowSame:0,samePaid:0,cofactorMonotone:0,nonzeroShift:0,divisorChecks:0,pairBudgetChecks:0,tailChecks:0,cofactorMomentChecks:0,denominatorChecks:0,integerCensus:0,literalChecks:0,nonempty:0},results=[],examples={same:null,different:null,largeDenom:null,positive:null,repeatedPair:null},census=[];
for(let X of [4096,16384,65536]){
const Y=4*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(Y+1)),C=108,Lmax=Math.floor((Y+B+2)/T);
let stats=[{name:"all",test:e=>true},{name:"large-denom",test:e=>e.b>=T/2},{name:"positive",test:e=>2*e.w>e.g},{name:"fast",test:e=>4*e.w<=e.g},{name:"narrow",test:e=>e.p<=Math.floor(1.5*T)}].map(z=>({...z,lists:0,selected:0,pairs:0,cofactors:0,denoms:0,maxS:0,maxF:0,maxPair:0,maxCofactorRepeat:0,maxBudgetRatio:0,largeDenomDeep:0}));
let roots=0,targeted=0,events=0,canonHigh=0,canonLarge=0,targetHigh=0,targetLarge=0,denomBins={canonical:[0,0,0,0],targeted:[0,0,0,0]};
function scan(H0,t0,can){
 let H=H0,t=t0,ev=[];
 for(let j=0;j<2000&&H<Y;j++){let a=first(t,elig(H));if(!a.p){totals.stops++;break}
 let J=H+a.p-1,n=t+a.w,A=J+2*a.s,L=A/a.p,C0=n-2*a.s,d=gcd(A,C0),b=A/d,m=d/a.p;
 ok(Number.isInteger(L)&&L%2===0&&Number.isInteger(m)&&L===b*m,"cofactor decomposition");
 if(a.p>=T)ok(L<=Lmax,"high cofactor upper");
 let e={H,t,J,n,p:a.p,w:a.w,s:a.s,g:a.p-1,L,b,m,x:2*n-J-6*a.s};
 ev.push(e);H=J;t=n;events++;totals.events++;
 if(totals.events%9973===0){let v=null;for(let w=1;w<=2*Math.floor(Math.sqrt(e.H+1));w++){let n=e.t+w,g=gcd(n%2?n-2:n,n%2?e.H+1:e.H-1),p=fac(g).find(q=>q<=Math.floor(Math.sqrt(e.H+1)));if(p){v=[p,w];break}}ok(v&&v[0]===e.p&&v[1]===e.w,"literal");totals.literalChecks++}
 if(j===1999&&H<Y)totals.cap++;
 }
 if(H>=Y)totals.exits++;
 let high=ev.filter(e=>e.p>=T),lastByCofactor=new Map();
 for(let e of high){
  let prior=lastByCofactor.get(e.L);if(prior){ok(e.p>prior.p&&e.p-prior.p>=2,"cofactor label monotonicity");totals.cofactorMonotone++;}lastByCofactor.set(e.L,e);
  ok(e.L>=e.p+1,"adaptive cofactor lower");
  totals.high++;if(can)canonHigh++;else targetHigh++;
  let bin=e.b<=2?0:e.b<T/2?1:e.b<T?2:3;denomBins[can?"canonical":"targeted"][bin]++;
  if(e.b>=T/2){totals.largeDenom++;if(can)canonLarge++;else targetLarge++;if(e.x>=X/4&&!examples.largeDenom)examples.largeDenom={X,e,can}}
  if(e.x>=X/4)totals.deep++;
  if(2*e.w>e.g){totals.positive++;let q=e.L-1,sgn=1-2*e.s;ok(e.H===e.p*q+sgn,"selected cofactor");
   for(let r of fac(e.H-1).concat(fac(e.H+1))){ok(4*r>=e.g,"positive roughness");totals.roughChecks++}
   if(e.p*((e.p-1)/4)**2>e.H+1){ok(prime(q),"prime cofactor");totals.primeCofactor++}
   if(!examples.positive&&prime(q)&&e.b>=T/2)examples.positive={X,e,can};
  }
 }
 let G=ev.reduce((a,e)=>a+e.g,0);
 for(let z of stats){
  let list=high.filter(z.test);if(!list.length)continue;
  z.lists++;totals.nonempty++;let F=list.reduce((a,e)=>a+e.g,0),U=G-F,S=new Set(list.map(e=>e.L)),D=new Set(list.map(e=>e.b)),P=new Map(),freq=new Map(),relaySum=0,n=list.length-1;
  z.selected+=list.length;z.pairs+=n;z.cofactors+=S.size;z.denoms+=D.size;z.maxS=Math.max(z.maxS,S.size);z.maxF=Math.max(z.maxF,F);
  for(let e of list){freq.set(e.L,(freq.get(e.L)||0)+1);if(e.b>=T/2&&e.x>=X/4)z.largeDenomDeep++}
  z.maxCofactorRepeat=Math.max(z.maxCofactorRepeat,...freq.values());
  for(let i=1;i<list.length;i++){
   let a=list[i-1],b=list[i],E=b.H-a.J,shift=E-1+2*(b.s-a.s),d=gcd(a.L,b.L-1);
   ok(E>=0&&E%2===0,"relay");ok((b.L-1)*b.p-a.L*a.p===shift,"pair equation");ok(shift%2!==0&&shift!==0&&shift%d===0&&d<=E+3,"odd gcd");
   relaySum+=E;totals.pairs++;totals.nonzeroShift++;totals.divisorChecks++;
   let key=a.L+","+b.L;if(!P.has(key))P.set(key,[]);P.get(key).push(E);
   if(a.L===b.L){ok(b.p>a.p&&E>=2*a.L-b.p-1&&E>=2*T-b.p+1,"same cofactor toll");totals.sameCofactor++;if(a.p<=Math.floor(1.5*T)&&b.p<=Math.floor(1.5*T)){totals.narrowSame++;ok(E>=2*T-Math.floor(1.5*T)+1,"narrow same toll");totals.samePaid++;}if(!examples.same)examples.same={X,a,b,E,can}}
   else if(!examples.different&&a.b>=T/2&&b.b>=T/2)examples.different={X,a,b,E,can};
   if(census.length<120&&totals.pairs%71===0)census.push({X,T,B,a:a.L,b:b.L,s:a.s,t:b.s,K:[0,4,16,64,256][census.length%5],C});
  }
  ok(relaySum<=U,"disjoint relays");
  let moment=0;
  for(let [key,v] of P){v.sort((a,b)=>a-b);z.maxPair=Math.max(z.maxPair,v.length);for(let i=0;i<v.length;i++){ok(i+1<=C*(v[i]+1),"ordered cost count");totals.pairBudgetChecks++}moment+=v.length*(v.length+1)/(2*C)-v.length;if(v.length>=2&&!examples.repeatedPair)examples.repeatedPair={X,can,key,relays:v.slice(),H0,t0,list:list.map(e=>[e.H,e.p,e.L,e.b,e.s])};}
  ok(relaySum+1e-8>=moment,"pair moment");
  if(n){ok(n*n<=2*C*P.size*(U+n),"cofactor support cost");totals.cofactorMomentChecks++;z.maxBudgetRatio=Math.max(z.maxBudgetRatio,n*n/(2*C*P.size*(U+n)))}
  for(let K of [0,4,16,64,256]){let short=0;for(let v of P.values())short+=v.filter(E=>E<=K).length;ok(short<=C*P.size*(K+1)&&n<=C*P.size*(K+1)+U/(K+1)+1e-8,"tail");totals.tailChecks++}
  let cap=[...D].reduce((a,b)=>a+Math.floor(Lmax/b),0);ok(S.size<=cap,"denom support");totals.denominatorChecks++;
  if(z.name==="large-denom")ok(S.size<=Math.floor(2*Lmax/T)*D.size,"large denom support");
 }
}
for(let H=X;H<Y;H+=4){scan(H,(H+6)/2,true);roots++;totals.roots++}
let seen=new Set();
for(let H=X;H<Y;H+=Math.max(2,2*Math.floor(Math.sqrt(X)/8))){
 let f=elig(H);for(let s=0;s<2;s++)for(let p of f[s]){if(p<T)continue;let J=H+p-1,r=s?p+2:0,lo=H/2+1,hi=3*H+3+2*p;
 for(let frac of [1,2,3,4,5]){let base=Math.floor(lo+(hi-lo)*frac/6),n=base+mod(r-base,2*p);if(n>hi)continue;
 let W=gap(n,p,s,f),l=Math.max(1,n-(3*H+3)),u=Math.min(W,n-H/2);if(l>u)continue;
 for(let w of new Set([l,u])){let t=n-w,key=H+","+t;if(seen.has(key))continue;seen.add(key);let a=first(t,f);ok(a.p===p&&a.w===w,"target exact");scan(H,t,false);targeted++;totals.targeted++}
 }
 }
}
results.push({X,T,B,Lmax,roots,targeted,events,canonHigh,canonLarge,targetHigh,targetLarge,denomBins,stats:stats.map(({test,...z})=>z)});
}
for(let v of census){let {T,B,a,b,s,t,K,C}=v,d=gcd(a,b-1),count=0;
 for(let p=T;p<=B;p++)for(let r=T;r<=B;r++){let E=(b-1)*r-a*p+1-2*(t-s);if(E<0||E>K||E%2)continue;count++}
 if(count){ok(d<=K+3,"census gcd");ok(count<=9*d*(Math.floor(K/d)+1),"census lattice");}
 ok(count<=C*(K+1),"census bound");totals.integerCensus++;
}
return {totals,results,examples,censusCount:census.length};
}
console.log(JSON.stringify(audit(),null,2));
