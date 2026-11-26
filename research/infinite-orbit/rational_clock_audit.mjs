// Run: node research/infinite-orbit/rational_clock_audit.mjs
function audit(){
const max=4*262144+4096,spf=new Int32Array(max+1);for(let p=2;p*p<=max;p++)if(!spf[p])for(let n=p*p;n<=max;n+=p)if(!spf[n])spf[n]=p;
function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
function gcd(a,b){while(b)[a,b]=[b,a%b];return Math.abs(a)}
function mod(a,b){return (a%b+b)%b}
function elig(H){let B=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=B),fac(H+1).filter(p=>p<=B)]}
function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let z=1+mod((i?q+2:0)-t-1,2*q);if(z<w||(z===w&&q<p)){p=q;w=z;s=i}}return {p,w,s}}
function gap(n,p,s,f){let W=2*p;for(let i=0;i<2;i++)for(let q of f[i])if(q!==p){let z=mod(n-(i?q+2:0),2*q);if(!z&&q<p)return 0;W=Math.min(W,z||2*q)}return W}
function ok(a,m){if(!a)throw Error(m)}
function event(H,t,a){let J=H+a.p-1,n=t+a.w,A=J+2*a.s,C=n-2*a.s,k=gcd(A,C);ok(A%a.p===0&&C%a.p===0,"post gcd");return {H,t,J,n,p:a.p,w:a.w,s:a.s,g:a.p-1,a:C/k,b:A/k,d:2*n-J,x:n*2-J-6*a.s}}
let totals={roots:0,targeted:0,events:0,stops:0,exits:0,caps:0,selected:0,selectedFast:0,selectedLong:0,pairs:0,same:0,switches:0,lockedSwitches:0,fastSame:0,longSame:0,blockChecks:0,lockBlocks:0,lockedSelected:0,lockedFast:0,strictTube:0,upwardReturns:0},results=[],examples={sameFast:null,switch:null,lockedSwitch:null,fastLong:null};
for(let X of [4096,16384,65536,262144]){
let Y=4*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(Y+1)),configs=[1,2,3,4,8,16].flatMap(Q=>[false,true].map(nr=>({Q,nr,lock:18*Q*Q*B<=X,selected:0,fast:0,long:0,same:0,switches:0,blocks:0,macroCost:0,maxF:0,maxFast:0,maxK:0,lockedSwitches:0,fastSame:0})));
let roots=0,targeted=0,events=0;
function scan(H0,t0,can){
 let H=H0,t=t0,ev=[];
 for(let j=0;j<2000&&H<Y;j++){let a=first(t,elig(H));if(!a.p){totals.stops++;break}let e=event(H,t,a);ev.push(e);H=e.J;t=e.n;events++;totals.events++;if(j===1999&&H<Y)totals.caps++}
 if(H>=Y)totals.exits++;
 for(let z of configs){
 let prev=null,F=0,U=0,k=0,S=0,fast=0,long=0,dev=0,relay=0,btime=0,firstg=0,swgain=0,swrelay=0;
 for(let e of ev){
  if(e.p<T||e.b>z.Q||(z.nr&&e.x<=0)){U+=e.g;if(prev){relay+=e.g;btime+=e.w}continue}
  let mu=e.a/e.b,df=Math.abs(e.w-mu*e.g);ok(mu>=.5-3/X-1e-10&&mu<=3+3/X+1e-10,"slope range");
  ok(Math.abs(e.b*e.n-e.a*e.J-2*(e.a+e.b)*e.s)===0,"exact line");
  F+=e.g;k++;totals.selected++;z.selected++;dev+=df;
  let isFast=4*e.w<=e.g,isLong=e.w>=e.p-2;
  if(isFast){fast+=e.g;totals.selectedFast++;z.fast++}if(isLong){long+=e.g;totals.selectedLong++;z.long++}
  if(prev){
   totals.pairs++;let D=e.J-prev.J;ok(D===relay+e.g&&e.n-prev.n===btime+e.w,"relay");
   let m=prev.a/prev.b,delta=Math.abs(mu-m);
   ok(delta*X<=9*D+1e-8,"slope Lipschitz");
   if(e.a===prev.a&&e.b===prev.b){
    totals.same++;z.same++;
    ok(e.b*(e.w+btime)-e.a*D===2*(e.a+e.b)*(e.s-prev.s),"same slope exact");
    ok(df<=4*relay+10+1e-8,"same slope mismatch");
    if(isFast){totals.fastSame++;z.fastSame++;ok((mu-.25)*e.g<=4*relay+10+1e-8,"same fast demand");if(!examples.sameFast&&relay>0)examples.sameFast={X,Q:z.Q,nr:z.nr,prev,e,relay,btime,can}}
    if(isLong)totals.longSame++;
    if(relay===0){ok(Math.abs(e.w-mu*e.g)<=10+1e-8,"zero relay line");totals.strictTube++}
   }else{
    totals.switches++;z.switches++;S++;swgain+=e.g;swrelay+=relay;
    ok(delta+1e-12>=1/(z.Q*z.Q),"Farey spacing");ok(9*D*z.Q*z.Q>=X,"switch demand");
    if(!examples.switch)examples.switch={X,Q:z.Q,nr:z.nr,prev,e,relay,btime,can};
    if(z.lock){ok(18*relay*z.Q*z.Q>=X&&relay>=e.g,"locked switch charge");totals.lockedSwitches++;z.lockedSwitches++;if(!examples.lockedSwitch)examples.lockedSwitch={X,Q:z.Q,nr:z.nr,prev,e,relay,btime,can}}
   }
   if(!examples.fastLong&&isFast&&prev.w>=prev.p-2&&e.a===prev.a&&e.b===prev.b)examples.fastLong={X,Q:z.Q,nr:z.nr,prev,e,relay,btime,can};
  }else firstg=e.g;
  prev=e;relay=btime=0;
 }
 if(!k)continue;
 z.blocks++;totals.blockChecks++;z.maxF=Math.max(z.maxF,F);z.maxFast=Math.max(z.maxFast,fast);z.maxK=Math.max(z.maxK,k);
 ok(S*X<=9*z.Q*z.Q*(F+U),"switch count");ok(dev<=4*U+10*(k-1)+4*B+4*B*S+1e-7,"general alignment");
 if(z.lock){totals.lockBlocks++;totals.lockedSelected+=k;totals.lockedFast+=fast;ok(dev<=4*U+10*(k-1)+4*B+1e-7,"locked alignment");ok(fast<=32*U+80*(k-1)+32*B+1e-7,"locked fast budget");ok(swrelay>=swgain,"switch gain charge")}
 }
}
for(let H=X;H<X+Math.min(3*X,32768);H+=4){scan(H,(H+6)/2,true);roots++;totals.roots++}
// Enumerate exact resonance arrivals on reduced fractions a/b, b<=8; use both shortest and longest feasible wait.
let seen=new Set();
for(let H=X;H<Y;H+=Math.max(2,2*Math.floor(Math.sqrt(X)/64))){
 let f=elig(H);for(let s=0;s<2;s++)for(let p of f[s]){
 if(p<T)continue;let J=H+p-1,A=J+2*s;
 for(let b=1;b<=8;b++){if(A%b)continue;for(let a=Math.ceil(b/2);a<=3*b;a++){
 if(gcd(a,b)!==1)continue;let n=a*(A/b)+2*s;if(n%2!==s||mod(n-(s?p+2:0),2*p)!==0)continue;
 let W=gap(n,p,s,f),l=Math.max(1,n-(3*H+3)),u=Math.min(W,n-H/2);
 if(l>u)continue;
 for(let w of new Set([l,u])){let t=n-w,key=H+","+t;if(seen.has(key))continue;seen.add(key);let z=first(t,f);ok(z.p===p&&z.w===w,"target clock");scan(H,t,false);targeted++;totals.targeted++}
 }}
 }
}
results.push({X,T,B,roots,targeted,events,configs:configs.map(z=>({Q:z.Q,nr:z.nr,lock:z.lock,selected:z.selected,fast:z.fast,long:z.long,same:z.same,switches:z.switches,lockedSwitches:z.lockedSwitches,blocks:z.blocks,maxF:z.maxF,maxFast:z.maxFast,maxK:z.maxK,fastSame:z.fastSame}))});
}
return {totals,examples,results}
}
console.log(JSON.stringify(audit(),null,2));
