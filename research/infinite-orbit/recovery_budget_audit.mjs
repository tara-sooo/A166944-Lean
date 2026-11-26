// Run: node research/infinite-orbit/recovery_budget_audit.mjs
function audit(){
const max=1048576+2048,spf=new Int32Array(max+1);for(let p=2;p*p<=max;p++)if(!spf[p])for(let n=p*p;n<=max;n+=p)if(!spf[n])spf[n]=p;
function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
function elig(H){let b=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=b),fac(H+1).filter(p=>p<=b)]}
function mod(a,b){return (a%b+b)%b}
function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let v=1+mod((i?q+2:0)-t-1,2*q);if(v<w||(v===w&&q<p)){p=q;w=v;s=i}}return {p,w,s}}
function ok(x,m){if(!x)throw Error(m)}
let summaries=[],totalEvents=0,capHits=0,runChecks=0,prefixChecks=0,recoveryChecks=0,weightedChecks=0,highChecks=0,nontrivial=0,shallowAfterDeep=0,negativeSmall=0,exactCostChecks=0,exactPositive=0,deepRecovery=0,upwardChecks=0,monotoneChecks=0,mediumCostChecks=0,upwardExamples=[],examples=[];
const configs=[{R:3,M:4,r:5},{R:5,M:14,r:7},{R:7,M:34,r:11}];
for(let X of [4096,16384,65536]){
let Y=16*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(Y+1));
let states=[],roots=0,intermediate=0;
for(let H=X;H<X+Math.min(4*X,32768);H+=4){states.push([H,(H+6)/2,1]);roots++}
for(let H=X;H<Y;H+=Math.max(2,Math.floor(Math.sqrt(X)/4)*2)){let t=H/2+((H*37+19)%(H+1));states.push([H,t,0]);intermediate++}
let stats=configs.flatMap(c=>[1,2,4].map(k=>({...c,k,A:T-1-c.M-2,Q:T-1,tags:0,goodGain:0,shallowGain:0,badGain:0,lowGain:0,maxShallow:0,maxGoodRun:0,goodRuns:0,deepThenShallow:0,nontrivialPrefix:0,recoveryGain:0,recoveryDemand:0,weightedLhs:0,weightedRhs:0,canonShallow:0,arbitraryShallow:0}))).filter(c=>c.A>0);
// Add actual first-arrival states at prescribed positive strata; this is not canonical ancestry.
let targeted=0;for(let H=X;H<Y;H+=2){let f=elig(H);for(let s=0;s<2;s++)for(let p of f[s]){if(p<T)continue;for(let h of [1,2,4,8]){let H2=H+p-1,n=(H2+2*h*p+6*s)/2;if(n%2!==s||mod(n-(s?p+2:0),2*p)!==0)continue;let w=p-2,t=n-w;if(t<H/2||t>3*H+3)continue;let a=first(t,f);if(a.p!==p||a.w!==w)continue;states.push([H,t,0]);targeted++;}}}
let nCap=0,stop=0,exit=0;
for(let [H0,t0,can] of states){
let H=H0,t=t0,ev=[];
for(let n=0;n<3000&&H<Y;n++){let a=first(t,elig(H));if(!a.p){stop++;break}let g=a.p-1,d=2*t-H,d2=d+2*a.w-g;ok(d>=0&&d2>=0,"d envelope");let h=(d2-6*a.s)/(2*a.p);ok(Number.isInteger(h)&&(h>=0||a.p===3&&a.s===1&&d2===0&&h===-1),"adjusted multiplier");if(h<0)negativeSmall++;ev.push({H,t,p:a.p,w:a.w,s:a.s,g,d,d2,h});H+=g;t+=a.w;totalEvents++;if(n===2999&&H<Y)nCap++}
if(H>=Y)exit++;
for(let z of stats){
const {R,M,r,k,A,Q}=z, D=2*k*B+6;
let good=e=>e.p>=T&&e.w>=e.p-2, shallow=e=>good(e)&&e.h<=k;
let F=0,U=0,L=0,out=0,lastSh=-1,sh=0,nb=0;
let runF=0,runL=0,runN=0,runSh=0,runHasDeep=false,runLive=false,runLastCap=0;
let prevSh=null,betweenDrop=0,betweenGain=0,seenDeep=false,prevGood=null;
function finish(){if(runLive){z.goodRuns++;z.maxGoodRun=Math.max(z.maxGoodRun,runF);ok(runLastCap*A<=D*Q,"run cap");runChecks++;z.maxShallow=Math.max(z.maxShallow,runSh)}runF=runL=runN=runSh=runLastCap=0;runHasDeep=runLive=false;prevGood=null}
for(let i=0;i<ev.length;i++){
 let e=ev[i];
 if(e.p<=R){L+=e.g;if(runLive)runL+=e.g}
 else{out++;if(good(e)){F+=e.g;if(!runLive){runLive=true;runF=runL=runN=runSh=runLastCap=0;runHasDeep=false}if(prevGood){ok(e.d2>=prevGood.d2+e.g-2-M&&e.d2>prevGood.d2,"strict post monotone");monotoneChecks++;if(prevGood.h>k&&e.h<=k){ok((2*k-1)*e.p>=2*prevGood.h*prevGood.p-M-9,"upward return");upwardChecks++;if(upwardExamples.length<4)upwardExamples.push({X,R,k,first:[prevGood.H,prevGood.p,prevGood.h,prevGood.d2],second:[e.H,e.p,e.h,e.d2]});}}prevGood=e;
 runF+=e.g;runN++;ok(runL<=M*(runN-1),"relay cap");ok(A*runF<=Q*e.d2,"growth lower");highChecks++;if(shallow(e)){runSh+=e.g;runLastCap=runF;ok(e.d2<=D,"shallow");capHits++;if(runHasDeep){z.deepThenShallow++;shallowAfterDeep++}}else runHasDeep=true}
 else {U+=e.g;nb++;finish()}}
 if(prevSh!==null){if(shallow(e)){let demand=prevSh.d2-e.d;ok(betweenDrop>=demand,"recovery telescope");recoveryChecks++;z.recoveryGain+=betweenGain;z.recoveryDemand+=Math.max(0,demand);if(demand>0){nontrivial++;if(examples.length<3)examples.push({X,R,k,from:prevSh.H,to:e.H,drop:demand,relayGain:betweenGain})}betweenDrop=betweenGain=0}else{betweenDrop+=Math.max(0,e.d-e.d2);betweenGain+=e.g}}
 if(good(e)&&!shallow(e))seenDeep=true;if(shallow(e)){if(seenDeep){deepRecovery++;seenDeep=false;}lastSh=i;sh+=e.g;prevSh=e}
 }
 finish();ok(L<=M*(out+1),"global low bound");ok(A*sh<=D*Q*(nb+1),"run-count bound");
 if(lastSh>=0){let pre=ev.slice(0,lastSh+1),f=0,u=0,um=0,uh=0,neg=0,pos=0;for(let e of pre){if(good(e)){f+=e.g;pos+=e.d2-e.d}else if(e.p>R){u+=e.g;if(e.p<T)um+=e.g;else uh+=e.g;}if(!good(e))neg+=Math.max(0,e.d-e.d2)}
 let last=ev[lastSh];ok(neg>=pos-last.d2+ev[0].d,"negative resource");
 ok(A*f*(r-1)<=Q*((last.d2-ev[0].d+M)*(r-1)+(r-1+M)*u),"exact endpoint cost");ok(A*f*(r-1)<=Q*((last.d2-ev[0].d+M)*(r-1)+(r-1+M)*um)+(Q+M)*(r-1)*uh,"medium and high separated cost");mediumCostChecks++;exactCostChecks++;if(A*f>Q*(last.d2-ev[0].d+M))exactPositive++;ok(A*f*(r-1)<=Q*((D+M)*(r-1)+(r-1+M)*u),"gain cost");
 let weight=1+(H0%17);z.weightedLhs+=weight*A*f*(r-1);z.weightedRhs+=weight*Q*((D+M)*(r-1)+(r-1+M)*u);
 prefixChecks++;if(f>D)z.nontrivialPrefix++;if(can)z.canonShallow+=sh;else z.arbitraryShallow+=sh;
 }
 z.tags++;z.goodGain+=F;z.badGain+=U;z.lowGain+=L;z.shallowGain+=sh;
}
}
for(let z of stats){ok(z.weightedLhs<=z.weightedRhs,"weighted");weightedChecks++}
summaries.push({X,T,B,roots,intermediate,targeted,stop,exit,nCap,stats:stats.map(z=>({R:z.R,k:z.k,tags:z.tags,goodGain:z.goodGain,shallowGain:z.shallowGain,badGain:z.badGain,maxShallow:z.maxShallow,maxGoodRun:z.maxGoodRun,goodRuns:z.goodRuns,deepThenShallow:z.deepThenShallow,nontrivialPrefix:z.nontrivialPrefix,recoveryGain:z.recoveryGain,recoveryDemand:z.recoveryDemand,canonShallow:z.canonShallow,arbitraryShallow:z.arbitraryShallow}))});
}
return {totalEvents,capHits,runChecks,prefixChecks,recoveryChecks,weightedChecks,highChecks,nontrivial,shallowAfterDeep,negativeSmall,exactCostChecks,exactPositive,deepRecovery,upwardChecks,monotoneChecks,mediumCostChecks,upwardExamples,examples,summaries};
}
console.log(JSON.stringify(audit(),null,2));
