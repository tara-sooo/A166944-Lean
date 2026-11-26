// Run: node research/infinite-orbit/stitched_survivor_audit.mjs
function audit(){
function ok(b,m){if(!b)throw Error(m)}
function gcd(a,b){while(b)[a,b]=[b,a%b];return Math.abs(a)}
function mod(a,b){return (a%b+b)%b}
const top=16*1048576+100,lim=Math.ceil(Math.sqrt(top))+2,sieve=new Uint8Array(lim+1),pr=[];
for(let p=2;p<=lim;p++)if(!sieve[p]){pr.push(p);if(p*p<=lim)for(let n=p*p;n<=lim;n+=p)sieve[n]=1}
function factors(n){let a=[];for(let p of pr){if(p*p>n)break;if(n%p===0){a.push(p);while(n%p===0)n/=p}}if(n>1)a.push(n);return a}
function minEvent(H,t){let b=Math.floor(Math.sqrt(H+1)),p0=0,w0=Infinity,s0=0;for(let s of [0,1])for(let p of factors(H-1+2*s)){if(p>b)continue;let w=1+mod((s?p+2:0)-t-1,2*p);if(w<w0||(w===w0&&p<p0)){p0=p;w0=w;s0=s}}return [p0,w0,s0]}
function largestPrime(n){let lo=0,hi=pr.length;while(lo<hi){let m=(lo+hi)>>1;if(pr[m]<=n)lo=m+1;else hi=m}return pr[lo-1]}
let H=256,t=131,totals={anchors:0,repairs:0,gain:0,highGain:0,repairGain:0,repairHorizonFail:0,repairClockFail:0,repairBothFail:0,repairEligibleFail:0,repairFull:0,repairCompetitionFail:0,scalar:0,projection:0,segments:0,goodQ:0,skippedQ:0,lowCutViolations:0,clockRange:0,exactBridgeTests:0,exactBridgeSuccess:0,exactBridgeStopped:0,exactBridgeHigh:0,exactBridgeOvershoot:0,exactBridgeClock:0,exactBridgeCap:0,exactBridgeEvents:0,horizonTests:0,horizonSuccess:0,horizonVisited:0},blocks=[],example=null,firstFailure=null;
function scalar(p,w){ok(p>=3&&p<=Math.floor(Math.sqrt(H+1))&&p<=lim&&!sieve[p]&&w>=1&&w<=2*p,"scalar event");let d=2*t-H,HH=H+p-1,tt=t+w,dd=2*tt-HH;ok(d>=0&&dd>=0&&tt<=3*HH+3&&t<=3*H+3&&dd-d===2*w-(p-1)&&dd-d>=-(p-1)&&dd-d<=5*(p-1),"scalar envelope");H=HH;t=tt;totals.scalar++;totals.gain+=p-1}
function connect(H1,t1,cap){
let E=H1-H,W=t1-t;ok(E>=0&&E%2===0&&W>=E&&W<=2*E,"connector slope");
if(!E){ok(!W,"zero connector");return}
let startH=H,startT=t,cum=0,paid=0;
while(cum<E){let p=largestPrime(Math.min(cap,E-cum+1)),g=p-1;ok(p>=3&&g<=E-cum,"greedy repair");
let w=Math.floor(W*(cum+g)/E)-paid,n=t+w,s=n%2,he=(H-1+2*s)%p===0,ce=(n-2*s)%p===0,el=p*p<=H+1;
if(!he)totals.repairHorizonFail++;if(!ce)totals.repairClockFail++;if(!he&&!ce)totals.repairBothFail++;if(!el)totals.repairEligibleFail++;
let real=false;if(he&&ce&&el){let z=minEvent(H,t);real=z[0]===p&&z[1]===w&&z[2]===s;if(real)totals.repairFull++;else totals.repairCompetitionFail++;}
if(!real&&!firstFailure)firstFailure={H,t,p,w,s,he,ce,el,actual:minEvent(H,t)};
for(let [R,K] of [[3,6],[5,30],[7,210]])if(p<=R&&Math.ceil(H/K)*K<=H+g-1&&Math.ceil(H/K)*K>H)totals.lowCutViolations++;
scalar(p,w);cum+=g;paid+=w;totals.repairs++;totals.repairGain+=g;
ok(Math.abs(t-(startT+W*(H-startH)/E))<1.0000001,"balanced clock");
}ok(H===H1&&t===t1,"connector end");
}
for(let X of [4096,65536,1048576]){
let T=Math.sqrt(X),S=Math.floor(T**.25),ps=pr.filter(p=>p>=T/2&&p<=T),before={...totals},anchors=[],width=15*X/S,cap=Math.max(3,Math.floor(T/8));
ok(ps.length>=S,"labels");
for(let j=0;j<S;j++){
let p=ps[Math.floor(j*ps.length/S)],lo=Math.ceil(X+j*width+16*T),hi=Math.floor(X+(j+1)*width-16*T),good=0,kept=0;
let q=Math.ceil((lo-1)/p);if(q%2===0)q++;
for(;p*q+1<=hi;q+=2){let k=Math.floor(Math.sqrt(2)*q/2);if(gcd(q,k)!==1)continue;good++;totals.goodQ++;
let h=p*q+1,n=2*p*k;if(anchors.length&&h-anchors[anchors.length-1].H<16*T){totals.skippedQ++;continue}
anchors.push({H:h,n,p,q,k,j});kept++}
ok(kept>0,"segment occupied");totals.segments++;
}
let blockBridge=0,blockBfs=0;let minGap=Infinity,maxGap=0,minProjection=Infinity,maxProjection=0;
for(let z of anchors){let {H:h,n,p,q,k}=z;
let oldH=H,E=h-H,W=n-1-t;
if(totals.anchors) {minGap=Math.min(minGap,E);maxGap=Math.max(maxGap,E)}
// First connector spans a scale boundary; cap additionally limited by current eligibility.
let cc=Math.min(cap,Math.floor(Math.sqrt(H+1)));
if(totals.anchors){
totals.exactBridgeTests++;let hh=H,tt=t,outcome=null;
for(let step=0;step<2000;step++){
if(hh===h){outcome=tt===n-1?"exactBridgeSuccess":"exactBridgeClock";break}
if(hh>h){outcome="exactBridgeOvershoot";break}
let [p0,w0]=minEvent(hh,tt);if(!p0){outcome="exactBridgeStopped";break}if(p0>cc){outcome="exactBridgeHigh";break}
hh+=p0-1;tt+=w0;totals.exactBridgeEvents++;
}totals[outcome||"exactBridgeCap"]++;blockBridge++;
// Relax the clock and earliest rule but retain actual eligible neighbor divisibility.
// This finite DAG tests existence of ANY low-only horizon bridge.
if(blockBfs<24){blockBfs++;totals.horizonTests++;let reach=new Uint8Array(E/2+1);reach[0]=1;
for(let i=0;i<reach.length;i++)if(reach[i]){totals.horizonVisited++;let hh=H+2*i;for(let p0 of pr){if(p0<3)continue;if(p0>cc||p0*p0>hh+1)break;if((hh-1)%p0&&(hh+1)%p0)continue;let j=i+(p0-1)/2;if(j<reach.length)reach[j]=1;}}
if(reach[reach.length-1])totals.horizonSuccess++;
}}
connect(h,n-1,cc);
ok(H===h&&t===n-1&&gcd(n,H-1)===p&&n%2===0,"anchor gcd");
let actual=minEvent(H,t);ok(actual[0]===p&&actual[1]===1&&actual[2]===0,"anchor exact MIN");
let proj=2*(n/p)-(q+1);ok(proj>=0&&2*n-(H+p-1)===p*proj,"anchor deficit");
for(let [M,N] of [[1,2],[1,1],[3,2],[2,1],[4,3],[7,5]]){let v=N*(n/p)-M*(q+1);ok(Math.abs(v-(N*Math.sqrt(2)-M)*q)<=2*N+M,"irrational projection");totals.projection++;}
minProjection=Math.min(minProjection,proj);maxProjection=Math.max(maxProjection,proj);
if(!example&&totals.anchors>0)example={X,H:h,n,p,q,k,repairGain:E,repairWait:W,previousPostH:oldH,projection:proj};
scalar(p,1);totals.anchors++;totals.highGain+=p-1;
}
blocks.push({X,T,S,distinct:new Set(anchors.map(z=>z.p)).size,minGap,maxGap,minProjection,maxProjection,anchors:anchors.length,counts:Object.fromEntries(Object.keys(totals).map(k=>[k,totals[k]-before[k]]))});
}
return {totals,blocks,example,firstFailure}
}
console.log(JSON.stringify(audit(),null,2));
