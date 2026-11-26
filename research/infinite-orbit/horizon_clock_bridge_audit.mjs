// Run: node research/infinite-orbit/horizon_clock_bridge_audit.mjs
function audit(){
function ok(v,m){if(!v)throw Error(m)}
function gcd(a,b){a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a}
function mod(a,b){return (a%b+b)%b}
const lim=4097,pr=[],sieve=new Uint8Array(lim+1);
for(let p=2;p<=lim;p++)if(!sieve[p]){pr.push(p);if(p*p<=lim)for(let n=p*p;n<=lim;n+=p)sieve[n]=1}
function factors(n){let a=[];for(let p of pr){if(p*p>n)break;if(n%p===0){a.push(p);while(n%p===0)n/=p}}if(n>1)a.push(n);return a}
function edges(H,cap){let out=[];for(let s=0;s<2;s++)for(let p of factors(H-1+2*s))if(p>=3&&p<=cap&&p*p<=H+1)out.push({p,s,g:p-1,c:s?p+2:0});return out}
function next(t,e){return t+1+mod(e.c-t-1,2*e.p)}
function earliest(H,t){let es=edges(H,Math.floor(Math.sqrt(H+1)));es.sort((a,b)=>next(t,a)-next(t,b)||a.p-b.p);return es[0]}
function maxWait(H,n,p){let W=2*p;for(let e of edges(H,Math.floor(Math.sqrt(H+1))))if(e.p!==p){let z=mod(n-e.c,2*e.p);if(!z&&e.p<p)return 0;W=Math.min(W,z||2*e.p)}return W}
function anchors(X,alternating){
let T=Math.sqrt(X),S=Math.floor(T**.25),ps=pr.filter(p=>p>=T/2&&p<=T),width=15*X/S,out=[];
function slot(p,lo,hi){let q=Math.ceil((lo-1)/p);if(q%2===0)q++;for(;p*q+1<=hi;q+=2){let k=Math.floor(Math.sqrt(2)*q/2);if(gcd(q,k)===1)return {H:p*q+1,n:2*p*k,p,q,k}}return null}
if(alternating){let a=ps.filter(p=>p<=5*T/8),b=ps.filter(p=>p>=7*T/8);
for(let j=0;j<S;j++){let lo=Math.ceil(X+j*width+16*T),hi=Math.floor(X+(j+1)*width-16*T),p=a[Math.floor(j*a.length/S)],r=b[Math.floor(j*b.length/S)];
for(let start=lo;start+512*T<=hi;start+=512*T){let x=slot(p,start+8*T,start+248*T),y=slot(r,start+264*T,start+504*T);if(x&&y)out.push(x,y)}}
}else for(let j=0;j<S;j++){let p=ps[Math.floor(j*ps.length/S)],lo=Math.ceil(X+j*width+16*T),hi=Math.floor(X+(j+1)*width-16*T),q=Math.ceil((lo-1)/p);if(q%2===0)q++;
for(;p*q+1<=hi;q+=2){let k=Math.floor(Math.sqrt(2)*q/2),H=p*q+1;if(gcd(q,k)!==1||out.length&&H-out[out.length-1].H<16*T)continue;out.push({H,n:2*p*k,p,q,k});}}
return out}
let totals={tests:0,horizon:0,parity:0,scalar:0,terminal:0,bracket:0,exactClock:0,flexTerminal:0,flexBracket:0,flexClock:0,exactMin:0,reverseStates:0,reverseIntervals:0,reverseMax:0,reverseEdges:0,scalarEvents:0,scalarClockViolations:0,exactClockEvents:0,flexClockEvents:0,competitionFailures:0,bruteTests:0,bruteStates:0,anchorTests:0,noLast1:0,noLast2:0,noLastFlex:0},blocks=[],examples={scalar:null,clock:null,flex:null,terminal:null},first=null;
function terminalOptions(H,t,cap){let s=mod(t,2),a=gcd(H+2*s,t-2*s);return factors(a).filter(p=>p>=3&&p<=cap&&H-p+1>=4&&p*p<=H-p+2)}
function merge(a){if(!a.length)return a;a.sort((x,y)=>x[0]-y[0]||x[1]-y[1]);let r=[a[0]];for(let i=1;i<a.length;i++){let last=r[r.length-1],z=a[i];if(z[0]<=last[1]+1)last[1]=Math.max(last[1],z[1]);else r.push(z)}return r}
function preimage(l,u,e){let a=l+mod(e.c-l,2*e.p),b=u-mod(u-e.c,2*e.p);return a<=b?[a-2*e.p,b-1]:null}
function contains(a,t){return a&&a.some(z=>z[0]<=t&&t<=z[1])}
function search(A,B,cap,doBrute=false){
let H=A.H+A.p-1,t=A.n,J=B.H,n=B.n-1,E=J-H,W=n-t,N=E/2;
ok(N>0&&W>=E&&W<=2*E,"bridge geometry");
let es=Array.from({length:N},(_,i)=>edges(H+2*i,cap).filter(e=>i+e.g/2<=N));
let reach=new Uint8Array(N+1),parent=new Int32Array(N+1),last=new Array(N+1),par=null,lo=new Float64Array(N+1),hi=new Float64Array(N+1);lo.fill(Infinity);hi.fill(-Infinity);lo[0]=hi[0]=t;reach[0]=1;
for(let i=0;i<N;i++)if(reach[i])for(let e of es[i]){let j=i+e.g/2;if(!reach[j]){reach[j]=1;parent[j]=i;last[j]=e}if(j===N&&e.s===mod(n,2))par={i,e};lo[j]=Math.min(lo[j],next(lo[i],e));hi[j]=Math.max(hi[j],next(hi[i],e))}
let terminal=terminalOptions(J,n,cap).some(p=>J-p+1>=H);
if(!terminal&&!examples.terminal)examples.terminal={H,t,J,n,cap,gcd:gcd(J+2*mod(n,2),n-2*mod(n,2))};
let bracket=reach[N]&&lo[N]<=n&&n<=hi[N],mw=Math.min(maxWait(J,B.n,B.p),B.n-J/2),f0=B.n-mw,f1=n,flexBracket=reach[N]&&lo[N]<=f1&&hi[N]>=f0,flexTerminal=false;
for(let v=f0;v<=f1;v++)if(terminalOptions(J,v,cap).some(p=>J-p+1>=H)){flexTerminal=true;break}
let scalar=false;
if(par){let path=[par.e],i=par.i;while(i){path.push(last[i]);i=parent[i]}path.reverse();let hh=H,tt=t;
for(let e of path){let j=hh+e.g,target=t+W*(j-H)/E,nn= j===J?n:2*Math.floor((target-e.s+1)/2)+e.s;
ok(nn>tt&&nn-tt<=2*e.p&&nn%2===e.s&&mod(hh-1+2*e.s,e.p)===0&&e.p*e.p<=hh+1,"balanced parity path");
ok(nn>=j/2&&nn<=3*j+3&&Math.abs(nn-target)<=1.00001,"envelope interpolation");
totals.scalarEvents++;if(mod(nn-2*e.s,e.p))totals.scalarClockViolations++;hh=j;tt=nn;}
ok(hh===J&&tt===n,"scalar target");scalar=true;if(!examples.scalar)examples.scalar={H,t,J,n,cap,events:path.length,first:path.slice(0,8)};
}
// Exact backward interval DP with scalar envelope at every state. Forward extremes ignore intermediate envelope, so only necessary.
function inverse(a,b,record){
let R=new Array(N+1);R[N]=[[a,b]];let visited=0,inter=0,max=0;
for(let i=N-1;i>=0;i--){if(!reach[i])continue;let hh=H+2*i,v=[];
let lower=Math.max(t,hh/2,Math.ceil(a-3*(J-hh))),upper=Math.min(b-1,3*hh+3);
for(let e of es[i]){let j=i+e.g/2;if(!R[j]||!R[j].length)continue;for(let z of R[j]){totals.reverseEdges++;let p=preimage(z[0],z[1],e);if(!p)continue;p[0]=Math.max(p[0],lower);p[1]=Math.min(p[1],upper);if(p[0]<=p[1])v.push(p)}}
if(v.length){R[i]=merge(v);visited++;inter+=R[i].length;max=Math.max(max,R[i].length);}
}
totals.reverseStates+=visited;totals.reverseIntervals+=inter;totals.reverseMax=Math.max(totals.reverseMax,max);
let yes=contains(R[0],t);
if(yes){let i=0,tt=t,path=[],competition=0;
while(i<N){let e=es[i].find(e=>contains(R[i+e.g/2],next(tt,e)));ok(e,"inverse witness");let hh=H+2*i,nn=next(tt,e),real=earliest(hh,tt);
if(real.p!==e.p||next(tt,real)!==nn)competition++;
ok(nn-tt>=1&&nn-tt<=2*e.p&&nn%2===e.s&&mod(nn-2*e.s,e.p)===0&&mod(hh-1+2*e.s,e.p)===0,"witness congruences");
path.push({H:hh,t:tt,p:e.p,w:nn-tt,s:e.s});i+=e.g/2;tt=nn;}
ok(tt>=a&&tt<=b&&earliest(J,tt).p===B.p&&next(tt,earliest(J,tt))===B.n,"witness exact terminal anchor");
totals[record==="clock"?"exactClockEvents":"flexClockEvents"]+=path.length;totals.competitionFailures+=competition;if(!examples[record])examples[record]={H,t,J,n,arrival:tt,cap,events:path.length,competition,first:path.slice(0,8)};
}
return yes;
}
let clock=!!(bracket&&terminal&&inverse(n,n,"clock")),flex=!!(flexBracket&&flexTerminal&&inverse(f0,f1,"flex"));
if(clock)ok(flex,"fixed implies flexible");
if(doBrute){let states=new Array(N+1);states[0]=new Set([t]);for(let i=0;i<N;i++)if(states[i])for(let tt of states[i]){totals.bruteStates++;for(let e of es[i]){let j=i+e.g/2,nn=next(tt,e),hh=H+2*j;if(nn>f1||nn<hh/2||nn>3*hh+3)continue;(states[j]??=new Set()).add(nn);}}let end=states[N]||new Set();ok(end.has(n)===clock&&[...end].some(v=>v>=f0&&v<=f1)===flex,"literal state census");totals.bruteTests++;}
return {horizon:!!reach[N],parity:!!par,scalar,terminal,bracket:!!bracket,exactClock:clock,flexTerminal,flexBracket:!!flexBracket,flexClock:flex,lo:lo[N],hi:hi[N],W,E,mw};
}
for(let X of [4096,65536,1048576])for(let alternating of (X===4096?[false]:[false,true])){
let as=anchors(X,alternating),cap=Math.floor(Math.sqrt(X)/8),before={...totals},cases=[],T=Math.sqrt(X);
for(let B of as){totals.anchorTests++;let w=maxWait(B.H,B.n,B.p),a=terminalOptions(B.H,B.n-1,cap).length,b=terminalOptions(B.H,B.n-2,cap).length;
if(!a)totals.noLast1++;if(!a&&!b)totals.noLast2++;let any=false;for(let i=1;i<=w;i++)if(terminalOptions(B.H,B.n-i,cap).length){any=true;break}if(!any)totals.noLastFlex++;}
let count=Math.min(alternating?4:24,as.length-1);
for(let i=0;i<count;i++){let A=as[i],B=as[i+1],r=search(A,B,cap,X===4096&&i<6);totals.tests++;for(let key of ["horizon","parity","scalar","terminal","bracket","exactClock","flexTerminal","flexBracket","flexClock"])if(r[key])totals[key]++;cases.push(r);}
blocks.push({X,alternating,anchors:as.length,cap,totals:Object.fromEntries(Object.keys(totals).map(k=>[k,totals[k]-before[k]])),ranges:cases.slice(0,3)});
}
return {totals,blocks,examples}
}
console.log(JSON.stringify(audit(),null,2));
