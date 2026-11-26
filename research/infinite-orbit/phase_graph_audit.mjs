// Run: node research/infinite-orbit/phase_graph_audit.mjs
function audit(){
const max=16*262144+2*1024+10,spf=new Int32Array(max+1);for(let p=2;p*p<=max;p++)if(!spf[p])for(let n=p*p;n<=max;n+=p)if(!spf[n])spf[n]=p;
function factors(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
function elig(H){let b=Math.floor(Math.sqrt(H+1));return [factors(H-1).filter(p=>p<=b),factors(H+1).filter(p=>p<=b)]}
function maxwait(p,s,f){let W=2*p;for(let i=0;i<2;i++)for(let q of f[i])if(q!==p)W=Math.min(W,i!==s?2*q-1:q<p?2*q-2:2*q);return W}
function mod(a,b){return (a%b+b)%b}
function first(H,t,f){let w=Infinity,p=0,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let r=i?q+2:0;let z=1+mod(r-t-1,2*q);if(z<w||(z===w&&q<p)){w=z;p=q;s=i}}return {w,p,s}}
function gcd(a,b){while(b){[a,b]=[b,a%b]}return a}
function literal(H,t){let B=Math.floor(Math.sqrt(H+1));for(let w=1;w<=2*B;w++){let n=t+w,g=gcd(n%2?n-2:n,n%2?H+1:H-1);let p=factors(g).find(x=>x<=B);if(p)return {p,w,s:n%2}}return {p:0,w:Infinity,s:0}}
function ok(x,m){if(!x)throw Error(m)}
let local=0, attained=0, strict=0, tie=0, opp=0, exactAffine=0, affineSurvivors=0,crtAttain=0,lit=0;
function mb(a,p){return (a%p+p)%p}
function inv(a,p){let x=0n,y=1n,b=p;while(a){let q=b/a;[b,a]=[a,b-q*a];[x,y]=[y,x-q*y]}ok(b===1n,"inverse");return mb(x,p)}
for(let H=4;H<=10000;H+=2){
 let f=elig(H),actual=new Map();let P=2;for(let a of f)for(let p of a)P*=p;
 let cap=P<=20000?P:300;
 for(let t=0;t<cap;t++){let z=first(H,t,f);if(!z.p)continue;let W=maxwait(z.p,z.s,f);ok(z.w<=W,"upper");actual.set(z.p,Math.max(actual.get(z.p)||0,z.w));local++}
 for(let s=0;s<2;s++)for(let p of f[s]){
 let W=maxwait(p,s,f);if(W<2*p)strict++;if(f[1-s].length&&W===2*f[1-s][0]-1)opp++;if(f[s].some(q=>q<p&&W===2*q-2))tie++;if(P<=20000){ok(actual.get(p)===W,"attainment");attained++}
 // CRT construction of arrival n attaining all allowed backward gaps.
 let a=BigInt(s),M=2n;for(let i=0;i<2;i++)for(let q of f[i]){let Q=BigInt(q),r=i?2:0,shift=i!==s?-1:i===s&&q<p?-2:0;let b=BigInt(r+shift);a+=M*mb((b-a)*inv(M%Q,Q),Q);M*=Q}
 a+=M*BigInt(H+1);let t=a-BigInt(W);let w0=Infinity,p0=0;
 for(let i=0;i<2;i++)for(let q of f[i]){let w=Number(1n+mb(BigInt(i?q+2:0)-t-1n,BigInt(2*q)));if(w<w0||(w===w0&&q<p0)){w0=w;p0=q}}
 ok(w0===W&&p0===p,"CRT max attainment");crtAttain++;
 }
 for(let m of [1,2]){let t=m*H,z=first(H,t,f);if(!z.p)continue;let p=f[0][0],q=f[1][0],w=p?m*(p-1):Infinity;let other=q? (m===1?3:q===3?1:q+4):Infinity;
 let pred=!!p&&w<other;
 ok((t+z.w===m*(H+z.p-1))===pred,"affine classification");
 if(pred)affineSurvivors++;exactAffine++;let zz=literal(H,t);ok(zz.p===z.p&&zz.w===z.w,"literal");lit++}
}
let windows=[];
for(let X of [4096,16384,65536,262144]){
 let Y=16*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(X)),K=210,V=12;let safe=H=>Math.min(H%K,K-H%K)>V;
 let N=(Y-X)/2,types=["factor","nondecrease","long","longSafe"],stats=[];
 let finalGain,finalLen;
 for(let mode=0;mode<4;mode++){
  let gain=new Int32Array(N),len=new Int32Array(N),nx=new Int32Array(N);let nEdges=0,nStarts=0,best=0,bi=0,vertices=0;
  for(let i=N-1;i>=0;i--){
   let H=X+2*i;if(mode===3&&!safe(H))continue;vertices++;
   let f=elig(H),bestg=0,bestl=0,bestp=0;
   for(let s=0;s<2;s++)for(let p of f[s]){
    if(p<T||p>B)continue;
    let W=maxwait(p,s,f),g=p-1,H2=H+g;
    if(mode===1&&W<Math.ceil(g/2))continue;
    if(mode>=2&&W<p-2)continue;
    if(mode===3&&!safe(H2))continue;
    nEdges++;let gi=g+(H2<Y?gain[(H2-X)/2]:0),li=1+(H2<Y?len[(H2-X)/2]:0);
    if(gi>bestg){bestg=gi;bestl=li;bestp=p}
   }
   gain[i]=bestg;len[i]=bestl;nx[i]=bestp;
   if(bestg){nStarts++;if(bestg>best){best=bestg;bi=i}}
  }
  let H=X+2*bi,steps=[];while(H<Y&&nx[(H-X)/2]){let p=nx[(H-X)/2];steps.push([H,p]);H+=p-1}
  let entryMax=0;for(let i=0;i<=Math.floor((B-1)/2);i++)entryMax=Math.max(entryMax,gain[i]);
  stats.push({mode:types[mode],vertices,nEdges,nStarts,maxGain:best,maxLen:len[bi],entryMax,example:steps});
  if(mode===3){finalGain=gain;finalLen=len}
 }
 // Exact phase search for any eligible safe long run with >=2 events. The first arrival is enough:
 // check existence of t in [ceil(H/2),3H+3] and w>=p-2, then deterministic continuation.
 let best=0,example=null,arrivalChecks=0,feasible=0,two=0,starts=0;
 for(let i=0;i<N;i++){
 let H=X+2*i;if(!safe(H)||finalGain[i]===0)continue;
 let f=elig(H);
 for(let s=0;s<2;s++)for(let p of f[s]){
 let g=p-1,H2=H+g;
 if(p<T||p>B||maxwait(p,s,f)<p-2||!safe(H2)||H2>=Y||finalGain[(H2-X)/2]===0)continue;
 starts++;
 let minT=H/2,maxT=3*H+3,r=s?p+2:0;
 let n=minT+p-2+mod(r-(minT+p-2),2*p);
 for(;n<=maxT+2*p;n+=2*p){
  arrivalChecks++;
  let back=2*p,valid=true;
  for(let a=0;a<2;a++)for(let q of f[a]){
   if(a===s&&q===p)continue;let x=mod(n-(a?q+2:0),2*q);
   if(!x&&q<p){valid=false;break}
   back=Math.min(back,x||2*q)
  }
  if(!valid)continue;
  let lo=Math.max(p-2,n-maxT),hi=Math.min(back,n-minT);
  if(lo>hi)continue;
  let t=n-lo,z=first(H,t,f);ok(z.p===p&&z.w===lo,"arrival interval");feasible++;
  let h=H2,tt=n,gg=g,steps=[[H,t,p,lo]];
  while(h<Y){
   let ff=elig(h),a=first(h,tt,ff);
   if(a.p<T||a.p>B||a.w<a.p-2||!safe(h+a.p-1))break;
   steps.push([h,tt,a.p,a.w]);h+=a.p-1;tt+=a.w;gg+=a.p-1;
  }
  if(steps.length>=2)two++;
  if(gg>best){best=gg;example=steps}
 }
 }
 }
 // For singleton maximum, a projected edge may have no arrival within bounded range;
 // test all projected edges by scanning n until first feasible arrival, retaining best exact singleton.
 let singleton=0,singletonExample=null,oneChecks=0;
 for(let i=0;i<N;i++){
 let H=X+2*i;if(!safe(H)||finalGain[i]===0)continue;
 let f=elig(H);
 for(let s=0;s<2;s++)for(let p of f[s]){
 if(p<T||p>B||p-1<=singleton||maxwait(p,s,f)<p-2||!safe(H+p-1))continue;
 let minT=H/2,maxT=3*H+3,r=s?p+2:0;
 for(let n=minT+p-2+mod(r-(minT+p-2),2*p);n<=maxT+2*p;n+=2*p){
  oneChecks++;let t=Math.min(maxT,n-(p-2));if(t<minT)continue;let z=first(H,t,f);if(z.p===p&&t+z.w===n&&z.w>=p-2){singleton=p-1;singletonExample=[H,t,p,z.w];break}
 }
 }
 }
 if(singleton>best){best=singleton;example=[singletonExample]}
 if(example)for(let [h,t,p,w] of example){let z=literal(h,t);ok(z.p===p&&z.w===w,"literal path");lit++}
 windows.push({X,T,B,K,V,stats,exact:{maxGain:best,example,starts,arrivalChecks,feasible,two,oneChecks}});
}
return {local,attained,crtAttain,strict,tie,opp,exactAffine,affineSurvivors,lit,windows}
}
console.log(JSON.stringify(audit(),null,2));
