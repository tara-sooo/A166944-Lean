// Run: node research/infinite-orbit/mixed_relay_audit.mjs
function audit(){
 const max=16*65536+2048,spf=new Int32Array(max+1);for(let p=2;p*p<=max;p++)if(!spf[p])for(let n=p*p;n<=max;n+=p)if(!spf[n])spf[n]=p;
 function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function elig(H){let B=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=B),fac(H+1).filter(p=>p<=B)]}
 function mod(x,p){return (x%p+p)%p}
 function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let z=1+mod((i?q+2:0)-t-1,2*q);if(z<w||(z===w&&q<p)){p=q;w=z;s=i}}return {p,w,s}}
 function maxwait(p,s,f){let W=2*p;for(let i=0;i<2;i++)for(let q of f[i])if(q!==p)W=Math.min(W,i!==s?2*q-1:q<p?2*q-2:2*q);return W}
 function ok(x,m){if(!x)throw Error(m)}
 function gcd(a,b){while(b)[a,b]=[b,a%b];return a}
 function literal(H,t){let B=Math.floor(Math.sqrt(H+1));for(let w=1;w<=2*B;w++){let n=t+w,g=gcd(n%2?n-2:n,n%2?H+1:H-1),p=fac(g).find(q=>q<=B);if(p)return {p,w,s:n%2}}return {p:0,w:Infinity,s:0}}
 let results=[],tableChecks=0,clockChecks=0,canonChecks=0;
 for(let R of [3,5,7]){
 const ps=[3,5,7].filter(p=>p<=R),K=2*ps.reduce((a,b)=>a*b,1),safeK=210,V=12,safe=H=>Math.min(H%safeK,safeK-H%safeK)>V;
 const low=(h)=>[ps.filter(p=>mod(h-1,p)===0),ps.filter(p=>mod(h+1,p)===0)];
 const C=new Map(),E=new Map();let maxRelay=0,maxEvents=0,maxTime=0;
 for(let h=0;h<K;h+=2)for(let t=0;t<K;t++){
 let H=h,tt=t,n=0;for(;;){let z=first(tt,low(H));if(!z.p)break;H+=z.p-1;tt+=z.w;n++;ok(H-h<K,"low barrier");}
 let e=H-h,b=tt-t;ok(b<=3*e,"time budget");ok(low(H).every(a=>a.length===0),"terminal rough");C.set(h*K+t,{e,b,n});
 let key=2*h+(t%2);if(!E.has(key))E.set(key,new Set());E.get(key).add(e);maxRelay=Math.max(maxRelay,e);maxEvents=Math.max(maxEvents,n);maxTime=Math.max(maxTime,b);tableChecks++;
 }
 for(let X of [4096,16384,65536]){
 let Y=16*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(X)),N=(Y-X)/2;
 let g=new Int32Array(N),ng=new Int32Array(N),nmax=new Int32Array(N),hiEdges=0,relayEdges=0,branches=0,peak=0,peakH=0,peakN=0;
 function good(H,p,s,f){return p>=T&&p<=B&&maxwait(p,s,f)>=p-2&&safe(H)&&safe(H+p-1)}
 for(let i=N-1;i>=0;i--){let H=X+2*i;if(!safe(H))continue;let f=elig(H);
 for(let s=0;s<2;s++)for(let p of f[s]){
 if(!good(H,p,s,f))continue;ok(f[0].concat(f[1]).every(q=>q>R),"high rough");hiEdges++;
 let gain=p-1,H2=H+gain;if(gain>g[i]){g[i]=gain;ng[i]=1}nmax[i]=Math.max(nmax[i],1);
 for(let e of E.get(2*(H2%K)+s)){
 let J=H2+e;if(J>=Y||!g[(J-X)/2])continue;relayEdges++;if(e)branches++;
 let j=(J-X)/2,v=gain+e+g[j];if(v>g[i]){g[i]=v;ng[i]=1+ng[j]}nmax[i]=Math.max(nmax[i],1+nmax[j]);
 }
 }
 if(g[i]>peak){peak=g[i];peakH=H}peakN=Math.max(peakN,nmax[i]);
 }
 let exactPeak=0,exactN=0,example=null,arrivals=0,feasible=0,success=0,interrupt=0,complete=0,nonzero=0,solo=0;
 // enumerate first high arrivals only for candidates with projected second high; singleton separately
 for(let i=0;i<N;i++){
 let H=X+2*i;if(!g[i])continue;let f=elig(H);
 for(let s=0;s<2;s++)for(let p of f[s]){
 if(!good(H,p,s,f))continue;let H2=H+p-1;
 let potential=[...E.get(2*(H2%K)+s)].some(e=>H2+e<Y&&g[(H2+e-X)/2]>0);
 if(!potential&&p-1<=exactPeak)continue;
 let loT=H/2,hiT=3*H+3,r=s?p+2:0;
 for(let n=loT+p-2+mod(r-(loT+p-2),2*p);n<=hiT+2*p;n+=2*p){
 if(potential)arrivals++;else solo++;
 let cap=2*p,valid=true;for(let a=0;a<2;a++)for(let q of f[a]){if(q===p)continue;let z=mod(n-(a?q+2:0),2*q);if(!z&&q<p){valid=false;break}cap=Math.min(cap,z||2*q)}
 if(!valid)continue;let l=Math.max(p-2,n-hiT),u=Math.min(cap,n-loT);if(l>u)continue;
 let t=n-l,z=first(t,f);ok(z.p===p&&z.w===l,"first");feasible++;
 let h=H2,tt=n,last=h,count=1,steps=[[H,t,p,l]],bestSteps=steps.slice();
 while(h<Y){
 let cc=C.get((h%K)*K+tt%K),end=h+cc.e,endt=tt+cc.b;
 // execute actual low-only prefix, then inspect exact high continuation
 let failed=false;
 while(h<end&&h<Y){let f0=elig(h),z0=first(tt,f0),zl=first(tt,low(h));if(z0.p!==zl.p||z0.w!==zl.w){interrupt++;failed=true;break}
 steps.push([h,tt,z0.p,z0.w]);h+=z0.p-1;tt+=z0.w;}
 if(failed||h>=Y)break;ok(h===end&&tt===endt,"relay transfer");complete++;if(cc.e)nonzero++;
 let ff=elig(h),a=first(tt,ff);if(!a.p||!good(h,a.p,a.s,ff)||a.w<a.p-2)break;
 steps.push([h,tt,a.p,a.w]);h+=a.p-1;tt+=a.w;last=h;count++;bestSteps=steps.slice();
 }
 if(count>=2)success++;let total=last-H;ok(total<=g[i],"projected cap");if(total>exactPeak){exactPeak=total;example=bestSteps}exactN=Math.max(exactN,count);
 if(!potential)break;
 }
 }
 }
 // canonical control: full deterministic trajectories up to upper bound or first stop, count mixed spans
 let canonical={roots:0,events:0,good:0,maxMixedGain:0,maxMixedHigh:0,low:0,stop:0};
 for(let H0=X+(4-X%4)%4;H0<X+Math.min(X,4096);H0+=4){
 let h=H0,t=(h+6)/2,runStart=null,runN=0;canonical.roots++;
 for(let j=0;j<2000&&h<Y;j++){
 let f=elig(h),z=first(t,f);if(!z.p){canonical.stop++;break}
 canonical.events++;if(z.p<=R){canonical.low++}else if(good(h,z.p,z.s,f)&&z.w>=z.p-2){canonical.good++;if(runStart===null){runStart=h;runN=0}runN++;canonical.maxMixedGain=Math.max(canonical.maxMixedGain,h+z.p-1-runStart);canonical.maxMixedHigh=Math.max(canonical.maxMixedHigh,runN);if(runStart>=X)ok(h+z.p-1-runStart<=g[(runStart-X)/2],"canonical mixed cap");canonChecks++;}else{runStart=null;runN=0}
 h+=z.p-1;t+=z.w;
 }
 }
 if(example)for(let [h,t,p,w] of example){let a=literal(h,t);ok(a.p===p&&a.w===w,"literal mixed");clockChecks++}
 results.push({R,K,X,T,B,maxRelay,maxEvents,maxTime,hiEdges,relayEdges,nonzeroRelayEdges:branches,projectedGain:peak,projectedCount:peakN,peakH,exactPeak,exactN,arrivals,feasible,success,interrupt,complete,nonzero,solo,example,canonical});
 }
 }
 return {tableChecks,clockChecks,canonChecks,results};
}
console.log(JSON.stringify(audit(),null,2));
