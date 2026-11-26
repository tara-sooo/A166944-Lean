// Run: node research/infinite-orbit/first_exit_audit.mjs
function audit(){
 const max=16*262144+2048,spf=new Int32Array(max+1);for(let p=2;p*p<=max;p++)if(!spf[p])for(let n=p*p;n<=max;n+=p)if(!spf[n])spf[n]=p;
 function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function elig(H){let B=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=B),fac(H+1).filter(p=>p<=B)]}
 function mod(x,p){return (x%p+p)%p}
 function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let z=1+mod((i?q+2:0)-t-1,2*q);if(z<w||(z===w&&q<p)){p=q;w=z;s=i}}return {p,w,s}}
 function ok(x,m){if(!x)throw Error(m)}
 let results=[];
 for(let R of [3,5,7,11]){
 const ps=[3,5,7,11].filter(p=>p<=R),K=2*ps.reduce((a,b)=>a*b,1);
 const low=(h)=>[ps.filter(p=>mod(h-1,p)===0),ps.filter(p=>mod(h+1,p)===0)];
 // avoid huge 2310² table here: independently scan actual low paths and check universal K bounds
 let D=0,relays=0,negative=0,stopped=0;
 for(let X of [4096,16384,65536,262144]){
 let Y=16*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(X)),N=(Y-X)/4,counts={R,K,X,roots:N,stop:0,interrupted:0,fullLow:0,firstLongHigh:0,firstBand:0,stratumEligible:0,stratum1:0,maxGain:0,maxDeficit:0,phaseMatched:0,examples:[]},seen=new Set();
 for(let H0=X;H0<Y;H0+=4){
 let H=H0,t=(H0+6)/2,lowGain=0;
 for(;;){let a=first(t,elig(H)),b=first(t,low(H));
 if(!a.p){ok(!b.p,"stop low");counts.stop++;break}
 if(a.p>R){
 if(b.p){ok(a.w<=2*R,"small competitor cap");counts.interrupted++}else counts.fullLow++;
 if(a.p>=T&&a.p<=B){counts.firstBand++;if(a.w>=a.p-2){counts.firstLongHigh++;ok(!b.p,"rough first high");seen.add(H);let d=2*t-H,post=2*(t+a.w)-(H+a.p-1),adj=post-6*a.s;ok(adj%(2*a.p)===0,"adjusted multiple");if(a.p>Math.max(9,d+1)){counts.stratumEligible++;ok(adj===2*a.p,"unit multiplier");counts.stratum1++;if(counts.examples.length<2)counts.examples.push([H0,H,t,a.p,a.w,d,post,a.s])}}}
 break}
 ok(a.p===b.p&&a.w===b.w,"low match");H+=a.p-1;t+=a.w;lowGain+=a.p-1;ok(lowGain<K,"barrier");counts.phaseMatched++;
 }
 counts.maxGain=Math.max(counts.maxGain,lowGain);counts.maxDeficit=Math.max(counts.maxDeficit,2*t-H);ok(2*t-H<=6+5*lowGain,"deficit");ok(H-H0===lowGain,"gain");
 }
 counts.distinctLongHighH=seen.size;results.push(counts);
 }
 }
 return results
}
console.log(JSON.stringify(audit(),null,2));
