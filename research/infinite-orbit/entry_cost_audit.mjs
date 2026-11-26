// Run: node research/infinite-orbit/entry_cost_audit.mjs
function audit(){
 const max=16*262144+4096,spf=new Int32Array(max+1);for(let p=2;p*p<=max;p++)if(!spf[p])for(let n=p*p;n<=max;n+=p)if(!spf[n])spf[n]=p;
 const prime=n=>n>=2&&!spf[n];
 function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function elig(H){let B=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=B),fac(H+1).filter(p=>p<=B)]}
 function mod(x,p){return (x%p+p)%p}
 function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let z=1+mod((i?q+2:0)-t-1,2*q);if(z<w||(z===w&&q<p)){p=q;w=z;s=i}}return {p,w,s}}
 function ok(x,m){if(!x)throw Error(m)}
 function gcd(a,b){while(b)[a,b]=[b,a%b];return a}
 function literal(H,t){let B=Math.floor(Math.sqrt(H+1));for(let w=1;w<=2*B;w++){let n=t+w,g=gcd(n%2?n-2:n,n%2?H+1:H-1),p=fac(g).find(q=>q<=B);if(p)return {p,w,s:n%2}}return {p:0,w:Infinity,s:0}}
 let results=[],localChecks=0,entryChecks=0,wordChecks=0;
 for(let X of [4096,16384,65536,262144]){
 let Y=16*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(X)),K=210,V=12,safe=H=>Math.min(H%K,K-H%K)>V;
 const good=(H,p,w)=>p>=T&&p<=B&&w>=p-2&&safe(H)&&safe(H+p-1);
 let canonical={roots:0,primeRoots:0,events:0,stop:0,primeStops:0,found:0,primeFound:0,applicable:0,unit:0,thresholds:[8,32,128,512].map(D=>({D,all:0,prime:0,stopped:0,primeStopped:0,allBeyond:0,primeBeyond:0})),example:null};
 for(let H0=X;H0<4*X;H0+=4){
 let M=(H0+2)/2,pr=prime(M),H=H0,t=(H0+6)/2,kind="beyond",E=0;
 canonical.roots++;if(pr)canonical.primeRoots++;
 while(H-H0<512){let a=first(t,elig(H));if(!a.p){kind="stop";canonical.stop++;if(pr)canonical.primeStops++;break}
 canonical.events++;E=H-H0;
 if(a.p>=T&&a.p<=B&&a.w>=a.p-2){kind="good";canonical.found++;if(pr)canonical.primeFound++;let d=2*t-H;
 ok(d>=0&&d<=6+5*E,"canonical prefix deficit");
 if(a.p>Math.max(9,d+1)){canonical.applicable++;let post=2*(t+a.w)-(H+a.p-1);ok(post===2*a.p+6*a.s,"unit entry");canonical.unit++;if(pr&&!canonical.example)canonical.example={M,H0,H,t,p:a.p,w:a.w,E,d,post,s:a.s}}
 break}
 H+=a.p-1;t+=a.w;
 }
 E=H-H0;
 for(let z of canonical.thresholds){if(E<z.D&&kind==="good"){z.all++;if(pr)z.prime++}else if(E<z.D&&kind==="stop"){z.stopped++;if(pr)z.primeStopped++}else{z.allBeyond++;if(pr)z.primeBeyond++}}
 }
 let unitRuns=[3,7,11].map(R=>({R,starts:0,maxSpan:0,maxHigh:0,maxHighExample:null,maxGainExample:null,high2:0,high3:0,high4:0,lowEvents:0,fullWords:0}));
 for(let H=X;H<Y;H+=2){if(!safe(H))continue;let f=elig(H);
 for(let s=0;s<2;s++)for(let p of f[s]){
 if(p<T||p>B||p<=9||!safe(H+p-1))continue;
 let H2=H+p-1,n=(H2+2*p+6*s)/2;localChecks++;
 if(n%2!==s||mod(n-(s?p+2:0),2*p)!==0)continue;
 let lo=Math.max(p-2,Math.ceil((3*p-1+6*s-(p-2))/2),n-(3*H+3)),hi=Math.min(2*p,Math.floor((3*p-1+6*s)/2),n-H/2);
 for(let i=0;i<2;i++)for(let q of f[i]){if(q===p)continue;let a=mod(n-(i?q+2:0),2*q);if(!a&&q<p)hi=-1;else hi=Math.min(hi,a||2*q)}
 if(lo>hi)continue;
 let t=n-lo,a=first(t,f),d=2*t-H;ok(a.p===p&&a.w===lo&&p>Math.max(9,d+1)&&d>=0,"unit state");entryChecks++;
 for(let z of unitRuns){let h=H2,tt=n,count=1,last=h,steps=[[H,t,p,lo]],best=steps.slice();z.starts++;
 while(h<Y){let b=first(tt,elig(h));if(!b.p)break;
 if(b.p<=z.R){z.lowEvents++;steps.push([h,tt,b.p,b.w]);h+=b.p-1;tt+=b.w;continue}
 if(!good(h,b.p,b.w))break;
 steps.push([h,tt,b.p,b.w]);h+=b.p-1;tt+=b.w;last=h;count++;best=steps.slice();
 }
 if(count>=2)z.high2++;if(count>=3)z.high3++;if(count>=4)z.high4++;
 if(last-H>z.maxSpan){z.maxSpan=last-H;z.maxGainExample=best}
 if(count>z.maxHigh){z.maxHigh=count;z.maxHighExample=best}
 }
 }
 }
 for(let z of unitRuns){for(let w of [z.maxGainExample,z.maxHighExample])if(w)for(let [h,t,p,v] of w){let a=literal(h,t);ok(a.p===p&&a.w===v,"literal word");wordChecks++}}
 results.push({X,T,B,canonical,unitRuns});
 }
 return {localChecks,entryChecks,wordChecks,results}
}
console.log(JSON.stringify(audit(),null,2));
