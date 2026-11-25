function audit(){
 const mod=(x,p)=>(x%p+p)%p, abs=x=>x<0n?-x:x;
 function gcd(a,b){a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a}
 function inv(a,p){let x=0n,y=1n,b=p;while(a){let q=b/a;[b,a]=[a,b%a];[x,y]=[y,x-q*y]}if(b!==1n)throw Error("inverse");return mod(x,p)}
 function add(c,m,r,p){let k=mod((r-c)*inv(mod(m,p),p),p);return [c+m*k,m*p]}
 function primes(B){let a=new Uint8Array(B+1);let out=[];for(let i=2;i<=B;i++)if(!a[i]){out.push(i);if(i*i<=B)for(let j=i*i;j<=B;j+=i)a[j]=1}return out}
 function minfac(g){if(g===1n)return 1n;for(let p=3n;p*p<=g;p+=2n)if(g%p===0n)return p;return g}
 function isPrime(x){if(x===2n)return true;return x>2n&&x%2n===1n&&minfac(x)===x}
 function plan(ps){let E=[0n],ticks=[],t=0n;for(let i=0;i<ps.length;i++){let p=ps[i];if(p%4n!==1n||p<13n)throw Error("label");t+=(p-(i===0?7n:1n))/2n;ticks.push(t);E.push(E.at(-1)+p-1n)}return {E,ticks,t}}
 function trace(M,T,cap=false){let C=2n*M-2n, t=M+2n,events=[];for(let j=1n;j<=T;j++){let n=t+j,g=n%2n===0n?gcd(n,C-1n):gcd(n-2n,C+1n),p=minfac(g);if(cap&&p*p>C+1n)p=1n;if(p>1n){C+=p-1n;events.push([j,p,2n*n-C])}}return {C,events}}
 function exact(ps,L){let {E,ticks,t}=plan(ps);let T=t+BigInt(L);let constraints=new Map();for(let j=1n,i=0;j<=T;j++){let p=i<ticks.length&&j===ticks[i]?ps[i]:1n;let h=abs(2n*j+(j%2n===1n?7n:1n)-E[i]);for(let q of primes(Number(h)).filter(q=>q%2===1&&h%BigInt(q)===0n)){let qb=BigInt(q);if(p!==1n&&qb>p)continue;let r=mod(-j-(j%2n===1n?2n:0n),qb);if(!constraints.has(q))constraints.set(q,new Set(Array.from({length:q},(_,a)=>a)));let s=constraints.get(q);if(qb===p){for(let a of s)if(a!==Number(r))s.delete(a)}else s.delete(Number(r));}if(p!==1n)i++}return constraints}
 const stringify=o=>JSON.stringify(o,(_,v)=>typeof v==="bigint"?v.toString():v);
 function run(ps,L){let {E,ticks,t}=plan(ps),T=t+BigInt(L),B=Number(2n*T+7n);
 let [C,P]=[0n,4n];let selected=new Map(ps.map((p,i)=>[Number(p),mod(1n-E[i],p)]));
 for(let q of primes(B).filter(x=>x>2)){let p=BigInt(q),r=selected.get(q);let ok=a=>mod(a+2n,p)!==0n&&E.every((e,i)=>selected.has(q)&&ps[i]===p?mod(a+e,p)===1n:mod(a+e-1n,p)!==0n&&mod(a+e+1n,p)!==0n);if(r===undefined){r=0n;while(r<p&&!ok(r))r++}if(r>=p||!ok(r))throw Error("no residue q="+q);[C,P]=add(C,P,r,p)}
 let M=(C+P)/2n+1n;let a=trace(M,T),b=trace(M,T,true);let expected=ps.map((p,i)=>[ticks[i],p,0n]);if(stringify(a.events)!==stringify(expected)||stringify(b)!==stringify(a))throw Error("CRT trace");
 let cert=[];let c=C,m=P;let fresh=primes(B+1000).filter(q=>q>B);for(let i=0;i<E.length;i++)for(let s of [-1n,1n]){let p=BigInt(fresh[cert.length]);if(!p)throw Error("fresh");[c,m]=add(c,m,mod(-E[i]-s,p),p);cert.push([i,s,p])}let lifted=(c+m)/2n+1n;let liftedTrace=trace(lifted,T,true);if(stringify(liftedTrace.events)!==stringify(expected)||!cert.every(([i,s,p])=>{let x=2n*lifted-2n+E[i]+s;return x>p&&x%p===0n}))throw Error("composite lift");
 let [r,D]=[1n,2n];for(let [i,p] of ps.entries())[r,D]=add(r,D,mod((1n-E[i]+2n)*inv(2n,p),p),p);
 let small=null,first=null,scanned=0;let H=10000000n;let S=exact(ps,L);let matching=0,smallCertificates=0;for(let m=r===1n?r+D:r;m<=H;m+=D){scanned++;let tr=trace(m,t,true);if(stringify(tr.events)!==stringify(expected))continue;if(first===null)first=m;if(isPrime(tr.C-1n)&&isPrime(tr.C+1n)&&small===null)small={M:m,C:tr.C,primeRoot:isPrime(m)};if([...S].every(([q,allowed])=>allowed.has(Number(m%BigInt(q))))){matching++;if(tr.C+1n<BigInt(Math.floor(L/2)+1)**2n)smallCertificates++;}}
 return {ps,ticks,t,L,B,E,CRTrootDigits:String(M).length,compositeLiftDigits:String(lifted).length,selectedResidue:r,selectedModulus:D,scanned,firstMatchingPrefix:first,matchingFullWord:matching,smallCertificates,firstTwin:small,cert};}
 function resetAudit(maxC){let checked=0,phaseChecks=0,semiprimeCases=0,bothComposite=0,maxRatio=0,example=null;let primePool=primes(Math.floor(Math.sqrt(maxC+1)));let factor=z=>{let a=[];for(let p of primePool){if(p*p>z)break;while(z%p===0){a.push(p);z/=p}}if(z>1)a.push(z);return a};for(let C=12;C<=maxC;C+=4){let B=Math.floor(Math.sqrt(C+1)),t=C/2,lists=[factor(C-1),factor(C+1)],first=Infinity;for(let side=0;side<2;side++)for(let p of new Set(lists[side]))if(p<=B){let m=2*p,target=side?p+2:0;let w=((target-t)%m+m)%m||m;let f=(p%4===1?(p+(side?5:-1))/2:(3*p+(side?5:-1))/2);f=(f-1)%m+1;if(w!==f)throw Error("phase formula");phaseChecks++;first=Math.min(first,w);}
 let L=first===Infinity?Math.ceil((3*B+5)/2):first-1;if(L>=Math.floor((3*B+5)/2)&&lists.some(a=>a.length>1))throw Error("reset quiet certificate");if(2*L-5>=B&&((2*L-5)/3)**3>C+1){checked++;for(let side=0;side<2;side++){let a=lists[side];if(a.length>1){semiprimeCases++;if(a.length!==2||a[0]%4!==3||3*a[0]<=2*L-5||a[1]%4!==(side?3:1)||(!side&&a[1]<=B))throw Error("semiprime criterion")}}if(lists.every(a=>a.length===2)){bothComposite++;let ratio=L/Math.sqrt(C+1);if(ratio>maxRatio){maxRatio=ratio;example={C,L,factors:lists,first,ratio}}}}
 }return {maxC,phaseChecks,checked,semiprimeCases,bothComposite,example}}
 let results=[run([13n],200),run([13n,37n],200),run([13n,37n,73n],200)];return JSON.parse(stringify({results,reset:resetAudit(200000)}));
}

console.log(JSON.stringify(audit(),null,2));
