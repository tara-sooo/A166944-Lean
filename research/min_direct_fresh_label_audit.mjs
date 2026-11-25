function audit(){
 const gcd=(a,b)=>{a=a<0n?-a:a;b=b<0n?-b:b;while(b)[a,b]=[b,a%b];return a},mod=(a,b)=>(a%b+b)%b,md=(a,b)=>(a%b+b)%b;
 function fac(n){let a=[];n=n<0n?-n:n;for(let p=3n;p*p<=n;p+=2n)if(n%p===0n){a.push(p);while(n%p===0n)n/=p}if(n>1n)a.push(n);return a}
 function primes(B){let a=[];for(let p=3;p<=B;p+=2)if(a.every(q=>q*q>p||p%q))a.push(p);return a}
 function tr(M,T,adaptive=false){let C=2n*M-2n,E=0n,word=[];for(let j=1;j<=T;j++){let n=M+2n+BigInt(j),g=gcd(n%2n===0n?n:n-2n,C+(n%2n===0n?-1n:1n)),p=fac(g)[0]??1n;if(adaptive&&p*p>C+1n)p=1n;word.push(Number(p));if(p>1n){E+=p-1n;C+=p-1n}}return {word,E:Number(E),C}}
 function cyl(word,primeRoot=false){let T=word.length,B=2*T+7,S=new Map(primes(B).map(q=>[q,new Set(Array.from({length:q},(_,i)=>i).filter(i=>!primeRoot||i))])),E=0;
 for(let j=1;j<=T;j++){let p=word[j-1],h=BigInt(2*j+(j%2?7:1)-E),fs=fac(h).map(Number);if(p!==1&&!fs.includes(p))return {invalid:true};for(let q of fs){if(p!==1&&q>p)continue;let r=md(-j-(j%2?2:0),q),A=S.get(q);if(q===p){for(let a of A)if(a!==r)A.delete(a)}else A.delete(r)}if(p>1)E+=p-1}
 return classify(T,B,E,S)}
 function classify(T,B,E,S){let dead=[],forced=[],free=new Map();for(let [q,A] of S){if(!A.size)dead.push(q);let Z=[...A].filter(a=>{let r=md(2*a-2+E,q);return r!==1&&r!==q-1});if(!Z.length)forced.push(q);else free.set(q,Z)}return {T,B,E,S,dead,forced,free}}
 // Event-list implementation independent of tickwise gcd factorization.
 function compressed(word,primeRoot=false,full=false){
 let T=word.length,events=[];for(let j=1;j<=T;j++)if(word[j-1]>1)events.push([j,word[j-1]]);
 let N=events.length,labels=new Set(events.map(x=>x[1])),B=2*T+7,qs=full?primes(B):[...new Set([...labels,...primes(2*N+(primeRoot?3:2))])].sort((a,b)=>a-b),S=new Map();
 const hit=(lo,hi,res,par,q)=>{if(hi<lo)return false;let b=md(res,q);if(b%2!==par)b+=q;return lo+md(b-lo,2*q)<=hi};
 for(let q of qs){
 let A=new Set(Array.from({length:q},(_,i)=>i).filter(i=>!primeRoot||i)),E=0,a=0;
 for(let [b,p] of [...events,[T+1,0]]){
  for(let e of [-1,1]){
   let c=md((2-E+e)*((q+1)/2),q),r=-c-(e===1?2:0),par=e===1?1:0;
   if(hit(a+1,b-1,r,par,q)||(p>q&&hit(b,b,r,par,q)))A.delete(c);
  }
  if(p===q){let c=md((2-E+(b%2?1:-1))*((q+1)/2),q),r=-c-(b%2?2:0);if(!hit(b,b,r,b%2,q))A.clear();else for(let v of A)if(v!==c)A.delete(v)}
  if(p){a=b;E+=p-1}
 }
 S.set(q,A);
 }
 let E=events.reduce((s,e)=>s+e[1]-1,0);return {...classify(T,B,E,S),N,labels}
 }
 function inv(a,p){let x=0n,y=1n,b=p;while(a){let q=b/a;[b,a]=[a,b%a];[x,y]=[y,x-q*y]}if(b!==1n)throw Error("inverse");return mod(x,p)}
 function add(a,m,r,p){return [a+m*mod((r-a)*inv(mod(m,p),p),p),m*p]}
 let stats={cylinders:0,exactMembership:0,forcedChecks:0,free:0,forced:0,primeFree:0,primeForced:0,primeDead:0,compressedChecks:0,fullResidueChecks:0,omittedPrimeChecks:0,arbitrarySchedules:0,arbitraryFeasible:0,arbitraryPrimeFeasible:0,examples:{},construct:[],maxCertificate:null,primeOnly:null},seen=new Set();
 function check(word,fromActual){
 for(let primeRoot of [false,true]){
 let c=compressed(word,primeRoot),d=compressed(word,primeRoot,true),v=cyl(word,primeRoot);
 if(!v.invalid){for(let [q,A] of d.S){let Z=v.S.get(q);if(A.size!==Z.size||[...A].some(a=>!Z.has(a)))throw Error("plateau exact residue");stats.fullResidueChecks++}}
 if(v.invalid&&!c.dead.length)throw Error("invalid selected event");
 if(!!c.dead.length!==!!d.dead.length||!c.dead.length&&!!c.forced.length!==!!d.forced.length)throw Error("compressed decision");
 for(let [q,A] of d.S)if(!c.S.has(q)){if(!A.size||d.forced.includes(q))throw Error("omitted prime");stats.omittedPrimeChecks++}
 stats.compressedChecks++;
 if(!fromActual&&!c.dead.length)stats[primeRoot?"arbitraryPrimeFeasible":"arbitraryFeasible"]++;
 }
 }
 for(let M=5;M<=151;M+=2)for(let T=0;T<=24;T++){let {word}=tr(BigInt(M),T),key=word.join(",");if(seen.has(key))continue;seen.add(key);let c=cyl(word),d=cyl(word,true);if(c.dead.length)throw Error("realized impossible");stats.cylinders++;stats[c.forced.length?"forced":"free"]++;stats[d.dead.length?"primeDead":d.forced.length?"primeForced":"primeFree"]++;check(word,true);
 if(c.forced.length&&!stats.examples.forced)stats.examples.forced={M,T,word,E:c.E,forced:c.forced};if(!c.forced.length&&T>5&&word.filter(p=>p>1).length>=2&&!d.dead.length&&!d.forced.length&&!stats.examples.free)stats.examples.free={M,T,word,E:c.E};if(!c.forced.length&&!d.dead.length&&d.forced.length&&!stats.primeOnly)stats.primeOnly={M,T,word,E:c.E,forced:d.forced};
 for(let R=5;R<=105;R+=2){let yes=[...c.S].every(([q,A])=>A.has(R%q)),v=tr(BigInt(R),T);if(yes!==(v.word.join(",")===key))throw Error("membership");stats.exactMembership++;if(yes&&c.forced.length){let q=Math.min(...c.forced),v2=tr(BigInt(R),T+2*q),p=v2.word.slice(T).find(a=>a>1);if(!p||p>2*(T+2*q)+7)throw Error("forced bound");stats.forcedChecks++}}
 }
 // Exhaustive candidate words, not just realized ones, with 0/1/2 selected events.
 for(let T=1;T<=12;T++){let labels=primes(2*T+7);for(let i=1;i<=T;i++)for(let p of labels){let w=Array(T).fill(1);w[i-1]=p;check(w,false);stats.arbitrarySchedules++;for(let j=i+1;j<=T;j++)for(let q of labels.filter(q=>q<=7)){let v=w.slice();v[j-1]=q;check(v,false);stats.arbitrarySchedules++}}}
 let ex=stats.examples.free;
 for(let ex2 of [{M:5,T:0,word:[],E:0},ex])for(let p of [53,101,257])for(let side of [-1,1]){let c=compressed(ex2.word,true,true);if(p<=c.B||c.forced.length||c.dead.length)continue;let k=p%4===md(1-c.E,4)?1:3,j=(k*p+c.E-(side===1?7:1))/2;if(!Number.isInteger(j)||j<=c.T||j>c.T+2*p)throw Error("tick formula");let [a,m]=[1n,2n];for(let q of primes(2*j+7)){let A=c.S.get(q)??new Set(Array.from({length:q},(_,i)=>i).filter(i=>i));let v=[...A].find(x=>{let r=md(2*x-2+c.E,q);return q===p?r===(side===1?1:q-1):r!==1&&r!==q-1});if(v===undefined)throw Error("CRT option");[a,m]=add(a,m,BigInt(v),BigInt(q))}
 let R=a+m;if(2n*R-1n<BigInt(2*j+7)**2n)R+=m*BigInt(2*j+7)**2n;let v=tr(R,j,true),expect=[...ex2.word,...Array(j-c.T-1).fill(1),p];if(v.word.join(",")!==expect.join(","))throw Error("escape witness");if(gcd(a,m)!==1n)throw Error("reduced");stats.construct.push({T:c.T,E:c.E,p,side,j,rootDigits:String(R).length,reduced:true});}
 return stats
}

console.log(JSON.stringify(audit(),null,2));
