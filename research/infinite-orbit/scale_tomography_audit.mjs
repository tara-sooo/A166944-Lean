// Run: node research/infinite-orbit/scale_tomography_audit.mjs
function audit(){
function ok(x,m){if(!x)throw Error(m)}
const N=200000;let sieve=new Uint8Array(N+1);let primes=[];for(let i=2;i<=N;i++)if(!sieve[i]){primes.push(i);if(i*i<=N)for(let j=i*i;j<=N;j+=i)sieve[j]=1}
let qs=new Map(),bs=new Map(),last=2,idx=0;
function extend(){let b=(idx%2?-1:1)*(2*Math.floor(idx/2)+1),p=Math.max(last+1,b*b+4,5);while(p<=N&&sieve[p])p++;ok(p<=N,"prime pool");last=p;idx++;qs.set(b,p);bs.set(p,b)}
function mod(x,p){return (x%p+p)%p}
function rho(p){if(p===2)return 1;while(last<p)extend();let b=bs.get(p);return b===undefined?1:mod(-b*((p+1)/2),p)}
function fac(h){let n=Math.abs(h),a=[];for(let p of primes){if(p*p>n)break;if(n%p===0){a.push(p);while(n%p===0)n/=p}}if(n>1)a.push(n);return a}
function label(k,j,E){let h=2*j+(j%2?7:1)-E;for(let p of fac(h))if(mod(rho(p)+k+j+(j%2?2:0),p)===0)return p;return 1}
function first(k,T){for(let j=1;j<=T;j++){let p=label(k,j,0);if(p>1)return {k,j,p,r:mod(-k-j-(j%2?2:0),p)}}return null}
function gcd(a,b){while(b)[a,b]=[b,a%b];return a<0n?-a:a}
function mb(a,p){return (a%p+p)%p}
function inv(a,p){let x=0n,y=1n,b=p;while(a){let q=b/a;[b,a]=[a,b-q*a];[x,y]=[y,x-q*y]}ok(b===1n,"inverse");return mb(x,p)}
function crt(conds){let a=1n,P=2n;for(let [p,r] of conds){p=BigInt(p);a+=P*mb((BigInt(r)-a)*inv(P%p,p),p);P*=p}return [a,P]}
let firsts=new Map(),scans=[],tomo=0,exact=0;
for(let K of [64,256,1024,4096,16384]){
  for(let k=0;k<=K;k+=2){if(firsts.has(k))continue;firsts.set(k,first(k,2048))}
  let ws=new Map(),nonunit=0,maxp=0;
  for(let [k,w] of firsts){if(k>K||!w)continue;nonunit++;maxp=Math.max(maxp,w.p);ok(w.r===rho(w.p),"recovery");if(!ws.has(w.p))ws.set(w.p,w)}
  const [a,P]=crt([...ws].map(([p,w])=>[p,w.r]));let bound=a>=5n?a:a+P;let firstCandidate=bound;
  let defaultProduct=1n;for(let [p,w] of ws)if(w.r===1)defaultProduct*=BigInt(p);
  let lifted=a+P*1000000n; // selected congruences alone are not sufficient, full CRT of all tested h factors below
  let selected=[...ws.values()].sort((u,v)=>u.p-v.p);
  let cert=new Map();for(let w of selected)for(let j=1;j<=w.j;j++)for(let p of fac(2*j+(j%2?7:1)))cert.set(p,rho(p));
  let [c,Q]=crt(cert);let M=c+Q*1000000n;
  for(let w of selected){for(let j=1;j<=w.j;j++){let R=M+BigInt(w.k),n=R+2n+BigInt(j),C=2n*R-2n;let g=j%2?gcd(n,C-1n):gcd(n-2n,C+1n);let p=g===1n?1:fac(Number(g))[0];ok(p===(j===w.j?w.p:1),"literal first word");ok(p===1||BigInt(p)**2n<=C+1n,"eligibility");exact++}}
  let m=BigInt(K);let count=a>=m?a:a+P*((m-a+P-1n)/P);let bounded=count<=2n*m?1n+(2n*m-count)/P:0n;
  scans.push({K,roots:K/2+1,observed:nonunit,distinct:ws.size,maxp,positiveCRTmodulusDigits:String(P).length,leastPositiveRoot:String(firstCandidate),defaultProduct:String(defaultProduct),boundedCandidates:String(bounded),witnesses:K===64?selected:undefined,fullLiftDigits:String(M).length});
}
// targeted tomography: choose p and a root residue guaranteeing one side, exclude both sides for others
for(let p of primes.filter(p=>p>=3&&p<=127)){
 let cond=new Map(), T=2*p;
 for(let q of primes){if(q>4*p+7)break;if(q===2)continue;let target;
 if(q===p)target=mod((q+1)/2,q); // 2R=1 mod p: C+1=2R-1
 else{for(let a=0;a<q;a++)if(mod(2*a-3,q)!==0&&mod(2*a-1,q)!==0){target=a;break}}
 ok(target!==undefined,"avoid residues");cond.set(q,mod(target-rho(q),q))}
 // solve offset even, not odd: CRT helper starts residue 1, shift by odd modulus if needed
 let [k,P]=crt(cond); // odd k, parity flip via subtract 1 then use a separate CRT below
 let oddProduct=P/2n;k+=oddProduct;ok(k%2n===0n,"even offset");
 let got=0;
 for(let j=1;j<=T;j++){let h=2*j+(j%2?7:1);let a=1;for(let q of fac(h))if(mb(BigInt(rho(q)+j+(j%2?2:0))+k,BigInt(q))===0n){a=q;break}if(a!==1){got=a;break}}
 ok(got===p,"tomography");tomo++;
}
return {scans,tomo,exact}
}
console.log(JSON.stringify(audit(),null,2));
