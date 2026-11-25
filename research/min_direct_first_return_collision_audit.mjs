// Exact short-return collision density and simultaneous one-event stars.
function audit(){
 const gcd=(a,b)=>{b=Math.abs(b);while(b)[a,b]=[b,a%b];return Math.abs(a)},mod=(a,b)=>(a%b+b)%b;
 const isPrime=n=>{if(n<2)return false;for(let d=2;d*d<=n;d++)if(n%d===0)return false;return true};
 const primes=n=>{let a=[];for(let p=3;p<=n;p+=2)if(isPrime(p))a.push(p);return a};
 const minfac=n=>{if(n===1)return 0;for(let d=3;d*d<=n;d+=2)if(n%d===0)return d;return n};
 let s={periods:[],stars:[],literalChecks:0,crtResidueChecks:0};
 for(let T of [2,4,6]){
  let ps=primes(2*T+7),P=ps.reduce((a,p)=>a*p,1),indeg=new Uint8Array(P),edges=0;
  for(let i=0;i<P;i++){let M=2*P+1+2*i,E=0;for(let j=1;j<=T;j++){let g=j%2?gcd(M+j+2,2*j+7-E):gcd(M+j,2*j+1-E),p=minfac(g);if(p)E+=p-1;if(j%2===0&&E===2*j){indeg[(i+j/2)%P]++;edges++;break}}}
  let hist={},C=0,S=0,max=0;for(let d of indeg){hist[d]=(hist[d]||0)+1;if(!d)S++;else C+=d-1;max=Math.max(max,d)}
  if(S!==C+P-edges)throw Error("balance");
  s.periods.push({T,P,edges,hist,collisionExcess:C,excessDensity:C/P,max});
 }
 function star(ps){
  let B=ps.at(-1)+6,ls=primes(B),target=[],period=2n,M=1n,allowedCount=1n;
  for(let l of ls){let allowed=[];for(let r=0;r<l;r++){
   if(ps.includes(l)&&r!==0)continue;
   if(ps.some(p=>mod(2*r-p-2,l)===0||p!==l&&mod(2*r-p,l)===0))continue;
   allowed.push(r);
  }if(!allowed.length)throw Error("empty CRT "+l+" "+ps);
   let f=BigInt(l),r=BigInt(allowed[0]);while(M%f!==r)M+=period;period*=f;allowedCount*=BigInt(allowed.length);
   target.push({l,count:allowed.length,residue:allowed[0]});
  }
  let extra=B+1;while(!isPrime(extra))extra++;
  let ex=BigInt(extra),r=(ex+1n)/2n;while(M%ex!==r)M+=period;period*=ex;
  let threshold=BigInt((B+extra+10)**2);if(M<threshold)M+=period*((threshold-M+period-1n)/period);
  for(let p of ps){let k=(p-1)/2,root=M-BigInt(k),H=2n*root-2n;
   for(let {l,residue} of target){let L=BigInt(l);if(M%L!==BigInt(residue)|| (H-1n)%L===0n || (H+1n)%L===0n&&l!==p)throw Error("root exclusions");s.crtResidueChecks++}
   for(let j=1;j<=k;j++){let n=root+2n+BigInt(j),e=n%2n?-1n:1n,A=e===1n?n:n-2n,D=H-e;while(D)[A,D]=[D,A%D];if(j<k&&A!==1n||j===k&&A!==BigInt(p))throw Error("literal");
    if(j===k)H+=BigInt(p-1);s.literalChecks++;
   }if(H!==2n*M-2n||root+2n+BigInt(k)!==M+2n)throw Error("return");
  }
  if((2n*M-1n)%ex||ex*ex>2n*M-1n)throw Error("target active");
  s.stars.push({ps,B,extra,target:M.toString(),period:period.toString(),allowedResidueCount:allowedCount.toString(),roots:ps.map(p=>(M-BigInt((p-1)/2)).toString())});
 }
 for(let ps of [[13,61],[61,241,421],[61,241,421,601]])star(ps);
 return s;
}
console.log(JSON.stringify(audit(),null,2));
