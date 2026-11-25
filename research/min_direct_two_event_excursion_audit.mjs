// Actual two-event canonical returns with a long high-deficit excursion.
function audit(){
 const prime=n=>{if(n<2)return false;for(let d=2;d*d<=n;d++)if(n%d===0)return false;return true};
 const primes=n=>{let a=[];for(let p=3;p<=n;p+=2)if(prime(p))a.push(p);return a};
 const mod=(a,b)=>(a%b+b)%b;
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a<0n?-a:a};
 function merge(M,Q,l,a){let L=BigInt(l),A=BigInt(a);while(mod(M,L)!==A)M+=Q;return [M,Q*L]}
 function fixedResidue(r){let M=1n,Q=2n;for(let [p,a] of [[3,2],[5,4],[7,3],[11,4],[13,0],[17,0],[19,0],[r,r-3]])[M,Q]=merge(M,Q,p,mod(a*((p+1)/2),p));return [M,Q]}
 function run(M,r){let H=2n*M-2n,t=M+2n,ev=[],peak=6n,high=0,first=null,ticks=0;
  for(let j=1;j<=(r+5)/2;j++){if(2n*t-H>=BigInt(Math.ceil(r/2)))high++;
   let n=++t,e=n%2n?-1n:1n,g=gcd(e===1n?n:n-2n,H-e),p=0;
   if(g!==1n){if(g!==7n&&g!==BigInt(r))throw Error("unexpected gcd "+g);p=Number(g);if(g*g>H+1n)throw Error("eligibility");H+=g-1n;ev.push({j,p,d:(2n*t-H).toString()})}
   peak=peak>2n*t-H?peak:2n*t-H;ticks++;
   if(H%4n===0n&&2n*t-H===6n&&first===null)first=j;
  }
  if(JSON.stringify(ev)!==JSON.stringify([{j:7,p:7,d:"14"},{j:(r-1)/2,p:r,d:"0"}])||first!==(r+5)/2||peak!==BigInt(r-3)||high!==(r-3)/4||H!==2n*M+BigInt(r+3)|| (H+1n)%11n||121n>H+1n)throw Error("word");
  return {ticks,high,peak:peak.toString(),first,ev}
 }
 let rs=[];for(let r=223;rs.length<6;r+=220)if(prime(r))rs.push(r);
 let s={rs,crtCases:0,crtResidueChecks:0,literalTicks:0,intervalCandidates:0,intervalSurvivors:0,intervalLiteralCases:0,bonferroniChecks:0,examples:[]};
 for(let r of rs){let [M0,Q0]=fixedResidue(r),M=M0,Q=Q0,ps=primes(r-1).filter(p=>p>21);
  for(let p of ps){let a=0;while(mod(2*a+5,p)===0||mod(2*a+3,p)===0)a++;[M,Q]=merge(M,Q,p,a)}
  if(M<BigInt(r*r+100))M+=Q;
  for(let i=0;i<3;i++){let root=M+BigInt(i)*Q;for(let p of primes(r)){let x=mod(2n*root,BigInt(p));if(p<=21&&p!==7&&(x===1n||x===BigInt(3%p)))throw Error("first side");if(p<=21&&(x===BigInt(mod(-3,p))||x===BigInt(mod(-5,p))))throw Error("second side small");if(p>21&&p!==r&&(x===BigInt(p-3)||x===BigInt(p-5)))throw Error("second side");s.crtResidueChecks++}
   let v=run(root,r);s.literalTicks+=v.ticks;s.crtCases++;
   if(i===0)s.examples.push({r,rootDigits:root.toString().length,gap:v.first,peak:v.peak,high:v.high,root:root.toString().length<80?root.toString():undefined})
  }
  let start=M0+Q0*1000n,L=20000,valid=0,counts=new Array(8).fill(0);
  let small=ps.slice(0,7);
  for(let j=0;j<L;j++){
   let root=start+BigInt(j)*Q0,twice=2n*root,viol=0;
   for(let p of small){let x=Number(twice%BigInt(p));if(x===p-3||x===p-5)viol++}
   for(let k=0;k<=7;k++){if(k<=viol){let c=1;for(let i=1;i<=k;i++)c=c*(viol-i+1)/i;counts[k]+=c}}
   let ok=ps.every(p=>{let x=Number(twice%BigInt(p));return x!==p-3&&x!==p-5});
   if(ok){valid++;if(valid<=5){let v=run(root,r);s.literalTicks+=v.ticks;s.intervalLiteralCases++}}
   s.intervalCandidates++;
  }
  s.intervalSurvivors+=valid;
  // Exact finite inclusion-exclusion counts for the first seven fresh primes.
  // Compare direct counts of survivors against each partial sum.
  let good=0;for(let j=0;j<L;j++){let x=2n*(start+BigInt(j)*Q0);if(small.every(p=>x%BigInt(p)!==BigInt(p-3)&&x%BigInt(p)!==BigInt(p-5)))good++}
  let partial=0;for(let k=0;k<=7;k++){partial+=(k%2?-1:1)*counts[k];if((k%2&&partial>good)||(!(k%2)&&partial<good)||k===7&&partial!==good)throw Error("bonferroni");s.bonferroniChecks++}
 }
 return s
}
console.log(JSON.stringify(audit(),null,2));
