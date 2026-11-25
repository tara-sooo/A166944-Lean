function audit(N=1000000){
 const max=2*N+10000, spf=new Int32Array(max+1);for(let i=2;i<=max;i++)if(!spf[i]){spf[i]=i;if(i*i<=max)for(let j=i*i;j<=max;j+=i)if(!spf[j])spf[j]=i}
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a};
 const factors=z=>{let a=[];while(z>1){let p=spf[z];if(!p)throw Error("factor range");a.push(p);z/=p}return a};
 const prime=z=>z>1&&spf[z]===z;
 function next(t,C){let b=Math.floor(Math.sqrt(C+1)),best=null;for(let s of [-1,1])for(let p of new Set(factors(C+s))){if(p>b)continue;let r=s===-1?0:p+2,w=((r-t)%(2*p)+2*p)%(2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={w,p,s}}return best}
 function literal(t,C,T){for(let w=1;w<=T;w++){let n=t+w,s=n%2?1:-1,g=gcd(n%2?n-2:n,C+s);if(g>1){let p=spf[g];if(p*p<=C+1)return {w,p,s}}}return null}
 const stat={roots:0,primeRoots:0,resets:0,primeReset:0,balance:0,cofactorChecks:0,near:0,twinLabels:0,terminalTwinNear:0,nearPlusBlocked:0,nearMinusBlocked:0,nearBothComposite:0,semiprime:0,bothSemi:0,primeBothSemi:0,balancedBothSemi:0,primeBalancedBothSemi:0,closeSemiprime:0,actualBest:null,bestBalanced:null,bestPrimeBalanced:null,examples:[],nearExamples:[],nearSquareChecks:0,nearSquareFactorChecks:0,nearSquareBothSemi:0,nearSquareBest:null,formulaChecks:0,literalChecks:0,gapMin:null,gapHistogram:{},primeRootNear:0};
 const same=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
 for(let M=7;M<=N;M+=2){stat.roots++;if(prime(M))stat.primeRoots++;let C=2*M-2,t=M+2,e=next(t,C);if(M<=10000){if(!same(e,literal(t,C,2*Math.floor(Math.sqrt(C+1)))))throw Error("literal first");stat.literalChecks++}if(!e)continue;let Z=C+e.p-1,n=t+e.w;if(2*n!==Z||n%2||e.s!==-1)continue;stat.resets++;if(prime(M))stat.primeReset++;let p=e.p,m=Z/p,d=m-p,v=m-1;if(!Number.isInteger(m)||m%4||p%4!==1||p<13)throw Error("reset geometry");
 if(2*Math.floor(Math.sqrt(v))<=e.w&&Math.sqrt(v)<p){stat.cofactorChecks++;if(!prime(v))throw Error("generic cofactor theorem")}
 if(p>=37&&9*v<p*p){stat.balance++;if(!prime(v))throw Error("strong cofactor")}
 if(d===3){stat.near++;if(!prime(p+2))throw Error("near twin");if(prime(M))stat.primeRootNear++;if(prime(Z-1)&&prime(Z+1))stat.terminalTwinNear++;if(!prime(Z-1)&&!prime(Z+1))stat.nearBothComposite++;if(next(n,Z)?.p!==3||next(n,Z)?.w!==4)throw Error("forced p3");stat.nearExamples.push({M,primeRoot:prime(M),p,m,Z,w:e.w,next:next(n,Z),factors:[factors(Z-1),factors(Z+1)]})}
 let f=next(n,Z);if(M<=10000){if(!same(f,literal(n,Z,2*Math.floor(Math.sqrt(Z+1)))))throw Error("literal reset");stat.literalChecks++}
 let b=Math.floor(Math.sqrt(Z+1)),L=f?f.w-1:Infinity;
 if(L>=5&&p>=37&&9*v<p*p){if(Z%3||m%3)throw Error("mod3");let g=v-p,low=p%3===2?6:10;if(g<low||g%4!==2)throw Error("gap");stat.gapMin=stat.gapMin===null?g:Math.min(stat.gapMin,g);if(g<=50)stat.gapHistogram[g]=(stat.gapHistogram[g]||0)+1;}
 const A=p+m, nearSquare=d*d+5<2*A, h=(A+1)/2;
 if(nearSquare){stat.nearSquareChecks++;if(!((h-1)**2<Z-1&&Z+1<h*h))throw Error("adjacent squares");let bound=h-Math.ceil(Math.sqrt(h*h-(Z+1)));if(f&&f.w>Math.floor((3*bound+5)/2))throw Error("improved certificate");for(let s of [-1,1]){let a=factors(Z+s);if(a.length>1){stat.nearSquareFactorChecks++;if(a[0]>bound)throw Error("fermat bound")}}}
 if(!f)continue;
 for(let s of [-1,1])for(let r of new Set(factors(Z+s))){let u=r-p,H=u*(u-d)+s;if(H%r!==0||H===0||Math.abs(H)<r)throw Error("factor congruence");stat.formulaChecks++}
 if(2*L-5>=b&&((2*L-5)/3)**3>Z+1){stat.semiprime++;let a=factors(Z-1),c=factors(Z+1);if(a.length===2&&c.length===2){stat.bothSemi++;if(prime(M))stat.primeBothSemi++;let rec={M,primeRoot:prime(M),p,m,d,Z,L,ratio:L/Math.sqrt(Z+1),factors:[a,c],first:e,next:f};if(!stat.actualBest||rec.ratio>stat.actualBest.ratio)stat.actualBest=rec;if(m<=4*p&&p>=37&&9*v<p*p){stat.balancedBothSemi++;if(!stat.bestBalanced||rec.ratio>stat.bestBalanced.ratio)stat.bestBalanced=rec;if(prime(M)){stat.primeBalancedBothSemi++;if(!stat.bestPrimeBalanced||rec.ratio>stat.bestPrimeBalanced.ratio)stat.bestPrimeBalanced=rec}}if(d<=15)stat.closeSemiprime++;if(nearSquare){stat.nearSquareBothSemi++;if(!stat.nearSquareBest||rec.ratio>stat.nearSquareBest.ratio)stat.nearSquareBest=rec}if(stat.examples.length<5)stat.examples.push(rec)}}
 }
 for(let p=13;p*p+2*p+3<=2*N;p+=4)if(prime(p)){let M=(p*(p+2)+3)/2;let e=next(M+2,2*M-2);if(prime(p+2)){stat.twinLabels++;if(e?.p!==p)stat.nearPlusBlocked++;if(p>=37){let z=p*(p+2)+2,a=factors(z),r=a[0];let expected=a.length===1||a.length===2&&a.every(q=>q%4===3)&&3*r>p-6;if((e?.p===p)!==expected)throw Error("exact near-twin competition");}}else {stat.nearMinusBlocked++;if(e?.p===p)throw Error("near non-twin won")}}
 return stat
}

console.log(JSON.stringify(audit(Number(process.argv[2] || 1000000)),null,2));
