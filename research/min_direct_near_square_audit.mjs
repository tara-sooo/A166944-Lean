function audit(P=12000){
 const maxN=2*P*P+100;
 if(!Number.isSafeInteger(maxN)||P<53||P>100000)throw Error("unsupported bound");
 const limit=Math.ceil(Math.sqrt(maxN))+5, sp=new Uint8Array(limit+1), primes=[];
 for(let i=2;i<=limit;i++)if(!sp[i]){primes.push(i);if(i*i<=limit)for(let j=i*i;j<=limit;j+=i)sp[j]=1}
 function fac(n){let a=[];for(let p of primes){if(p*p>n)break;while(n%p===0){a.push(p);n/=p}}if(n>1)a.push(n);return a}
 const isPrime=n=>n>=2&&(n<=limit?!sp[n]:fac(n).length===1);
 const pos=(x,m)=>(x%m+m-1)%m+1;
 function next(t,C){let best=null;const b=Math.floor(Math.sqrt(C+1));for(let side=0;side<2;side++)for(let p of new Set(fac(C+(side?1:-1))))if(p<=b){let w=pos((side?p+2:0)-t,2*p);if(!best||w<best.w||w===best.w&&p<best.p)best={w,p,side}}return best}
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a};
 function literal(t,C,T){for(let j=1;j<=T;j++){let n=t+j,g=gcd(n%2?n-2:n,C+(n%2?1:-1));let p=g>1?fac(g)[0]:1;if(p>1&&p*p<=C+1)return {w:j,p,side:n%2}}return null}
 let tightTests=0,tightHits=[],nearTests=0,nearWins=0,thinTests=0,thinWins=0,semis=0,both=0,firstBoth=null,firstOne=null,largest=null,firstThin=null,firstThinBoth=null,mod3Tests=0,literalTests=0,sharpTests=0,priorThinTests=0,priorThinComposite=0,primeRootCases=0,firstPrimeRootCase=null,thinTwins=0;
 let cofactorTests=0;
 for(let p of primes){if(p<53||p>P||p%4!==1)continue;
 let C=(p+1)**2,M=C/2+1,e=next(M+2,C),e0=next(C/2,C),cond=isPrime(p+2)&&isPrime(C+1);
 if((e?.p===p&&e.side===0)!==cond||(e0?.p===p&&e0.side===0)!==cond)throw Error("tight iff");tightTests++;
 if(cond){let Z=p*(p+3),n=next(Z/2,Z);if(n?.p!==3||n.w!==4||n.side!==0)throw Error("tight next");tightHits.push({p,M,Z,next:n});}
 // Independently test every composite odd cofactor in the range at small p.
 if(p<=300)for(let q=p+2;q<2*p;q+=4)if(!isPrime(q)){let C=p*q+1;let e=next(C/2+3,C),e0=next(C/2,C);if(e?.p===p&&e.side===0||e0?.p===p&&e0.side===0)throw Error("composite cofactor");cofactorTests++}
 for(let q of primes){if(q<=p||q%4!==3)continue;if(q>=2*p)break;let m=q+1,Z=p*m,C=p*q+1,M=C/2+1,thin=(m-p)**2<2*(m+p)-5,h=(q-p)/2;
 nearTests++;if(thin)thinTests++;
 let prePlus=fac(C+1),b0=Math.floor(Math.sqrt(C+1));
 let predicted=prePlus.every(r=>r>b0|| (r%4===1?r>=p-4:3*r>p-6));
 let e=next(M+2,C),e0=next(C/2,C);
 if((e?.p===p&&e.side===0)!==predicted||(e0?.p===p&&e0.side===0)!==predicted)throw Error("first hit characterization");
 if(!predicted)continue;nearWins++;if(thin)thinWins++;
 if(p>=73&&prePlus.length>2)throw Error("prior semiprime");
 if(p>=73&&h*h<2*(p+h)+1&&p>4*h+13){priorThinTests++;if(prePlus.length>1){priorThinComposite++;if(prePlus.length!==2||prePlus.some(r=>r%4!==3))throw Error("prior thin parity")}}
 let n=next(Z/2,Z);if(n===null){if(thin)thinTwins++;continue}
 let a=fac(Z-1),c=fac(Z+1),L=n.w-1,b=Math.floor(Math.sqrt(Z+1));
 if(L>=4){if(p%3!==1||q%3!==2)throw Error("mod3");mod3Tests++}
 if(thin){let S=(p+m+1)/2;if(!((S-1)**2<Z-1&&Z+1<S*S))throw Error("square interval");let U=S-Math.sqrt(S*S-(Z+1));for(let f of [a,c])if(f.length>1&&f[0]>U+1e-8)throw Error("factor bound");if(n.w>Math.floor((3*U+5)/2+1e-8))throw Error("improved clock");sharpTests++;
 if(a.length===2&&a[0]%4===3&&a[1]%4===1){let A=(a[0]+a[1])/2;if(A<S+1)throw Error("parity sharpen")}}
 if(2*L-5<b||((2*L-5)/3)**3<=Z+1)continue;
 if(a.length>1||c.length>1){semis++;let obj={p,q,m,M,C,Z,L,ratio:L/Math.sqrt(Z+1),minus:a,plus:c,priorPlus:prePlus,next:n,thin,primeRoot:isPrime(M)};
 if(!firstOne)firstOne=obj;if(thin&&!firstThin)firstThin=obj;if(a.length>1&&c.length>1){both++;if(!firstBoth)firstBoth=obj;if(thin&&!firstThinBoth)firstThinBoth=obj}if(!largest||obj.ratio>largest.ratio)largest=obj;if(obj.primeRoot){primeRootCases++;if(!firstPrimeRootCase)firstPrimeRootCase=obj}
 let eLit=literal(M+2,C,e.w),nLit=literal(Z/2,Z,n.w);if(JSON.stringify(eLit)!==JSON.stringify(e)||JSON.stringify(nLit)!==JSON.stringify(n))throw Error("literal");literalTests++;}
 }
 }
 return {P,tightTests,tightHits,cofactorTests,nearTests,nearWins,thinTests,thinWins,thinTwins,mod3Tests,sharpTests,priorThinTests,priorThinComposite,semis,both,firstOne,firstBoth,firstThin,firstThinBoth,largest,primeRootCases,firstPrimeRootCase,literalTests}
}

console.log(JSON.stringify(audit(Number(process.argv[2]||12000)),null,2));
