// Exhaustive bounded CRT scan of descending two-relay resonance.
// Number intermediates are exact for P<=50000; use BigInt for cancellations/products.
function audit(P=50000){
 if(!Number.isInteger(P)||P<103||P>50000)throw Error('use 103<=P<=50000');
 const prime=new Uint8Array(P+1);prime.fill(1,2);for(let i=2;i*i<=P;i++)if(prime[i])for(let j=i*i;j<=P;j+=i)prime[j]=0;
 const mod=(x,m)=>(x%m+m)%m,inv=(x,m)=>{let a=mod(x,m),b=m,u=1,v=0;while(b){let q=Math.floor(a/b);[a,b]=[b,a-q*b];[u,v]=[v,u-q*v]}return a===1?mod(u,m):null};
 let s={P,pairs:0,crt:0,scale:0,longWait:0,composite:0,firstPrime:0,phaseRejected:0,strictScale:0,strictCofactorChecks:0,clock:0,clockWithFirstPrime:0,firstHit:0,abstractFull:0,algebraChecks:0,clockStages:[0,0,0],failureLabels:{},examples:[],minGap:null,firstPrimeExample:null,nearest:null,literalChecks:0};
 function fac(n){let fs=[];for(let r=3;r*r<=n;r+=2)if(n%r===0){fs.push(r);while(n%r===0)n/=r}if(n>1)fs.push(n);return fs}
 function next(t,H){let best=null;for(let e of [1,-1])for(let p of fac(H-e)){if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}return best}
 function gcd(a,b){while(b){[a,b]=[b,a%b]}return Math.abs(a)}
 function literal(t,H){for(let w=1;w<=2*Math.floor(Math.sqrt(H+1));w++){let n=t+w,e=n%2?-1:1,g=gcd(n%2?n-2:n,H-e);if(g>1){let p=fac(g)[0];if(p*p<=H+1)return {p,e,w}}}return null}
 function isPrime(n){return n>=3&&fac(n)[0]===n}
 for(let p=103;p<=P;p+=12)if(prime[p])for(let b=Math.floor((p+1)/4)+1;b<(p+1)/2;b++){if(!prime[b]||b%3!==1)continue;let a=p+1-b,c=a-b;if(!prime[a]||a%3!==1)continue;s.pairs++;let A=inv(c+1,a),B=inv(c-1,b);if(A===null||B===null)continue;let bi=inv(a,b);
 for(let ea of [1,-1])for(let eb of [1,-1]){let ra=mod(1-ea*A,a),rb=mod(eb*B,b),Q=ra+a*mod((rb-ra)*bi,b);s.crt++;if(Q<p+2||Q>=p*p/64||Q%12!==1)continue;s.scale++;
 let u=((c+1)*(Q-1)+ea)/a,v=((c-1)*Q-eb)/b,K=(c-1)*u-(c+1)*v,C=-(c*c-1)+(c-1)*ea+(c+1)*eb;
 let kmin=ea===eb?5:ea===-1?3:1;
 if(!Number.isInteger(u)||!Number.isInteger(v)||u%2!==1||v%2!==0||K>-kmin||K%2===0||BigInt(b)*BigInt(K)+BigInt(c)*BigInt(c-1)*BigInt(u)!==BigInt(C)||11n*BigInt(c)**3n*BigInt(Q)<=9n*BigInt(a)*BigInt(b)*BigInt(kmin))throw Error('algebra');
 s.algebraChecks++;
 let Ib=(1-eb)/2,Ia=(1-ea)/2,w2=(c+4-6*Ib)/2;if(w2<=6)continue;s.longWait++;
 let fs=fac(Q);if(fs[0]===Q||w2>=2*fs[0]||c>4*fs[0])continue;s.composite++;
 if(11264n*BigInt(fs[0])**3n*BigInt(Q)<=27n*BigInt(p)**2n*BigInt(kmin))throw Error('factor lower');
 let H1=p*(Q-2)+1,H2=p*Q-1,n1=p*(Q-1)/2;if(!Number.isSafeInteger(H1)||p*p*p<=64*(H2+1))throw Error('scale');
 let firstPrime=isPrime(Q-2);if(firstPrime)s.firstPrime++;
 let Da=a%4===1?0:2*a,wa=(a-1+Da+6*Ia)/2,wb=(3*b-1+6*Ib-Da-6*Ia)/2;
 if(wa+wb+w2!==p+2)throw Error('wait sum');
 if(wa<=0||wb<=0||wa>2*a||wb>2*b){s.phaseRejected++;continue}
 let qa=(p*(Q-1)-ea)/a,qb=(p*Q-b-eb)/b;
 if(qa!==2*(Q-1)-u||qb!==2*Q-1+v)throw Error('cofactor');
 let strict=p**3>4096*(H2+1);
 if(strict){s.strictScale++;if(wa<=2*Math.sqrt(qa)||wb<=2*Math.sqrt(qb)||qa>=a*a||qb>=b*b)throw Error('strong scale gate');s.strictCofactorChecks+=2}
 let hit=next(n1-7,H1),firstOK=hit?.p===p&&hit.e===1&&hit.w===7;if(firstOK)s.firstHit++;
 let t=n1,H=H1+p-1,ev=[],expect=[{p:a,e:ea,w:wa},{p:b,e:eb,w:wb},{p,e:-1,w:w2}],matched=0;
 for(let i=0;i<3;i++){let r=next(t,H);ev.push(r);let l=literal(t,H);if(JSON.stringify(r)!==JSON.stringify(l))throw Error('literal');s.literalChecks++;
 if(JSON.stringify(r)!==JSON.stringify(expect[i])){let k=r?String(r.p):'stop';s.failureLabels[k]=(s.failureLabels[k]||0)+1;break;}s.clockStages[i]++;matched++;t+=r.w;H+=r.p-1}
 let rec={p,a,b,c,Q,ea,eb,w2,r:fs[0],u,v,K,qa,qb,wa,wb,firstPrime,firstOK,matched,ev};
 if(matched===3){s.clock++;if(firstPrime)s.clockWithFirstPrime++;if(firstOK)s.abstractFull++;if(s.examples.length<5)s.examples.push(rec)}
 if(!s.minGap||c<s.minGap.c)s.minGap=rec;
 if(firstPrime&&!s.firstPrimeExample)s.firstPrimeExample=rec;
 if(!s.nearest||matched>s.nearest.matched)s.nearest=rec;
 }
 }
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||50000)),null,2));
