function audit(N=300000,steps=180){
 const cap=4*N+10000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function next(t,H){let best=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error('range');while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}}return best}
 function literal(t,H){for(let w=1;w<=2*Math.floor(Math.sqrt(H+1));w++){let n=t+w,e=n%2?-1:1,g=gcd(n%2?n-2:n,H-e);if(g>1&&spf[g]**2<=H+1)return {p:spf[g],e,w}}return null}
 function omega(z){let k=0;while(z>1){z/=spf[z];k++}return k}
 const pi=new Int32Array(cap+1),A=new Float64Array(cap+1);for(let i=1;i<=cap;i++){let prime=i>=3&&spf[i]===i;pi[i]=pi[i-1]+(prime?1:0);A[i]=A[i-1]+(prime?i-1:0)}
 function Bof(Y){let b=1+Math.floor(Math.cbrt(512*(Y+1)));while(b**3<=512*(Y+1))b++;while((b-1)**3>512*(Y+1))b--;return b}
 let s={N,steps,events:0,truncated:0,windows:0,budgetChecks:0,goodEvents:0,goodPrimeOther:0,goodSemiOther:0,lowPositive:0,goodPositive:0,positiveDemand:0,goodOnly:0,lowOnly:0,both:0,full16Windows:0,richChecks:0,lowMultiplicityChecks:0,literalChecks:0,largestGood:null,largestGoodFraction:null,richExample:null};
 function window(ev,hs,ts,i,j){if(i===j)return;let Y=hs[j],G=Y-hs[i],d=2*ts[i]-hs[i],W=ts[j]-ts[i],B=Bof(Y),C=Math.floor(Math.sqrt(Y+1)),lo=0,good=0,lc=new Map(),gc=new Map(),last=new Map();
 for(let k=i;k<j;k++){let z=ev[k],g=z.p-1;if(z.p<=B){lo+=g;lc.set(z.p,(lc.get(z.p)||0)+1)}else if(4*z.w>=g){good+=g;gc.set(z.p,(gc.get(z.p)||0)+1);let q=(z.H-z.e)/z.p;if(spf[q]!==q||q<z.p||omega(z.H-1)>2||omega(z.H+1)>2)throw Error('rough certificate');if(last.has(z.p)&&last.get(z.p)>=q)throw Error('cofactor order');last.set(z.p,q);s.goodEvents++;if(omega(z.H+z.e)===1)s.goodPrimeOther++;else s.goodSemiOther++;if(!s.largestGood||z.p>s.largestGood.p)s.largestGood={...z,Y,q};}}
 if(G-d>2*W||4*W>G+11*(lo+good)||11*(lo+good)<G-2*d)throw Error('budget');
 s.windows++;s.budgetChecks++;if(lo)s.lowPositive++;if(good)s.goodPositive++;let D=Math.max(0,G-2*d);
 if(D){s.positiveDemand++;if(22*lo>=D){s.lowMultiplicityChecks++;let m=Math.max(0,...lc.values());if(22*m*A[Math.min(B,C)]<D)throw Error('low max')}if(22*good>=D){let A0=A[C]-A[Math.min(B,C)],rich=0,richgain=0,maxCap=0;if(A0<=0)throw Error('empty high support');for(let [p,m] of gc){if(44*m*A0>=D){rich++;richgain+=m*(p-1)}let bound=pi[Math.floor((Y+1)/p)]-pi[p-1];if(m>bound)throw Error('prime cofactor capacity');maxCap=Math.max(maxCap,(p-1)*bound)}if(44*richgain<D||44*rich*maxCap<D)throw Error('rich');s.richChecks++;if(!s.richExample||rich>s.richExample.rich)s.richExample={X:hs[i],Y,G,d,lo,good,rich,threshold:D/(44*A0),B,C};}
 if(22*lo>=D&&22*good>=D)s.both++;else if(22*lo>=D)s.lowOnly++;else if(22*good>=D)s.goodOnly++;else throw Error('dichotomy')}
 if(good&&(!s.largestGoodFraction||good*s.largestGoodFraction.G>s.largestGoodFraction.good*G))s.largestGoodFraction={X:hs[i],Y,G,d,lo,good,B,C};
 if(Y>=16*hs[i])s.full16Windows++;
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,hs=[H],ts=[t],ev=[];for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+1>=cap){s.truncated++;break}let r=next(t,H);if(!r)break;let {p,e,w}=r;if(M<=1000){let l=literal(t,H);if(JSON.stringify(l)!==JSON.stringify(r))throw Error('literal');s.literalChecks++}if(w>2*p||w>3*(p-1)||p*p>H+1||2*t-H>5*(H-hs[0])+6)throw Error('envelope');ev.push({M,H,t,p,e,w});H+=p-1;t+=w;hs.push(H);ts.push(t);s.events++}
 if(ev.length){window(ev,hs,ts,0,ev.length);if(ev.length>=4){window(ev,hs,ts,1,ev.length);window(ev,hs,ts,Math.floor(ev.length/2),ev.length)}}
 }
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||300000),Number(process.argv[3]||180)),null,2));
