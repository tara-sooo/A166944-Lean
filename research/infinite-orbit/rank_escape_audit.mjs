// Run: node research/infinite-orbit/rank_escape_audit.mjs
function audit(){
const max=4*65536+4096,spf=new Int32Array(max+1);
for(let p=2;p*p<=max;p++)if(!spf[p])for(let x=p*p;x<=max;x+=p)if(!spf[x])spf[x]=p;
function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
function prime(n){return Number.isInteger(n)&&n>=2&&n<=max&&!spf[n]}
function gcd(a,b){a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a}
function mod(a,b){return (a%b+b)%b}
function elig(H){let B=Math.floor(Math.sqrt(H+1));return [fac(H-1).filter(p=>p<=B),fac(H+1).filter(p=>p<=B)]}
function first(t,f){let p=0,w=Infinity,s=0;for(let i=0;i<2;i++)for(let q of f[i]){let z=1+mod((i?q+2:0)-t-1,2*q);if(z<w||(z===w&&q<p)){p=q;w=z;s=i}}return {p,w,s}}
function gap(n,p,f){let W=2*p;for(let i=0;i<2;i++)for(let q of f[i])if(q!==p){let z=mod(n-(i?q+2:0),2*q);if(!z&&q<p)return 0;W=Math.min(W,z||2*q)}return W}
function ok(v,m){if(!v)throw Error(m)}
let totals={roots:0,targeted:0,events:0,stops:0,exits:0,caps:0,high:0,words:0,rows:0,rank:0,rankNonzero:0,certified:0,rankWords:0,sourcePrime:0,rankPrime:0,repeat:0,clockRows:0,clockRank:0,clockCertified:0,bothRankWords:0,formChecks:0,offsetChecks:0,literal:0,censuses:0,candidateWords:0,rankCandidateWords:0,repeatParity:0,certifiedWords:0,tollRows:0,tollTriples:0,rankWordBounds:0,nonrankRows:0,nonrankEven:0,rankGapMin:0,synthetic:0,primitiveChecks:0,clockPrimitiveChecks:0,uniformBoundChecks:0,uniformCertWords:0,uniformClockCertWords:0,rankDistinct3:0,rankDistinct4:0,rankDistinct5:0},results=[],examples={rank:null,rankPrime:null,nonrank:null,clock:null};
for(let X of [4096,16384,65536]){
 const Y=4*X,T=Math.ceil(Math.sqrt(X)/2),B=Math.floor(Math.sqrt(Y+1));let roots=0,targeted=0,events=0,words=0,rankWords=0,rankPrime=0;
 function inspect(list,can){
 let p=list[0].p,q=list[0].q,c=list[0].c,s=list[0].s,e=list[0].e,H=list[0].H,n=list[0].n,d1=list[1].p-p;
 let A=0,hiGain=0,rows=[];
 for(let i=0;i<list.length;i++){let a=list[i],d=a.p-p,j=a.q-q-i,k=a.c-c,E=a.H-H-hiGain,C=A+E+e-a.e,R=C-d*(i+j),V=a.n-n,S=V-2*(a.s-s)-d*k;
 ok(E>=0&&E%2===0&&d%2===0&&mod(j,2)===i%2,"parity");
 ok(d*q+j*p===R&&d*c+k*p===S,"row identities");ok(mod(R,2)===i%2,"R parity");totals.rows++;
 rows.push({d,j,k,E,R,S,V,i});hiGain+=a.p-1;A+=d-1;}
 totals.words++;words++;
 if(!d1)return;
 let {j:j1,R:R1,k:k1,S:S1}=rows[1],rank=true,crank=true,cert=true;
 for(let x of rows.slice(1)){let z=d1*x.R-x.d*R1,det=d1*x.j-x.d*j1;ok(z===det*p,"rank elimination");if(det)rank=false;else totals.rank++;if(det){totals.rankNonzero++;ok(det%2===0&&Math.abs(z)>=2*p,"nonrank even toll");totals.nonrankRows++;totals.nonrankEven++;}
 if(Math.abs(z)<p){ok(det===0,"rank threshold");totals.certified++;}else cert=false;
 let zz=d1*x.S-x.d*S1,dd=d1*x.k-x.d*k1;totals.clockRows++;ok(zz===dd*p,"clock elimination");if(dd)crank=false;else totals.clockRank++;if(Math.abs(zz)<p){ok(dd===0,"clock threshold");totals.clockCertified++;}
 }
 if(cert)totals.certifiedWords++;
 let K=Math.max(2,...rows.map(x=>Math.abs(x.d))),L=rows[rows.length-1].E,V=rows[rows.length-1].V,J0=rows.length-1;
 let Hbound=J0*(K+1)+L+2+K*(J0+Math.max(...rows.map(x=>Math.abs(x.j)))),Cbound=V+2+K*Math.max(...rows.map(x=>Math.abs(x.k)));
 for(let x of rows){ok(Math.abs(x.R)<=Hbound&&Math.abs(x.S)<=Cbound,"uniform residual bounds");totals.uniformBoundChecks++;}
 if(2*K*Hbound<p){ok(rank,"uniform horizon certificate");totals.uniformCertWords++;}if(2*K*Cbound<p){ok(crank,"uniform clock certificate");totals.uniformClockCertWords++;}
 let primeQ=prime(q);if(primeQ)totals.sourcePrime++;
 if(rank){rankWords++;totals.rankWords++;if(primeQ){rankPrime++;totals.rankPrime++;}
 let labels=new Set(rows.map(x=>x.d)),cof=new Set(rows.filter((x,i)=>prime(list[i].q)).map(x=>x.i+x.j));if(labels.size<rows.length)totals.repeat++;if(labels.size>=3)totals['rankDistinct'+labels.size]++;
 let gg=gcd(d1,j1),D0=d1/gg,J1=j1/gg;ok(gg%2===1&&R1%gg===0&&D0%2===0&&mod(J1,2)===1,"primitive anchor");
 for(let x of rows){let ell=x.d/D0;ok(Number.isInteger(ell)&&x.j===ell*J1&&x.R===ell*(R1/gg)&&mod(ell,2)===x.i%2,"primitive row");totals.primitiveChecks++;if(crank){ok(gg*x.k===ell*k1&&gg*x.S===ell*S1,"clock primitive");totals.clockPrimitiveChecks++;}}
 let steps=[],bs=[];for(let i=0;i+1<rows.length;i++){let x=rows[i],y=rows[i+1],dl=(y.d-x.d)/D0,B0=R1/gg+D0*(i+1)+D0*J1*(y.d+x.d)/D0,Egap=y.E-x.E,C=Egap-1+list[i].e-list[i+1].e;ok(Number.isInteger(dl)&&mod(dl,2)===1&&mod(B0,2)===1&&dl*B0===C&&Math.abs(dl)<=Egap+3&&Math.abs(B0)<=Egap+3,"rank gap factorization");steps.push(dl);bs.push(B0);totals.tollRows++;}
 for(let i=0;i+1<bs.length;i++){let Dgap=bs[i+1]-bs[i],factor=1+J1*(rows[i+2].d-rows[i].d)/D0,local=rows[i+2].E-rows[i].E+6;ok(Dgap===D0*factor&&mod(factor,2)===1&&Math.abs(D0)<=local&&Math.min(Math.abs(D0*steps[i]),Math.abs(D0*steps[i+1]))<=local,"rank triple toll");totals.tollTriples++;totals.rankGapMin++;}
 ok(Math.abs(D0)<=L+6&&Math.max(...rows.map(x=>Math.abs(x.d)))<=(L+6)*(L+3*(rows.length-1)),"rank word width");totals.rankWordBounds++;
 let seen=new Map();
 for(let x of rows){ok(d1*x.j===x.d*j1&&d1*x.R===x.d*R1,"rank");let C=x.R+x.d*(x.i+x.j),calc=C-rows.slice(0,x.i).reduce((s,y)=>s+y.d-1,0)-e+list[x.i].e;ok(calc===x.E,"reconstructed offset");totals.offsetChecks++;if(seen.has(x.d)){ok(mod(x.i-seen.get(x.d),2)===0,"repeat parity");totals.repeatParity++;}seen.set(x.d,x.i);}
 for(let d of labels)for(let b of cof){ok(R1+d1*b+j1*d!==0,"cross determinant");totals.formChecks++;}
 if(!examples.rank)examples.rank={X,can,list,rows};if(primeQ&&!examples.rankPrime&&labels.size>=3)examples.rankPrime={X,can,list,rows};
 if(crank){ok(labels.size===rows.length,"joint rank no repeats");totals.bothRankWords++;if(!examples.clock)examples.clock={X,can,list,rows};}
 }else if(!examples.nonrank)examples.nonrank={X,can,list,rows};
 }
 function scan(H,t,can){let list=[];
 for(let it=0;it<2000&&H<Y;it++){let a=first(t,elig(H));if(!a.p){totals.stops++;break}let {p,w,s}=a,e=1-2*s,q=(H-e)/p,J=H+p-1,n=t+w,c=(n-2*s)/p;
 ok(Number.isInteger(q)&&Number.isInteger(c),"coordinate");
 let v={H,t,p,w,s,e,q,J,n,c};events++;totals.events++;
 if(totals.events%9973===0){let found=null;for(let w0=1;w0<=2*Math.floor(Math.sqrt(H+1));w0++){let n0=t+w0,d=gcd(n0%2?n0-2:n0,n0%2?H+1:H-1),p0=fac(d).find(f=>f<=Math.floor(Math.sqrt(H+1)));if(p0){found=[p0,w0];break}}ok(found&&found[0]===p&&found[1]===w,"literal");totals.literal++;}
 if(p>=T){totals.high++;list.push(v);for(let k=3;k<=Math.min(5,list.length);k++)inspect(list.slice(-k),can);}
 H=J;t=n;if(it===1999&&H<Y)totals.caps++;
 }if(H>=Y)totals.exits++;}
 for(let H=X;H<Y;H+=4){scan(H,(H+6)/2,true);roots++;totals.roots++}
 let seen=new Set();for(let H=X;H<Y;H+=Math.max(2,2*Math.floor(Math.sqrt(X)/8))){let f=elig(H);for(let s=0;s<2;s++)for(let p of f[s]){if(p<T)continue;let r=s?p+2:0,lo=H/2+1,hi=3*H+3+2*p;for(let frac of [1,3,5]){let base=Math.floor(lo+(hi-lo)*frac/6),n=base+mod(r-base,2*p);if(n>hi)continue;let W=gap(n,p,f),l=Math.max(1,n-(3*H+3)),u=Math.min(W,n-H/2);if(l>u)continue;for(let w of new Set([l,u])){let t=n-w,key=H+","+t;if(seen.has(key))continue;seen.add(key);let a=first(t,f);ok(a.p===p&&a.w===w,"target");scan(H,t,false);targeted++;totals.targeted++;}}}}
 let counts=[];
 for(let K of [4,8,16])for(let L of [0,4,16]){
 let all=new Set(),rankSet=new Set(),recon=new Set(),Q=Math.floor((Y+1)/T);
 for(let p=T;p<=B;p++)if(prime(p))for(let q=p;q<=Q;q++)if(prime(q))for(let e of [-1,1]){
 let H=p*q+e;if(H<X||H>=Y||p*p>H+1)continue;
 for(let E1=0;E1<=L;E1+=2){let H1=H+p-1+E1;if(H1>=Y)continue;
 for(let f of [-1,1])for(let r of fac(H1-f)){if(r<T||r>B||r===p||Math.abs(r-p)>K||r*r>H1+1)continue;let u=(H1-f)/r,d1=r-p,j1=u-q-1;
 for(let E2=E1;E2<=L;E2+=2){let H2=H+p+r-2+E2;if(H2>=Y)continue;
 for(let g of [-1,1])for(let v of fac(H2-g)){if(v<T||v>B||v===r||Math.abs(v-p)>K||v*v>H2+1)continue;let z=(H2-g)/v,d2=v-p,j2=z-q-2,key=[p,q,e,r,u,f,v,z,g,E1,E2].join(",");all.add(key);if(d1*j2===d2*j1)rankSet.add(key);}
 }
 }}
 }
 for(let d1=-K;d1<=K;d1+=2){if(!d1)continue;let Jmax=Math.ceil((Math.abs(d1)*(Q+1)+L+3)/T+2);for(let j1=-2*Jmax+1;j1<=2*Jmax;j1+=2)for(let E1=0;E1<=L;E1+=2)for(let e of [-1,1])for(let f of [-1,1]){
 let R1=-1+E1+e-f-d1*(1+j1),gg=gcd(d1,j1);if(R1%gg)continue;
 let step=Math.abs(d1)/gg,base=0;while(mod(R1-j1*base,Math.abs(d1))!==0)base++;
 for(let p=T+mod(base-T,step);p<=B;p+=step){let q=(R1-j1*p)/d1,r=p+d1,u=q+1+j1;if(!prime(p)||!prime(q)||!prime(r)||q<p||r<T||r>B||u<r||u%2!==1)continue;
 let H=p*q+e,H1=r*u+f;if(H<X||H>=Y||H1!==H+p-1+E1||H1>=Y||p*p>H+1||r*r>H1+1)continue;
 for(let d2=-K;d2<=K;d2+=2){if(d2===d1||d2*j1%d1)continue;let j2=d2*j1/d1;if(j2%2)continue;let v=p+d2,z=q+2+j2;if(!prime(v)||v<T||v>B||z<v||z%2!==1)continue;
 for(let g of [-1,1]){let R2=d2*R1/d1;if(!Number.isInteger(R2))continue;let E2=R2+d2*(2+j2)-(d1-2)-e+g,H2=v*z+g;if(E2<E1||E2>L||E2%2||H2!==H+p+r-2+E2||H2>=Y||v*v>H2+1)continue;
 recon.add([p,q,e,r,u,f,v,z,g,E1,E2].join(","));}
 }
 }
 }}
 ok(rankSet.size===recon.size&&[...rankSet].every(k=>recon.has(k)),"rank census");totals.censuses++;totals.candidateWords+=all.size;totals.rankCandidateWords+=rankSet.size;counts.push({K,L,all:all.size,rank:rankSet.size});
 }
 results.push({X,T,B,roots,targeted,events,words,rankWords,rankPrime,counts});
}
// Integer-model synthetic rank triples; verify factorization and primitive toll without claiming MIN.
for(let D of [-12,-8,-4,-2,2,4,8,12])for(let J of [-7,-5,-3,-1,1,3,5,7])if(gcd(D,J)===1)for(let R=-51;R<=51;R+=2)for(let l1=-5;l1<=5;l1+=2)for(let l2=-6;l2<=6;l2+=2)for(let e0 of [-1,1])for(let e1 of [-1,1])for(let e2 of [-1,1]){let b0=R+D+D*J*l1,b1=R+2*D+D*J*(l1+l2),E0=l1*b0+1+e1-e0,E1=(l2-l1)*b1+1+e2-e1;if(E0<0||E1<0)continue;ok(E0%2===0&&E1%2===0&&Math.abs(D)<=E0+E1+6&&Math.min(Math.abs(D*l1),Math.abs(D*(l2-l1)))<=E0+E1+6,"synthetic toll");totals.synthetic++;}
return {totals,results,examples}
}
console.log(JSON.stringify(audit(),null,2));
