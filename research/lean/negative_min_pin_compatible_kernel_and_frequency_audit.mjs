// Rational Buchstab enclosure, pin-compatible marginal kernel, averaged frequency exponent and double-pin DHR coefficient. No asymptotic numerical test.
function audit(){
 const S=10n**25n,N=20000,E=1200000,B=BigInt,assert=(v,m)=>{if(!v)throw Error(m)},ceil=(a,b)=>(a+b-1n)/b;
 const lo=[],hi=[];
 for(let i=0;i<=6*N;i++){
  if(i<N){lo[i]=hi[i]=0n;continue;}
  if(i<=2*N){lo[i]=hi[i]=S;continue;}
  lo[i]=lo[i-1]+lo[i-1-N]/B(i-N);
  hi[i]=hi[i-1]+ceil(hi[i-N],B(i-1-N));
  assert(lo[i]<=hi[i],"Buchstab");
 }
 function M(t){const l=Math.floor(N*E/t),r=Math.ceil(N*E/t);assert(l>=N&&r<lo.length,"M range");return[lo[l],hi[r]]}
 function log(a,b){a=B(a);b=B(b);assert(a>=b&&b>0n,"log");const x=a-b,y=a+b,x2=x*x,y2=y*y;let p=x,q=y,l=0n;for(let j=0;j<64;j++){l+=2n*S*p/(q*B(2*j+1));p*=x2;q*=y2;}return[l,l+64n+ceil(2n*S*p*y2,q*129n*(y2-x2))]}
 const dec=v=>Number(v)/Number(S);
 const b0=228000,u0=250000,c=480000,d=750000;
 const [bL,bU]=M(b0),[uL,uU]=M(u0),[mL,mU]=log(3,2).map(v=>v+S);
 const gL=(2n*mL-uU)*S/(bU-uL),gU=ceil((2n*mU-uL)*S,bL-uU);
 assert(gL>0n&&gU<45n*S/100n,"g in (0,.45)");
 assert(bU<32n*S/10n,"row upper");
 const rU=2n*log(49,38)[1];
 assert(S-gU>rU,"pin bound");
 let min=10n*S,cells=0,first=10n*S,second=10n*S;
 for(const [a,b,kind] of [[b0,u0,0],[u0,d/2,1]])for(let l=a;l<b;){const r=Math.min(b,l+120),m=M(r)[0];
  const lower=kind===0?m-ceil(gU*(bU-m),S):2n*(m-mU);
  const L=ceil(2n*B(E)*log(d-l,l)[1],B(d));
  const gap=lower-L;if(gap<min)min=gap;if(kind===0&&gap<first)first=gap;if(kind===1&&gap<second)second=gap;
  assert(gap>0n,"tail "+l+" "+dec(gap));cells++;l=r;
 }
 const band208=249600, [vL,vU]=M(band208);
 const lowMassU=vU-uL,highMassU=uU-mL;
 const hiSquareU=ceil(2n*(S-gL)*lowMassU*highMassU,S*S)+ceil((S*S-gL*gL)*lowMassU*lowMassU,S*S*S);
 assert(hiSquareU<1n*S/100n,"model .208 square upper "+dec(hiSquareU));
 // Compatibility with prior mixed .11 lower: unchanged F x F triple boxes.
 const one= S*750n*25n*10000n/(1850n*2110n*6815n);
 assert(one*one/S>3n*S/100000n,"mixed factor model compatibility");
 const newerBox=S*500n*25n*10000n/(1850n*2110n*6565n);assert(newerBox*newerBox/S>2n*S/100000n,"DHR lower compatibility");
 // Aggregate h over dyadic blocks, balanced .515.
 const X=515000;const firstErr=14*2*X+5*X+3*1000000;
 assert(firstErr<20*1000000,"BC averaged first");
 const secondErr=7*2*X+X;assert(secondErr<8*1000000,"BC averaged second");
 // DHR explicit coefficient using F2>=1, beta2<=4.2665, e^-2gamma>1/4.
 function dhr(z,lev,pmin,pmax,div){
  const sN=B(lev)*10000n,sD=B(z)*42665n;
  assert(sN>sD&&2*pmax+lev<1000000,"DHR level");
  const f=S-ceil(S*sD*sD,sN*sN);
  const p=log(pmax,pmin)[0],factor=f*p/S*p/S;
  const coeff=factor*1000000n**2n/(4n*B(z)**2n*B(div));
  return {z:z/1e6,s:lev/z,f:dec(f),coeff:dec(coeff),raw:coeff};
 }
 const vectorRatio=2n*log(189,114)[0]-S;assert(vectorRatio>0n,".114 vector positivity");const pm=log(211000,208500)[0];const vectorCoeff=4n*1000000n**2n*vectorRatio*pm/S*pm/S*9n/(303000n**2n*160n);assert(vectorCoeff>3n*S/1000000n,".114 vector coefficient");
 const dh=[dhr(135000,577000,208500,211000,16),dhr(130000,577000,208500,211000,16),dhr(125000,577000,208500,211000,16)];
 assert(dh[0].raw>4n*S/10000000n,".135 explicit coefficient");
 // Finite CRT counts for both pins and genuine least exceptions.
 const gcd=(a,b)=>b?gcd(b,a%b):a;let crt=0,pinChecks=0;
 const primes=[3,5,7,11,13,17];
 for(const p of [7,11,13])for(const q of [7,11,13])if(p!==q)for(const r of primes)if(r!==p&&r!==q){
  let num=0;const mod=2*p*q*r;
  for(let n=1;n<mod;n+=2)if(n%p===0&&(n+2)%q===0&&(n*(n+2))%r===0)num++;
  assert(num===2,"conditional two roots");crt++;
 }
 for(let n=3;n<20000;n+=2){
  const fac=x=>{const a=[];for(let p=2;p*p<=x;p++)while(x%p===0){a.push(p);x/=p;}if(x>1)a.push(x);return a;};
  const p=fac(n),q=fac(n+2),i=p.filter(v=>v>=7&&v<=17).length,j=q.filter(v=>v>=7&&v<=17).length;
  if(i&&j){assert(p[0]>=2&&q[0]>=2,"actual factors");assert(gcd(n,n+2)===1,"odd disjoint");pinChecks++;}
 }
 return {bMass:[dec(bL),dec(bU)],uMass:[dec(uL),dec(uU)],cMass:[dec(mL),dec(mU)],g:[dec(gL),dec(gU)],pinRatioUpper:dec(rU),pinFloorLower:dec(S-gU),tailCells:cells,minGap:dec(min),lowerBandMargin:dec(first),upperBandMargin:dec(second),model208Upper:dec(hiSquareU),mixedBoxModelLower:dec(one*one/S),BC:{first:firstErr/20000000,second:secondErr/8000000},vector114:{ratio:dec(vectorRatio),coefficient:dec(vectorCoeff)},modelDHRBox:dec(newerBox*newerBox/S),DHR:dh.map(({raw,...x})=>x),crt,pinChecks};
}
console.log(JSON.stringify(audit(),null,2));
