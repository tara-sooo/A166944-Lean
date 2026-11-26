// Uniform deficit-range supply inputs and cumulative positive-variation precursor checks.
function audit(N=60000){
 const lim=1800000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i%2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function factors(x){ok(x>0&&x<lim,"range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function inv(a,b){let c=b,x=1,y=0;a=mod(a,b);while(c){let q=Math.floor(a/c);[a,c]=[c,a-q*c];[x,y]=[y,x-q*y]}ok(a===1,"inverse");return mod(x,b)}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g,D=dp-6*I,e=1-2*I;z={H,p,w,I,e,d,dp,D,x:D/2,g,q:(H-e)/p}}}return z}
 const st={roots:0,events:0,cap:0,blocks:0,selected:0,pairs:0,close:0,zeroDisplacement:0,linearCap:0,subquadraticCap:0,nearOrigin:0,awayOrigin:0,bandChecks:0,divisorChecks:0,horizonChecks:0,tupleChecks:0,budgetChecks:0,rangeChecks:0,positiveSupplyChecks:0,actualPrecursorChecks:0,actualHighUpChecks:0,syntheticGeometricControls:0,syntheticPrecursorWindows:0,translatedPrimeIntervals:0,weightedCandidateControls:0,weightedCandidateHits:0,examples:[]};
 function inspect(rows,T){
  if(!rows.length)return;let G=rows.reduce((a,z)=>a+z.g,0),V=rows.reduce((a,z)=>a+Math.abs(z.dp-z.d),0),P=rows.reduce((a,z)=>a+Math.max(z.dp-z.d,0),0),C=Math.floor(Math.sqrt(rows.at(-1).H+1)),Fup=0,Ulow=0;
  for(let z of rows){if(z.p<T)Ulow+=z.g;else if(8*(z.dp-z.d)>z.g){Fup+=z.g;ok(z.w*2>z.g,"up long");if(z.g>48)ok(z.D>0,"large up nonreset");st.actualHighUpChecks++}}
  ok(8*(T-1)*P<=(T-1)*G+40*(T-1)*Ulow+8*(3*(T-1)+4)*Fup,"positive supply");st.positiveSupplyChecks++;
  let l=rows.filter(z=>z.p>=T&&z.x>0);if(!l.length)return;let F=l.reduce((a,z)=>a+z.g,0),L=Math.min(...l.map(z=>z.x)),Dmax=Math.max(...l.map(z=>z.x)),W=Math.max(T,Dmax-L+1),A=Math.floor(T/3),B=Math.floor(T/3),sumE=0,sumv=0,close=0,bad=0,tuple=new Map;
  st.blocks++;st.selected+=l.length;if(Dmax>=T*T)st.linearCap++;else st.subquadraticCap++;
  if(L<W)st.nearOrigin++;else st.awayOrigin++;
  ok(Dmax-L<=V/2+3,"range");st.rangeChecks++;
  for(let z of l){let fs=factors(z.x).filter(p=>p>=T);ok(fs.includes(z.p)&&fs.reduce((a,b)=>a*b,1)<=z.x&&fs.length<=Math.floor(Math.log(z.x)/Math.log(T)+1e-10),"divisors");st.divisorChecks++}
  for(let i=1;i<l.length;i++){let u=l[i-1],v=l[i],E=v.H-u.H-u.g,d=v.dp-u.dp,c=v.x-u.x;sumE+=E;sumv+=Math.abs(d);st.pairs++;
   if(E>B||Math.abs(d)>A){bad+=v.g;continue}
   ok(u.p!==v.p&&c===d/2-3*(v.I-u.I),"close");if(c===0){ok(u.x%(u.p*v.p)===0,"same x");st.zeroDisplacement++}
   let U=T;while(2*U<=u.p)U*=2;let a=L,b=L+W-1;if(L<W){a=T;while(2*a<=u.x)a*=2;b=2*a-1}
   let h=u.x/u.p,n=Math.floor(b/h)-Math.ceil(a/h)+1;
   ok(h>=a/(2*U)&&h<=b/U&&n>=1&&n<=Math.ceil((b-a+1)/h)+1&&n+1>=(b-a+1)/h,"prime interval");st.bandChecks++;
   let prod=u.p*v.p,H0=u.e+u.p*mod((v.e-u.g-E-u.e)*inv(u.p,v.p),v.p);ok(mod(u.H-H0,prod)===0,"CRT");st.horizonChecks++;
   let key=[u.x,c,E,u.I,v.I,u.p,v.p].join(","),arr=tuple.get(key)||[];ok(!arr.includes(u.H),"unique H");arr.push(u.H);tuple.set(key,arr);
   close+=v.g;st.close++;if(c===0&&st.examples.length<3)st.examples.push({p:u.p,r:v.p,x:u.x,E,d,H:u.H,H2:v.H,T})
  }
  for(let [key,arr] of tuple){let a=key.split(",").map(Number),p=a[5],r=a[6];ok(arr.length<=1+Math.floor((Math.max(...arr)-Math.min(...arr))/(p*r)),"tuple span");st.tupleChecks++}
  ok(sumE<=G-F&&sumv<=V&&F===l[0].g+close+bad,"partition");ok((F-l[0].g-close)*(A+1)*(B+1)<=C*((A+1)*(G-F)+(B+1)*V),"gain");st.budgetChecks++;
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;
  for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
  for(let T of [11,17,31,61])inspect(rows,T);
  // Any positive endpoint above 12 requires positive variation since last <=half.
  for(let i=0;i<rows.length;i++){let d=rows[i].dp;if(d<24)continue;let j=i;while(j>0&&rows[j].d>d/2)j--;let a=rows[j].d,V=rows.slice(j,i+1).reduce((s,z)=>s+Math.max(0,z.dp-z.d),0);ok(a<=d/2&&V>=d-a,"actual precursor");st.actualPrecursorChecks++}
 }
 // Enumerate translated deficit ranges, compare band-weight counts against exact
 // prime-multiplier incidence counts. The constants of the analytic sieve are not fitted.
 for(let T of [17,31,53])for(let W of [T,2*T,5*T])for(let L of [T,2*T,5*T,T*T,3*T*T]){
  let weight=0,other=0,hi=L+W-1;
  for(let x=L;x<=hi;x++)for(let p of factors(x).filter(p=>p>=T&&p<8*T)){let U=T;while(2*U<=p)U*=2;weight+=1/U;st.weightedCandidateHits++}
  for(let U=T;U<8*T;U*=2)for(let h=Math.max(1,Math.ceil(L/(2*U)));h<=Math.floor(hi/U);h++){let a=Math.max(U,Math.ceil(L/h)),b=Math.min(2*U-1,Math.floor(hi/h));if(a>b)continue;let n=0;for(let p=a;p<=b;p++)if(spf[p]===p)n++;other+=n/U;ok(b-a+1<=Math.ceil(W/h)+1,"translated size");st.translatedPrimeIntervals++}
  // count occurrences with multiplicity? p^2 contributes just once for fixed h=x/p.
  ok(Math.abs(weight-other)<1e-8,"weighted incidence");st.weightedCandidateControls++;
 }
 // Scalar geometric-window controls for the precursor lemma (not MIN trajectories).
 for(let j=4;j<=10;j++)for(let q of [2,4,8,16,32,64]){let X=16**j,d=X/q,L=1;while(5*16**(j-L)>d/4)L++;if(j-L<0)continue;
  let horizons=Array.from({length:L+1},(_,i)=>16**(j-L+i)),ds=[Math.floor(d/8)],P=[];
  for(let k=0;k<L;k++){let v=k===L-1?d:ds.at(-1);P.push(Math.max(0,v-ds.at(-1)));ds.push(v);ok(v<=5*horizons[k+1],"synthetic envelope")}
  ok(ds[0]<=d/4&&P.reduce((a,b)=>a+b,0)>=3*d/4,"geometric precursor");
  ok(P.some((v,k)=>v>= (d/X)*horizons[k]),"relative precursor");st.syntheticGeometricControls++;st.syntheticPrecursorWindows+=L;
 }
 ok(st.close&&st.zeroDisplacement&&st.linearCap&&st.subquadraticCap&&st.actualPrecursorChecks&&st.weightedCandidateHits,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
