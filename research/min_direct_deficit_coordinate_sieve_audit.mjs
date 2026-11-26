// Deficit-coordinate prime-line sieve inputs and uncapped close-transition budgets.
function audit(N=60000){
 const lim=1800000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i%2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function inv(a,b){if(b===1)return 0;let c=b,x=1,y=0;a=mod(a,b);while(c){let q=Math.floor(a/c);[a,c]=[c,a-q*c];[x,y]=[y,x-q*y]}ok(a===1,"inverse");return mod(x,b)}
 function factors(x){ok(x>0&&x<lim,"factor range");let l=[];while(x>1){let p=spf[x];l.push(p);while(x%p===0)x/=p}return l}
 function next(H,t){let v=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!v||w<v.w||w===v.w&&p<v.p){let d=2*t-H,g=p-1,dp=d+2*w-g,D=dp-6*I;v={H,t,p,w,I,e:1-2*I,d,dp,D,x:D/2,h:D/(2*p),g}}}return v}
 function J(x){let a=1;for(let p of factors(x))if(p>2)a*=p/(p-2);return a}
 const st={roots:0,events:0,cap:0,blocks:0,selected:0,pairs:0,close:0,nearZeroIntervals:0,awayIntervals:0,dyadicIntervals:0,deficitCRT:0,horizonCRT:0,primeLineResidues:0,uniqueDivisors:0,signedDisplacements:0,nonzeroMinors:0,budgetChecks:0,actualTupleChecks:0,actualTupleDuplicates:0,syntheticIntervals:0,syntheticCRT:0,syntheticResidues:0,meanChecks:0,gcdMeanChecks:0,maxMeanRatio:0,examples:[]};
 function intervals(L,H,W,T){if(L>=W)return [[L,L+W-1]];let hi=Math.min(H,2*W),a=T,out=[];while(a<=hi){out.push([a,Math.min(2*a-1,hi)]);a*=2}return out}
 function inspect(rows,T,C,A,B){let l=rows.filter(z=>z.p>=T&&z.p<=C&&z.h>=1&&z.x<T*T-A-4),F=l.reduce((s,z)=>s+z.g,0);if(!l.length)return;
  let min=Math.min(...l.map(z=>z.x)),max=Math.max(...l.map(z=>z.x)),W=Math.max(C,max-min+1),parts=intervals(min,max,W,T);
  st.blocks++;st.selected+=l.length;if(min>=W)st.awayIntervals++;else st.nearZeroIntervals++;st.dyadicIntervals+=parts.length;
  ok(parts.reduce((s,[a,b])=>s+b-a+1,0)<=2*W,"shell length");
  let G=rows.reduce((s,z)=>s+z.g,0),V=rows.reduce((s,z)=>s+Math.abs(z.dp-z.d),0),R=0,D=0,close=0,badE=0,badV=0,tuples=new Map();
  ok(max-min<=V/2+3,"range");
  for(let i=1;i<l.length;i++){let u=l[i-1],v=l[i],E=v.H-u.H-u.g,d=v.dp-u.dp,c=v.x-u.x;R+=E;D+=Math.abs(d);st.pairs++;
   if(E>B){badE+=v.g;continue}if(Math.abs(d)>A){badV+=v.g;continue}
   ok(u.p!==v.p&&c!==0&&c===d/2-3*(v.I-u.I),"nonzero");
   ok(factors(u.x).filter(p=>p>=T).length===1&&factors(v.x).filter(p=>p>=T).length===1,"unique large factors");st.uniqueDivisors+=2;
   let h=u.h,k=v.h,g=gcd(h,k),a=h/g,b=k/g,m=c/g;ok(c%g===0,"gcd");
   let x0=h*mod(-m*inv(a,b),b),step=h*b,z=(u.x-x0)/step;ok(Number.isInteger(z)&&mod(x0,h)===0&&mod(x0+c,k)===0,"deficit CRT");st.deficitCRT++;
   let part=parts.find(([lo,hi])=>lo<=u.x&&u.x<=hi);ok(part,"shell membership");let [lo,hi]=part,n=Math.floor((hi-x0)/step)-Math.ceil((lo-x0)/step)+1;ok(n>=1&&n<=Math.ceil((hi-lo+1)/step)+1,"parameter count");
   let p0=x0/h,r0=(x0+c)/k;ok(u.p===p0+b*z&&v.p===r0+a*z,"prime forms");
   for(let f of pr){if(f>=Math.min(u.p,v.p,31))break;if(a%f&&b%f){let r1=mod(-p0*inv(b,f),f),r2=mod(-r0*inv(a,f),f);ok((r1===r2)===(m%f===0)&&mod(z,f)!==r1&&mod(z,f)!==r2,"sieve roots");st.primeLineResidues++}}
   let P=u.p*v.p,H0=u.e+u.p*mod((v.e-u.g-E-u.e)*inv(u.p,v.p),v.p);ok(mod(u.H-H0,P)===0,"horizon CRT");st.horizonCRT++;
   let key=[u.x,c,E,u.I,v.I].join(","),l0=tuples.get(key)||{set:new Set(),P,min:u.H,max:u.H};if(l0.set.has(u.H))st.actualTupleDuplicates++;ok(!l0.set.has(u.H)&&l0.P===P,"tuple uniqueness");l0.set.add(u.H);l0.min=Math.min(l0.min,u.H);l0.max=Math.max(l0.max,u.H);tuples.set(key,l0);
   st.signedDisplacements++;if(u.h*((v.H-v.e)/v.p)-v.h*((u.H-u.e)/u.p+1))st.nonzeroMinors++;
   st.close++;close+=v.g;
   if(st.examples.length<4&&Math.max(h,k)>=4)st.examples.push({H:u.H,H2:v.H,p:u.p,r:v.p,x:u.x,x2:v.x,h,k,c,E,v:d,T,C})
  }
  for(let o of tuples.values()){ok(o.set.size<=1+Math.floor((o.max-o.min)/o.P),"tuple horizon count");st.actualTupleChecks++}
  ok(R<=G-F&&D<=V&&F===l[0].g+close+badE+badV,"budgets");ok((F-l[0].g-close)*(A+1)*(B+1)<=C*((A+1)*(G-F)+(B+1)*V),"budget bound");st.budgetChecks++;
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;
  for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
  for(let T of [17,31,47,71])inspect(rows,T,4*T,Math.floor(T/2),Math.floor(T/3))
 }
 // Verify exact progression and two-root condition for signed shifts and translated intervals.
 for(let h=1;h<=23;h++)for(let k=1;k<=23;k++)for(let c of [-17,-6,-1,1,6,17]){let g=gcd(h,k);if(c%g)continue;let a=h/g,b=k/g,m=c/g,x0=h*mod(-m*inv(a,b),b),P=h*b;
  let L=1000+13*h,W=503+2*k,first=Math.ceil((L-x0)/P),last=Math.floor((L+W-1-x0)/P),count=0;
  for(let x=L;x<L+W;x++)if(x%h===0&&(x+c)%k===0){ok(mod(x-x0,P)===0,"synthetic CRT");count++;st.syntheticCRT++}
  ok(count===Math.max(0,last-first+1),"translated count");st.syntheticIntervals++;
  for(let f of [29,31,37]){let u=mod(-(x0/h)*inv(b,f),f),v=mod(-((x0+c)/k)*inv(a,f),f);ok((u===v)===(m%f===0),"synthetic roots");st.syntheticResidues++}
 }
 // Weighted divisor mean: sum_{c<=Q} sum_{g|c} J(c/g)/g = sum_g (sum_{n<=Q/g}J(n))/g.
 let S=[0];for(let n=1;n<=2048;n++){S.push(S.at(-1)+J(n));ok(S[n]<=Math.E*n+1e-8,"J mean");st.meanChecks++}
 for(let Q of [1,2,4,8,16,32,64,128,256,512,1024,2048]){let z=0,y=0;for(let c=1;c<=Q;c++)for(let g=1;g<=c;g++)if(c%g===0)z+=J(c/g)/g;for(let g=1;g<=Q;g++)y+=S[Math.floor(Q/g)]/g;ok(Math.abs(z-y)<1e-7*Math.max(1,z)&&y<=Math.E*Math.PI**2/6*Q+1e-6,"gcd mean");st.gcdMeanChecks++;st.maxMeanRatio=Math.max(st.maxMeanRatio,y/Q)}
 ok(st.close&&st.awayIntervals&&st.nearZeroIntervals&&st.syntheticCRT&&st.primeLineResidues&&!st.actualTupleDuplicates,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
