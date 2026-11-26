// Variable-order grouped sieve support, exact periodic uniform mass, and MIN crossing-clock budgets.
function audit(N=20000){
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(x,p)=>(x%p+p)%p;
 const lim=800000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i>2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const st={pointwise:0,relativeMean:0,support:0,periods:0,meanChecks:0,translatedChecks:0,intervalChecks:0,gapChecks:0,maxGap:0,roots:0,events:0,cap:0,blocks:0,crossings:0,anchors:0,bypass:0,nearEndpoint:0,clockChecks:0,coverageChecks:0,massChecks:0};
 let seed=179;function rand(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n}
 function choose(n,k){if(k>n)return 0n;let x=1n;for(let i=1;i<=k;i++)x=x*BigInt(n-i+1)/BigInt(i);return x}
 for(let t=0;t<30000;t++){let m=1+rand(8),k0=rand(4),u=[],d=[],truth=1n;for(let i=0;i<m;i++){let n=rand(16),k=2*(k0+i);let z=0n;for(let j=0;j<=k;j++)z+=(j%2?-1n:1n)*choose(n,j);u.push(z);d.push(choose(n,k+1));if(n)truth=0n}
 let hi=u.reduce((a,b)=>a*b,1n),lo=hi;for(let i=0;i<m;i++)lo-=d[i]*u.reduce((a,b,j)=>i===j?a:a*b,1n);ok(lo<=truth&&truth<=hi,"pointwise");st.pointwise++}
 // Uniform relative expectation budget for all numbers of groups; exact rational majorant.
 // mu_i<=2, Q_i>=1/20, k0>=6. Tail ratio <=1/4.
 for(let k0=6;k0<=30;k0++){let k=2*k0+1,f=1n;for(let j=1;j<=k;j++)f*=BigInt(j);ok(20n*4n*(2n**BigInt(k))*100n<=3n*f,"relative error <1/100");st.relativeMean++}
 for(let m=1;m<=60;m++)for(let k0=0;k0<=10;k0++){let L=2n**BigInt(m),B=0n;for(let i=0;i<m;i++)B+=BigInt(2*(k0+i)+1)*(L>>BigInt(i));ok(B<=BigInt(4*k0+6)*L,"weighted support");st.support++}
 const configs=[[3,11],[5,13],[7,17]];
 const cs=configs.map(([S,Z])=>{
 let P=pr.filter(p=>p<=S).reduce((a,p)=>a*p,1),period=pr.filter(p=>p<=Z).reduce((a,p)=>a*p,1),pref=new Int32Array(period+1),positions=[];
 for(let j=0;j<period;j++){let yes=(2*j)%P===0&&pr.every(p=>p>Z||p<=S||!([1,p-1].includes((2*j)%p)));pref[j+1]=pref[j]+Number(yes);if(yes)positions.push(j)}
 let n=pref[period],Q=pr.filter(p=>p>S&&p<=Z).reduce((a,p)=>a*(1-2/p),1);ok(Math.abs(n-period/P*Q)<1e-8,"mean");st.meanChecks++;st.periods++;
 let count=(l,r)=>{let a=Math.floor(l/period),b=Math.floor(r/period);return (b-a)*n+pref[mod(r,period)]-pref[mod(l,period)]};
 for(let i=0;i<3000;i++){let l=rand(5*period)-2*period,W=1+rand(5*period),n0=count(l,l+W);ok(Math.abs(n0*period-W*n)<=period*n,"translated discrepancy");st.translatedChecks++}
 for(let i=0;i<positions.length;i++){let gap=(positions[(i+1)%positions.length]+(i===positions.length-1?period:0))-positions[i];ok(gap<=period,"gap");st.maxGap=Math.max(st.maxGap,2*gap);st.gapChecks++}
 // Integer-scaled smoothing: exact full-period length, hence mean exactly one.
 for(let i=0;i<3000;i++){let l=rand(4*period)-period,w=1+rand(3*period);let m=count(l,l+w)*period;ok(m<=n*(w+period-1)&&m>=n*(w-period+1),"interval smoothing");st.intervalChecks++}
 return {S,Z,P,period,n,count}
 });
 function factors(x){ok(x>0&&x<lim,"range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g;z={H,p,w,d,dp,g,Z:H+g}}}return z}
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
 if(!rows.length)continue;
 for(let c of cs){let G=0,U=0,F=0,W=0,mlo=0,mhi=0,nh=0,low=0,T=2*c.Z+1;
 for(let z of rows){let m=c.count(z.H/2,z.Z/2);G+=z.g;W+=z.w;if(m){ok(z.p>c.S,"ordinary barrier");st.crossings++;if(c.count(z.H/2,z.H/2+1)){ok(z.p>c.Z,"anchor");st.anchors++}
 for(let J=z.H/2;J<z.Z/2;J++)if(c.count(J,J+1)){let a=2*J-z.H,b=z.Z-2*J;if(a>c.S*c.S&&b>c.S*c.S/2)st.bypass++;else st.nearEndpoint++}}
 if(m&&z.p>=T){nh++;mhi+=m;if(4*z.w>=z.g)F+=z.g}else {U+=z.g;mlo+=m;if(m)low++}
 }
 let a=rows[0].H/2,b=rows.at(-1).Z/2;ok(mlo+mhi===c.count(a,b),"mass");st.massChecks++;
 // Uniform full-period smoothing, with normalization kappa=2period/n.
 ok(c.n*U<=2*c.period*mlo+c.n*2*(c.period-1)*nh+c.n*2*(c.period-1),"coverage");st.coverageChecks++;
 ok(4*W-G===G+2*(rows.at(-1).dp-rows[0].d)&& (4*W-G)*(T-1)<=11*U*(T-1)+(7*(T-1)+8)*F,"clock");st.clockChecks++;
 st.blocks++;
 }}
 ok(st.anchors&&st.bypass&&st.crossings&&st.clockChecks,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||20000)),null,2));
