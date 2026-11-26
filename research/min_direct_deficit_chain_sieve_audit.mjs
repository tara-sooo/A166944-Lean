// Higher-dimensional deficit-coordinate chain sieve inputs, CRT, gcd/lcm and component budgets.
function audit(N=60000){
 const lim=1800000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i%2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)},lcm=(a,b)=>a/gcd(a,b)*b;
 function inv(a,b){let c=b,x=1,y=0;a=mod(a,b);while(c){let q=Math.floor(a/c);[a,c]=[c,a-q*c];[x,y]=[y,x-q*y]}ok(a===1,"inverse");return mod(x,b)}
 function factors(x){ok(x>0&&x<lim,"range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g,D=dp-6*I,e=1-2*I;z={H,p,w,I,e,d,dp,D,x:D/2,g,q:(H-e)/p,h:D/(2*p)}}}return z}
 const st={roots:0,events:0,cap:0,blocks:0,selected:0,edges:0,close:0,autoLong:0,components:0,componentChecks:0,windows:{3:0,4:0,5:0},distinctWindows:{3:0,4:0,5:0},witnessWindows:0,repeatChecks:0,crtChecks:0,gcdChecks:0,detChecks:0,parameterChecks:0,coverChecks:0,budgetChecks:0,syntheticSystems:0,syntheticResidues:0,syntheticPrimeWindows:0,syntheticGcdCases:0,examples:[]};
 function arithmetic(h,c,x,actual){
  let j=h.length,P=h.reduce(lcm,1),ds=h.map((v,i)=>h.reduce((d,w,k)=>k===i?d:lcm(d,gcd(v,w)),1)),u=h.map((v,i)=>v/ds[i]),D=ds.reduce(lcm,1);
  ok(P===D*u.reduce((v,w)=>v*w,1),"lcm decomposition");
  for(let i=0;i<j;i++)for(let k=i+1;k<j;k++){ok(gcd(u[i],u[k])===1&&mod(c[i]-c[k],gcd(h[i],h[k]))===0,"gcd compatibility");st.gcdChecks++}
  let x0=mod(x,P),z=(x-x0)/P,forms=h.map((v,i)=>[P/v,(x0+c[i])/v]);ok(forms.every(([a,b],i)=>Number.isInteger(b)&&a*z+b===(x+c[i])/h[i]),"forms");st.parameterChecks++;
  for(let i=0;i<j;i++)for(let k=i+1;k<j;k++){let [a,b]=forms[i],[v,w]=forms[k],det=a*w-v*b;ok(det!==0&&det===P*(c[k]-c[i])/(h[i]*h[k]),"det");st.detChecks++}
  if(!actual)for(let f of [11,13,17,19,23,29,31]){if(forms.some(([a])=>a%f===0))continue;let rr=forms.map(([a,b])=>mod(-b*inv(a,f),f));for(let i=0;i<j;i++)for(let k=i+1;k<j;k++)ok((rr[i]===rr[k])===(mod(forms[i][0]*forms[k][1]-forms[k][0]*forms[i][1],f)===0),"root collision");st.syntheticResidues++}
 }
 function inspect(rows,T,A,B){
  let l=rows.filter(z=>z.p>=T&&z.p<2*T&&z.x>0&&z.x<T*T),G=rows.reduce((s,z)=>s+z.g,0),F=l.reduce((s,z)=>s+z.g,0),V=rows.reduce((s,z)=>s+Math.abs(z.dp-z.d),0);
  if(!l.length)return;st.blocks++;st.selected+=l.length;let groups=[],a=0,Es=0,Vs=0,bad=0;
  for(let i=1;i<l.length;i++){let u=l[i-1],v=l[i],E=v.H-u.H-u.g,d=v.dp-u.dp;Es+=E;Vs+=Math.abs(d);st.edges++;
   if(E<=B&&Math.abs(d)<=A){ok(u.p!==v.p&&u.x!==v.x,"close distinct");ok(4*v.w>=v.g,"automatic long");st.close++;st.autoLong++}
   else {groups.push(l.slice(a,i));a=i;bad++}
  }groups.push(l.slice(a));st.components+=groups.length;ok(Es<=G-F&&Vs<=V,"budgets");
  for(let j of [3,4,5]){let W=0,small=0;
   for(let g of groups){let n=g.length;if(n<=j){small+=g.reduce((s,z)=>s+z.g,0);continue}
    let ww=0;for(let a=1;a+j<=n;a++){let v=g.slice(a,a+j),xs=v.map(z=>z.x),ps=v.map(z=>z.p),w=v.at(-1).g;W+=w;ww+=w;st.windows[j]++;
     let witness=false,allPrime=v.every(z=>spf[z.q]===z.q&&z.w>6);
     for(let k=0;k<j;k++)for(let m=k+1;m<j;m++)if(xs[k]===xs[m]){ok(ps[k]===ps[m]&&v[m].q>v[k].q,"repeat");st.repeatChecks++;if(allPrime){ok(v[m].q-v[k].q===2,"equal-D twin");witness=true}}
     if(witness)st.witnessWindows++;
     if(new Set(xs).size!==j)continue;st.distinctWindows[j]++;
     arithmetic(v.map(z=>z.h),xs.map(x=>x-xs[0]),xs[0],true);
     let u=v[0],z=v[1],E=z.H-u.H-u.g,P=u.p*z.p,H0=u.e+u.p*mod((z.e-u.g-E-u.e)*inv(u.p,z.p),z.p);ok(mod(u.H-H0,P)===0,"first pair CRT");st.crtChecks++;
     if(st.examples.length<4)st.examples.push({j,T,A,B,p:ps,x:xs,H:v.map(z=>z.H),w:v.map(z=>z.w)})
    }ok(g.reduce((s,z)=>s+z.g,0)<=2*(j+1)*ww,"component weight");st.componentChecks++;
   }ok(F<=small+2*(j+1)*W&&small<=2*T*j*(bad+1),"cover");st.coverChecks++;
   ok(bad*(A+1)*(B+1)<=(A+1)*(G-F)+(B+1)*V,"bad budget");st.budgetChecks++;
  }
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;for(let i=0;i<180;i++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
  for(let T of [17,31,61])inspect(rows,T,Math.floor((T-1)/4),Math.floor((T-1)/20))
 }
 // Abstract congruence systems with distinct offsets, not MIN realizations.
 let seed=4381;function rand(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n}
 for(let i=0;i<20000;i++){let j=3+rand(3),h=Array.from({length:j},()=>1+rand(20)),x=2000+rand(10000),c=h.map((v,k)=>k?mod(-x,v)+k*v:0);x-=mod(x,h[0]);c=h.map((v,k)=>k?mod(-x,v)+k*v:0);if(new Set(c).size!==j)continue;arithmetic(h,c,x,false);st.syntheticSystems++;if(h.some((v,k)=>h.some((w,m)=>m!==k&&gcd(v,w)>1)))st.syntheticGcdCases++;
 }
 // Genuine prime tuples in the abstract deficit coordinate, without claiming clock realizability.
 for(let j of [3,4,5])for(let T of [31,61,101]){let ps=pr.filter(p=>p>=T&&p<2*T);for(let i=0;i+j<=ps.length;i++){let h=ps.slice(i,i+j).map((p,k)=>2+(k%2)),xs=h.map((v,k)=>v*ps[i+k]);if(new Set(xs).size!==j)continue;arithmetic(h,xs.map(x=>x-xs[0]),xs[0],false);st.syntheticPrimeWindows++}}
 ok(st.close&&st.autoLong&&st.syntheticSystems&&st.syntheticGcdCases&&st.syntheticPrimeWindows,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
