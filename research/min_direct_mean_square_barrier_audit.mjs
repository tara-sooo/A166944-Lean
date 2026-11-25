// Mean-square CRT barrier discrepancy and smoothed union coverage.
function audit(N=50000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 const primes=S=>{let a=[];for(let p=3;p<=S;p+=2)if(spf[p]===p)a.push(p);return a};
 const stats={periods:[],formula:[],momentChecks:0,divisorChecks:0,randomUnionChecks:0,roots:0,events:0,a1:0,terminal:0,capped:0,blocks:0,highCoverageChecks:0,convolutionChecks:0,cauchyChecks:0,farShareChecks:0,jointChecks:0};
 const tables=new Map();
 let seed=13991;function rand(n){seed=(Math.imul(1664525,seed)+1013904223)>>>0;return seed%n}
 function build(R,kind){
  const ps=primes(R),P=ps.reduce((a,p)=>a*p,1),pre=new Uint32Array(P+1);
  for(let j=0;j<P;j++)pre[j+1]=pre[j]+(ps.every(p=>kind==="H"?mod(j,p)<=(p-3)/2:p===3||[0,1].every(I=>{let r=mod(2*j-6*I,2*p);return r<2||r>p-3}))?1:0);
  let A=pre[P],Lambda=1,D2=1;
  for(let p of ps.filter(p=>p>=11)){let k=1/(((p-3)/2)*Math.sin(Math.PI/p));Lambda*=k;D2*=1+(1/(k*k)-1)/p}
  let V=P*Lambda*Lambda*D2;
  function count(j){return Math.floor(j/P)*A+pre[mod(j,P)]}
  function lengths(l){
   let sum=new Float64Array(P+1),abs=new Float64Array(P+1),ss=0;
   for(let j=0;j<P;j++){
    let c=count(j+l)-count(j),z=P*c-A*l;
    sum[j+1]=sum[j]+c;abs[j+1]=abs[j]+Math.abs(z);ss+=(z/(A*l))**2;
   }
   if(sum[P]!==A*l)throw Error("mean");
   let var0=ss/P;
   if(var0>4*V/l+1e-9)throw Error("variance");
   stats.momentChecks+=P;
   const periodic=(ar,j)=>Math.floor(j/P)*ar[P]+ar[mod(j,P)];
   return {l,var0,sum:(a,b)=>periodic(sum,b)-periodic(sum,a),abs:(a,b)=>periodic(abs,b)-periodic(abs,a)};
  }
  let out={R,kind,P,A,V,count,ls:[]};
  for(let l of [...new Set([1,Math.floor(Math.sqrt(P)),Math.max(1,Math.floor(P/4)),Math.floor(P/2),P])]){
   let f=lengths(l);stats.periods.push({R,kind,P,A,l,V,var:f.var0,bound:4*V/l});
   if(R<=13&&kind==="H"&&l!==P)out.ls.push(f);
  }
  return out;
 }
 function merge(a){let b=[];for(let [x,y] of a){if(x>=y)continue;if(b.length&&x<=b.at(-1)[1])b.at(-1)[1]=Math.max(y,b.at(-1)[1]);else b.push([x,y])}return b}
 function checkUnion(tab,f,a,b,intervals,coverAll=false){
  let {P,A,count,V}=tab,{l}=f;
  let u=merge(intervals),v=merge(u.map(([x,y])=>[x-l+1,y])),n=b-a+l-1;
  let len=u.reduce((s,[x,y])=>s+y-x,0),lenV=v.reduce((s,[x,y])=>s+y-x,0);
  let cuts=u.reduce((s,[x,y])=>s+count(y)-count(x),0);
  if(lenV>len+(l-1)*u.length||coverAll&&cuts!==count(b)-count(a))throw Error("cover");
  let conv=v.reduce((s,[x,y])=>s+f.sum(x,y),0),err=f.abs(a-l+1,b);
  if(l*cuts>conv||P*conv>A*l*lenV+err+1e-6)throw Error("convolution");
  let sigma=Math.sqrt(4*V/l),upper=Math.sqrt(n*(n+P))*sigma;
  if(err/(A*l)>upper+1e-7)throw Error("cauchy");
  stats.convolutionChecks++;stats.cauchyChecks++;
  return {len,cuts,err:err/(A*l),upper,l};
 }
 for(let R of [5,7,11,13,17,19]){
  let ps=primes(R).filter(p=>p>=11),D2=ps.reduce((a,p)=>a*(1+((((p-3)/2)*Math.sin(Math.PI/p))**2-1)/p),1),s=0;
  for(let k=1;k<=50000;k++){let f=1;for(let p of ps)if(k%p===0)f*=(((p-3)/2)*Math.sin(Math.PI/p))**2;s+=f;if(s>D2*k+1e-7)throw Error("divisor average");stats.divisorChecks++}
  for(let kind of ["H","d"]){
   let t=build(R,kind);if(R<=13&&kind==="H"){
    tables.set(R,t);
    for(let i=0;i<500;i++){
     let a=rand(t.P*2)-t.P,b=a+1+rand(t.P*2),pos=a,u=[];
     while(pos<b&&u.length<20){pos+=rand(1+Math.ceil((b-a)/20));let z=Math.min(b,pos+1+rand(1+Math.ceil((b-a)/20)));if(pos<z)u.push([pos,z]);pos=z}
     for(let f of t.ls){checkUnion(t,f,a,b,u);stats.randomUnionChecks++}
    }
   }
  }
 }
 for(let R of [100,200,500,1000,2000]){
  let ps=primes(R),logP=ps.reduce((a,p)=>a+Math.log(p),0),logL=0,logD2=0,logD1=0;
  for(let p of ps.filter(p=>p>=11)){let inv=((p-3)/2)*Math.sin(Math.PI/p);logL-=Math.log(inv);logD2+=Math.log1p((inv*inv-1)/p);logD1+=Math.log1p((inv-1)/p)}
  let logE=logP+Math.min(0,logL+logD1+Math.log1p(logP)),logV=logP+2*logL+logD2;
  stats.formula.push({R,log10P:logP/Math.log(10),log10EoverV:(logE-logV)/Math.log(10),log10Eover100V:(logE-logV)/Math.log(10)-2});
 }
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 function inspect(ev,roots,lo,hi,R){
  if(lo>=hi)return;
  let tab=tables.get(R),a=ev[lo].H/2,b=ev[hi-1].Z/2,G=2*(b-a),U=[],Gf=0,Ff=0,W=0,mf=0,near=0,A0=0,B=0,Znear=0,Dnear=0,C=0;
  let k=Math.floor(Math.sqrt(Math.sqrt(ev[lo].H-1)));if(k<4)return;
  let cnum=9*k-20,den=5*k;
  for(let i=lo;i<hi;i++){
   let v=ev[i],g=v.p-1;C=Math.max(C,v.p);
   if(v.p>R)U.push([v.H/2,v.Z/2]);
   else if(tab.count(v.Z/2)!==tab.count(v.H/2))throw Error("low crossed");
   if(v.near){near++;if(v.D===0&&v.dp<v.d){Znear++;Dnear+=v.d-v.dp}}
   else Gf+=g;
   if(v.a1&&v.p>R){W+=v.p;if(!v.near){Ff+=g;mf++}}
   else if(!v.near&&v.p>R){if(v.p>=47&&v.p>=5*v.d+15&&v.D===0)A0++;else B++}
  }
  let Nroot=roots.filter(t=>t>ev[lo].t&&t<=ev[hi-1].n).length;
  if(cnum*W+den*Ff>den*(Gf+Dnear+2*C)||A0+Znear>Nroot+1)throw Error("far share");
  stats.farShareChecks++;
  let totalNorm=2*tab.P*(tab.count(b)-tab.count(a))/tab.A,periodLoss=Math.max(0,G-totalNorm);
  for(let f of tab.ls){
   let r=checkUnion(tab,f,a,b,U,true);stats.highCoverageChecks++;
   if(totalNorm>G-Gf+Ff+C*(A0+B)+2*f.l*(mf+A0+B+near)+2*r.err+1e-7)throw Error("partition");
   if(cnum*Gf>(den+cnum)*(2*f.l*(mf+near)+(C+2*f.l)*(Nroot+1+B)+periodLoss+2*r.err)+den*2*C+1e-5)throw Error("joint");
   stats.jointChecks++;
  }
  stats.blocks++;
 }
 for(let M=5;M<=N;M+=2){
  stats.roots++;let H=2*M-2,t=M+2,ev=[],roots=[];
  for(let i=0;i<steps;i++){
   if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");
   let a=next(t,H);if(!a){stats.terminal++;break}
   let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,I=(1-a.e)/2,D=dp-6*I,a1=a.p>=47&&a.p>=5*d+15&&D===2*a.p,q=(H-a.e)/a.p,x=(q+a.p)/2,j=(q-a.p)/2,near=x>=64&&2*j*j<=x;
   if(a1)stats.a1++;
   let rt=H/2+3;if(H%4===0&&rt>t&&rt<n)roots.push(rt);if(Z%4===0&&dp===6)roots.push(n);
   ev.push({...a,H,Z,t,n,d,dp,I,D,a1,near});H=Z;t=n;stats.events++;if(i===steps-1)stats.capped++;
  }
  for(let R of tables.keys()){inspect(ev,roots,0,ev.length,R);if(ev.length>=4)inspect(ev,roots,Math.floor(ev.length/2),ev.length,R)}
 }
 return stats
}
console.log(JSON.stringify(audit(Number(process.argv[2]||50000),Number(process.argv[3]||180)),null,2));
