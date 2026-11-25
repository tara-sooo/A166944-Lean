// Short paired RESET halo and long canonical age audit. Finite parameters.
function audit(X,stress=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),H=T+B,Q=Math.max(5,Math.ceil(B/10)),lo=2*X-2,hi=7*X,lim=hi+B+20,L=stress?32:16,kappa=stress?3:2,M=stress?24:8,Z=stress?B:Math.ceil(B/2);
 const spf=new Int32Array(lim),r=new Int32Array(lim),fail=(b,s)=>{if(!b)throw Error(X+" "+s)},mod=(a,m)=>((a%m)+m)%m;
 function gcd(a,b){while(b){let t=a%b;a=b;b=t}return a}
 for(let p=2;p<lim;p++)if(!spf[p]){spf[p]=p;if(p*p<lim)for(let j=p*p;j<lim;j+=p)if(!spf[j])spf[j]=p}
 function factors(n){let a=[];while(n>1){let p=spf[n];if(p!==2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const labels=new Map();for(let C=lo;C<=hi;C+=2){let a=factors(C-1),b=factors(C+1);r[C]=Math.min(a[0]||B+1,b[0]||B+1);labels.set(C,[...a.map(p=>[p,-1]),...b.map(p=>[p,1])]);}
 const phase=(p,s)=>s===-1?0:p+2,high=(C,p)=>p>=Q&&r[C]>3&&2*r[C]>p;
 const paths=[],groups=new Map(),slots=new Map(),centres=new Set();let N=0,events=0,raw=0,rawHigh=0,resetRaw=0,literal=0,canonicalChecks=0,virtual=0,resetCount=0,ageLong=0,agePaid=0,ageSum=0,bridgeChecks=0,pairCount=0;
 const sk=a=>`${a.C}|${a.p}|${a.v}`,pk=(a,b)=>`${a.C}|${a.p}|${b.C-a.J}|${b.p}`;
 for(let root=X;root<2*X;root++)if(spf[root]===root){
  N++;let t=root+2,C=2*root-2,C0=C,cut=Math.floor((7*root-1)/4),es=[],canonical=[{C,t}],lastReset=null,prevLongEnd=-1,totalAge=0;
  while(C-C0<T){
   let v=Infinity,p=0,s=0;for(let [q,sg] of labels.get(C)){let j=t+1+mod(phase(q,sg)-t-1,2*q);if(j<v||(j===v&&q<p)){v=j;p=q;s=sg}}
   if(X<=1024){let vv=Infinity,pp=0;for(let j=t+1;j<=Math.min(cut,t+2*B);j++){let g=j%2?gcd(j-2,C+1):gcd(j,C-1),q=factors(g)[0];if(q){vv=j;pp=q;break}}fail((!p||v>cut)?vv===Infinity:vv===v&&pp===p,"literal MIN");literal++}
   if(!p||v>cut)break;
   let w=v-t,J=C+p-1,k=(2*v-J-6*(v%2))/(2*p),hh=high(C,p),a={C,t,v,p,s,w,J,k,high:hh,mark:false,age:false};
   fail(w<=2*r[C]&&w<=3*(p-1)&&Number.isInteger(k),"clock and phase");
   let can=C/2+3;if(C%4===0&&can>=t&&can<v&&can>canonical[canonical.length-1].t){canonical.push({C,t:can});if(can>t)virtual++;}
   if(hh){rawHigh+=w;slots.set(sk(a),(slots.get(sk(a))||0)+1);if(k===0){
     resetRaw+=w;resetCount++;let c=canonical[canonical.length-1];fail(c.t<v&&c.C%4===0&&2*c.t-c.C===6,"prior canonical");
     if(lastReset){fail(c.t>=lastReset.v,"canonical between resets");fail(canonical.some(x=>x.t>=lastReset.v&&x.t<=lastReset.v+7),"bridge");bridgeChecks++;}
     let age=v-c.t;fail(age>=1&&c.t>=prevLongEnd,"disjoint age interval");prevLongEnd=v;totalAge+=age;ageSum+=age;canonicalChecks++;
     if(age>Z){a.age=true;ageLong++;agePaid+=w;}
     lastReset=a;
   }}
   es.push(a);events++;raw+=w;C=J;t=v;
   if(C%4===0&&2*t-C===6&&t>canonical[canonical.length-1].t)canonical.push({C,t});
  }
  fail(totalAge<=t-(root+2),"total age");
  let prev=-1;for(let i=0;i<es.length;i++)if(es[i].high){if(prev>=0){let a=es[prev],b=es[i],e=b.C-a.J;if(a.k===0&&b.k===0&&e<=L&&a.p>L+3){
    fail(a.p!==b.p&&e>=0&&e%2===0,"short pair");
    let z=pk(a,b),g=groups.get(z)||{a,b,n:0,rootMin:root,rootMax:root};fail(g.a.v===a.v&&g.b.v===b.v,"unique reset slots");g.n++;g.rootMin=Math.min(g.rootMin,root);g.rootMax=Math.max(g.rootMax,root);groups.set(z,g);pairCount++;centres.add(`${a.C}|${a.p}`);
   }}prev=i;}
  paths.push({root,es});
 }
 const support=new Set();let formChecks=0,roughChecks=0,crtChecks=0;
 for(let z of centres){let [C,p]=z.split("|").map(Number),s=labels.get(C).find(([a])=>a===p)[1];for(let e=0;e<=L;e+=2){let A=C+p-1+e;if(!labels.has(A))continue;
   for(let [q,t] of labels.get(A))if(high(A,q)){
     fail(p!==q,"distinct q");let a=(C+s)/p,forms=[a,C-s,A-1,A+1];fail(forms.every(Number.isInteger),"four forms");formChecks++;
     for(let d=3;d<Math.min(p/2,q/2);d+=2)if(spf[d]===d){fail(forms.every(f=>f%d!==0),"four rough forms");roughChecks++}
     let c=mod(C,p*q);fail((c+s)%p===0&&(c+p-1+e+t)%q===0,"CRT");crtChecks++;
     support.add(`${C}|${p}|${e}|${q}`);
   }
 }}
 let eligible=new Set(),heavy=0,maxMass=0,capSum=0,eligibleMass=0,heavyMass=0,oldRootChecks=0;
 for(let [z,g] of groups){fail(support.has(z),"actual pattern support");fail(g.n<=slots.get(sk(g.a))&&g.n<=slots.get(sk(g.b)),"endpoint mass");let cap=M*B/(g.a.p+g.b.p);maxMass=Math.max(maxMass,g.n);
  if(g.n<=cap){eligible.add(z);capSum+=cap*(g.a.p+g.b.p);eligibleMass+=g.n}else{heavy++;heavyMass+=g.n;fail(g.rootMax-g.rootMin>=2*(g.n-1),"root span");oldRootChecks++;}
 }
 let haloBudget=0,marked=0,paid=0,paidHigh=0,paidReset=0,paidOther=0,ageExtra=0,remaining=0,heavyPairInc=0,coveredPairs=0;
 for(let {es} of paths){let prev=-1,hs=[],chosen=[];
  for(let i=0;i<es.length;i++)if(es[i].high){if(prev>=0){let a=es[prev],b=es[i],z=pk(a,b);if(a.k===0&&b.k===0&&groups.has(z)){
   if(eligible.has(z)){let h=[a.C-kappa*a.p,b.J+kappa*b.p];hs.push(h);haloBudget+=3*(h[1]-h[0]);chosen.push([prev,i]);}
   else heavyPairInc++;
  }}prev=i;}
  for(let a of es){if(hs.some(h=>h[0]<=a.C&&a.J<=h[1])){a.mark=true;marked++;paid+=a.w;if(a.high){paidHigh+=a.w;if(a.k===0)paidReset+=a.w}else paidOther+=a.w;}
   if(a.age&&!a.mark)ageExtra+=a.w;
   if(a.high&&!a.age&&!a.mark)remaining+=a.w;
  }
  for(let [i,j] of chosen){for(let k=i;k<=j;k++)fail(es[k].mark,"pair complete coverage");coveredPairs++;}
 }
 fail(paid===paidHigh+paidOther&&paid<=haloBudget&&paidHigh+ageExtra+remaining===rawHigh,"union partition");
 return {X,B,T,Q,L,kappa,M,Z,N,events,raw,rawHigh,resetRaw,literal,canonicalChecks,virtual,resetCount,ageLong,agePaid,ageSum,bridgeChecks,pairCount,groups:groups.size,support:support.size,formChecks,roughChecks,crtChecks,eligible:eligible.size,eligibleMass,heavy,heavyMass,maxMass,oldRootChecks,haloBudget,marked,paid,paidHigh,paidReset,paidOther,ageExtra,remaining,heavyPairInc,coveredPairs};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536])) console.log(JSON.stringify(audit(X)));console.log(JSON.stringify(audit(65536,true)));
