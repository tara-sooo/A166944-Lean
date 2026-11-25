// Long low-label runs and weighted A1 tail recovery.
function audit(N=60000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(x,p)=>(x%p+p)%p;
 const primes=S=>{let a=[];for(let p=3;p<=S;p+=2)if(spf[p]===p)a.push(p);return a};
 const st={roots:0,events:0,a1:0,terminal:0,capped:0,blocks:0,markedBlocks:0,marks:0,lowRunChecks:0,longRuns:0,longZeroChecks:0,shortPaidRuns:0,shortStartChecks:0,shortPrecedingA1:0,shortExceptional:0,allocationChecks:0,nearExclusionChecks:0,conservationChecks:0,tailBounds:0,synthetic:0,periods:[],maxTailWeight:0};
 const tables=[];
 for(let R of [7,11,13,17]){
  let ps=primes(R),P=ps.reduce((a,p)=>a*p,1),pre=new Uint32Array(P+1);
  for(let j=0;j<P;j++)pre[j+1]=pre[j]+(ps.every(p=>mod(j,p)<=(p-3)/2)?1:0);
  let A=pre[P],V=P;
  for(let p of ps.filter(p=>p>=11)){let k=1/(((p-3)/2)*Math.sin(Math.PI/p));V*=k*k*(1+(1/(k*k)-1)/p)}
  const cnt=j=>Math.floor(j/P)*A+pre[mod(j,P)];
  for(let l of [1,2,4,8,16,Math.floor(Math.sqrt(P)),P]){
   let zero=new Uint32Array(P+1),varsum=0;
   for(let j=0;j<P;j++){let c=cnt(j+l)-cnt(j);zero[j+1]=zero[j]+(c===0?1:0);varsum+=(P*c/(A*l)-1)**2}
   let sigma2=varsum/P;
   if(zero[P]/P>sigma2+1e-9||sigma2>4*V/l+1e-9)throw Error("zero variance");
   const zcnt=j=>Math.floor(j/P)*zero[P]+zero[mod(j,P)];
   tables.push({R,P,A,l,V,cnt,zcnt,sigma2});
   st.periods.push({R,P,l,zeros:zero[P],sigma2,V});
  }
 }
 function checkLong(tab,a,b,runs){
  let {P,l,zcnt,sigma2,V,cnt}=tab,ln=0,interior=0;
  for(let [x,y] of runs){
   if(y-x<2*l)continue;
   if(cnt(y)!==cnt(x))throw Error("low barrier");
   let v=y-x-l+1;
   if(zcnt(y-l+1)-zcnt(x)!==v)throw Error("zero run");
   interior+=v;ln+=y-x;st.longRuns++;st.longZeroChecks++;
  }
  let z=zcnt(b)-zcnt(a);
  if(ln>2*interior||interior>z||z>(b-a+P)*sigma2+1e-7||2*ln>16*(b-a+P)*V/l+1e-6)throw Error("long budget");
  return 2*ln;
 }
 let seed=19;function rand(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n}
 for(let tab of tables){
  for(let z=0;z<60;z++){
   let a=rand(tab.P*2)-tab.P,b=a+1+rand(tab.P),runs=[],x=a;
   while(x<b){let y=x+1;while(y<b&&tab.cnt(y+1)===tab.cnt(x))y++;if(tab.cnt(y)===tab.cnt(x))runs.push([x,y]);x=y}
   checkLong(tab,a,b,runs);st.synthetic++;
  }
 }
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 function inspect(ev,roots,lo,hi,tab,T,witness=false){
  if(lo>=hi)return;
  let {R,P,l,V,cnt}=tab;
  let k=Math.floor(Math.sqrt(Math.sqrt(ev[lo].H-1)));if(k<4)return;
  // T/5-20*l-9 is the exact lower bound on 2*p_prev for a short run.
  const minPrev=(T/5-20*l-9)/2;
  if(minPrev<=1)return;
  let den=5*k,cnum=9*k-20,m=0,W=0,C=0,G=0,B=0,A0=0,Z=0,near=0,highDrop=0,resetDrop=0;
  let pend=[],paid=0,paidHigh=0,paidReset=0,paidLow=0;
  let runs=[],run=null,runPaid=0,shortPaid=0,longPaid=0,shortA=0,shortOther=0,shortFirst=0;
  function close(){
   if(!run)return;
   let gain=run.z-run.h;
   if(cnt(run.z/2)!==cnt(run.h/2)||runPaid>gain*den)throw Error("run capacity");
   runs.push([run.h/2,run.z/2]);st.lowRunChecks++;
   if(gain>=4*l)longPaid+=runPaid;
   else if(runPaid){
    shortPaid+=runPaid;st.shortPaidRuns++;
    if(run.x0+5*gain<T/5-1e-8)throw Error("short start");
    st.shortStartChecks++;
    if(run.prev<lo)shortFirst++;
    else if(ev[run.prev].a1){
     let p=ev[run.prev].p;
     if(p<minPrev-1e-8)throw Error("preceding mark");
     shortA++;st.shortPrecedingA1++;
    }else{shortOther++;st.shortExceptional++}
   }
   run=null;runPaid=0;
  }
  for(let i=lo;i<hi;i++){
   let v=ev[i],g=v.p-1,x=(v.d+3)*den,y=(v.dp+3)*den;
   G+=g;C=Math.max(C,v.p);
   if(v.near)near++;
   if(v.p>R){
    close();
    if(!v.near&&!v.a1){if(v.p>=47&&v.p>=5*v.d+15&&v.D===0)A0++;else B++}
   }else{
    if(!run)run={h:v.H,z:v.Z,x0:v.d+3,prev:i-1};
    run.z=v.Z;
    if(v.d+3>run.x0+5*(v.H-run.h)||v.dp+3>run.x0+5*(v.Z-run.h))throw Error("upward budget");
   }
   if(v.a1&&v.p>R&&v.p>=T){
    let a=k*v.p,b=(10*k-20)*v.p;
    if(!(x<=a&&a<b&&b<=y)||pend.some(o=>Math.min(b,o.b)>Math.max(a,o.a)))throw Error("pending overlap");
    pend.push({a,b,p:v.p});m++;W+=v.p;
   }
   if(y>=x)continue;
   const reset=v.D===0,drop=v.d-v.dp;
   if(reset){Z++;resetDrop+=drop}
   else if(v.p>R&&!v.near)highDrop+=drop;
   let left=[],length=0;
   for(let o of pend){
    if(o.b>x)throw Error("pending above");
    let a=Math.max(o.a,y),b=Math.min(o.b,x);
    if(b>a){
     if(!reset&&v.near)throw Error("near recovery");
     if(!reset)st.nearExclusionChecks++;
     if(v.p<=R&&(!run||x/den<T/5-1e-8))throw Error("low recovery");
     length+=b-a;
    }
    if(Math.min(o.b,y)>o.a)left.push({...o,b:Math.min(o.b,y)});
   }
   pend=left;
   if(length>drop*den)throw Error("allocation");
   paid+=length;
   // Assign resets separately even when low label, so low supply is nonreset only.
   if(reset)paidReset+=length;
   else if(v.p>R)paidHigh+=length;
   else{paidLow+=length;runPaid+=length}
   st.allocationChecks++;
  }
  close();st.blocks++;
  if(!m)return;
  st.markedBlocks++;st.marks+=m;st.maxTailWeight=Math.max(st.maxTailWeight,W);
  let pending=pend.reduce((a,o)=>a+o.b-o.a,0),Nroot=roots.filter(t=>t>ev[lo].t&&t<=ev[hi-1].n).length;
  if(paid+pending!==cnum*W||paid!==paidHigh+paidLow+paidReset||paidLow!==shortPaid+longPaid||pending>2*C*den||paidHigh>den*highDrop||paidReset>den*resetDrop)throw Error("conservation");
  if(Z>Nroot+1||shortOther>near+A0+B||A0>Nroot+1||shortFirst>1)throw Error("exception count");
  let a=ev[lo].H/2,b=ev[hi-1].Z/2,LG=checkLong(tab,a,b,runs);
  let prevCount=ev.slice(lo,hi).filter(v=>v.a1&&v.p>R&&v.p>=minPrev-1e-8).length;
  if(shortA>prevCount||prevCount>G/(minPrev-1)+1e-6||longPaid>LG*den||shortPaid>4*l*den*(shortA+shortOther+shortFirst))throw Error("short budget");
  let rhs=LG+4*l*(G/(minPrev-1)+near+Nroot+2+B)+C*(Nroot+1+B)+2*C;
  if(cnum*W>den*rhs+1e-6)throw Error("tail budget");
  st.conservationChecks++;st.tailBounds++;
 }
 for(let M=5;M<=N;M+=2){
  st.roots++;let H=2*M-2,t=M+2,ev=[],roots=[];
  for(let i=0;i<steps;i++){
   if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");
   let a=next(t,H);if(!a){st.terminal++;break}
   let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,I=(1-a.e)/2,D=dp-6*I,a1=a.p>=47&&a.p>=5*d+15&&D===2*a.p,q=(H-a.e)/a.p,x=(q+a.p)/2,j=(q-a.p)/2,near=x>=64&&2*j*j<=x;
   if(a1)st.a1++;
   let rt=H/2+3;if(H%4===0&&rt>t&&rt<n)roots.push(rt);if(Z%4===0&&dp===6)roots.push(n);
   ev.push({...a,H,Z,t,n,d,dp,I,D,a1,near});H=Z;t=n;st.events++;if(i===steps-1)st.capped++;
  }
  if(ev.length)for(let tab of tables.filter(v=>v.R<=13&&v.l<=4))for(let T of [151,251,401,601]){
   if(T/5-20*tab.l-9<=2)continue;
   inspect(ev,roots,0,ev.length,tab,T);if(ev.length>=4)inspect(ev,roots,Math.floor(ev.length/2),ev.length,tab,T);
  }
 }

 // Exact two-event CRT witness: large A1 then a short low-label recovery.
 let p=1001;while(spf[p]!==p||p%4!==3||p%3!==1||p%7!==5||(2*p-3)%49===0)p+=2;
 let H=0n,P=4n;
 for(let s of primes(3*p+6)){
  let r=0;
  if(s===p)r=1;
  else if(s===7)r=mod(-p,s);
  else {while(r===1||r===s-1||((2*p-3)%s===0&&(r+p)%s===0))r++;if(r>=s)throw Error("CRT residues")}
  let L=BigInt(s),a=Number(P%L),b=s,u=1,v=0;
  while(b){let q=Math.floor(a/b);[a,b]=[b,a-q*b];[u,v]=[v,u-q*v]}
  if(a!==1)throw Error("CRT inverse");
  H+=P*BigInt(mod(u*mod(r-Number(H%L),s),s));P*=L;
 }
 if(H<4000000000000000n)H+=P;
 let H0=H,t=H/2n+3n,relative=0,actual=[];
 function literal(w,label){
  let d=Number(2n*t-H),n=t+BigInt(w);
  for(let j=1;j<=w;j++){let tick=t+BigInt(j),e=tick%2n?-1n:1n,a=e===1n?tick:tick-2n,b=H-e;while(b)[a,b]=[b,a%b];if(a!==(j===w?BigInt(label):1n))throw Error("literal CRT");}
  let Z=H+BigInt(label-1),dp=Number(2n*n-Z),I=Number(n%2n),D=dp-6*I;
  if(BigInt(label)**2n>H+1n)throw Error("eligibility");
  actual.push({p:label,w,H,Z,t:relative,n:relative+w,d,dp,I,D,a1:label>=47&&label>=5*d+15&&D===2*label,near:false});
  H=Z;t=n;relative+=w;
 }
 literal((3*p-7)/2,p);literal(1,7);
 if(!actual[0].a1||actual[1].dp!==2*p-4||actual[1].D<=0)throw Error("witness recovery");
 let before={shortPaid:st.shortPaidRuns,shortA:st.shortPrecedingA1,bounds:st.tailBounds,long:st.longRuns};
 for(let tab of tables.filter(t=>t.R<=13&&t.l<=4)){
  let M=2n*BigInt(tab.P),base=4000000000000000n+((H0-4000000000000000n)%M+M)%M;
  if(base>H0||Math.floor(Math.sqrt(Math.sqrt(Number(base)-1)))<=4*p)throw Error("conservative lower horizon");
  // Translation preserves H-barrier residues, and lowers the horizon for the
  // conservative far-only recovery interval. Actual ticks verified above.
  let ev=actual.map(v=>({...v,H:Number(base+v.H-H0),Z:Number(base+v.Z-H0)}));
  inspect(ev,[],0,ev.length,tab,601,true);
 }
 st.witness={p,labels:[p,7],rootDigits:(H0/2n+1n).toString().length,ticks:relative,ordinaryDrop:4,shortPaid:st.shortPaidRuns-before.shortPaid,shortPrecedingA1:st.shortPrecedingA1-before.shortA,tailBounds:st.tailBounds-before.bounds,longRuns:st.longRuns-before.long};
 if(st.witness.shortPaid===0||st.witness.shortPrecedingA1===0||st.witness.longRuns===0)throw Error("witness coverage");

 return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000),Number(process.argv[3]||180)),null,2));
