// Lower recovery levels exclude short low runs following A1 or near nonresets.
function audit(N=120000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(x,p)=>(x%p+p)%p;
 const primes=R=>{let a=[];for(let p=3;p<=R;p+=2)if(spf[p]===p)a.push(p);return a};
 const st={roots:0,events:0,stopped:0,capped:0,a1:0,blocks:0,markedBlocks:0,marks:0,allocations:0,paymentChecks:0,lowRuns:0,shortPaid:0,shortB:0,shortReset:0,longPaid:0,priorA1Checks:0,priorNearChecks:0,initialRunChecks:0,budgetChecks:0,barrierChecks:0,formulaChecks:0,synthetic:0,witness:[]};
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 let tables=new Map();
 for(let R of [7,11,13,17]){
  let ps=primes(R),P=ps.reduce((a,p)=>a*p,1),pre=new Uint32Array(P+1),V=P;
  for(let j=0;j<P;j++)pre[j+1]=pre[j]+(ps.every(p=>mod(j,p)<=(p-3)/2)?1:0);
  let A=pre[P];for(let p of ps.filter(p=>p>=11)){let k=1/(((p-3)/2)*Math.sin(Math.PI/p));V*=k*k*(1+(1/k**2-1)/p)}
  const count=j=>Math.floor(j/P)*A+pre[mod(j,P)];
  tables.set(R,{P,V,count});
 }
 function inspect(ev,roots,lo,hi,R,T,witness=false){
  if(lo>=hi)return;
  let tb=tables.get(R),l=Math.floor(T/24);
  if(tb)l=Math.min(l,tb.P);
  if(T<48||l<1||ev[lo].H<4097)return;
  let marks=0,W=0,G=0,C=0,B=0,Z=0,pend=[],paid=0,paidHigh=0,paidReset=0,paidLong=0,paidShort=0,run=null,runs=[],shortB=0,shortZ=0,nearChecks=0,a1Checks=0;
  // Units are fifths of one ordinary-deficit unit.
  function close(){
   if(!run)return;
   let g=run.g;st.lowRuns++;
   if(tb){
    if(tb.count(run.end/2)!==tb.count(run.start/2))throw Error("low horizon barrier");
    st.barrierChecks++;
   }
   if(run.pay>5*g)throw Error("low run capacity");
   if(g>=4*l){paidLong+=run.pay;if(run.pay)st.longPaid++}
   else if(run.pay){
    if(run.prev<lo)throw Error("initial low run payment");
    let v=ev[run.prev];
    if(v.a1||v.near&&v.D!==0)throw Error("short run exclusion");
    if(v.D===0){shortZ++;st.shortReset++}else{shortB++;st.shortB++}
    paidShort+=run.pay;st.shortPaid++;
   }
   runs.push(g);run=null;
  }
  for(let i=lo;i<hi;i++){
   let v=ev[i],g=v.p-1,x=5*(v.d+3),y=5*(v.dp+3);
   G+=g;C=Math.max(C,v.p);
   if(v.p>R){
    close();
    if(!v.near&&!v.a1&&v.D!==0)B++;
   }else{
    if(!run)run={prev:i-1,start:v.H,end:v.Z,g:0,pay:0,x0:x};
    run.g+=g;run.end=v.Z;
   }
   if(v.a1&&v.p>R&&v.p>=T){
    let a=v.p,b=5*v.p;
    if(x>a||y<b||pend.some(o=>Math.min(b,o.b)>Math.max(a,o.a)))throw Error("upward allocation");
    pend.push({a,b,p:v.p,i});W+=v.p;marks++;
   }
   if(y>=x)continue;
   let reset=v.D===0,drop=v.d-v.dp;if(reset)Z++;
   let length=0,left=[];
   for(let o of pend){
    if(o.b>x)throw Error("pending above");
    let a=Math.max(y,o.a),b=Math.min(x,o.b);
    if(b>a){
     length+=b-a;st.paymentChecks++;
     if(!reset&&v.near)throw Error("near payment");
     if(!reset&&v.p<=R){
      if(!run||run.prev<lo||run.prev<o.i)throw Error("initial or early run");
      st.initialRunChecks++;
      let u=ev[run.prev];
      if(u.a1){
       // If a later A1, the pending level is below its pre-state.
       if(run.prev!==o.i&&(5*(u.d+3)<b||u.p<5*(b/5)))throw Error("later A1 bound");
       if(run.x0<2*b||run.g*5<run.x0-b||run.g*5<=o.p)throw Error("A1 run length");
       a1Checks++;st.priorA1Checks++;
      }
      if(u.near&&u.D!==0){
       if(4*u.p<3*o.p||2*run.x0<3*b||5*run.g<run.x0-b||10*run.g<o.p)throw Error("near precursor length");
       nearChecks++;st.priorNearChecks++;
      }
     }
    }
    if(Math.min(o.b,y)>o.a)left.push({...o,b:Math.min(o.b,y)});
   }
   pend=left;
   if(length>5*drop)throw Error("event capacity");
   paid+=length;
   if(reset)paidReset+=length;else if(v.p>R)paidHigh+=length;else run.pay+=length;
   st.allocations++;
  }
  close();st.blocks++;
  if(!marks)return;
  st.markedBlocks++;st.marks+=marks;
  let pending=pend.reduce((a,o)=>a+o.b-o.a,0),Nroot=roots.filter(t=>t>ev[lo].t&&t<=ev[hi-1].n).length;
  let LG=runs.filter(g=>g>=4*l).reduce((a,b)=>a+b,0);
  if(paid+pending!==4*W||paid!==paidHigh+paidReset+paidLong+paidShort||pending>10*C||Z>Nroot+1||shortZ>Nroot+1||shortB>B||paidHigh>5*C*B||paidReset>5*C*(Nroot+1)||paidLong>5*LG||paidShort>20*l*(B+Nroot+1))throw Error("conservation");
  if(4*W>5*(LG+(C+4*l)*(Nroot+B+1)+2*C))throw Error("finite tail budget");
  st.budgetChecks++;
  if(tb){
   if(l===tb.P&&LG!==0||LG>16*(G/2+tb.P)*tb.V/l+1e-6)throw Error("long capacity");
   let rhs=960*(G/2+tb.P)*tb.V/T+1.25*((7/6)*C*(Nroot+B+1)+2*C);
   if(W>rhs+1e-6)throw Error("closed form");
   st.formulaChecks++;
  }
  if(witness)st.witness.push({R,T,l,W,marks,B,Nroot,paid:paid/5,paidLong:paidLong/5,paidShort:paidShort/5,pending:pending/5,LG,shortB,shortZ,a1Checks,nearChecks});
 }
 for(let M=5;M<=N;M+=2){
  st.roots++;let H=2*M-2,t=M+2,ev=[],roots=[];
  for(let i=0;i<steps;i++){
   if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");
   let a=next(t,H);if(!a){st.stopped++;break}
   let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,I=(1-a.e)/2,D=dp-6*I,a1=a.p>=47&&a.p>=5*d+15&&D===2*a.p,q=(H-a.e)/a.p,x=(q+a.p)/2,j=(q-a.p)/2,near=x>=64&&2*j*j<=x;
   if(a1)st.a1++;
   let rt=H/2+3;if(H%4===0&&rt>t&&rt<n)roots.push(rt);if(Z%4===0&&dp===6)roots.push(n);
   ev.push({...a,H,Z,t,n,d,dp,I,D,a1,near});H=Z;t=n;st.events++;if(i===steps-1)st.capped++;
  }
  if(ev.some(v=>v.a1))for(let R of [7,11,13,17,47,71])for(let T of [48,96,151,251,401]){
   inspect(ev,roots,0,ev.length,R,T);
   if(ev.length>=4)inspect(ev,roots,Math.floor(ev.length/2),ev.length,R,T);
  }
 }
 // Four actual events: the first is A1; two fast nonresets bring x below p;
 // the last label7 gives a four-unit recovery at wait1.
 const word=[10039,6709,4513,7],p=word[0],r=word[2],sh=[0];
 for(let v of word)sh.push(sh.at(-1)+v-1);
 let H=0n,P=4n,crt=0;
 for(let s of primes(3*p+6)){
  let at=word.indexOf(s),rr=at>=0?mod((at===3?-1:1)-sh[at],s):0;
  const valid=x=>sh.slice(0,3).every((h,i)=>word[i]===s?mod(x+h,s)===1:![1,s-1].includes(mod(x+h,s)))&&(s!==7||mod(x+sh[3],s)===s-1)&&((2*r-3)%s!==0||s===7||mod(x+sh[3],s)!==s-1);
  if(at>=0){if(!valid(rr))throw Error("CRT selected")}
  else{while(rr<s&&!valid(rr))rr++;if(rr===s)throw Error("CRT empty")}
  let L=BigInt(s),a=Number(P%L),b=s,u=1,v=0;while(b){let q=Math.floor(a/b);[a,b]=[b,a-q*b];[u,v]=[v,u-q*v]}
  if(a!==1)throw Error("CRT inverse");H+=P*BigInt(mod(u*mod(rr-Number(H%L),s),s));P*=L;crt+=4;
 }
 if(H<100000000n)H+=P;
 let H0=H,t=H/2n+3n,rel=0,ev=[];
 for(let i=0;i<word.length;i++){
  let p=word[i],d=Number(2n*t-H),w=i===3?1:(3*p-d-1)/2,n=t+BigInt(w);
  for(let j=1;j<=w;j++){let tick=t+BigInt(j),e=tick%2n?-1n:1n,a=e===1n?tick:tick-2n,b=H-e;while(b)[a,b]=[b,a%b];if(a!==(j===w?BigInt(p):1n))throw Error("literal")}
  let Z=H+BigInt(p-1),dp=Number(2n*n-Z),I=Number(n%2n),D=dp-6*I;
  if(BigInt(p)**2n>H+1n)throw Error("eligibility");
  ev.push({p,w,d,dp,I,D,H,Z,t:rel,n:rel+w,a1:p>=47&&p>=5*d+15&&D===2*p,near:false});H=Z;t=n;rel+=w;
 }
 for(let R of [7,11,13,17,7000]){
  let tb=tables.get(R),M=tb?2n*BigInt(tb.P):4n,base=100000000n+((H0-100000000n)%M+M)%M;
  if(base>H0)throw Error("lower horizon");
  inspect(ev.map(v=>({...v,H:Number(base+v.H-H0),Z:Number(base+v.Z-H0)})),[],0,ev.length,R,10000,true);
 }
 if(!st.witness.some(w=>w.shortB>0)||!st.witness.some(w=>w.a1Checks>0))throw Error("witness coverage");
 st.witnessInfo={word,rootDigits:(H0/2n+1n).toString().length,ticks:rel,crt,postDeficits:ev.map(v=>v.dp)};
 // Arithmetic controls for the two precursor types, not simulated MIN paths.
 for(let p=48;p<2000;p++)for(let j=1;j<=10;j++){
  let y=p/5+4*p/5*j/10,l=Math.floor(p/24);
  if(2*p-y<=4*l||10*y-y<=4*l||1.5*p-y<=4*l)throw Error("synthetic separation");
  st.synthetic++;
 }
 return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||120000),Number(process.argv[3]||180)),null,2));
