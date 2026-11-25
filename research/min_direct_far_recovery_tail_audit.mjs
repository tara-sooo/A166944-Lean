// Far-only deficit recovery, weighted A1 tail and joint horizon capacity.
function audit(N=60000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 let s={nearResetShareChecks:0,combinedRootChecks:0,roundedBlocks:0,roundedSlots:0,roundedMatches:0,roundedExceptions:0,roundedFarChecks:0,roots:0,events:0,a1:0,terminal:0,capped:0,blocks:0,markedBlocks:0,marks:0,nearMarks:0,nearPairChecks:0,intervalChecks:0,allocationChecks:0,denseChecks:0,tailMarks:0,tailSlots:0,tailMatched:0,tailBounds:0,farShareChecks:0,jointChecks:0,lowBandChecks:0,periods:[],witness:[]};
 const tables={};
 for(let R of [5,7,11,13]){
  let ps=[];for(let p=3;p<=R;p+=2)if(spf[p]===p)ps.push(p);
  let P=ps.reduce((a,p)=>a*p,1);
  for(let kind of ["H","d"]){
   let pre=new Uint32Array(P+1);
   for(let j=0;j<P;j++)pre[j+1]=pre[j]+(ps.every(p=>kind==="H"?mod(j,p)<=(p-3)/2:p===3||[0,1].every(I=>{let r=mod(2*j-6*I,2*p);return r<2||r>p-3}))?1:0);
   let A=pre[P],mn=0,mx=0;
   for(let j=0;j<=P;j++){let a=P*pre[j]-A*j;mn=Math.min(mn,a);mx=Math.max(mx,a)}
   let D=mx-mn;
   function count(j){return Math.floor(j/P)*A+pre[mod(j,P)]}
   tables[kind+R]={P,A,D,count};
   s.periods.push({R,kind,P,A,discrepancy:D/A})
  }
 }
 function inspect(ev,roots,lo,hi,R,S,A0,geometry=true,asWitness=false){
  if(lo>=hi||A0<257)return;
  let k=Math.floor(Math.sqrt(Math.sqrt(A0-1)));while((k+1)**4<=A0-1)k++;while(k**4>A0-1)k--;
  if(k<4)return;
  let den=5*k,cnum=9*k-20,C=0,G=0,Gfar=0,Nnear=0,FF=0,mf=0,m=0,W=0,tailW=0,tailm=0,nearMark=0;
  let rd=tables["d"+R],sd=tables["d"+S],ht=tables["H"+R],T=Math.max(R+1,Math.ceil(4*rd.D/rd.A+8));
  const cnt=(tab,x)=>tab.count(Math.floor((x-3*den)/(2*den))+1);
  const nslots=(tab,a,b)=>cnt(tab,b)-cnt(tab,a);
  let pending=[],paid=0,resetPaid=0,farPaid=0,tailSlots=0,tailMatched=0,smallSlots=0,smallPaid=0,smallLost=0;
  let Dreset=0,Z=0,DnearReset=0,Znear=0,A0far=0,Bhigh=0,Dhigh=0,Jhigh=0,F=0,j=0,allFarDrop=0,otherCap=0,otherCount=0;
  for(let i=lo;i<hi;i++){
   const v=ev[i],g=v.p-1,x=(v.d+3)*den,y=(v.dp+3)*den;
   C=Math.max(C,v.p);G+=g;if(v.near)Nnear++;else Gfar+=g;
   if(!v.near&&v.p>R&&!(v.a1&&v.p>R)){otherCap+=g;otherCount++;if(v.p>=47&&v.p>=5*v.d+15&&v.D===0)A0far++;else Bhigh++}
   if(v.a1&&v.p>R){
    let a=k*v.p,b=(10*k-20)*v.p,tail=v.p>=T;
    if(!(x<=a&&a<b&&b<=y)||pending.some(o=>Math.min(b,o.b)>Math.max(a,o.a)))throw Error("mark interval");
    pending.push({a,b,tail,p:v.p});m++;W+=v.p;
    if(v.near)nearMark++;else{FF+=g;mf++}
    if(tail){tailW+=v.p;tailm++;tailSlots+=nslots(rd,a,b)}
    smallSlots+=nslots(sd,a,b);
    s.intervalChecks++;
   }
   if(y>=x)continue;
   let reset=v.D===0,drop=v.d-v.dp;
   if(reset){Dreset+=drop;Z++;if(v.near){DnearReset+=drop;Znear++}}
   else if(!v.near){
    allFarDrop+=drop;
    if(v.p>R){Dhigh+=drop;Jhigh++}
    if(v.p>S&&v.p<=R){F+=drop;j++}
   }
   let aLen=0,aTail=0,aSmall=0,remain=[];
   for(let o of pending){
    if(o.b>x)throw Error("pending above pre");
    let a=Math.max(o.a,y),b=Math.min(o.b,x);
    if(b>a){
     if(!reset&&v.near)throw Error("near paid");
     if(!reset&&v.p>=o.p)throw Error("smaller label");
     aLen+=b-a;let nr=o.tail?nslots(rd,a,b):0,ns=nslots(sd,a,b);
     if(nr&&v.p<=R||ns&&v.p<=S)throw Error("cut lower bound");
     aTail+=nr;aSmall+=ns;s.denseChecks++;
     if(reset||v.p>R)smallLost+=ns;else{if(ns&&v.p<=S)throw Error("low");smallPaid+=ns}
    }
    if(Math.min(o.b,y)>o.a)remain.push({...o,b:Math.min(o.b,y)});
   }
   pending=remain;paid+=aLen;tailMatched+=aTail;
   if(reset)resetPaid+=aLen;else farPaid+=aLen;
   if(aLen>drop*den||2*aTail>drop||2*aSmall>drop||2*rd.P*aTail>rd.A*drop+2*rd.D||2*sd.P*aSmall>sd.A*drop+2*sd.D)throw Error("capacity");
   s.allocationChecks++;
  }
  if(!m)return;
  let pendingLen=0,pendTail=0,pendSmall=0;
  for(let o of pending){pendingLen+=o.b-o.a;pendSmall+=nslots(sd,o.a,o.b);if(o.tail)pendTail+=nslots(rd,o.a,o.b)}
  if(paid+pendingLen!==cnum*W||pendingLen>2*C*den||tailMatched+pendTail!==tailSlots||smallPaid+smallLost+pendSmall!==smallSlots)throw Error("conservation");
  let Nroot=roots.filter(t=>t>ev[lo].t&&t<=ev[hi-1].n).length;
  if(Z>Nroot+1||cnum*W+den*FF>den*(Gfar+Dreset+2*C)||farPaid>den*allFarDrop||resetPaid>den*Dreset)throw Error("far share");
  s.farShareChecks++;
  if(cnum*W+den*FF>den*(Gfar+DnearReset+2*C)||A0far+Znear>Nroot+1)throw Error("near reset share");
  s.nearResetShareChecks++;s.combinedRootChecks++;
  // Normalized dense discrepancy and tail upper bound, exact integer arithmetic.
  if(2*rd.P*tailSlots*den<rd.A*cnum*tailW-(2*rd.D+2*rd.A)*tailm*den)throw Error("tail density");
  let tailUpper=(2*rd.D+2*rd.A)*tailm+rd.A*(Dhigh+Dreset+2*C+2)+2*rd.D*(Jhigh+Z+1);
  if(rd.A*cnum*tailW>den*tailUpper)throw Error("tail upper");
  s.tailBounds++;
  let sdLoss=sd.A*(Dhigh+Dreset+2*C+2)+2*sd.D*(Jhigh+Z+1);
  let target=sd.A*cnum*W-(2*sd.D+2*sd.A)*m*den-sdLoss*den;
  if(den*(sd.A*F+2*sd.D*j)<target||den*sd.P*F<target)throw Error("lower band");
  s.lowBandChecks++;
  if(geometry){
   let H0=ev[lo].H,H1=ev[hi-1].Z,total=ht.count(H1/2)-ht.count(H0/2),sum=0,nearCap=0,farA1Cap=0,other=0;
   for(let i=lo;i<hi;i++){
    let v=ev[i],b=ht.count(v.Z/2)-ht.count(v.H/2);
    if(v.p<=R&&b||2*ht.P*b>ht.A*(v.p-1)+2*ht.D)throw Error("H cut");
    sum+=b;if(v.near)nearCap+=b;else if(v.p>R&&v.a1)farA1Cap+=b;else other+=b;
   }
   if(total!==sum||2*ht.P*nearCap>ht.A*(G-Gfar)+2*ht.D*Nnear||2*ht.P*farA1Cap>ht.A*FF+2*ht.D*mf||2*ht.P*other>ht.A*otherCap+2*ht.D*otherCount)throw Error("H split");
   let right=2*ht.D*(mf+otherCount+Nnear+1)+ht.A*otherCap;
   if(ht.A*cnum*Gfar>(den+cnum)*right+ht.A*den*(DnearReset+2*C))throw Error("joint bound");
   s.jointChecks++;
   let rootCap=ht.A*C+2*ht.D;
   let right2=2*ht.D*(mf+Nnear+1)+rootCap*(Nroot+1+Bhigh);
   if(ht.A*cnum*Gfar>(den+cnum)*right2+ht.A*den*2*C)throw Error("root coupled");
  
  }
  s.markedBlocks++;s.marks+=m;s.nearMarks+=nearMark;s.tailMarks+=tailm;s.tailSlots+=tailSlots;s.tailMatched+=tailMatched;
  // Exact rounded geometric deficit levels for the far-only part of marks.
  // S small and mark lower cutoff T0 large enough to guarantee five slots.
  let Bgap=2*Math.ceil(sd.D/sd.A)+4,T0=Math.max(47,200*Bgap);
  // Smaller finite A0 may make the interval ratio less than (1.5)^5.
  if(k>=40&&C>T0){
   let a=BigInt(T0),b=5n,num=3n*BigInt(T0)+20n*BigInt(Bgap),dd=2n*BigInt(T0),levels=[];
   while(a<=2n*BigInt(C)*b){
    // find first shifted deficit barrier >= a/b by integer search.
    let z=Number((a+ b-1n)/b);if(z%2===0)z++;
    while(sd.count((z-3)/2+1)===sd.count((z-3)/2))z+=2;
    if(BigInt(z)*b<a||BigInt(z)*b>=a+BigInt(Bgap)*b||levels.length&&2*z<3*levels.at(-1).z)throw Error("rounded geometry");
    levels.push({a,b,z,p:null});a*=num;b*=dd;
   }
   let slots=0,matched=0,lost=0,seen=new Set();
   for(let i=lo;i<hi;i++){
    let v=ev[i],x=v.d+3,y=v.dp+3;
    if(v.a1&&v.p>T0){
     let refs=levels.filter(l=>5n*l.a>BigInt(v.p)*l.b&&BigInt(k)*l.a<=BigInt((2*k-4)*v.p-k*Bgap)*l.b);
     // At k=40 and Bgap/T0<=.005, the ratio >=8.975>1.55^5? 1.55^5=8.9466.
     if(refs.length<5||refs.length>6)throw Error("rounded slots");
     for(let l of refs){if(l.p!==null||x>=l.z||y<l.z)throw Error("rounded up");l.p=v.p;slots++}
    }
    if(y>=x)continue;
    for(let l of levels)if(l.p!==null&&y<l.z&&l.z<=x){
     if(v.D===0)lost++;else{
      if(v.near||v.p<=S||v.p>=l.p||seen.has(i))throw Error("rounded far");
      seen.add(i);matched++;s.roundedFarChecks++;
     }l.p=null;
    }
   }
   lost+=levels.filter(l=>l.p!==null).length;
   if(matched+lost!==slots||lost>(Nroot+2)*levels.length)throw Error("rounded exceptions");
   s.roundedBlocks++;s.roundedSlots+=slots;s.roundedMatches+=matched;s.roundedExceptions+=lost;
  }
  if(asWitness)s.witness.push({R,S,k,c:cnum/den,m,W,tailm,tailW,tailSlots,tailMatched,actualFarDrop:allFarDrop,Dreset,smallPaid,smallLost,F,j,paid:paid/den,pending:pendingLen/den});
 }
 for(let M=5;M<=N;M+=2){
  s.roots++;let H=2*M-2,t=M+2,ev=[],roots=[];
  for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");let a=next(t,H);if(!a){s.terminal++;break}
   let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,I=(1-a.e)/2,D=dp-6*I,a1=a.p>=47&&a.p>=5*d+15&&D===2*a.p,q=(H-a.e)/a.p,x=(q+a.p)/2,j=(q-a.p)/2,near=x>=64&&2*j*j<=x;
   if(a1)s.a1++;let rt=H/2+3;if(H%4===0&&rt>t&&rt<n)roots.push(rt);if(Z%4===0&&dp===6)roots.push(n);
   if(near&&H>=257){for(let v of ev){if(!v.a1||v.H<257)continue;let k=Math.floor(Math.sqrt(Math.sqrt(v.H-1)));if(a.p*k<(k-2)*v.p)throw Error("near label bound");s.nearPairChecks++}}
   ev.push({...a,H,Z,t,n,d,dp,I,D,a1,near});H=Z;t=n;s.events++;if(i===steps-1)s.capped++;
  }
  if(ev.length)for(let [R,S] of [[7,5],[11,5],[11,7],[13,7]]){s.blocks++;inspect(ev,roots,0,ev.length,R,S,ev[0].H);if(ev.length>=4){let j=Math.floor(ev.length/2);s.blocks++;inspect(ev,roots,j,ev.length,R,S,ev[j].H)}}
 }
 // Reconstruct the previous exact eight-event canonical witness.
 const word=[7687,5233,3541,2389,1621,1093,733,7369],sh=[0];for(let p of word)sh.push(sh.at(-1)+p-1);
 let H=0n,P=4n,ticks=0,checks=0;
 for(let l=3;l<=3*Math.max(...word)+6;l+=2){if(spf[l]!==l)continue;let j=word.indexOf(l),a=j>=0?mod(1-sh[j],l):0;
  const valid=x=>sh.slice(0,-1).every((h,i)=>{let v=mod(x+h,l);return word[i]===l?v===1:v!==1&&v!==l-1});
  if(j>=0){if(!valid(a))throw Error("selected CRT")}else{while(a<l&&!valid(a))a++;if(a===l)throw Error("empty CRT")}
  let L=BigInt(l),x=Number(P%L),y=mod(a-Number(H%L),l),u=1,v=0,b=l;while(b){let q=Math.floor(x/b);[x,b]=[b,x-q*b];[u,v]=[v,u-q*v]}if(x!==1)throw Error("inverse");H+=P*BigInt(mod(u*y,l));P*=L;checks+=word.length;
 }
 if(H<100000000n)H+=P;let H0=H,t=H/2n+3n,rel=0,ev=[];
 for(let p of word){let d=Number(2n*t-H),w=(3*p-d-1)/2;for(let j=1;j<=w;j++){let n=t+BigInt(j),e=n%2n?-1:1,x=e===1?n:n-2n,y=H-BigInt(e);while(y)[x,y]=[y,x%y];if(j<w?x!==1n:x!==BigInt(p)||e!==1)throw Error("literal");ticks++}
  let Z=H+BigInt(p-1),dp=Number(2n*(t+BigInt(w))-Z);if(dp!==2*p||BigInt(p*p)>H+1n)throw Error("post");ev.push({p,w,d,dp,D:dp,I:0,t:rel,n:rel+w,a1:p>=47&&p>=5*d+15});H=Z;t+=BigInt(w);rel+=w;
 }

 for(let v of ev)v.near=false;
 for(let [R,S] of [[7,5],[11,5],[11,7],[13,7]])inspect(ev,[],0,ev.length,R,S,100000001,false,true);
 s.witnessInfo={rootDigits:(H0/2n+1n).toString().length,ticks,checks};

 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000),Number(process.argv[3]||180)),null,2));
