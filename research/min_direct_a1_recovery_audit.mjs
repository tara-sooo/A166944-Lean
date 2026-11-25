// A1 deficit recovery: local decrease ratios, pair bounds and low-run logarithmic budget.
function audit(N=100000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 const cut=[5,7,11,13].map(S=>{let K=2;for(let p=3;p<=S;p+=2)if(spf[p]===p)K*=p;return {S,K}});
 const s={N,roots:0,events:0,terminal:0,capUnresolved:0,a1:0,down:0,downNonreset:0,downReset:0,smallDeficitChecks:0,ratioChecks:0,resetLossChecks:0,a1PairChecks:0,resetFreePairs:0,resetFreeNonincreasingPairs:0,smallTargetPairs:0,lowCrossingChecks:0,blockChecks:0,lowRunChecks:0,rootCountChecks:0,example:null};
 const tol=1e-9;
 function checkBlock(ev,roots,i,j){
  if(i>=j)return;const a=ev[i],b=ev[j-1],Y=b.Z,C=Math.floor(Math.sqrt(Y+1)),Nroot=roots.filter(t=>t>a.t&&t<=b.n).length;
  for(let R of [47,71,101,151])for(let {S,K} of cut){
   let T=R/5,phi=d=>Math.log(Math.max(T,d+3)),eps=Math.log1p(K/T);
   let m=0,n=0,J=0,z=0,loss=0,run=0,startD=0,lastD=0;
   function close(){if(run){if(run>K||phi(startD)-phi(lastD)>eps+tol)throw Error("low run");s.lowRunChecks++;run=0}}
   for(let k=i;k<j;k++){
    let v=ev[k];
    if(v.p<=S){if(!run)startD=v.d;run+=v.p-1;lastD=v.dp;continue}
    close();
    if(v.a1&&v.p>R){m++;if(phi(v.dp)-phi(v.d)<Math.log(10)-tol)throw Error("A1 log");}
    else if(v.D===0){z++;loss+=Math.max(0,Math.log((v.p+6)/T));}
    else{n++;if(v.dp<v.d)J++}
   }
   close();
   if(z>Nroot+1)throw Error("root count");s.rootCountChecks++;
   if(m*Math.log(10)>phi(b.dp)-phi(a.d)+J*Math.log(1.5)+loss+eps*(m+n+z+1)+tol)throw Error("block potential");
   if((Math.log(10)-eps)*m>Math.log(1.5)*n+eps*n+loss+eps*(z+1)+phi(b.dp)-phi(a.d)+tol)throw Error("count coupling");
   s.blockChecks++;
  }
 }
 for(let M=5;M<=N;M+=2){s.roots++;let H=2*M-2,t=M+2,ev=[],roots=[],last=-1;
  for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");let a=next(t,H);if(!a){s.terminal++;break}
   let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,D=dp-3*(1-a.e),a1=a.p>=47&&a.p>=5*d+15&&D===2*a.p;
   let v={...a,t,n,H,Z,d,dp,D,a1};
   if([2,4,8].includes(d)||[2,4,8].includes(dp)||dp<0)throw Error("small deficits");s.smallDeficitChecks++;
   if(dp<d){
    s.down++;
    if(a.p<7&&D===0||a.p===3)throw Error("small reset/decrease");
    if(D!==0){if(dp<2*a.p||2*(d+3)>3*(dp+3))throw Error("ratio");s.downNonreset++;s.ratioChecks++;}
    else{if(d+3>a.p+6)throw Error("reset loss");s.downReset++;s.resetLossChecks++}
   }
   if(a1){
    s.a1++;if(dp+3<10*(d+3))throw Error("A1 ratio");
    if(last>=0){
     let prev=ev[last],decs=ev.slice(last+1).filter(x=>x.dp<x.d),loss=decs.reduce((z,x)=>z+x.d-x.dp,0),gain=decs.reduce((z,x)=>z+x.p-3,0);
     if(loss<prev.dp-d||gain<loss||gain<(10*prev.p-a.p+15)/5-tol)throw Error("pair loss");
     s.a1PairChecks++;
     if(decs.every(x=>x.D!==0)){
      s.resetFreePairs++;
      if(decs.length*Math.log(1.5)+tol<Math.log((prev.dp+3)/(d+3)))throw Error("pair log");
      if(a.p<=prev.p){if(decs.length<6)throw Error("six decreases");s.resetFreeNonincreasingPairs++;if(!s.example)s.example={M,p:prev.p,r:a.p,decreases:decs.map(x=>({p:x.p,d:x.d,dp:x.dp}))}}
      if(a.p<=61)throw Error("small target reset");
      if(prev.dp>d){let z=decs.at(-1);if(!z||z.p> d/2)throw Error("last decrease");s.lowCrossingChecks++}
     }else if(a.p<=61)s.smallTargetPairs++;
    }
    last=ev.length;
   }
   let rt=H/2+3;if(H%4===0&&rt>t&&rt<n)roots.push(rt);
   if(Z%4===0&&dp===6)roots.push(n);
   ev.push(v);H=Z;t=n;s.events++;if(i===steps-1)s.capUnresolved++;
  }
  if(ev.length){checkBlock(ev,roots,0,ev.length);if(ev.length>=4)checkBlock(ev,roots,Math.floor(ev.length/2),ev.length)}
 }
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||100000),Number(process.argv[3]||180)),null,2));
