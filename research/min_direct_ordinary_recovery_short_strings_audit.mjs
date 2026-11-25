// Ordinary capped-linear/logarithmic recovery and mod-3 short-string constraints.
function audit(N=100000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 let s={roots:0,events:0,terminal:0,capped:0,a1:0,blocks:0,segments:0,marks:0,separatorChecks:0,markChecks:0,nonresetLossChecks:0,resetLossChecks:0,budgetChecks:0,adjacentD2:0,nonzeroMod3:0,a1Strings:0,a1StringLabels:0,shortInteriorChecks:0,affineChecks:0,residueWords:0,residueChecks:0,witness:null};
 function budget(ev,lo,hi,R){
  let T=R/5, f=x=>x<=T?0:x<=2*R?x-T:2*R-T+2*R*Math.log(x/(2*R)), m=0,M=0,delta=0,loss=0,actual=0,resets=0,caploss=0;
  function segment(a,b){
   let last=-1;for(let i=a;i<b;i++)if(ev[i].a1&&ev[i].p>R)last=i;
   if(last<0)return;
   s.segments++;let end=b===hi?last+1:b;
   delta+=f(ev[end-1].dp+3)-f(ev[a].d+3);
   for(let k=a;k<end;k++){
    let v=ev[k],change=f(v.dp+3)-f(v.d+3);
    if(v.a1){let vmin=f(2*v.p)-f(v.p/5);
     if(v.p<=R||change+1e-7<vmin||vmin+1e-7<1.8*R)throw Error("mark");
     m++;M+=vmin;s.markChecks++;
    }else if(change < -1e-9){
     if(v.D===0){if(v.p<7||-change>f(v.p+6)+1e-7)throw Error("reset");resets+=f(v.p+6);s.resetLossChecks++}
     else{if(v.p<5||v.dp>=v.d||-change>Math.min(v.d-v.dp,2*R*Math.log(1.5))+1e-7)throw Error("nonreset");loss+=-change;actual+=v.d-v.dp;caploss+=Math.min(v.d-v.dp,2*R*Math.log(1.5));s.nonresetLossChecks++}
    }
   }
  }
  let left=lo;for(let k=lo;k<hi;k++)if(ev[k].a1&&ev[k].p<=R){if(f(ev[k].d+3)!==0)throw Error("separator");segment(left,k);left=k+1;s.separatorChecks++}segment(left,hi);
  if(m!==ev.slice(lo,hi).filter(v=>v.a1&&v.p>R).length||M+1e-6<1.8*R*m||M>delta+resets+loss+1e-6||loss>caploss+1e-6||caploss>actual+1e-6)throw Error("budget");
  s.blocks++;s.budgetChecks++;s.marks+=m;
  return {R,m,markedLower:M,delta,resetBound:resets,actualDecrease:actual,cappedDecrease:caploss,loss};
 }
 function strings(ev){
  for(let i=1;i<ev.length;i++){let a=ev[i-1],b=ev[i];
   if(a.p<5||b.p<5||a.D!==2*a.p||b.D!==2*b.p)continue;
   if(3*b.p!==2*a.p+1+2*b.w+6*(a.I-b.I))throw Error("affine");s.affineChecks++;s.adjacentD2++;
   let h=a.Z%3;if(h){let a3=a.p%3,I=a.I,allowed=h===1?(a3===1&&I===0?3:a3===2&&I===1?2:0):(a3===1&&I===1?3:a3===2&&I===0?2:0);
    if(b.w!==allowed||!allowed)throw Error("mod3 competition");s.nonzeroMod3++;}
  }
  for(let i=0;i<ev.length;i++){if(!ev[i].a1)continue;let j=i+1;while(j<ev.length&&ev[j].p>=5&&ev[j].D===2*ev[j].p)j++;
   let a=ev.slice(i,j);if(a[0].H%3!==0)throw Error("A1 H mod3");
   for(let k=0;k<a.length-2;k++){if(a[k].p%3!==1)throw Error("interior mod3");if(a[k+1].w<=8){if(![3,6].includes(a[k+1].w))throw Error("short interior");s.shortInteriorChecks++}}
   s.a1Strings++;s.a1StringLabels+=a.length;
  }
 }
 for(let M=5;M<=N;M+=2){s.roots++;let H=2*M-2,t=M+2,ev=[];
  for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");let a=next(t,H);if(!a){s.terminal++;break}let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,I=(1-a.e)/2,D=dp-6*I,a1=a.p>=47&&a.p>=5*d+15&&D===2*a.p;if(a1)s.a1++;ev.push({...a,H,Z,t,n,d,dp,I,D,a1});H=Z;t=n;s.events++;if(i===steps-1)s.capped++}
  strings(ev);
  if(ev.length)for(let R of [47,71,101,151,1009]){budget(ev,0,ev.length,R);if(ev.length>=4)budget(ev,Math.floor(ev.length/2),ev.length,R)}
 }
 // Enumerate residues for the affine recurrence of k interior waits in {3,6}.
 // Work mod 3^k; only integrality is imposed (a necessary relaxation).
 for(let k=1;k<=9;k++){
  let P=3**k;
  for(let I0 of [0,1]){
   let residues=new Set();
   for(let mask=0;mask<2**k;mask++){
    let I=I0,A=1,B=0,Q=1;
    for(let i=0;i<k;i++){let w=(mask>>i&1)?6:3,J=(I+w)%2;B=2*B+Q*(1+2*w+6*(I-J));A*=2;Q*=3;I=J;}
    let x=0;while(mod(A*x+B,P)!==0)x++;residues.add(x);s.residueWords++;
    let a=x+P*100;I=I0;
    for(let i=0;i<k;i++){let w=(mask>>i&1)?6:3,J=(I+w)%2,num=2*a+1+2*w+6*(I-J);if(num%3)throw Error("integer recurrence");a=num/3;I=J;s.residueChecks++}
   }
   if(residues.size>2**k)throw Error("residue bound");
  }
 }
 // Rebuild exact earlier recovery word.
 const word=[7687,5233,3541,2389,1621,1093,733,7369],sh=[0];for(let p of word)sh.push(sh.at(-1)+p-1);
 let H=0n,P=4n,ticks=0,checks=0;
 for(let l=3;l<=3*Math.max(...word)+6;l+=2){if(spf[l]!==l)continue;let j=word.indexOf(l),a=j>=0?mod(1-sh[j],l):0;
  const valid=x=>sh.slice(0,-1).every((h,i)=>{let v=mod(x+h,l);return word[i]===l?v===1:v!==1&&v!==l-1});
  if(j>=0){if(!valid(a))throw Error("selected CRT")}else{while(a<l&&!valid(a))a++;if(a===l)throw Error("empty CRT")}
  let L=BigInt(l),x=Number(P%L),y=mod(a-Number(H%L),l),u=1,v=0,b=l;while(b){let q=Math.floor(x/b);[x,b]=[b,x-q*b];[u,v]=[v,u-q*v]}if(x!==1)throw Error("inverse");H+=P*BigInt(mod(u*y,l));P*=L;checks+=word.length}
 if(H<100000000n)H+=P;let H0=H,t=H/2n+3n,ev=[];
 for(let p of word){let d=Number(2n*t-H),w=(3*p-d-1)/2;for(let j=1;j<=w;j++){let n=t+BigInt(j),e=n%2n?-1:1,x=e===1?n:n-2n,y=H-BigInt(e);while(y)[x,y]=[y,x%y];if(j<w?x!==1n:x!==BigInt(p)||e!==1)throw Error("literal");ticks++}
 let Z=H+BigInt(p-1),dp=Number(2n*(t+BigInt(w))-Z);if(dp!==2*p||BigInt(p*p)>H+1n)throw Error("post");ev.push({p,H:Number(H%12n),Z:Number(Z%12n),d,dp,D:dp,I:0,w,a1:p>=47&&p>=5*d+15});H=Z;t+=BigInt(w)}
 strings(ev);s.witness={rootDigits:(H0/2n+1n).toString().length,ticks,checks,budgets:[1009,7000,7500].map(R=>budget(ev,0,ev.length,R))};
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||100000),Number(process.argv[3]||180)),null,2));
