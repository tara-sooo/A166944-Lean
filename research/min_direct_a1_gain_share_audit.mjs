// A1 gain share, barrier capacity coupling, and sharp six-decrease recovery.
function audit(N=100000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 const s={N,roots:0,events:0,a1:0,down:0,prefixChecks:0,blockChecks:0,otherGainChecks:0,barrierChecks:0,positiveResidualChecks:0,terminal:0,capped:0,witness:null};
 const tables=[5,7,11,13].map(R=>{let ps=[];for(let p=3;p<=R;p+=2)if(spf[p]===p)ps.push(p);let P=ps.reduce((a,p)=>a*p,1),A=ps.reduce((a,p)=>a*(p-1)/2,1),pre=new Uint32Array(P+1);for(let j=0;j<P;j++)pre[j+1]=pre[j]+(ps.every(p=>mod(2*j,p)%2===0&&mod(2*j,p)<=p-3)?1:0);if(pre[P]!==A)throw Error("period");let C=j=>Math.floor(j/P)*A+pre[j%P];return {R,P,A,count:(h,z)=>C(z/2)-C(h/2)}});
 function block(ev,i,j){
  if(i>=j)return;let G=ev[j-1].Z-ev[i].H,C=Math.floor(Math.sqrt(ev[j-1].Z+1)),m=0,F=0,last=-1;
  for(let k=i;k<j;k++){let v=ev[k];if(v.a1){m++;F+=v.p-1;last=k;let Gp=v.Z-ev[i].H,n=k-i+1-m;if(14*F+24*m+10*n>5*Gp+5*(v.dp-ev[i].d))throw Error("exact budget");s.prefixChecks++}}
  if(14*F>5*G+10*C+30)throw Error("gain share");s.blockChecks++;
  if(last>=0){let other=ev[last].Z-ev[i].H-F;if(5*other<9*F+24*m+10*(last-i+1-m)-10*C-30)throw Error("other gain");s.otherGainChecks++}
  for(let {R,P,A,count} of tables){
   let Ng=0,Nc=0,F1=0,m1=0,Fo=0,mo=0,B1=0,Bo=0;
   for(let k=i;k<j;k++){let v=ev[k],b=count(v.H,v.Z);if(v.p<=R){if(b)throw Error("low");continue}if(v.near){Ng+=v.p-1;Nc++;continue}if(v.a1){F1+=v.p-1;m1++;B1+=b}else{Fo+=v.p-1;mo++;Bo+=b}}
   let res=G-Ng-2*P*(Nc+1);
   if(A*(Fo+2*P*mo+2*P*m1)*14< A*(14*res-5*G-10*C-30))throw Error("coupled capacity");
   if(2*P*Bo< A*(res-F1-2*P*m1)||A*(C+2*P)*mo<2*P*Bo)throw Error("other capacity");
   s.barrierChecks++;if(14*res-5*G-10*C-30-28*P*m1>0)s.positiveResidualChecks++;
  }
 }
 for(let M=5;M<=N;M+=2){s.roots++;let t=M+2,H=2*M-2,ev=[];
  for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");let a=next(t,H);if(!a){s.terminal++;break}let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,D=dp-3*(1-a.e),a1=a.p>=47&&a.p>=5*d+15&&D===2*a.p,q=(H-a.e)/a.p,x=(q+a.p)/2,k=(q-a.p)/2;
   if(a1){if(5*(dp-d)<9*(a.p-1)+24)throw Error("A1 gain");s.a1++}if(dp<d)s.down++;
   ev.push({...a,t,H,Z,d,dp,D,a1,near:x>=64&&2*k*k<=x});t=n;H=Z;s.events++;if(i===steps-1)s.capped++;
  }
  if(ev.length){block(ev,0,ev.length);if(ev.length>=4)block(ev,Math.floor(ev.length/2),ev.length)}
 }
 // Complete CRT construction of a sharp six-decrease recovery.
 const word=[7687,5233,3541,2389,1621,1093,733,7369],sh=[0];for(let p of word)sh.push(sh.at(-1)+p-1);
 let H=0n,P=4n,checks=0;
 for(let l=3;l<=3*Math.max(...word)+6;l+=2){if(spf[l]!==l)continue;let j=word.indexOf(l),a=j>=0?mod(1-sh[j],l):0;
  const valid=x=>sh.slice(0,-1).every((h,i)=>{let v=mod(x+h,l);return word[i]===l?v===1:v!==1&&v!==l-1});
  if(j>=0){if(!valid(a))throw Error("selected CRT")}else{while(a<l&&!valid(a))a++;if(a===l)throw Error("empty CRT")}
  let L=BigInt(l),x=Number(P%L),y=mod(a-Number(H%L),l),u=1,v=0,b=l;
  while(b){let q=Math.floor(x/b);[x,b]=[b,x-q*b];[u,v]=[v,u-q*v]}
  if(x!==1)throw Error("inverse");H+=P*BigInt(mod(u*y,l));P*=L;if(H%L!==BigInt(a))throw Error("CRT");checks+=word.length;
 }
 let min=BigInt(Math.max(...word)**2+100);if(H<min)H+=P*((min-H+P-1n)/P);
 let H0=H,t=H/2n+3n,seq=[],ticks=0;
 for(let i=0;i<word.length;i++){let p=word[i],d=2n*t-H,w=(3*p-Number(d)-1)/2;
  if(!Number.isInteger(w)||w<=0)throw Error("witness wait");
  for(let j=1;j<=w;j++){let n=t+BigInt(j),e=n%2n?-1:1,x=e===1?n:n-2n,y=H-BigInt(e);while(y)[x,y]=[y,x%y];if(j<w?x!==1n:x!==BigInt(p)||e!==1)throw Error("literal witness");ticks++}
  H+=BigInt(p-1);t+=BigInt(w);let dp=2n*t-H;if(dp!==2n*BigInt(p)||BigInt(p*p)>H-BigInt(p)+2n)throw Error("post/eligibility");
  let a1=p>=47&&p>=5*Number(d)+15;if(a1!==(i===0||i===7)||i>0&&i<7&&dp>=d)throw Error("class");
  seq.push({p,w,d:Number(d),post:Number(dp),a1});
 }
 s.witness={rootDigits:(H0/2n+1n).toString().length,ticks,checks,seq};
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||100000),Number(process.argv[3]||180)),null,2));
