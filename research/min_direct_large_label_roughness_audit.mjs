// Deterministic large-label/low-deficit roughness and factor-role checks.
function audit(N=150000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 function fac(x){let a=[];while(x>1){let p=spf[x];if(!p)throw Error("range");a.push(p);x/=p}return a}
 function next(t,H){let a=null;for(let e of [1,-1])for(let p of new Set(fac(H-e))){if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}return a}
 const s={N,roots:0,events:0,terminal:0,capUnresolved:0,qualified:0,reset:0,nonreset:0,roughChecks:0,scoreChecks:0,primeCofactorChecks:0,nonresetTriples:0,oddTriples:0,evenResetClassTriples:0,abstract:0,abstractTicks:0,examples:[],blockChecks:0,chargeChecks:0};
 function inspect(H,t,a,fs){
  const {p,e,w}=a,d=2*t-H,g=p-1,D=d+2*w-g-3*(1-e),c=mod(1-H,4),k=p%4===c?1:3,I=(1-e)/2;
  if(p<47||p<5*d+15)return false;
  s.qualified++;
  if(D!==(k-1)*p||w!==(k*p+6*I-d-1)/2)throw Error("winner");
  let L=k===1?Math.floor((p-7)/3):p-1;
  if(d>L-3)throw Error("deficit");
  for(let ef of [1,-1])for(let f of new Set(fs[ef===1?0:1])){
   if(f<=L)throw Error("roughness");
   s.roughChecks++;
   if(f===p||f*f>H+1)continue;
   let kf=f%4===c?1:3,S=kf*f+3*(1-ef);
   if(S<=k*p+6*I)throw Error("score order");
   if(k===3&&kf===1&&f<=3*p-6)throw Error("reset class");
   s.scoreChecks++;
  }
  if(k===1)s.reset++;else{
   s.nonreset++;
   if(p**3>H+1){if(fs[e===1?0:1].length!==2)throw Error("prime cofactor");s.primeCofactorChecks++}
   if(p**4>H+1){
    if(fs.some(v=>v.length>3))throw Error("four factors");
    for(let v of fs)if(v.length===3&&v.some(f=>f*f>H+1))throw Error("ineligible triple");
    let v=fs[e===1?0:1];
    if(v.length===3){s.nonresetTriples++;let b=[...v];b.splice(b.indexOf(p),1);
      if(e===-1){if(b.filter(f=>f%4===c).length!==1||H+1<=p*p*(3*p-6))throw Error("odd triple");s.oddTriples++}
      else if(b.every(f=>f%4===c)){if(H-1<=p*(3*p-6)**2)throw Error("even triple");s.evenResetClassTriples++}
    }
   }
  }
  if(s.examples.length<5)s.examples.push({H,t,p,e,w,d,D,L});
  return true
 }
 for(let M=5;M<=N;M+=2){
  s.roots++;let H=2*M-2,t=M+2,ev=[];
  for(let i=0;i<steps;i++){
   if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");let a=next(t,H);if(!a){s.terminal++;break}
   let d=2*t-H,Z=H+a.p-1,n=t+a.w,good=inspect(H,t,a,[fac(H-1),fac(H+1)]);
   if(a.p>=47&&!good){if(a.p>=5*d+15)throw Error("classification");if(d<=(a.p-15)/5)throw Error("charge");s.chargeChecks++}
   ev.push({p:a.p,H,Z,d,good});H=Z;t=n;s.events++;if(i===steps-1)s.capUnresolved++;
  }
  for(let R of [47,71,101,151]){
   let g=0,m=0,g1=0,m1=0,g2=0,m2=0;for(let a of ev){if(a.p<=R)continue;g+=a.p-1;m++;if(a.good){g1+=a.p-1;m1++}else{g2+=a.p-1;m2++;if(5*a.d<=a.p-15)throw Error("bad charge")}}
   if(g!==g1+g2||m!==m1+m2)throw Error("split");s.blockChecks++;
  }
 }
 // Abstract actual starts, using small enough factorizations to verify every competitor;
 // these are not canonical-ancestry claims.
 for(let H=10000;H<=200000;H+=2){
  let f=[fac(H-1),fac(H+1)];
  if(f.some(v=>v[0]<47))continue;
  for(let d of [0,2,6]){let t=(H+d)/2,a=next(t,H);if(!a)continue;
   if(inspect(H,t,a,f)){s.abstract++;let hit=null;for(let j=1;j<=a.w;j++){let n=t+j,e=n%2?-1:1,x=e===1?n:n-2,y=H-e;while(y)[x,y]=[y,x%y];let p=x===1?0:spf[x];s.abstractTicks++;if(p&&p*p<=H+1){hit={p,e,w:j};break}}if(!hit||hit.p!==a.p||hit.e!==a.e||hit.w!==a.w)throw Error("literal")}
  }
 }
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||150000),Number(process.argv[3]||180)),null,2));
