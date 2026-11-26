// Fast direct recovery: exact odd multiplier shift, phase CRT and two-sided support bounds.
function audit(N=60000){
 const lim=2200000,spf=new Int32Array(lim);
 for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function factors(x){ok(Number.isInteger(x)&&x>0&&x<lim,"factor range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function inv(a,b){let c=b,x=1,y=0;a=mod(a,b);while(c){let q=Math.floor(a/c);[a,c]=[c,a-q*c];[x,y]=[y,x-q*y]}ok(a===1,"inverse");return mod(x,b)}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g;z={H,p,w,I,e:1-2*I,d,dp,g,h:(dp-6*I)/(2*p),n:t+w}}}return z}
 const st={roots:0,events:0,cap:0,controls:0,pairs:0,clockChecks:0,oddShiftChecks:0,forwardDivisor:0,reverseDivisor:0,crt:0,phaseCRT:0,positiveSource:0,resetTarget:0,largeH:0,smallCap:0,lowRelay:0,oppositeSide:0,sourceSupportChecks:0,targetSupportChecks:0,tupleCapacity:0,disjointBudget:0,synthetic:0,syntheticHigh:0,examples:[]};
 function inspect(v,T){
  let B=Math.floor(T/16),W=Math.max(1,Math.floor(T/16)),Q=5*B+2*W+7;ok(Q<T,"cutoff");
  let hi=v.map((z,i)=>({...z,i})).filter(z=>z.p>=T),S=new Map,R=new Map,tuples=new Map,F=0,capCount=0,last=-1,disLow=0,Glo=v.filter(z=>z.p<T).reduce((a,z)=>a+z.g,0);
  for(let i=1;i<hi.length;i++){let a=hi[i-1],b=hi[i],p=a.p,r=b.p;if(p>6*T||r>6*T||2*a.w<=a.g||b.w>W)continue;
   let low=v.slice(a.i+1,b.i),E=low.reduce((s,z)=>s+z.g,0),V=low.reduce((s,z)=>s+z.w,0);if(E>B)continue;
   ok(p!==r&&b.H-a.H===p-1+E&&V<=3*E&&b.n-a.n===V+b.w,"clock");st.clockChecks++;
   let h=a.h,k=b.h,c=E-1-2*(V+b.w)+6*(b.I-a.I);
   ok(Number.isInteger(h)&&h>=1&&Number.isInteger(k)&&k>=0&&c%2!==0&&Math.abs(c)<=Q&&2*h*p-(2*k+1)*r===c,"odd shift");st.oddShiftChecks++;st.positiveSource++;
   let D=2*h*p-c,A=(2*k+1)*r+c;ok(D>0&&A>0&&factors(D).includes(r)&&factors(A).includes(p),"divisors");st.forwardDivisor++;st.reverseDivisor++;
   let fb=factors(D).filter(z=>z>=T),fa=factors(A).filter(z=>z>=T);ok(T**fb.length<=D&&T**fa.length<=A,"factor multiplicity");
   let H0=a.e+p*mod((b.e-(p-1+E)-a.e)*inv(p,r),r);ok(mod(a.H-H0,p*r)===0,"horizon CRT");st.crt++;
   let aa=a.e+p*(2*a.I-2*h-1),bb=b.e+r*(2*b.I-2*k-1),del=b.H-a.H;
   ok(mod(a.H-aa,4*p)===0&&mod(b.H-bb,4*r)===0&&mod(bb-del-aa,4)===0,"clock phase");
   let H1=aa+4*p*mod(((bb-del-aa)/4)*inv(p,r),r);ok(mod(a.H-H1,4*p*r)===0,"phase CRT");st.phaseCRT++;
   let key=[p,h,c,E,a.I,b.I,r].join(","),o=tuples.get(key)||{p,r,hs:[]};o.hs.push(a.H);tuples.set(key,o);
   let s=S.get(p)||new Set;s.add(h);S.set(p,s);let t=R.get(r)||new Set;t.add(k);R.set(r,t);
   let m=Math.floor(Math.sqrt(T));if(Math.min(h,k)<=m){ok(h<=6*(m+1)+1,"cap transfer");capCount++;st.smallCap++}
   if(k===0)st.resetTarget++;if(h>=T)st.largeH++;if(E)st.lowRelay++;if(a.I!==b.I)st.oppositeSide++;
   if(a.i>last){disLow+=E;last=b.i;ok(disLow<=Glo,"disjoint budget");st.disjointBudget++}
   st.pairs++;F++;if(st.examples.length<4&&(k===0||h>=T||E>0))st.examples.push({T,B,W,p,r,H:a.H,H2:b.H,h,k,E,V,wait:b.w,c,sourcePost:a.dp,targetPost:b.dp})
  }
  if(!F)return;st.controls++;
  let start=v[0].H,end=v.at(-1).H,span=end-start,bmax=Math.max(1,Math.floor(Math.log(12*(end+6*T)+Q)/Math.log(T)));
  for(let o of tuples.values()){ok(o.hs.every((h,i)=>!i||h-o.hs[i-1]>=o.p*o.r)&&o.hs.length<=1+Math.floor(span/(o.p*o.r)),"tuple capacity");st.tupleCapacity++}
  let ns=[...S.values()].reduce((a,s)=>a+s.size,0),nr=[...R.values()].reduce((a,s)=>a+s.size,0),mult=4*(B+1)*(2*Q+1)*bmax*(1+Math.floor(span/(T*T)));
  ok(F<=mult*ns&&F<=mult*nr,"support capacity");st.sourceSupportChecks++;st.targetSupportChecks++;
 }
 for(let n=5;n<=N;n+=2){let H=2*n-2,t=n+2,v=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;v.push(z);H+=z.g;t+=z.w}st.events+=v.length;if(v.length===180)st.cap++;
  for(let T of [17,31,61,101])inspect(v,T)
 }
 // Independent integer solutions to the shifted multiplier relation. Not actual MIN trajectories.
 for(let p of [31,61,101,251])for(let r of [29,59,103,257])for(let h=1;h<=500;h++){
   let k=Math.floor(h*p/r),c=2*h*p-(2*k+1)*r;ok(c%2!==0&&Math.abs(c)<=r,"odd remainder");
   if(Math.abs(c)>=Math.min(p,r))continue;
   ok(factors(2*h*p-c).includes(r)&&factors((2*k+1)*r+c).includes(p),"synthetic factors");
   let d=2*h*p,dd=2*k*r;
   ok(d-dd===r+c&&Math.abs(d-dd)<=2*r,"shift distance");
   st.synthetic++;if(h>=p)st.syntheticHigh++;
 }
 ok(st.pairs&&st.resetTarget&&st.lowRelay&&st.oppositeSide&&st.syntheticHigh,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
