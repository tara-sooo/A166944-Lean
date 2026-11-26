// Uniform growing-multiplier CRT/prime-line checks and equal-adjusted-deficit chains.
function audit(N=60000){
 const lim=1600000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i%2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function inv(a,b){if(b===1)return 0;let x=1,y=0,c=b;a=mod(a,b);while(c){let q=Math.floor(a/c);[a,c]=[c,a-q*c];[x,y]=[y,x-q*y]}ok(a===1,"inv");return mod(x,b)}
 function factors(x){ok(x>0&&x<lim,"range");let s=[];while(x>1){let p=spf[x];s.push(p);x/=p}return s}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let e=1-2*I,d=2*t-H,g=p-1,dp=d+2*w-g,D=dp-6*I;z={H,p,w,I,e,d,dp,D,h:D/(2*p),g,q:(H-e)/p}}}return z}
 const st={roots:0,events:0,cap:0,blocks:0,selected:0,pairs:0,closeNonzero:0,variableCapChecks:0,parameterChecks:0,parameterResidueChecks:0,horizonChecks:0,bandChecks:0,gcdSplitChecks:0,meanControls:0,meanTerms:0,weightedSumControls:0,weightedTerms:0,zeroEdges:0,zeroRuns:0,zeroRunEvents:0,zeroTripleChecks:0,zeroTripleTwins:0,zeroTripleNoTwin:0,zeroRunMax:0,zeroTwoBandChecks:0,zeroBandTwins:0,zeroBandNoTwinRuns:0,zeroProductChecks:0,zeroUnrestrictedPairs:0,zeroExamples:[],twinExamples:[],literalTicks:0,literalEvents:0,nonzeroExamples:[]};
 function J(n){let x=1;for(let f of new Set(factors(Math.abs(n))))if(f>2)x*=f/(f-2);return x}
 function inspect(rows,T,M,B,A){
  let l=rows.filter(z=>z.p>=T&&z.h>=1&&z.h<=M&&z.w>6&&4*z.w>=z.g),G=rows.reduce((s,z)=>s+z.g,0),F=l.reduce((s,z)=>s+z.g,0),V=rows.reduce((s,z)=>s+Math.abs(z.dp-z.d),0),Etotal=0,Vtotal=0,close=0,largeE=0,largeV=0;
  if(!l.length)return;st.blocks++;st.selected+=l.length;
  for(let i=1;i<l.length;i++){let u=l[i-1],v=l[i],E=v.H-u.H-u.g,d=v.dp-u.dp,c=d/2-3*(v.I-u.I);ok(c===v.h*v.p-u.h*u.p&&E>=0,"equation");Etotal+=E;Vtotal+=Math.abs(d);st.pairs++;
   if(E>B){largeE+=v.g;continue}if(Math.abs(d)>A){largeV+=v.g;continue}
   ok(u.p!==v.p,"close distinct");if(!c){ok(u.D===v.D&&u.D%(2*u.p*v.p)===0,"zero product");st.zeroUnrestrictedPairs++;continue}
   let h=u.h,k=v.h,g=gcd(h,k);ok(c%g===0,"gcd");let a=h/g,b=k/g,d0=c/g,p0=mod(-d0*inv(a,b),b),r0=(a*p0+d0)/b,z=(u.p-p0)/b;
   ok(Number.isInteger(z)&&v.p===r0+a*z&&v.p>=a*u.p/(2*b)&&v.p<=3*a*u.p/(2*b),"variable ratio");st.variableCapChecks++;
   let U=2**Math.floor(Math.log2(u.p)),L=Math.ceil(U/b)+2,lo=Math.ceil((U-p0)/b),hi=Math.ceil((2*U-p0)/b);ok(z>=lo&&z<hi&&hi-lo<=L,"parameter interval");st.parameterChecks++;
   let prod=u.p*v.p,shift=u.g+E,x=u.e+u.p*mod((v.e-shift-u.e)*inv(u.p,v.p),v.p),j=(u.H-x)/prod;ok(Number.isInteger(j)&&mod(x+shift,v.p)===mod(v.e,v.p),"horizon CRT");st.horizonChecks++;
   for(let f of pr){if(f>=Math.min(u.p,v.p,Math.floor((u.w-1)/2)+1,53))break;
    if(a%f&&b%f){let s=mod(-p0*inv(b,f),f),t=mod(-r0*inv(a,f),f);ok((s===t)===(d0%f===0),"roots");st.parameterResidueChecks++}
    ok(![1,f-1].includes(mod(x+prod*j,f)),"horizon roughness");
   }
   ok(J(a*b*d0)<=J(a)*J(b)*J(d0)+1e-9,"singular split");st.gcdSplitChecks++;close+=v.g;st.closeNonzero++;st.bandChecks++;
   if(st.nonzeroExamples.length<3&&Math.max(h,k)>=4)st.nonzeroExamples.push({p:u.p,r:v.p,h,k,c,E,d,H:u.H,H2:v.H});
  }
  ok(Etotal<=G-F&&Vtotal<=V,"budgets");
 }
 function zeroRuns(rows,T,B,band,root){
  let l=rows.filter(z=>z.p>=T&&z.D>0&&z.D/2<T**3&&z.w>6&&4*z.w>=z.g&&spf[z.q]===z.q&&(!band||z.p<2*T));
  for(let a=0;a<l.length;){let b=a+1;while(b<l.length&&l[b].D===l[b-1].D&&l[b].H-l[b-1].H-l[b-1].g<=B)b++;
   let n=b-a;if(n>=2){let v=l.slice(a,b),D=v[0].D,s=[...new Set(v.map(z=>z.p))],P=s.reduce((x,p)=>x*p,1);ok(s.length===2&&D%(2*P)===0&&n<=5,"zero chain");st.zeroEdges+=n-1;st.zeroRuns++;st.zeroRunEvents+=n;st.zeroRunMax=Math.max(st.zeroRunMax,n);st.zeroProductChecks++;
    let twins=0;
    for(let i=2;i<n;i++){let x=v[i-2],y=v[i-1],z=v[i];ok(x.p===z.p&&x.p!==y.p&&x.D===z.D,"alternation");let m=(z.q-x.q)/2,E=y.H-x.H-x.g+z.H-y.H-y.g;ok(Number.isInteger(m)&&m>=1&&z.H-x.H===x.p+y.p-2+E,"triple");
     if(x.p>y.p||band)ok(m===1,"max or band twin");
     if(m===1){twins++;st.zeroTripleTwins++;if(band)st.zeroBandTwins++;if(st.twinExamples.length<3&&!st.twinExamples.some(a=>a.H[0]===x.H&&a.p===x.p)){st.twinExamples.push({root,T,B,p:x.p,r:y.p,D,H:[x.H,y.H,z.H],q:[x.q,y.q,z.q],w:[x.w,y.w,z.w],sides:[x.e,y.e,z.e],E,post:[x.dp,y.dp,z.dp]})}}else{ok(m>=5&&y.p>=9*x.p-2*B,"non-twin large middle");st.zeroTripleNoTwin++}st.zeroTripleChecks++;
    }
    if(!twins)ok(n<=3,"no twin length");
    if(band){st.zeroTwoBandChecks++;if(!twins){ok(n<=2,"band no twin");st.zeroBandNoTwinRuns++}}
    if(st.zeroExamples.length<6)st.zeroExamples.push({T,B,band,D,labels:v.map(z=>z.p),q:v.map(z=>z.q),H:v.map(z=>z.H),twins})
   }a=b
  }
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;
  for(let i=0;i<180;i++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
  for(let [T,m,B,A] of [[17,8,8,12],[31,16,8,16],[47,32,12,24]])inspect(rows,T,m,B,A);
  for(let T of [11,17,31])for(let B of [2,4,Math.floor(T/2)]){zeroRuns(rows,T,B,false,M);zeroRuns(rows,T,B,true,M)}
 }
 // Uniform gcd summation: J has bounded mean and harmonic mean. Verify finite
 // arithmetic inequalities with conservative rational upper estimates for J.
 let HJ=[0],AJ=[0];for(let n=1;n<=1024;n++){let j=J(n);AJ.push(AJ.at(-1)+j);HJ.push(HJ.at(-1)+j/n);ok(AJ[n]<=Math.E*n+1e-8,"mean J");st.meanTerms++}
 for(let M of [1,2,4,8,16,32,64,128])for(let A of [1,2,4,8,16,32,64,128]){
  let sum=0;for(let g=1;g<=Math.min(M,A);g++){let n=Math.floor(M/g),q=Math.floor(A/g);sum+=AJ[n]*HJ[n]*AJ[q];st.weightedTerms++}
  ok(sum<=30*A*M*Math.log(2*M),"gcd-summed weight bound");st.weightedSumControls++;
 }st.meanControls=1;
 // Replay actual representative twin chain roots with the tickwise raw-GCD rule.
 for(let v of st.twinExamples){let H=2*v.root-2,t=v.root+2;for(let i=0;i<180&&H<=v.H[2];i++){let z=next(H,t);ok(z,"replay event");let found=null;
   for(let n=t+1;n<=t+z.w;n++){let I=n%2,e=1-2*I,d=gcd(n-2*I,H-e);let p=factors(d).filter(f=>f%2&&f*f<=H+1).sort((a,b)=>a-b)[0];st.literalTicks++;if(p){found={p,w:n-t,I};break}}
   ok(found&&found.p===z.p&&found.w===z.w&&found.I===z.I,"literal replay");st.literalEvents++;H+=z.g;t+=z.w
 }}
 ok(st.twinExamples.length&&st.literalTicks&&st.closeNonzero&&st.zeroEdges&&st.zeroProductChecks&&st.zeroTwoBandChecks,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
