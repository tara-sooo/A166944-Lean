// Exact square-band packing, finite-support filtering and bridge phase checks.
function audit(N=150000,steps=180){
 const cap=4*N+20000,spf=new Int32Array(cap+1);for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)spf[j]=i}
 const mod=(x,m)=>(x%m+m)%m,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function next(t,H){let best=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}}return best}
 function literal(t,H){for(let w=1;w<=2*Math.floor(Math.sqrt(H+1));w++){let n=t+w,e=n%2?-1:1,g=gcd(n%2?n-2:n,H-e);if(g>1&&spf[g]**2<=H+1)return {p:spf[g],e,w}}return null}
 let s={N,steps,events:0,paths:0,rangeTruncated:0,near:[0,0,0],pairs:[0,0,0],packing:[0,0,0],filteredPairs:0,filterChecks:0,filteredGainChecks:0,phaseChecks:0,phaseRepeated:0,phaseLowVariationChecks:0,primorialChecks:0,primorialIntervals:0,primorialFarBoundChecks:0,linearPackingFarChecks:0,literalChecks:0,largestNear:null,example:null,farGainExample:null};
 const eps=[[1,4],[1,2],[3,4]];
 for(let M=5;M<=N;M+=2){
  let H=2*M-2,t=M+2,ev=[];
  for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+1>=cap){s.rangeTruncated++;break}let v=next(t,H);if(!v)break;let {p,e,w}=v,n=t+w,q=(H-e)/p,x=(p+q)/2,k=(q-p)/2,I=(1-e)/2,D=2*n-(H+p-1)-6*I;
   if(!Number.isInteger(x)||!Number.isInteger(k)||k<0||H!==x*x-k*k+e)throw Error("coordinates");
   if(M<=500){if(JSON.stringify(v)!==JSON.stringify(literal(t,H)))throw Error("literal");s.literalChecks++}
   ev.push({p,e,w,n,H,q,x,k,I,D,i});H+=p-1;t=n;s.events++;
  }
  if(!ev.length)continue;s.paths++;
  for(let z=0;z<eps.length;z++){let [a,b]=eps[z],threshold=Math.ceil(16*b*b/((b-a)**2)),last=null,total=0;
   for(let v of ev){if(v.x<threshold||b*v.k*v.k>a*v.x)continue;total+=v.p-1;s.near[z]++;
    if(!s.largestNear||v.p>s.largestNear.p)s.largestNear={M,epsilon:a/b,...v};
    if(last){let j=v.x-last.x,extra=v.H-last.H-(last.p-1);
     if(j<1||b*extra<(b-a)*last.x+b*last.k-a||extra!==(2*j-1)*last.x+j*j+last.k*last.k-v.k*v.k+last.k+1+v.e-last.e)throw Error("square pair");
     s.pairs[z]++;
     if(!s.example||last.p>s.example.first.p)s.example={M,epsilon:a/b,first:last,second:v,extra,centerDifference:j};
    }last=v
   }
   let min=Math.ceil(Math.sqrt(Math.max(0,ev[0].H-1))),max=Math.floor((a/b+Math.sqrt((a/b)**2+4*(H+1)))/2);
   if(total>(max>=min?(max+min)*(max-min+1)/2:0))throw Error("packing");s.packing[z]++;
  }
  // Exact finite-support block maxima L(1)=2,L(2)=5,L(3)=11.
  for(let [R,L] of [[3,2],[5,5],[7,11]]){
   let K=L*(R-1),low=0,run=0,high=0,far=0,near=0,nearList=[];
   for(let v of ev){if(v.p<=R){run+=v.p-1;low+=v.p-1;if(run>K)throw Error("support");}else{run=0;high+=v.p-1;if(v.x>=256&&4*v.k*v.k<=3*v.x){near+=v.p-1;nearList.push(v)}else far+=v.p-1}}
   if((R-1)*low>K*high+K*(R-1))throw Error("filter gain");s.filterChecks++;
   let middleFar=0,nearBefore=0,exactS=0;
   for(let j=1;j<nearList.length;j++){let a=nearList[j-1],b=nearList[j],extra=b.H-a.H-a.p+1,F=ev.slice(a.i+1,b.i).filter(v=>v.p>R).reduce((z,v)=>z+v.p-1,0);
    if((R-1)*(extra-K)>(R-1+K)*F)throw Error("filter interval");
    if(a.p>4*(K+1)&&F===0)throw Error("finite support exclusion");
    middleFar+=F;nearBefore+=a.p-1;exactS+=extra;s.filteredPairs++;
   }
   if(middleFar>far||(R-1)*(exactS-K*Math.max(0,nearList.length-1))>(R-1+K)*far)throw Error("sum filter");s.filteredGainChecks++;
   if(nearBefore&&(!s.farGainExample||nearBefore>s.farGainExample.nearBefore))s.farGainExample={M,R,K,low,high,near,far,nearBefore,middleFar,exactS};
  }
  // Independent product barrier: no run of labels <=R can cross the next
  // even multiple of their product. Verify the global far-gain inequality.
  for(let [R,K] of [[3,6],[5,30],[7,210],[11,2310],[13,30030]]){
   let start=null,low=0,high=0,near=0,far=0,nearList=[];
   for(let v of ev){
    if(v.p<=R){if(start===null)start=v.H;let J=K*Math.ceil(start/K);if(v.H+v.p-1>J)throw Error("product barrier");low+=v.p-1;s.primorialChecks++;}
    else {start=null;high+=v.p-1;if(v.x>=256&&4*v.k*v.k<=3*v.x){near+=v.p-1;nearList.push(v)}else far+=v.p-1;}
   }
   if((R-1)*low>K*high+K*(R-1))throw Error("primorial global");
   s.primorialIntervals++;
   // Stronger linear-loss bound from at most one near event per square center.
   const lo=Math.ceil(Math.sqrt(ev[0].H-1)),hi=Math.floor((0.75+Math.sqrt(0.75**2+4*(H+1)))/2);
   const count=Math.max(0,hi-lo+1),sum=count*(lo+hi)/2,G0=H-ev[0].H;
   if(near>sum||nearList.length>count||(R-1+K)*far<(R-1)*(G0-sum-K*(count+1)))throw Error("linear-loss far bound");
   s.linearPackingFarChecks++;
   if(nearList.every(v=>v.p>=8*(K+1))){
    const C=Math.floor(Math.sqrt(H+1)),A=R-1,B=R-1+K;
    // F >= (A/(8B)) (N-C), and U <= K((N+F)/A+1).
    if(8*B*far<A*(near-C))throw Error("far fraction");
    // F >= A/(8B+A) * [A*(G-K)/B-C].
    const G=H-ev[0].H;
    if(BigInt(8*B+A)*BigInt(B)*BigInt(far)<BigInt(A)*(BigInt(A)*BigInt(G-K)-BigInt(B)*BigInt(C)))throw Error("combined far bound");
    s.primorialFarBoundChecks++;
   }
  }
  // Exact phase lattice for pairs of successive nonunit events of distinct labels,
  // and repeat of the same signed phase pattern within a source.
  let mp=new Map();
  for(let i=1;i<ev.length;i++){let a=ev[i-1],b=ev[i];if(a.p===b.p||a.p<5||b.p<5)continue;let p=a.p,r=b.p,T=b.n-a.n,g=b.H-a.H,s0=g-p+1;
   if(2*T!==s0+r-1+b.D-a.D+6*(b.I-a.I))throw Error("phase identity");
   if(mod(a.D-(s0+r-1-2*T+6*(b.I-a.I)),2*r)!==0)throw Error("phase congruence");
   let key=[p,r,s0,a.e,b.e,T].join(":"),old=mp.get(key);
   if(old){let DH=a.H-old.H,DT=a.n-old.n,DD=a.D-old.D;
    if(DH%(2*p*r)||DT%(2*p*r)||DD!==2*DT-DH||DD%(2*p*r))throw Error("phase lattice");
    if(Math.abs(DD)<2*p*r){if(DD||DH%(4*p*r))throw Error("locked phase");s.phaseLowVariationChecks++}s.phaseRepeated++;
   }mp.set(key,a);s.phaseChecks++;
  }
 }
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||150000),Number(process.argv[3]||180)),null,2));
