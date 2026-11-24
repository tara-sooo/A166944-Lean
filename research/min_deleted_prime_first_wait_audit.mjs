// Deleted-prime first-selection clock budget: exact finite CRT checks and complete-path samples.
function exactFirstWait(Y){
 const ps=[];for(let p=3;p<Y;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const L=2*ps.reduce((s,p)=>s*p,1),states=L*L/2;if(Y>11)throw Error("exact limit");
 const ck=(x,m)=>{if(!x)throw Error(m)},mod=(x,p)=>(x%p+p)%p;
 const rows=[];
 for(let T of [...new Set([Math.floor(Y*Math.sqrt(Math.log(Y))),2*Y,8*Y])]){
  let sums={T,A:0,F:0,R:0,completeLong:0,largeD:0,checks:0,byP:ps.map(p=>({p,F:0,first:0,deletedA:0,candidateCount:0,candidateWait:0,coupled:0}))};
  function walk(C,t,omit=0,watch=0){
   let el=0,g=0,first=0,wc=0,ww=0,seen=new Set(),F=0,R=0;
   for(;;){
    let w=Infinity,p0=0;
    for(let p of ps)if(p!==omit){let c=mod(C+g,p);if(c!==1&&c!==p-1)continue;let ph=c===1?0:p+2,f=1+mod(ph-t-el-1,2*p);if(f<w||(f===w&&p<p0)){w=f;p0=p}}
    if(watch){let m=Math.max(0,Math.min(T-el,w,2*watch));wc+=m;ww+=m*(m+1)/2;}
    if(el+w>T)break;
    if(seen.has(p0))R+=w;else{F+=w;seen.add(p0);if(p0===watch)first=w}
    g+=p0-1;el+=w;
   }
   return {A:el,F,R,wc,ww,first};
  }
  // Full first wait requires actual selected label, while candidate sum is only evaluated on the deleted walk.
  function full(C,t){
   let el=0,g=0,F=0,R=0,D=0,first=new Map(),pastT=false,total=0;
   for(;;){let w=Infinity,p0=0;for(let p of ps){let c=mod(C+g,p);if(c!==1&&c!==p-1)continue;let ph=c===1?0:p+2,f=1+mod(ph-t-total-1,2*p);if(f<w||(f===w&&p<p0)){w=f;p0=p}}if(!p0)break;
    total+=w;g+=p0-1;D=Math.max(D,2*total-g);
    if(total<=T){el=total;if(first.has(p0))R+=w;else{F+=w;first.set(p0,w)}}
   }return {A:el,F,R,first,total,D};
  }
  for(let C=0;C<L;C+=2)for(let t=0;t<L;t++){
   let a=full(C,t);ck(a.A===a.F+a.R,"partition");sums.A+=a.A;sums.F+=a.F;sums.R+=a.R;
   if(a.total>T){sums.completeLong++;ck(a.A>=T-2*Y,"time overshoot")}
   if(a.D>2*T)sums.largeD++;
   for(let j=0;j<ps.length;j++){let p=ps[j],v=sums.byP[j],f=a.first.get(p)||0,b=walk(C,t,p,p);
    if(!f)ck(a.A===b.A,"deleted equality");
    ck(b.ww<=(p+.5)*(b.A+2*Y)+p*(2*p+1),"candidate weighted bound");ck(b.wc<=T,"candidate time count");
    v.F+=f;v.first+=!!f;v.deletedA+=b.A;v.candidateCount+=b.wc;v.candidateWait+=b.ww;v.coupled+=!f;sums.checks++;
   }
  }
  for(let v of sums.byP){let p=v.p;ck(v.first*p*p<=v.candidateCount,"first probability");ck(v.F*p*p<=v.candidateWait,"first wait CRT");ck(v.deletedA<=sums.A+T*v.first,"coupling");ck(v.candidateWait<=(p+.5)*(v.deletedA+states*2*Y)+states*p*(2*p+1),"weighted bound")}
  ck(sums.largeD<=sums.completeLong&&sums.F===sums.byP.reduce((s,v)=>s+v.F,0),"sums");
  rows.push(sums);
 }
 return {Y,L,states,rows};
}
function sampledFirstWait(Y,N=8192){
 const ps=[];for(let p=3;p<Y;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 let rng=(0x61b3529f^Y)>>>0;
 function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let lim=4294967296-4294967296%p,x;do{x=u32()}while(x>=lim);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),seen=new Uint8Array(ps.length),T=Math.floor(Y*Math.sqrt(Math.log(Y))),z=Math.ceil(Math.sqrt(T)*Math.log(T)**.25);
 let A=0,F=0,R=0,Fsmall=0,Fbig=0,Rsmall=0,Rbig=0,long=0,tail=0,complete=0,Dsum=0,steps=0,maxSteps=0,repeatTags=0,repeatTail=0,firstLabels=0,repeatLabels=0;
 let bands=[3,11,31,Math.ceil(Math.sqrt(Y)),Math.ceil(Y/4),Math.ceil(Y/2)].sort((a,b)=>a-b).filter((p,i,a)=>i===0||p!==a[i-1]).map(P=>({P,first:0,repeat:0,firstWait:0,repeatWait:0}));
 for(let j=0;j<N;j++){
  let parity=uni(2);seen.fill(0);for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let v=uni(p);t[i]=v%2===parity?v:v+p}
  let el=0,gain=0,count=0,d=0,a=0,f=0,r=0;
  for(;;){let w=Infinity,k=-1;for(let i=0;i<ps.length;i++){let p=ps[i],cc=(c[i]+gain)%p;if(cc!==1&&cc!==p-1)continue;let ph=cc===1?0:p+2,b=(t[i]+el-ph)%(2*p);if(b<0)b+=2*p;let v=2*p-b;if(v<w||(v===w&&(k<0||p<ps[k]))){w=v;k=i}}
   if(k<0)break;let p=ps[k];el+=w;gain+=p-1;d=Math.max(d,2*el-gain);if(++count>20000)throw Error("guard");
   if(el<=T){a=el;if(seen[k]){r+=w;repeatLabels++;if(p<z)Rsmall+=w;else Rbig+=w;for(let b of bands)if(p>=b.P){b.repeat++;b.repeatWait+=w}}else{f+=w;firstLabels++;if(p<z)Fsmall+=w;else Fbig+=w;for(let b of bands)if(p>=b.P){b.first++;b.firstWait+=w}}seen[k]=1}
  }
  if(a!==f+r||a>T||el>T&&a<T-2*Y||d>2*T&&el<=T)throw Error("sum");
  A+=a;F+=f;R+=r;long+=el>T;tail+=d>2*T;complete+=el;Dsum+=d;steps+=count;maxSteps=Math.max(maxSteps,count);repeatTags+=r>0;repeatTail+=r>T/4;
 }
 return {Y,N,T,z,A:A/N,F:F/N,R:R/N,Fsmall:Fsmall/N,Fbig:Fbig/N,Rsmall:Rsmall/N,Rbig:Rbig/N,firstShare:A?F/A:0,A_over_T:A/N/T,R_over_T:R/N/T,long:long/N,tail:tail/N,completeMean:complete/N,Dmean:Dsum/N,steps:steps/N,maxSteps,repeatTags:repeatTags/N,repeatTail:repeatTail/N,firstLabels:firstLabels/N,repeatLabels:repeatLabels/N,bands:bands.map(b=>({P:b.P,first:b.first/N,repeat:b.repeat/N,firstWait:b.firstWait/N,repeatWait:b.repeatWait/N}))}
}
for(const Y of [5,7,11])console.log(JSON.stringify(exactFirstWait(Y)));
for(const Y of process.argv.slice(2).map(Number))console.log(JSON.stringify(sampledFirstWait(Y)));
