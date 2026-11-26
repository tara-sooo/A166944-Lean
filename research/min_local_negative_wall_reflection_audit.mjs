// Negative-offset reflected MIN and early-wall-jump twin certificate.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(m)},mod=(x,p)=>(x%p+p)%p,N=300000,spf=new Uint32Array(N+2);
 for(let p=2;p*p<=N+1;p++)if(!spf[p])for(let k=p*p;k<=N+1;k+=p)if(!spf[k])spf[k]=p;
 function factors(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,v){let p=Infinity,w=Infinity,e=0;for(let [b,s] of [[a+1,1],[a-1,-1]])for(let r of factors(b)){let t=mod((s===1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e}}
 let cache=new Map(),res=new Map(),hist={},examples=[],events=0,merges=0,clockChecks=0,zeroChecks=0,wallChecks=0,compositeChecks=0,twinDirectChecks=0,certified=0,finalTwin=0,finalComposite=0,finalThree=0,maxH=0,maxCompositeRatio=0,byRange=[];
 for(let a=6;a<=N;a+=6){
  let d=a,v=-a/2+3,trail=[],end;
  while(d){
   let key=d+":"+v;if(cache.has(key)){end=cache.get(key);merges++;break}
   trail.push(key);let {p,w,e}=next(d,v);ck(Number.isFinite(p)&&w<=3*(p-1),"event");
   let q=Math.min(...factors(d+1),...factors(d-1));ck(w<=2*q,"minimum clock");clockChecks++;
   if(v<0){ck(v+w<=0,"zero ceiling");zeroChecks++}
   ck(v+d/2>=0&&v+w+(d-p+1)/2>=0&&p<=d+1,"negative height/wall");wallChecks++;
   if(d===p-1){ck(e===1&&(v+w)%(2*p)===0&&v+w>=0,"final minus");end={h:v+w,p,w,preV:v};}
   d-=p-1;v+=w;events++;
  }
  ck(!!end,"terminal");
  for(let key of trail)cache.set(key,end);
  res.set(a,end);hist[end.h]=(hist[end.h]||0)+1;
  if(end.h&&examples.length<100)examples.push([a,end.h]);
  maxH=Math.max(maxH,end.h);let E=a-end.p+1;ck(E>=0,"pre gain");
  if(end.p===3)finalThree++;
  else if(spf[end.p-2]){
   finalComposite++;let b=end.p-2,q=spf[b];
   ck(end.w<=2*q&&a/2-3+end.h<=3*E+2*Math.sqrt(b)+1e-9,"composite inequality");compositeChecks++;
   maxCompositeRatio=Math.max(maxCompositeRatio,end.p/a);
  }else finalTwin++;
  if(end.p>=5&&end.p>5*E+7+4*Math.sqrt(end.p-2)-2*end.h){ck(!spf[end.p-2],"certified twin");certified++}
  if(!spf[a+1]&&!spf[a-1]&&a>=12){ck(end.p===a+1&&end.h===0,"direct twin reset");twinDirectChecks++}
 }
 for(let [lo,hi] of [[6,3000],[3006,30000],[30006,300000]]){
  let n=0,early=0,zero=0,twin=0,sumRatio=0,distinct=new Set();
  for(let a=lo;a<=hi;a+=6){let x=res.get(a),E=a-x.p+1;n++;if(x.h===0)zero++;if(x.p>=5&&!spf[x.p-2]){twin++;distinct.add(x.p)}if(x.p>=5&&x.p>5*E+7+4*Math.sqrt(x.p-2)-2*x.h)early++;sumRatio+=x.p/a}
  byRange.push({lo,hi,n,zero,twin,early,meanRatio:sumRatio/n,distinctTwinLabels:distinct.size})
 }
 const gcd=(a,b)=>{a=a<0n?-a:a;b=b<0n?-b:b;while(b){let x=a%b;a=b;b=x}return a};
 const literal=(u,v)=>{let n=v;for(;;){n++;let even=n%2n===0n,b=even?gcd(u-1n,n):gcd(u+1n,n-2n);if(b>1n){let d=Number(b);ck(Number.isSafeInteger(d)&&d<=N+1,"literal gcd");return {p:spf[d]||d,w:Number(n-v),e:even?1:-1}}}};
 let reflection=[];
 for(let Y of [31,101,251,997]){
  let J=4n;for(let p=3;p<=Y;p+=2)if(!spf[p])J*=BigInt(p);
  let s={Y,roots:0,zeroRoots:0,generalRoots:0,events:0,checks:0,wallHits:0,phaseHist:{}};
  for(let mult of [1n,2n]){
   let wall=J*mult;
   for(let a=6;a<=Y-1;a+=6){
    let end=res.get(a),general=Y>=5*a+11,zero=end.h===0;if(!general&&!zero)continue;
    s.roots++;if(general)s.generalRoots++;if(zero)s.zeroRoots++;
    let d=a,v=-a/2+3,u=wall-BigInt(a),V=wall/2n+BigInt(v);
    while(d){let x=next(d,v),z=literal(u,V);ck(x.p===z.p&&x.w===z.w&&x.e===z.e,"reflection literal");
     if(zero)ck(v+x.w<=0,"zero embedding");
     d-=x.p-1;v+=x.w;u+=BigInt(z.p-1);V+=BigInt(z.w);s.events++;s.checks++}
    ck(u===wall&&V===wall/2n+BigInt(end.h),"wall phase");s.wallHits++;s.phaseHist[end.h]=(s.phaseHist[end.h]||0)+1
   }
  }reflection.push(s)
 }
 return {N,roots:N/6,events,merges,clockChecks,zeroChecks,wallChecks,compositeChecks,twinDirectChecks,certified,finalTwin,finalComposite,finalThree,maxH,maxCompositeRatio,hist,examples,byRange,reflection}
}
console.log(JSON.stringify(audit(),null,2));
