// Synchronized local birth windows, random-time clock occupation and all-root soft frontier entropy.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=4000005,spf=new Int32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let x=p*p;x<=N;x+=p)if(!spf[x])spf[x]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 function rough(a){return Math.min(spf[a-1]||a-1,spf[a+1]||a+1)}
 function add(m,a){m.set(a,(m.get(a)||0)+1)}
 function H(m){let t=0;for(let v of m.values())t+=v*Math.log(v);return t}
 let out={roots:0,events:0,blocks:0,tailChecks:0,meanChecks:0,secondReplay:0,secondEvents:0,fiberChecks:0,windowChecks:0,rows:[]};
 for(let R of [12000,48000,192000,480000,1000000,2000000]){
  let S=Math.sqrt(2*R+1),T=Math.ceil(S),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nr=(hi-lo)/6+1,logS=Math.log(S),coef=2*Math.log(logS/Math.log(3))/(logS-Math.log(3));
  function score(q){let d=Math.log(S/Math.min(q,S));return {d,c:2*Math.log(logS/Math.log(Math.min(q,S)))+Math.log1p(d)+2*Math.log1p(Math.log1p(d))}}
  let mEnd=new Map(),mEndW=new Map(),mPick=new Map(),mPickW=new Map(),mapBest=new Map(),diff=new Float64Array(T+1),meanD=0,meanPenalty=0,meanN=0,meanLogN=0,meanLongestPenalty=0,maxN=0,windowMax=0;
  for(let A=lo;A<=hi;A+=6){
   let l=lo+Math.floor((A-lo)/W)*W,n0=3-l/2,end=n0+T,a=A,n=3-A/2,ne=0,ds=0,ps=0,len=0,seg=[],long=0,best=a;
   for(;;){
    let e=next(a,n),f=n+e.w,begin=Math.max(n,n0),stop=Math.min(f,end),duration=Math.max(0,stop-begin);
    if(duration){let q=rough(a),v=score(q);ck(duration<=2*q,"clock cap");seg.push({q,duration});len+=duration;ds+=duration*v.d;ps+=duration*v.c;diff[begin-n0]+=v.c;diff[stop-n0]-=v.c;out.blocks++;if(duration>long){long=duration;best=a}}
    if(f>end)break;a-=e.p-1;n=f;ne++;out.events++;ck(a>=A-3*T-6,"gain cap");
   }
   ck(len===T&&long>=T/(ne+1)-1e-10,"occupation");let base=Math.log(2*S*(ne+1)/T);ck(ds/T<=base+1+1e-8,"conditional mean");out.meanChecks++;
   for(let t of [0,1,2,4]){let count=seg.reduce((s,v)=>s+(v.q<T/(2*(ne+1)*Math.exp(t))?v.duration:0),0);ck(count<=T*Math.exp(-t)+1e-8,"tail");out.tailChecks++}
   ck(rough(best)>=T/(2*(ne+1))-1e-10,"longest");meanD+=ds/T;meanPenalty+=ps/T;meanN+=ne;meanLogN+=Math.log1p(ne);meanLongestPenalty+=score(rough(best)).c;maxN=Math.max(maxN,ne);add(mEnd,a);add(mEndW,l+":"+a);add(mapBest,best);out.roots++;
  }
  let running=0,pick=0,minP=Infinity,avg=0;
  for(let u=0;u<T;u++){running+=diff[u];let x=running/nr;avg+=x/T;if(x<minP){minP=x;pick=u}}
  ck(Math.abs(avg-meanPenalty/nr)<1e-8,"time mean");
  let fiber=new Map(),winSets=new Map(),directP=0,twMass=0,weighted=0;
  for(let A=lo;A<=hi;A+=6){
   let l=lo+Math.floor((A-lo)/W)*W,n0=3-l/2,end=n0+T,cut=n0+pick,a=A,n=3-A/2,x=null;
   for(;;){let e=next(a,n),f=n+e.w;if(x===null&&f>cut)x=a;if(f>end)break;a-=e.p-1;n=f;out.secondEvents++}
   ck(x!==null&&x<=A&&A-x<=3*T+6,"cut domain");let key=l+":"+x;ck(!fiber.has(key)||fiber.get(key)===a,"deterministic future");fiber.set(key,a);out.fiberChecks++;
   add(mPick,x);add(mPickW,key);let st=winSets.get(x)||new Set();st.add(l);winSets.set(x,st);directP+=score(rough(x)).c;twMass+=+(rough(x)>S);out.secondReplay++;
  }
  for(let s of winSets.values()){windowMax=Math.max(windowMax,s.size);ck(s.size<=Math.ceil((3*T+6)/W)+2,"window ambiguity");out.windowChecks++}
  for(let a of mPick.keys())weighted+=Math.exp(-score(rough(a)).c);
  const LE=H(mEnd)/nr,LEW=H(mEndW)/nr,LP=H(mPick)/nr,LPW=H(mPickW)/nr,Lbest=H(mapBest)/nr,Dbar=1+Math.log(2)+meanLogN/nr,f=x=>Math.log1p(x)+2*Math.log1p(Math.log1p(x)),Pbar=f(Dbar)+coef*Dbar,pc=directP/nr;
  ck(LPW<=LEW+1e-9&&LEW<=LE+1e-9&&LP<=LE+Math.log(windowMax)+1e-9,"entropy");ck(meanD/nr<=Dbar+1e-8&&meanPenalty/nr<=Pbar+1e-8&&Math.abs(pc-minP)<1e-8&&pc<=meanPenalty/nr+1e-8,"penalty");
  ck(nr*Math.exp(-LP-pc)<=weighted+1e-7,"weighted Jensen");
  let badWeight=0;for(let a=2*Math.ceil((lo-3*T-6)/2);a<=hi;a+=2)if(rough(a)<=S)badWeight+=Math.exp(-score(rough(a)).c);
  out.rows.push({R,S,T,W,nr,meanN:meanN/nr,meanLogN:meanLogN/nr,maxN,meanD:meanD/nr,Dbar,meanPenalty:meanPenalty/nr,Pbar,pick,minPenalty:pc,LE,LEW,LP,LPW,windowMax,meanLongestPenalty:meanLongestPenalty/nr,Lbest,score:LP+pc,scoreRatio:(LP+pc)/Math.log(Math.log(R)),bestWaitScore:Lbest+meanLongestPenalty/nr,upperActual:LE+Math.log(windowMax)+meanPenalty/nr,upperTheoretical:LE+Math.log(Math.ceil((3*T+6)/W)+2)+Pbar,weighted,jensen:nr*Math.exp(-LP-pc),badWeight,twinMass:twMass/nr});
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
