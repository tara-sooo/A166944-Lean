// Height occupation energy and joint label-deletion Laplace bounds.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(m)},mod=(a,b)=>(a%b+b)%b,lim=4000005,spf=new Uint32Array(lim+1);
 for(let p=2;p*p<=lim;p++)if(!spf[p])for(let n=p*p;n<=lim;n+=p)if(!spf[n])spf[n]=p;
 function fs(n){ck(n>=1&&n<=lim,"factor");let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function ev(u,v,y){let p=Infinity,w=Infinity,e=0;for(let [n,s] of [[u-1,1],[u+1,-1]])for(let r of fs(n)){if(r>=y)continue;let z=mod((s===1?0:r+2)-v,2*r)||2*r;if(z<w||z===w&&r<p){p=r;w=z;e=s}}return {p,w,e}}
 const rows=[];
 for(let [kind,y,R,end] of [["period",7,60,120],["period",11,420,840],["period",13,4620,9240],["period",17,60060,120120],["period",19,1021020,2042040],["local",127,100000,112000],["local",503,1000000,1012000],["local",997,1000000,1012000]]){
  let H=[];for(let p=y;p<=2*y;p++)if(!spf[p])H.push(p);
  let m=Math.floor((y-1)/2),cap=64*y,amax=3+3*(cap+2*y)+10,a=new Float64Array(amax+1),phi=new Float64Array(amax+1),sq=new Float64Array(amax+1);
  for(let h=1;h<=amax;h++){for(let p of H){if((2*h+1)%p===0)a[h]+=1/p;if((2*h-5)%p===0)a[h]+=1/p;}phi[h]=phi[h-1]+a[h];sq[h]=sq[h-1]+a[h]*a[h]}
  let basePr=H.reduce((s,p)=>s+2/p,0);
  let s={kind,y,roots:0,complete:0,censored:0,events:0,quietTicks:0,energyChecks:0,layerChecks:0,overlapChecks:0,smallChecks:0,localTimeChecks:0,sumG:0,sumN:0,sumHighN:0,sumHighGain:0,sumHighSmallGain:0,sumEnergy:0,sumCriticalEnergy:0,sumMaxHeight:0,sumPre:0,sumAny:0,sumCoarea:0,sumEnergyUpper:0,sumHeavyUpper:0,zeroHigh:0,zeroPre:0,maxEnergy:0,maxLocalTime:0,avoidanceChecks:0,worstAvoidanceRatio:0,laplaceChecks:0,laplace:[],usedCountSum:0,minN:null};
  let A=[];for(let p=5;p<y;p++)if(!spf[p])A.push(p);let counts=kind==="period"?new Float64Array(1<<A.length):null;
  let Kvals=[1,2,4,8,16];
  for(let X=Math.ceil(R/6)*6;X<end;X+=6){
   s.roots++;let u=X,v=X/2+3,h=3,G=0,N=0,M=3,intervals=[],marks=new Map(),used=0,hiN=0,hiG=0,smallG=0;
   while(G<=cap){
    let z=ev(u,v,y);if(!isFinite(z.p))break;let g=z.p-1,k=h+z.w,hp=k-g/2;
    ck(hp>=0&&k<=amax,"height");M=Math.max(M,k);intervals.push([hp+1,k,g]);
    if(k>=m){hiN++;let len=k-Math.max(m-1,hp);hiG+=len;if(z.p<=11)smallG+=len;}
    if(counts&&z.p!==3){let i=A.indexOf(z.p);ck(i>=0,"support");used|=1<<i}
    for(let j=1;j<z.w;j++){let t=v+j,e=t%2?-1:1,f=Math.abs(2*(h+j)+(e===1?1:-5));for(let p of fs(f))if(p>=y&&p<=2*y){if(!marks.has(p))marks.set(p,new Set());marks.get(p).add(mod(e-u,p));}s.quietTicks++}
    u+=g;v+=z.w;h=hp;G+=g;N++;s.events++;
   }
   if(G>cap){s.censored++;continue}
   s.complete++;if(counts)counts[used]++;
   s.minN=s.minN===null?N:Math.min(s.minN,N);
   let D=new Uint32Array(M+2);
   for(let [l,r] of intervals)for(let i=l;i<=r;i++)D[i]++;
   let E=0,EC=0,ds=0,charge=0,ht=0,maxD=0,heavy=Kvals.map(()=>0),smallCharge=0;
   for(let i=1;i<=M;i++){ds+=D[i];if(i>=m){ht+=D[i];E+=D[i]*D[i];if(a[i])EC+=D[i]*D[i];maxD=Math.max(maxD,D[i]);for(let j=0;j<Kvals.length;j++)heavy[j]+=Math.max(0,D[i]-Kvals[j]);}charge+=a[i]*D[i];}
   ck(ds===G/2&&ht===hiG,"total down length");s.localTimeChecks++;
   let overlap=0;
   for(let i=0;i<intervals.length;i++){let [l,r,g]=intervals[i];let len=Math.max(0,r-Math.max(l,m)+1);overlap+=len;if(g<=10)smallCharge+=Math.max(0,phi[r]-phi[Math.max(0,Math.max(l,m)-1)]);
    for(let j=i+1;j<intervals.length;j++){let [l2,r2]=intervals[j];overlap+=2*Math.max(0,Math.min(r,r2)-Math.max(m,l,l2)+1)}
   }
   ck(overlap===E,"pair overlap identity");s.overlapChecks++;
   let pre=1;for(let [p,S] of marks)pre*=1-S.size/p;pre=1-pre;
   for(let p of H){if(!marks.has(p))marks.set(p,new Set());for(let e of [1,-1])marks.get(p).add(mod(e-u,p));}
   let any=1;for(let [p,S] of marks)any*=1-S.size/p;any=1-any;
   let endpoint=phi[h]-phi[3],exact=endpoint+charge+basePr,bound=phi[M]+Math.sqrt(sq[M]*E)+basePr;
   ck(pre<=endpoint+charge+1e-8&&any<=exact+1e-8&&charge<=Math.sqrt(sq[M]*E)+1e-8&&any<=bound+1e-8,"energy");s.energyChecks++;
   let maxA=0;for(let i=m;i<=M;i++)maxA=Math.max(maxA,a[i]);
   let best=Infinity;
   for(let j=0;j<Kvals.length;j++){let K=Kvals[j],b=phi[M]+K*phi[M]+maxA*heavy[j]+basePr;ck(any<=b+1e-8,"heavy tail");best=Math.min(best,b);s.layerChecks++}
   ck(smallCharge<=maxA*smallG+1e-8,"small height charge");s.smallChecks++;
   if(!ht)s.zeroHigh++;if(pre===0)s.zeroPre++;s.sumG+=G;s.sumN+=N;s.sumHighN+=hiN;s.sumHighGain+=hiG;s.sumHighSmallGain+=smallG;s.sumEnergy+=E;s.sumCriticalEnergy+=EC;s.sumMaxHeight+=M;s.sumPre+=pre;s.sumAny+=any;s.sumCoarea+=exact;s.sumEnergyUpper+=bound;s.sumHeavyUpper+=best;s.maxEnergy=Math.max(s.maxEnergy,E);s.maxLocalTime=Math.max(s.maxLocalTime,maxD);
   if(counts){let k=0;for(let i=0;i<A.length;i++)if(used&(1<<i))k++;s.usedCountSum+=k;}
  }
  if(counts){ck(s.censored===0,"period complete");for(let D=0;D<counts.length;D++){let prob=1;for(let j=0;j<A.length;j++)if(D&(1<<j))prob*=1-2/A[j];let c=0;for(let k=0;k<counts.length;k++)if(!(k&D))c+=counts[k];ck(c<=s.complete*prob+1e-6,"joint avoidance");s.avoidanceChecks++;s.worstAvoidanceRatio=Math.max(s.worstAvoidanceRatio,c/(s.complete*prob));}
   for(let t of [.125,.5,1,2])for(let weight of [0,1]){
    let exact=0;for(let k=0;k<counts.length;k++){let z=0;for(let j=0;j<A.length;j++)if(k&(1<<j))z+=weight?A[j]-1:1;exact+=counts[k]*Math.exp(-t*z)}exact/=s.complete;
    let bound=A.reduce((a,p)=>a*(1-2/p*(1-Math.exp(-t*(weight?p-1:1)))),1);ck(exact<=bound+1e-10,"Laplace domination");s.laplaceChecks++;s.laplace.push({t,weight,exact,bound});
   }
  }
  rows.push(s);
 }
 return rows;
}
console.log(JSON.stringify(audit(),null,2));
