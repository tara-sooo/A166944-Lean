// First-coalescence branches, reset rigidity and first-crossing threshold overlap.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p;
 const N=1000000,spf=new Uint32Array(N+3);for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let x=p*p;x<=N+2;x+=p)if(!spf[x])spf[x]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity,q=Infinity;for(let [d,e] of [[a+1,0],[a-1,2]])for(let r of fs(d)){q=Math.min(q,r);let t=mod((e===0?0:r+2)-n,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}}return {p,w,q}}
 let out={roots:0,events:0,intervals:0,arrivalGroups:0,incomingDivisibilityChecks:0,doubleJumpChecks:0,resetChecks:0,slowSourceChecks:0,energyBalanceChecks:0,independentPairChecks:0,thresholdChecks:0,overlapChecks:0,gridChecks:0,rows:[]};
 for(let R of [3000,12000,48000,192000,480000]){
  let T=Math.ceil(8*Math.sqrt(2*R+1)),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),byPos=new Map(),byEvent=new Map(),keep=R===3000,paths=[],row={R,T,roots:0,mean:0,pairs:0,birthPairs:0,idleJumpPairs:0,jumpJumpPairs:0,ssPairs:0,oneSlowPairs:0,fastFastPairs:0,highHighPairs:0,highHighResetPairs:0,topSlowSlowPairs:0,topSlowIdlePairs:0,topSlowBirthPairs:0,topSlowJumpPairs:0,retiredPairs:0,maxPresent:0,uniqueDoubleKeys:0,uniqueTopSSKeys:0,thresholds:[],bands:[]};
  function put(b,s,e,p,slow,A,path){ck(s<=e,"interval");let ar=byPos.get(b)||[];ar.push({s,e,p,slow,A});byPos.set(b,ar);if(keep)path.push({b,s,e});out.intervals++}
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,end=n+T,p=0,slow=false,path=[];
   while(true){let x=next(a,n),f=n+x.w;
    if(f>end){put(a,n,end,p,slow,A,path);break}
    put(a,n,f-1,p,slow,A,path);
    let key=a+":"+f,E=byEvent.get(key)||{p:x.p,as:[],g:[]};
    E.as.push(A);E.g.push(A-a);byEvent.set(key,E);
    let b=a-x.p+1,h=f+b/2;
    ck(h>=0&&h<=T+3,"post height");
    if(f%2===0){ck(b%x.p===0&&h%x.p===0,"minus inverse gcd")}
    else{ck((b-2)%x.p===0&&(h-3)%x.p===0,"plus inverse gcd")}
    out.incomingDivisibilityChecks++;slow=4*x.w>=x.p;
    if(slow){ck(x.q>=x.p/8,"slow roughness");out.slowSourceChecks++}
    p=x.p;a=b;n=f;out.events++;
   }
   if(keep)paths.push(path);row.roots++;row.mean+=A-a;out.roots++;
  }
  let cutoff=Math.floor(Math.sqrt(T+3))+1,top=Math.ceil(T/16);
  for(let [b,ar] of byPos){
   ar.sort((x,y)=>x.s-y.s||x.p-y.p);
   let ends=ar.map(x=>x.e).sort((x,y)=>x-y),retire=ar.filter(x=>x.e===3-x.A/2+T).map(x=>x.e).sort((x,y)=>x-y);
   // sweep only starts and retirement times, removing intervals
   // whose final occupied tick precedes the sweep tick.
   let i=0,j=0,k=0,active=0;
   while(i<ar.length||k<retire.length){
    let n=Math.min(i<ar.length?ar[i].s:Infinity,k<retire.length?retire[k]:Infinity);
    while(j<ends.length&&ends[j]<n){active--;j++}
    ck(active>=0,"active nonnegative");
    let idle=active,birth=0,groups=new Map();
    while(i<ar.length&&ar[i].s===n){let e=ar[i++];active++;if(!e.p){birth++;continue}
     let g=groups.get(e.p)||{m:0,s:0};g.m++;g.s+=+e.slow;groups.set(e.p,g)}
    ck(birth<=1,"birth uniqueness");row.maxPresent=Math.max(row.maxPresent,active);
    let jumps=active-idle-birth;
    row.birthPairs+=birth*(idle+jumps);row.idleJumpPairs+=idle*jumps;
    let arr=[...groups],h=n+b/2;
    if(groups.size>=2)row.uniqueDoubleKeys++;
    let topSS=false;
    for(let [p,g] of arr){row.topSlowIdlePairs+=p>=top?g.s*idle:0;row.topSlowBirthPairs+=p>=top?g.s*birth:0}
    for(let x=0;x<arr.length;x++)for(let y=x+1;y<arr.length;y++){
     let [p,g]=arr[x],[r,f]=arr[y],pairs=g.m*f.m,ss=g.s*f.s,ff=(g.m-g.s)*(f.m-f.s);
     row.jumpJumpPairs+=pairs;row.ssPairs+=ss;row.fastFastPairs+=ff;row.oneSlowPairs+=pairs-ss-ff;out.doubleJumpChecks++;
     let c=n%2===0?0:3,off=n%2===0?0:2;
     ck((b-off)%(p*r)===0&&(h-c)%(p*r)===0,"two incoming labels");
     if(p*r>T+3){ck(h===c,"large product forces reset");out.resetChecks++}
     if(p>=cutoff&&r>=cutoff){row.highHighPairs+=pairs;ck(h===c,"high reset");row.highHighResetPairs+=pairs}
     if(p>=top&&r>=top){row.topSlowSlowPairs+=ss;if(ss)topSS=true;}
     if(p>=top)row.topSlowJumpPairs+=g.s*f.m;if(r>=top)row.topSlowJumpPairs+=f.s*g.m;
    }
    if(topSS)row.uniqueTopSSKeys++;
    // Birth + jump + idle branches form pair merger at this tick.
    // Retirements occur AFTER this tick. Distinct canonical births
    // imply at most one retirement per absolute tick.
    if(k<retire.length&&retire[k]===n){row.retiredPairs+=active-1;k++;ck(k===retire.length||retire[k]!==n,"unique retirement");}
    out.arrivalGroups++;
   }
  }
  row.pairs=row.birthPairs+row.idleJumpPairs+row.jumpJumpPairs;
  ck(row.pairs===row.retiredPairs,{R,pairs:row.pairs,retire:row.retiredPairs});out.energyBalanceChecks++;
  ck(row.jumpJumpPairs===row.ssPairs+row.oneSlowPairs+row.fastFastPairs,"jump pair decomposition");
  if(keep){let c=0;for(let i=0;i<paths.length;i++)for(let j=i+1;j<paths.length;j++){
    let a=paths[i],b=paths[j],u=0,v=0,found=false;
    while(u<a.length&&v<b.length){let x=a[u],y=b[v];if(x.b===y.b&&Math.max(x.s,y.s)<=Math.min(x.e,y.e)){found=true;break}if(x.e<y.e)u++;else v++}
    c+=+found;out.independentPairChecks++;
   }ck(c===row.pairs,{R,c,pairs:row.pairs})}
  // First-crossing energy for each integer gain threshold, independently
  // compare integrated energies with pairwise overlap lengths.
  let Jmax=128,dc=new Float64Array(Jmax+2),energy=new Float64Array(Jmax+2),integral=0,overlap=0;
  let bandMap=new Map();
  for(let E of byEvent.values()){
   let p=E.p,g=p-1,as=E.g.sort((a,b)=>a-b),diff=new Int32Array(Jmax+2);
   for(let d of as){let L=d,U=Math.min(Jmax,d+g-1);if(L<=U){diff[L]++;diff[U+1]--;dc[L]++;dc[U+1]--}}
   let n=0,local=0;for(let j=0;j<=Jmax;j++){n+=diff[j];local+=n*n;energy[j]+=n*n}
   integral+=local;
   let sum=0;
   // Integrate overlap of gain intervals for ordered pairs; finite
   // window clipping is applied exactly.
   for(let i=0;i<as.length&&as[i]<=Jmax;i++)for(let j=0;j<as.length&&as[j]<=Jmax;j++){
    sum+=Math.max(0,Math.min(Jmax,as[i]+g-1,as[j]+g-1)-Math.max(as[i],as[j])+1);out.overlapChecks++}
   ck(sum===local,"overlap identity");overlap+=sum;
   let Y=2**Math.floor(Math.log2(p)),s=Math.max(1,Math.floor(Y/2)),map=new Map(),used=new Set();
   for(let d of as){let J=s*Math.ceil(d/s);ck(J<=d+g-1,"grid coverage");map.set(J,(map.get(J)||0)+1);used.add(J)}
   let c=[...map.values()].reduce((a,b)=>a+b*b,0);
   ck(as.length**2<=used.size*c+1e-9&&used.size<=Math.floor((2*T+6)/s)+2,"grid energy");out.gridChecks++;
   let rec=bandMap.get(Y)||{Y,keys:0,mass:0,energy:0,assignedEnergy:0};rec.keys++;rec.mass+=as.length;rec.energy+=as.length**2;rec.assignedEnergy+=c;bandMap.set(Y,rec);
  }
  ck(integral===overlap,"global overlap");
  let n=0;for(let j=0;j<=Jmax;j++){n+=dc[j];ck(n<=row.roots,"one crossing per threshold");out.thresholdChecks++;if([0,6,12,24,48,96,128].includes(j))row.thresholds.push({J:j,mass:n,energy:energy[j]})}
  row.bands=[...bandMap.values()].sort((a,b)=>a.Y-b.Y);row.mean/=row.roots;row.cutoff=cutoff;row.top=top;row.birthShare=row.birthPairs/row.pairs;row.idleShare=row.idleJumpPairs/row.pairs;row.jumpShare=row.jumpJumpPairs/row.pairs;out.rows.push(row)
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
