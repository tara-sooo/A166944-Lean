// Exact dyadic cutoff insertion decomposition, wall-gap certificate, and root-biased repair controls.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(m)},mod=(a,p)=>(a%p+p)%p;
 const MAX=24576,spf=new Uint32Array(14*MAX+100),pr=[];
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let n=p*p;n<spf.length;n+=p)spf[n]=p;
 for(let p=3;p<spf.length;p+=2)if(!spf[p])pr.push(p);
 const factors=n=>{let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a};
 const V=y=>pr.filter(p=>p>=5&&p<=y).reduce((s,p)=>s*(1-2/p),1);
 let z={exactControls:0,oldRootClasses:0,fullRootClasses:0,insertions:0,acceptedInsertions:0,certificateChecks:0,wallGapChecks:0,unionResidueChecks:0,hazardChecks:0,fullMatchChecks:0,shortStableChecks:0,preemptionChecks:0,randomRoots:0,recoveryTrials:0,recoverySuccesses:0,rows:[],sample:[]};
 function sim(P,res,par,L){let G=0,t=0,h=3,path=[];
  while(true){let p0=0,w0=Infinity;
   for(let p of P)for(let e of [-1,1])if(mod(res[p]-G-e,p)===0){let x=mod(res[p]*((p+1)/2),p);if(mod(x,2)!==par)x+=p;let w=mod(x+(e===-1?0:p+2)-3-t,2*p)||2*p;if(w<w0||w===w0&&p<p0){p0=p;w0=w}}
   if(!p0||G+p0-1>L)return {ok:!p0,G,t,h,path};
   path.push({G,t,h,p:p0,w:w0});G+=p0-1;t+=w0;h+=w0-(p0-1)/2;ck(h>=0&&t<=9*G/4+8,"potential");
  }
 }
 function cert(path,y,Y,used,par,integers=false){
  const B=new Map(),P=pr.filter(p=>p>y&&p<=Y&&p!==used),G=path.G;
  function add(p,r){let S=B.get(p)||new Set();S.add(mod(r,p));B.set(p,S)}
  for(let e of path.path)for(let u=1;u<=e.w;u++){
   let b=e.h+u,np=mod(3+e.t+u-par,2);
   for(let q of factors(Math.abs(np?2*b-5:2*b+1)))if(q>y&&q<=Y&&q!==used&&(u<e.w||q<e.p))add(q,e.G+(np?1:-1));
  }
  for(let q of P){add(q,G-1);add(q,G+1)}
  let high=0,run=0,holes=0,offsets=new Set([-1,1]);
  for(let e of path.path){let g=e.p-1;if(e.p<=5){run+=g;ck(run<=16,"wall gap");z.wallGapChecks++}else{high+=g;run=0}holes+=Math.max(0,g/2-2);offsets.add(e.G+g-1);offsets.add(e.G+g+1)}
  ck(high>=3*(G-16)/11-1e-9,"high gain wall");
  ck(offsets.size===G/2+2-holes&&offsets.size<=5*G/11+30/11+1e-9,"union gaps");z.unionResidueChecks++;
  if(used)ck(offsets.size<=(G-used+1)/2+4,"one insertion holes");
  let good=1n,total=1n,prob=1,lambda=0,maxFrac=0;
  for(let q of P){let n=B.get(q).size;ck(n<=offsets.size,"forbidden subset");if(integers){total*=BigInt(q);good*=BigInt(q-n)}prob*=1-n/q;lambda+=n/q;maxFrac=Math.max(maxFrac,n/q);z.hazardChecks++}
  if(y>=96){ck(maxFrac<=.95,"uniform density");ck(lambda<=path.t/y+2*P.reduce((s,p)=>s+1/p,0)+1e-9,"total hazard");ck(prob>=Math.exp(-4*lambda)-1e-12,"retention lower");if(used)ck(maxFrac<=.55,"inserted hole density")}
  z.certificateChecks++;return {good,total,prob,lambda,maxFrac,B}
 }
 for(let y of [5,7,9,10]){
  let Y=2*y,L=2*y-2,base=pr.filter(p=>p<=y),all=pr.filter(p=>p<=Y),add=all.filter(p=>p>y),M=2*base.filter(p=>p>=5).reduce((s,p)=>s*p,1),Q=add.reduce((s,p)=>s*BigInt(p),1n),fullM=2*all.filter(p=>p>=5).reduce((s,p)=>s*p,1);
  let exact=[0n,0n],brute=[0n,0n],pre=0n,post=0n,oldSuccess=0,res=new Int32Array(Y+1);
  for(let j=0;j<M;j++){
   let par=mod(3*j,2);for(let p of base)res[p]=mod(6*j,p);
   let old=sim(base,res,par,L);
   if(old.ok){oldSuccess++;let c=cert(old,y,Y,0,par,true);ck(c.total===Q,"zero denominator");exact[0]+=c.good}
   for(let p of add)for(let r=0;r<p;r++){
    res[p]=r;z.insertions++;let a=sim([...base,p],res,par,L),m=a.path.filter(e=>e.p>y);
    if(!a.ok||m.length!==1)continue;
    ck(m[0].p===p,"single mark");z.acceptedInsertions++;let c=cert(a,y,Y,p,par,true);
    ck(c.total*BigInt(p)===Q,"one denominator");exact[1]+=c.good;
    if(old.ok&&m[0].G===old.G&&m[0].t===old.t)post+=c.good;else pre+=c.good;
   }z.oldRootClasses++;
  }
  for(let j=0;j<fullM;j++){
   let par=mod(3*j,2);for(let p of all)res[p]=mod(6*j,p);
   let a=sim(all,res,par,L);if(a.ok){let k=a.path.filter(e=>e.p>y).length;ck(k<=1,"one budget");brute[k]++}z.fullRootClasses++;
  }
  ck(exact.every((n,i)=>n===brute[i])&&pre+post===exact[1],"exact recursion count");
  z.rows.push({y,Y,L,M,fullM,oldSuccess,zero:String(exact[0]),one:String(exact[1]),pre:String(pre),post:String(post),F:Number(exact[0]+exact[1])/fullM,oldF:oldSuccess/M});z.exactControls++;
 }
 let seed=0x71234ab9;function u32(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0}
 function uniform(n){let bound=Math.floor(4294967296/n)*n,x;do{x=u32()}while(x>=bound);return x%n}
 function env(y,L){
  let Y=2*y,P=pr.filter(p=>p<=Y),res=new Int32Array(Y+1),par=uniform(2),xmod=new Int32Array(Y+1),N=L/2+1,heads=new Int32Array(N).fill(-1),ep=[],ec=[],en=[];
  for(let p of P){let r=p===3?0:uniform(p);res[p]=r;let x=mod(r*((p+1)/2),p);if(mod(x,2)!==par)x+=p;xmod[p]=x;for(let e of [-1,1])for(let i=mod((r-e)*((p+1)/2),p);i<N;i+=p){en.push(heads[i]);ep.push(p);ec.push(e===-1?0:p+2);heads[i]=ep.length-1}}
  function go(cut,only=0,forcedR=-1){let G=0,t=0,h=3,path=[],fx=0;
   if(only&&forcedR>=0){fx=mod(forcedR*((only+1)/2),only);if(mod(fx,2)!==par)fx+=only}
   while(true){let p0=0,w0=Infinity;
    for(let k=heads[G/2];k>=0;k=en[k]){let p=ep[k];if(p>cut&&p!==only||p===only&&forcedR>=0)continue;let w=mod(xmod[p]+ec[k]-3-t,2*p)||2*p;if(w<w0||w===w0&&p<p0){p0=p;w0=w}}
    if(only&&forcedR>=0)for(let e of [-1,1])if(mod(forcedR-G-e,only)===0){let w=mod(fx+(e===-1?0:only+2)-3-t,2*only)||2*only;if(w<w0||w===w0&&only<p0){p0=only;w0=w}}
    if(!p0||G+p0-1>L)return {ok:!p0,G,t,h,path};
    path.push({G,t,h,p:p0,w:w0});G+=p0-1;t+=w0;h+=w0-(p0-1)/2;ck(h>=0&&t<=9*G/4+8,"sample potential");
   }
  }return {res,par,go};
 }
 for(let [y,n] of [[96,2048],[384,1536],[1536,1024],[6144,512],[24576,256]]){
  let Y=2*y,L=2*y-2,band=pr.filter(p=>p>y&&p<=Y),sum=band.reduce((s,p)=>s+1/p,0),row={y,n,L,old:0,oldShort:0,full:0,zero:0,one:0,pre:0,post:0,lost:0,recovered:0,shortActivated:0,shortRetained:0,shortRepair:0,forced:0,forcedFit:0,forcedRepair:0,forcedWeight:0,zeroWeight:0,maxHazard:0,maxFrac:0,logControls:[.25,.5,.75].map(alpha=>({alpha,count:0,bound:V(Y)/V(Math.floor(Y**alpha)+1)}))};
  for(let k=0;k<n;k++){
   let E=env(y,L),old=E.go(y),a=E.go(Y);z.randomRoots++;
   if(old.ok)row.old++;if(a.ok)row.full++;if(old.ok&&!a.ok)row.lost++;if(!old.ok&&a.ok)row.recovered++;
   if(old.ok){let c=cert(old,y,Y,0,E.par);row.zeroWeight+=c.prob;row.maxHazard=Math.max(row.maxHazard,c.lambda);row.maxFrac=Math.max(row.maxFrac,c.maxFrac);
    ck([...c.B].every(([p,S])=>!S.has(E.res[p]))===(a.ok&&a.path.every(e=>e.p<=y)),"zero certificate actual");z.fullMatchChecks++;
   }
   if(a.ok){
    let m=a.path.filter(e=>e.p>y);ck(m.length<=1,"actual one");
    if(m.length){row.one++;let p=m[0].p,b=E.go(y,p);ck(b.ok&&JSON.stringify(b.path)===JSON.stringify(a.path),"single replay");let c=cert(b,y,Y,p,E.par);ck([...c.B].every(([q,S])=>!S.has(E.res[q])),"one certificate actual");z.fullMatchChecks++;if(old.ok&&m[0].G===old.G&&m[0].t===old.t)row.post++;else row.pre++}else row.zero++;
    for(let C of row.logControls)if(a.G<=Y**C.alpha)C.count++;
   }
   if(old.ok&&(old.G===0||35*(old.G+10)*2<18*(y-1))){
    row.oldShort++;let act=band.filter(p=>mod(E.res[p]-old.G-1,p)===0||mod(E.res[p]-old.G+1,p)===0);
    let c=cert(old,y,Y,0,E.par);ck([...c.B.values()].every(S=>S.size===2),"short no preemption");z.shortStableChecks++;
    if(!act.length){ck(a.ok&&a.G===old.G&&JSON.stringify(a.path)===JSON.stringify(old.path),"short survives");row.shortRetained++}
    else{row.shortActivated++;if(a.ok)row.shortRepair++;let p=a.path.find(e=>e.p>y);if(p){ck(p.G===old.G&&p.t===old.t,"no early preemption");z.preemptionChecks++}}
    let u=uniform(1<<24)/(1<<24)*sum,p=band.at(-1);for(let q of band){u-=1/q;if(u<0){p=q;break}}
    let r=mod(old.G+(uniform(2)?1:-1),p),b=E.go(y,p,r);row.forced++;z.recoveryTrials++;
    if(old.G+p-1<=L)row.forcedFit++;
    if(b.ok){let m=b.path.filter(e=>e.p===p);ck(m.length===1&&m[0].G===old.G&&m[0].t===old.t,"forced repair path");row.forcedRepair++;z.recoverySuccesses++;let c=cert(b,y,Y,p,E.par);row.forcedWeight+=c.prob;row.maxHazard=Math.max(row.maxHazard,c.lambda);row.maxFrac=Math.max(row.maxFrac,c.maxFrac)}
   }
  }
  row.zeroPred=row.zeroWeight/n;row.F=row.full/n;row.oldF=row.old/n;row.forcedRepairFraction=row.forcedRepair/row.forced;row.forcedWeightedRepair=row.forcedWeight/row.forced;row.activationReciprocal=2*sum;row.shortRecoveryContribution=row.oldShort/n*2*sum*row.forcedWeightedRepair;z.sample.push(row);
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
