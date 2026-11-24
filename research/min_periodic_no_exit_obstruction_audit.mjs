// Exact finite-period no-exit law and full-prefix representative audit.
function audit(Z,W){
 const ps=[];for(let p=3;p<=Z;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const D=2*ps.reduce((a,b)=>a*b,1),lo=ps.filter(p=>p<=W),hi=ps.filter(p=>p>W),DW=2*lo.reduce((a,b)=>a*b,1);
 if(D>1200000||D%W||DW%W)throw Error("period");
 const mod=(a,b)=>(a%b+b)%b,ck=(x,m)=>{if(!x)throw Error(m)},cell=C=>Math.floor((C-1)/W);
 function nxt(t,C,pr){let p=0,n=Infinity;for(let q of pr){let a=mod(C,q);if(a!==1&&a!==q-1)continue;let u=t+2*q-mod(t-(a===1?0:q+2),2*q);if(u<n||(u===n&&q<p)){p=q;n=u}}return {p,n}}
 function path(M,pr){let t=M+2,C=2*M-2,c=cell(C),rec=[];for(;;){let a=nxt(t,C,pr);if(!a.p)return {rec,exit:false,C,t};let C1=C+a.p-1;rec.push({t,C,p:a.p,n:a.n});if(cell(C1)!==c)return {rec,exit:true,C,t,key:[c,C,a.n,a.p].join("/")};t=a.n;C=C1;}}
 let predicted=0,terminalOnly=0,terminalPhases=0,forbidChecks=0,earlyExclusions=0,phaseData=new Map();
 for(let M=3;M<=DW+1;M+=2){
  let a=path(M,lo),id=mod(M,DW),num=0,terminalNum=0;
  if(!a.exit){
   terminalPhases++;num=1;terminalNum=1;
   for(let p of hi){
    let bad=new Set(),last=new Set();
    for(let j=0;j<p;j++){
     let shift=DW*j,cc=a.C+2*shift,tt=a.t+shift;
     if(nxt(tt,cc,[p]).p){bad.add(j);last.add(j);}
     for(let r of a.rec){let e=nxt(r.t+shift,r.C+2*shift,[p]);if(e.n<r.n+shift)bad.add(j);}
    }
    ck(last.size===2&&bad.size>=2,"terminal residues");
    num*=p-bad.size;terminalNum*=p-2;forbidChecks+=p;earlyExclusions+=bad.size-2;
   }
  }
  predicted+=num;terminalOnly+=terminalNum;phaseData.set(id,{pred:num,actual:0});
 }
 let noExit=0,packets=new Map(),vertices=new Map(),N=D/2,roughHorizons=0,repChecks=0,maxLocalHeight=0,fullEvents=0,maxPacket=0;
 // Descending root order: the already counted incidences are exactly larger origins.
 // A tag's rank cannot decrease after sharing an executed event.
 for(let M=D+1;M>=3;M-=2){
  let a=path(M,ps);fullEvents+=a.rec.length;
  if(!a.exit){noExit++;phaseData.get(mod(M,DW)).actual++;}
  else {let m=(packets.get(a.key)||0)+1;packets.set(a.key,m);maxPacket=Math.max(maxPacket,m);}
  let oldRank=0;
  for(let r of a.rec){
   let h=2*r.t-r.C,hh=2*r.n-(r.C+r.p-1);ck(h>=0&&hh>=0,"nonnegative height");maxLocalHeight=Math.max(maxLocalHeight,h,hh);
   let key=[r.C,r.n,r.p].join("/"),rank=(vertices.get(key)||0)+1;
   ck(rank>=oldRank,"no resurrection at executed A");repChecks++;vertices.set(key,rank);oldRank=rank;
  }
 }
 for(let c=2;c<=2*D;c+=2)if(!ps.some(p=>mod(c,p)===1||mod(c,p)===p-1))roughHorizons++;
 for(let a of phaseData.values())ck(a.pred===a.actual,"exact phase probability");
 ck(noExit===predicted&&predicted<=terminalOnly&&terminalOnly<=N,"exact total");
 let actualTotal=0;for(let m of packets.values())actualTotal+=m;
 ck(actualTotal+noExit===N,"conservation");
 let crt=D;for(let p of ps)crt=crt/p*(p-2);ck(roughHorizons===crt,"CRT rough count");
 let caps=[1,2,4,8].map(k=>{let cap=0,large=0;for(let m of packets.values()){cap+=Math.min(k,m);if(m>k)large+=m;}
  ck(N-large<=noExit+cap,"mass concentration inequality");return {k,cap,large,small:N-noExit-large};});
 return {Z,W,D,DW,N,terminalPhases,lowerPhases:DW/2,predicted,noExit,terminalOnly,roughHorizons,forbidChecks,earlyExclusions,fullEvents,repChecks,maxLocalHeight,packets:packets.size,maxPacket,caps}
}
for(const Z of [5,7,11,13,17])for(const W of [2,6,30]){let D=2;for(let p of [3,5,7,11,13,17])if(p<=Z)D*=p;if(D%W===0)console.log(JSON.stringify(audit(Z,W)));}

// Large-prime tail factor checks (conditional lower phases; W30 sampled).
function tailAudit(W,N=256){
 const ps=[];for(let p=3;p<=2000;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const lo=ps.filter(p=>p<=W),hi=ps.filter(p=>p>W),D=2*lo.reduce((a,b)=>a*b,1),threshold=10*W+14;
 const ck=(a,m)=>{if(!a)throw Error(m)},mod=(a,b)=>(a%b+b)%b,cell=C=>Math.floor((C-1)/W);
 function inv(a,p){let r=1,n=p-2;while(n){if(n%2)r=r*a%p;a=a*a%p;n=Math.floor(n/2);}return r;}
 function next(t,C,pr){let p=0,n=Infinity;for(let q of pr){let a=mod(C,q);if(a!==1&&a!==q-1)continue;let u=t+2*q-mod(t-(a===1?0:q+2),2*q);if(u<n||(u===n&&q<p)){p=q;n=u}}return {p,n}}
 let rng=(0x32af71d9^W)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 let count=Math.min(N,D/2),term=0,earlyPairs=0,tailPairs=0,tailClockChecks=0,earlierMax=0,maxForbidden=0,exactZero=0;
 for(let i=0;i<count;i++){
  let M=count===D/2?3+2*i:3+2*(u32()%(D/2)),C=2*M-2,t=M+2,c=cell(C),rec=[];
  let exit=false;for(;;){let a=next(t,C,lo);if(!a.p)break;let C1=C+a.p-1;if(cell(C1)!==c){exit=true;break;}rec.push({C,t,n:a.n});C=C1;t=a.n;}
  if(exit)continue;term++;
  for(let q of hi){let a=inv(mod(2*D,q),q),F=new Set([-1,1].map(s=>mod(mod(s-C,q)*a,q)));ck(F.size===2,"terminal signs");
   for(let x of rec)for(let s of [-1,1]){
    let j=mod(mod(s-x.C,q)*a,q),shift=D*j,e=next(x.t+shift,x.C+2*shift,[q]);ck(e.p===q,"eligible shift");
    let h=2*e.n-(x.C+2*shift+q-1);ck(h>=0,"candidate height nonnegative");
    if(q>threshold){tailClockChecks++;ck(e.n>=x.n+shift,"large candidate cannot preempt");}
    if(e.n<x.n+shift)F.add(j);
   }
   if(q>threshold){ck(F.size===2,"exact tail factor");tailPairs++;}
   if(F.size>2){earlyPairs++;earlierMax=Math.max(earlierMax,q);}
   maxForbidden=Math.max(maxForbidden,F.size);if(F.size===q)exactZero++;
  }
 }
 return {W,D,N:count,terminalPhases:term,threshold,tailPairs,tailClockChecks,earlyPairs,earlierMax,maxForbidden,exactZero};
}
for(const W of [2,6,30])console.log(JSON.stringify(tailAudit(W)));
