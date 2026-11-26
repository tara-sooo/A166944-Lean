// First-passage event barrier, dyadic low-gain rigidity and distinct-section survival.
function audit(){
 const ck=(b,m)=>{if(!b)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=2200000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)spf[n]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function ev(a,v){let p=Infinity,w=Infinity,e=0,q=Infinity;for(let [d,s] of [[a+1,-1],[a-1,1]])for(let r of fs(d)){q=Math.min(q,r);let t=mod((s===-1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e,q}}
 let z={roots:0,events:0,eventThresholdChecks:0,largeLabelCases:0,smallLabelCases:0,firstPassages:0,goodPassages:0,stageControls:0,distinctGoodChecks:0,lossChecks:0,survivalChecks:0,rootTransitions:0,rigidTransitions:0,rigidChecks:0,fixedBudgetChecks:0,roughnessChecks:0,newGoodRoots:0,budgetStops:0,rows:[]};
 for(let R of [12000,48000,192000,480000,1000000]){
  const Hmax=Math.ceil(4*Math.sqrt(2*R+1)),H0=Math.max(64,Math.floor(R**.24)),hs=[H0];while(hs.at(-1)*2<=Hmax)hs.push(hs.at(-1)*2);if(hs.at(-1)<Hmax)hs.push(Hmax);
  const L=Math.floor(Hmax/4),maps=hs.map(H=>new Map()),pass=hs.map(H=>0),good=hs.map(H=>0),newGood=hs.map(H=>0),allGoodTransitions=hs.map(H=>0),rigid=hs.map(H=>0);
  for(let A=6*Math.ceil(R/6);A<=2*R;A+=6){
   let a=A,v=3-A/2,h=3,G=0,W=0,k=0,prev=null;
   while(k<hs.length){
    let x=ev(a,v),b=h+x.w,H=hs[k];
    if(b>H){
     const I=H-h,t=H-3+G/2;
     ck(h<H&&I>0&&I<x.w&&W+I===t&&v+I===H-a/2,"passage");z.firstPassages++;pass[k]++;
     const yes=4*G<=H;
     if(yes){
      ck(I>=H-7*G/4-11-1e-8,"idle bound");let m=maps[k].get(a)||{m:0,minG:Infinity};m.m++;m.minG=Math.min(m.minG,G);maps[k].set(a,m);good[k]++;z.goodPassages++;
     }
     if(prev){
      z.rootTransitions++;
      if(prev.G<=L&&G<=L&&L<18*(prev.H+1)/35-10){ck(a===prev.a&&G===prev.G,"fixed-budget rigidity");z.fixedBudgetChecks++}
      if(prev.yes&&yes){allGoodTransitions[k]++;if(H/4<18*(prev.H+1)/35-10){ck(a===prev.a&&G===prev.G,"dyadic rigidity");rigid[k]++;z.rigidChecks++}}
      if(yes&&!prev.yes){newGood[k]++;z.newGoodRoots++}
     }
     prev={H,a,G,yes};k++;continue
    }
    let G1=G+x.p-1;
    // Check the first possibly over-budget event too, so the bound is
    // not conditioned on a successful passage.
    ck(h<=14+7*G/4+1e-8&&b-2*x.p<=h,"prior clock");ck(G1+1e-8>=18*b/35-10,"universal event barrier");z.eventThresholdChecks++;
    if(x.p<=(2*b+1)/5)z.smallLabelCases++;else{ck(b<=(3*x.p+5)/2,"clock quotient");z.largeLabelCases++}
    if(G1>L){z.budgetStops++;break}
    a-=x.p-1;v+=x.w;W+=x.w;G=G1;h=b-(x.p-1)/2;ck(h>=0&&h<H&&h===3+W-G/2&&W<=9*G/4+8,"event state");z.events++;
   }z.roots++
  }
  let stages=[];
  for(let i=0;i<hs.length;i++){
   let H=hs[i],M=maps[i],C=[...M.values()].reduce((a,m)=>a+m.m*m.m,0),row={H,pass:pass[i],good:good[i],D:M.size,Cper:good[i]?C/good[i]:0,newGood:newGood[i],bothGood:allGoodTransitions[i],rigid:rigid[i]};
   if(i+1<hs.length){
    let J=hs[i+1],M2=maps[i+1],lost=0,kept=0,lostKeys=0,massLost=0,groups=new Map();
    for(let [a,m] of M){
     let x=ev(a,H-a/2);z.distinctGoodChecks++;
     // At the H section the original final idle time is >=9H/16-11.
     // Hence every eligible prime is greater than half of that.
     ck(x.q>9*H/32-5.5-1e-8,"roughness at section");z.roughnessChecks++;
     if(x.w<=J-H){
      lost++;massLost+=m.m;ck(x.p>9*H/32-5.5-1e-8&&x.p<=2*J+1,"loss band");z.lossChecks++;
      let k=x.p+":"+x.e,g=groups.get(k)||{p:x.p,n:0};g.n++;groups.set(k,g);lostKeys++;
     }else{kept++;ck(M2.has(a)&&M2.get(a).minG<=m.minG,"stationary survival");z.survivalChecks++}
    }
    ck(M2.size>=M.size-lost&&kept+lost===M.size,"distinct recurrence");z.stageControls++;
    row.loss=lost;row.kept=kept;row.lostRootMass=massLost;row.lossBandLabels=groups.size;
    row.normalizedLoss=lost*Math.log(H)**3/R;
   }stages.push(row)
  }
  z.rows.push({R,Hmax,L,stages})
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
