// Fresh-to-known high transition and bounded comparable chain ledger.
function audit(U,N=256,A=5,F=2,rmax=3){
 const V=4*U,z=Math.ceil(Math.sqrt(2*U)),sieve=new Uint8Array(V+1),ps=[];
 for(let p=2;p<=V;p++)if(!sieve[p]){if(p>2)ps.push(p);if(p*p<=V)for(let q=p*p;q<=V;q+=p)sieve[q]=1}
 const L=2*ps.filter(p=>p<A).reduce((a,b)=>a*b,1),K=3;
 const mod=(x,p)=>(x%p+p)%p,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x72ae9f13^U^A)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let a=4294967296-4294967296%p,x;do{x=u32()}while(x>=a);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),seen=new Uint8Array(ps.length),nlong=new Int32Array(ps.length);
 let out={U,V,N,A,L,F,rmax,z,K,events:0,peakSum:0,freshWaitSum:0,seenSum:0,firstHighPairs:0,smallFreshPairs:0,largeFreshPairs:0,largeFreshSelfPairs:0,largeCongruenceChecks:0,smallTicketBudget:0,largeTicketBudget:0,pairWeight:0,pairWait:0,chainRepeats:0,chainWeight:0,chainSurplus:0,allRepeatSurplus:0,residualSurplus:0,ratioFailures:0,depthFailures:0,earlySmallLong:0,earlySmallWeight:0,earlySmallSurplus:0,checks:0};
 for(let a=0;a<N;a++){
  let parity=uni(2);seen.fill(0);nlong.fill(0);
  for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let x=uni(p);t[i]=x%2===parity?x:x+p;}
  let e=0,g=0,peak=0,fw=0,known=[],prev=null,block=null,chainDepth=0,chainGood=false,pair=0,chain=0,small=0,ticket=0,smallBudget=0,early=0,chainSurp=0,earlySurp=0,allSurp=0,resSurp=0;
  function close(){if(!block)return;ck(block.lowGain<L&&block.lowMax<=5*L,"low suffix");let b=Math.max(0,block.d+block.lowMax);if(block.rep){allSurp+=b;if(block.mark){chainSurp+=b;ck(b<=(4+5*L/A)*block.p,"chain positive bound")}else resSurp+=b;if(block.early)earlySurp+=b;} }
  for(;;){
   let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[j]+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i])){w=f;i=j}}
   if(e+w>U)break;
   let p=ps[i],rep=!!seen[i],dh=2*w-p+1,mark=false,isEarly=false;ck(w<=2*p,"wait");out.checks++;
   if(rep&&p<z&&4*w>p){nlong[i]++;if(nlong[i]<=K){early+=p;isEarly=true;out.earlySmallLong++;}}
   if(p>=A){
    close();
    if(!rep){
     chainDepth=0;chainGood=true;
     let tickets=new Set();
     if(p<z){smallBudget+=F*p;}
     else if(p>L+3){
      for(let j of known){let q=ps[j];if(q<A||q>F*p)continue;
       for(let d=0;d<L;d+=2)if([1,q-1].includes(mod(c[j]+g+p-1+d,q))){tickets.add(j);break;}}
      for(let j of tickets)ticket+=ps[j];
     }
     prev={i,p,g,fresh:true,tickets};
    }else{
     chainDepth++;
     if(chainGood&&p>F*prev.p){chainGood=false;out.ratioFailures++;}
     if(chainGood&&chainDepth<=rmax){mark=true;chain+=p;out.chainRepeats++;}
     else if(chainGood&&chainDepth===rmax+1)out.depthFailures++;
     if(prev.fresh&&p<=F*prev.p){
      pair+=p;out.firstHighPairs++;out.pairWait+=w;
      if(prev.p<z){small+=p;out.smallFreshPairs++}
      else {
       out.largeFreshPairs++;let d=g-prev.g-prev.p+1;ck(d>=0&&d<L&&d%2===0,"intermediate gain");
       if(i===prev.i){out.largeFreshSelfPairs++;ck(prev.p<=L+3,"self return impossible above LOW");}
       else{ck(prev.tickets.has(i),"known-p ticket");out.largeCongruenceChecks++}
      }
     }
     prev={i,p,g,fresh:false};
    }
    block={p,rep,d:dh,low:0,lowMax:0,lowGain:0,mark,early:isEarly};
   }else if(block){block.low+=dh;block.lowGain+=p-1;block.lowMax=Math.max(block.lowMax,block.low);}
   if(!rep){seen[i]=1;known.push(i);fw+=w;}
   e+=w;g+=p-1;peak=Math.max(peak,2*e-g);out.events++;
  }close();
  let geom=0;for(let j=0;j<rmax;j++)geom+=F**j;
  ck(small<=smallBudget&&pair-small<=ticket,"pair ticket ledger");
  ck(chain<=geom*pair&&chainSurp<=(4+5*L/A)*chain+1e-8&&allSurp===chainSurp+resSurp,"chain ledger");
  ck(early<=K*ps.filter(p=>p<z).reduce((a,b)=>a+b,0),"small initial repeat budget");
  out.peakSum+=peak;out.freshWaitSum+=fw;out.seenSum+=known.length;out.smallTicketBudget+=smallBudget;out.largeTicketBudget+=ticket;out.pairWeight+=pair;out.chainWeight+=chain;out.chainSurplus+=chainSurp;out.allRepeatSurplus+=allSurp;out.residualSurplus+=resSurp;out.earlySmallWeight+=early;out.earlySmallSurplus+=earlySurp;
 }
 return out;
}
for(const U of process.argv.slice(2).map(Number))for(const A of [5,7])if(Math.ceil(Math.sqrt(2*U))>2*[3,5].filter(p=>p<A).reduce((a,b)=>a*b,1)+3)console.log(JSON.stringify(audit(U,U>=65536?128:256,A)));
