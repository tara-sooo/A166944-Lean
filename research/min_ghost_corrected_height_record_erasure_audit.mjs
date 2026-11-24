// Exact corrected-height lattice and nonoverlapping backward record erasure.
function audit(U,N=128){
 const V=4*U,ps=[],sv=new Uint8Array(V+1);
 for(let p=2;p<=V;p++)if(!sv[p]){if(p>2)ps.push(p);if(p*p<=V)for(let q=p*p;q<=V;q+=p)sv[q]=1}
 const mod=(x,p)=>(x%p+p)%p,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x912ac53f^U)>>>0;
 function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let a=4294967296-4294967296%p,x;do{x=u32()}while(x>=a);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),last=new Int32Array(ps.length),best=new Int32Array(ps.length);
 const configs=[0,5,7,11],out={U,V,N,events:0,repeatEvents:0,nonrecords:0,recordRepeats:0,shortOpposite:0,positiveRecordChecks:0,peakSum:0,freshWaitSum:0,checks:0,scans:configs.map(A=>({A,L:A?2*ps.filter(p=>p<A).reduce((a,b)=>a*b,1):0,steps:0,erasedIntervals:0,erasedEvents:0,erasedElapsed:0,erasedGain:0,erasedNet:0,ordinaryElapsed:0,ordinaryGain:0,ordinaryNet:0,ordinaryFreshPos:0,ordinaryRecordPos:0,allRepeatPos:0,allRecordPos:0,repeatPositiveRemoved:0,strictErase:0,eraseCredit:0,ordinaryNegative:0,netRepeatAfterEraseCredit:0,netRepeatAfterAllCredit:0,positiveNetAfterErasePaths:0,positiveNetAfterAllPaths:0,positivePeakPaths:0,zeroRetainedRecordPos:0,maxIntervals:0}))};
 for(let n=0;n<N;n++){
  let parity=uni(2);last.fill(0);best.fill(0);
  for(let j=0;j<ps.length;j++){let p=ps[j];c[j]=uni(p);let a=uni(p);t[j]=a%2===parity?a:a+p;}
  let s=0,g=0,D=0,imax=0,fw=0,seq=[{s:0,g:0,h:0,J:-6*parity,chi:parity,p:0,fresh:false,old:0,best:0,w:0}];
  for(;;){
   let w=Infinity,b=-1;for(let j=0;j<ps.length;j++){let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let a=2*p-mod(t[j]+s-(cc===1?0:p+2),2*p);if(a<w||(a===w&&p<ps[b])){w=a;b=j}}
   if(s+w>U)break;
   let p=ps[b],old=last[b],prevBest=best[b],fresh=!old,pre=g;s+=w;g+=p-1;let chi=(parity+s)%2,h=2*s-g,J=h-6*chi,idx=seq.length;
   ck(w<=2*p&&mod(c[b]+pre,p)===(chi?p-1:1)&&mod(t[b]+s,p)===(chi?2%p:0),"clock and sign");
   ck(mod(J-c[b]+2*t[b],p)===0&&J%2===0,"height residue");
   if(fresh)fw+=w;else{
    out.repeatEvents++;let x=seq[old],ds=s-x.s,dg=g-x.g,dchi=chi-x.chi,dJ=J-x.J,m=(dg+2*dchi)/(2*p),l=(ds-(p+2)*dchi)/(2*p);
    ck(Number.isInteger(m)&&Number.isInteger(l)&&dJ===2*p*(2*l+dchi-m),"exact repeat lattice");
    if(p>=5){ck(m>=1,"positive gain stride");if(dJ>0){ck(ds>=(dchi===0?2*p:3*p+2*dchi),"positive return time");out.positiveRecordChecks++}if(ds<2*p){ck(dchi!==0&&dJ<=0,"rapid repeat nonpositive");out.shortOpposite++;}}
    if(J<=seq[prevBest].J)out.nonrecords++;else{out.recordRepeats++;ck(J-seq[prevBest].J>=2*p,"strict record lattice");}
   }
   seq.push({s,g,h,J,chi,p,fresh,old,best:prevBest,w});last[b]=idx;if(!prevBest||J>=seq[prevBest].J)best[b]=idx;
   if(h>D){D=h;imax=idx;}
   out.events++;out.checks++;
  }
  out.peakSum+=D;out.freshWaitSum+=fw;
  for(let cfg of out.scans){
   let A=cfg.A,L=cfg.L,high=[0];for(let j=1;j<=imax;j++)if(!A||seq[j].p>=A)high.push(j);
   let end=high.length-1,tail=seq[imax].J-seq[high[end]].J;
   if(A)ck(tail<=5*L+6,"tail bound");else ck(tail===0,"no tail");
   let posAll=0,posRec=0,retRec=0,retFresh=0,netOrd=0,netErase=0,erTime=0,erGain=0,ordTime=0,ordGain=0,removed=0,nErase=0,nOrd=0,strict=0,negative=0,cover=new Uint8Array(imax+1),loc=new Map(high.map((v,k)=>[v,k]));
   for(let k=1;k<=end;k++){
    let x=seq[high[k]],y=seq[high[k-1]],a=x.J-y.J;
    if(A)ck(a<=2*x.w-(x.p-1)+5*L+6,"ordinary high bound");
    else ck(a<=2*x.w-(x.p-1)+6,"ordinary all bound");
    if(!x.fresh){posAll+=Math.max(0,a);if(x.J>seq[x.best].J)posRec+=Math.max(0,a);}
   }
   for(let k=end;k>0;){
    let x=seq[high[k]],y=seq[high[k-1]],target=k-1,erase=!x.fresh&&x.J<=seq[x.best].J;
    if(erase){target=loc.get(x.best);ck(Number.isInteger(target)&&target<k,"erase predecessor");y=seq[high[target]];let d=x.J-y.J;ck(d<=0&&d%(2*x.p)===0,"erase nonpositive");netErase+=d;strict+=+(d<0);erTime+=x.s-y.s;erGain+=x.g-y.g;removed+=high[k]-high[target];nErase++;}
    else{let d=x.J-y.J;netOrd+=d;negative+=Math.max(0,-d);ordTime+=x.s-y.s;ordGain+=x.g-y.g;nOrd++;
     if(x.fresh)retFresh+=Math.max(0,d);else{ck(x.J>seq[x.best].J&&x.J-seq[x.best].J>=2*x.p,"retained record");retRec+=Math.max(0,d);if(x.p>=Math.max(17,10*L+14)&&d>0)ck(4*x.w>x.p,"long wait necessity");}
    }
    for(let j=high[target]+1;j<=high[k];j++){ck(!cover[j],"disjoint intervals");cover[j]=1}
    k=target;
   }
   let x=seq[high[end]];
   ck(netOrd+netErase===x.J-seq[0].J&&erTime+ordTime===x.s&&erGain+ordGain===x.g&&netErase<=0,"telescoping");
   for(let j=1;j<=high[end];j++)ck(cover[j]===1,"coverage");
   ck(retRec<=posRec&&posRec<=posAll&&D<=retFresh+retRec+(A?5*L+12:6),"peak");
   let rem=Math.max(0,retRec+netErase),rem2=Math.max(0,retRec+netErase-negative);ck(D<=retFresh+rem2+(A?5*L+12:6),'credit peak');if(A)ck(nErase*(A-2)<=erTime&&erGain>=2*erTime-6*nErase,'erase resource');cfg.strictErase+=strict;cfg.eraseCredit-=netErase;cfg.ordinaryNegative+=negative;cfg.netRepeatAfterEraseCredit+=rem;cfg.netRepeatAfterAllCredit+=rem2;cfg.positiveNetAfterErasePaths+=+(rem>0);cfg.positiveNetAfterAllPaths+=+(rem2>0);cfg.steps+=nOrd;cfg.erasedIntervals+=nErase;cfg.erasedEvents+=removed;cfg.erasedElapsed+=erTime;cfg.erasedGain+=erGain;cfg.erasedNet+=netErase;cfg.ordinaryElapsed+=ordTime;cfg.ordinaryGain+=ordGain;cfg.ordinaryNet+=netOrd;cfg.ordinaryFreshPos+=retFresh;cfg.ordinaryRecordPos+=retRec;cfg.allRepeatPos+=posAll;cfg.allRecordPos+=posRec;cfg.repeatPositiveRemoved+=posAll-retRec;cfg.positivePeakPaths+=+(D>0);cfg.zeroRetainedRecordPos+=+(D>0&&retRec===0);cfg.maxIntervals=Math.max(cfg.maxIntervals,nErase);
  }
 }
 return out;
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?128:256)));
