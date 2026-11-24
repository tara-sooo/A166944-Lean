// Common CRT finite-alphabet sample: fresh completed waits, signed repeat bank, and low-block surplus.
function sample(U,N=512){
 const V=4*U,z=Math.ceil(Math.sqrt(2*U)),sieve=new Uint8Array(V+1),ps=[];
 for(let p=2;p<=V;p++)if(!sieve[p]){if(p>2)ps.push(p);if(p*p<=V)for(let q=p*p;q<=V;q+=p)sieve[q]=1}
 let rng=(0x7bb192cd^U)>>>0;
 function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let a=4294967296-4294967296%p,x;do{x=u32()}while(x>=a);return x%p}
 const ck=(b,m)=>{if(!b)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),seen=new Uint8Array(ps.length);
 const hi=ps.filter(p=>p>=z),tail=new Float64Array(hi.length+1);
 for(let i=hi.length-1;i>=0;i--)tail[i]=tail[i+1]+1/hi[i]**2;
 const bound=new Float64Array(U+1);let j=0;for(let w=1;w<=U;w++){while(j<hi.length&&2*hi[j]<w)j++;bound[w]=2*w*tail[j]}
 const bp=new Float64Array(U+1);for(let w=1;w<=U;w++)bp[w]=bp[w-1]+bound[w];
 const cuts=[5,7,11],Ls=[6,30,210],blockSums=cuts.map(A=>({A,initPeak:0,freshBlockPos:0,repeatBlockPos:0,repeatMediumPos:0,repeatLargePos:0,repeatLargeCount:0,repeatLargePositive:0,freshBlocks:0,repeatBlocks:0,peakAfterBlocks:0,repeatPosAboveTenth:0,checks:0})); const rec=[];let sum={freshWait:0,freshLowWait:0,freshHighWait:0,repeatWait:0,freshGain:0,repeatGain:0,freshPos:0,repeatPos:0,freshNeg:0,repeatNeg:0,lastTime:0,peak:0,bankPeak:0,repeatNetPeak:0,highCompensator:0,events:0,freshEvents:0,repeatEvents:0,peakQuarter:0,freshWaitQuarter:0,bankPeakQuarter:0,allNoRepeat:0,freshWaitAboveTenth:0,checks:0};
 for(let a=0;a<N;a++){
  let parity=uni(2);seen.fill(0);
  for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let v=uni(p);t[i]=v%2===parity?v:v+p}
  const blocks=cuts.map((A,j)=>({A,L:Ls[j],base:0,lowMax:0,lowSigned:0,p:0,w:0,fresh:false,initPeak:0,freshPos:0,repeatPos:0,medium:0,large:0,freshN:0,repeatN:0,largeN:0,largePositive:0}));
 function close(b){ck(b.lowMax<=5*b.L,'low barrier peak');if(!b.p){b.initPeak=b.lowMax;return}let gain=Math.max(0,2*b.w-(b.p-1)+b.lowMax);if(b.fresh){b.freshPos+=gain;b.freshN++;ck(gain<=2*b.w+Math.max(0,5*b.L-b.p+1),'fresh block bound')}else{b.repeatPos+=gain;b.repeatN++;if(b.p<10*b.L+2)b.medium+=gain;else{b.large+=gain;b.largeN++;if(gain>0){b.largePositive++;ck(4*b.w>b.p,'large positive repeat requires wait')}}}}
 let e=0,g=0,fw=0,rw=0,fg=0,rg=0,fp=0,rp=0,fn=0,rn=0,fl=0,fh=0,D=0,bank=0,rnet=0,n=0,nf=0,comp=0;
  for(;;){
   let w=Infinity,b=-1;
   for(let i=0;i<ps.length;i++){let p=ps[i],cc=(c[i]+g)%p;if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[i]+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[b])){w=f;b=i}}
   if(e+w>U){comp+=bp[U-e];break}
   comp+=bp[w];let p=ps[b],d=2*w-(p-1);
   ck(w<=2*p,"wait bound");
   for(let b0 of blocks){if(p>=b0.A){close(b0);b0.p=p;b0.w=w;b0.fresh=!seen[b];b0.lowMax=0;b0.lowSigned=0;}else{b0.lowSigned+=d;b0.lowMax=Math.max(b0.lowMax,b0.lowSigned);}}

   if(!seen[b]){seen[b]=1;nf++;fw+=w;fg+=p-1;fp+=Math.max(0,d);fn+=Math.max(0,-d);if(p<z)fl+=w;else fh+=w}
   else{rw+=w;rg+=p-1;rp+=Math.max(0,d);rn+=Math.max(0,-d)}
   e+=w;g+=p-1;n++;
   ck(fw+rw===e&&fg+rg===g&&fp-fn===2*fw-fg&&rp-rn===2*rw-rg,"signed ledger");
   let bnow=2*rw-rg-fg;bank=Math.max(bank,bnow);rnet=Math.max(rnet,2*rw-rg);D=Math.max(D,2*e-g);
   ck(D<=2*fw+bank&&D<=fp+rp,"peak bound");
   sum.checks++;
  }
  for(let j=0;j<blocks.length;j++){let b=blocks[j],s=blockSums[j];close(b);ck(D<=b.initPeak+b.freshPos+b.repeatPos,'block peak');ck(b.repeatPos===b.medium+b.large,'block repeat split');s.initPeak+=b.initPeak;s.freshBlockPos+=b.freshPos;s.repeatBlockPos+=b.repeatPos;s.repeatMediumPos+=b.medium;s.repeatLargePos+=b.large;s.repeatLargeCount+=b.largeN;s.repeatLargePositive+=b.largePositive;s.freshBlocks+=b.freshN;s.repeatBlocks+=b.repeatN;s.peakAfterBlocks+=b.initPeak+b.freshPos+b.repeatPos;s.repeatPosAboveTenth+=b.repeatPos>U/10;s.checks++;}
  ck(fl+fh===fw&&fl<=2*ps.filter(p=>p<z).reduce((s,p)=>s+p,0),"small fresh deterministic budget");
  let row={freshWait:fw,freshLowWait:fl,freshHighWait:fh,repeatWait:rw,freshGain:fg,repeatGain:rg,freshPos:fp,repeatPos:rp,freshNeg:fn,repeatNeg:rn,lastTime:e,peak:D,bankPeak:bank,repeatNetPeak:rnet,highCompensator:comp,events:n,freshEvents:nf,repeatEvents:n-nf};
  for(let k of Object.keys(row))sum[k]+=row[k];
  sum.peakQuarter+=D>U/4;sum.freshWaitQuarter+=fw>U/4;sum.freshWaitAboveTenth+=fw>U/10;sum.bankPeakQuarter+=bank>U/4;sum.allNoRepeat+=n===nf;rec.push(row);
 }
 const mean={};for(let k of Object.keys(rec[0]))mean[k]=sum[k]/N;
 return {U,V,z,N,primes:ps.length,smallFreshBound:2*ps.filter(p=>p<z).reduce((s,p)=>s+p,0),uniformHighCompensatorBound:U*bound.reduce((a,b)=>Math.max(a,b),0),mean,counts:{peakQuarter:sum.peakQuarter,freshWaitQuarter:sum.freshWaitQuarter,freshWaitAboveTenth:sum.freshWaitAboveTenth,bankPeakQuarter:sum.bankPeakQuarter,allNoRepeat:sum.allNoRepeat},checks:sum.checks,blocks:blockSums.map(s=>Object.fromEntries(Object.entries(s).map(([k,v])=>[k,k==='A'||k==='checks'||k==='repeatPosAboveTenth'||k==='repeatLargeCount'||k==='repeatLargePositive'?v:v/N])))};
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(sample(U,U>=65536?256:512)));
