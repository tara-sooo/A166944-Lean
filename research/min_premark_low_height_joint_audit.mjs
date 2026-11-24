// Premark low-height rough-jump exclusion, mixed reset first marks, full and stopped paths.
function audit(X,Y=11,mode='stopped'){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=(x,m)=>{if(!x)throw Error(m)},mod=(x,m)=>(x%m+m)%m;
 let L=2;for(let p=3;p<Y;p++)if(spf[p]===p)L*=p;
 const cap=Math.max(2,Math.floor(B/4))*B,T=Math.max(Math.floor(L/4)+1,Math.ceil(X/256)),cell=C=>Math.floor((C-1)/L),kappa=8;
 const H=Math.max(12,Math.floor(Math.sqrt(B))),Q=Math.max(11,Math.ceil(B/2)),R0=Math.max(5,Math.floor((2*Q-H-1)/4)),J=Math.max(7,Math.floor(H/Math.sqrt(Math.log(H))));
 ck(H+4*R0<2*Q||B<60,"separation");
 const head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N),t=new Int32Array(N),K=new Int32Array(N),prev=new Int32Array(N),mark=new Uint8Array(N),high=new Uint8Array(N),largePrior=new Uint8Array(N),nonresetMedium=new Uint8Array(N),kind=new Uint8Array(N),terminal=new Uint8Array(N),admit=new Map();
 let barrier=2n;for(let p=3;p<=Math.min(B,2*H+2);p++)if(spf[p]===p)barrier*=BigInt(p);
 const stats={mode,X,Y,B,N,L,H,Q,R0,J,kappa,T,cap,stop:0,primeStop:0,cellStop:0,twin:0,bad:0,events:0,firstHigh:0,largeCross:0,largeReset:0,mediumNonreset:0,markV:0,markA:0,VTop:0,VTopMixed:0,VNonresetMedium:0,ALong:0,ATop:0,AOther:0,VOther:0,terminalUnmarkedLow:0,terminalUnmarkedHigh:0,stoppedFirstHigh:0,stoppedMarkedLow:0,stoppedMarkedExcluded:0,stoppedMarkedResidual:0,stoppedLowUnmarked:0,terminalCells:0,terminalKeys:0,roughC:0,topC:0,checks:0,largePrior:0,largePriorEvents:0,largePriorReset:0,largePriorNonreset:0,barrierChecks:0,fullResidual:0,fullFirstHigh:0,fullMarked:0,fullExcluded:0,fullUnmarkedLow:0,fullUnmarkedLowNonTwin:0,barrierDigits:String(barrier).length};
 const add=(i,C,entry)=>{next[i]=head[C/2];head[C/2]=i;if(entry)admit.set(cell(C),(admit.get(cell(C))||0)+1)};
 for(let i=0;i<N;i++){let M=X+2*i+1;t[i]=M+2;K[i]=Math.floor((7*M-1)/4);add(i,2*M-2,true)}
 function hit(tt,C,cut){let n=cut+1,p=0;for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(q>B)break;let u=tt+1+mod((s===-1?0:q+2)-tt-1,2*q);if(u<n||(u===n&&q<p)){n=u;p=q}while(v%q===0)v/=q}}return [n,p]}
 function reset(tt,C){return 2*tt-C===(tt%2?6:0)}
 function finish(i,typ){terminal[i]=typ;if(typ===1){stats.stop++;stats.cellStop++}else if(typ===2){stats.stop++;stats.primeStop++}else if(typ===3)stats.twin++;else stats.bad++}
 function markV(C,arr,V){
  for(let [tt,a] of V){
   let ht=2*tt-C;ck(ht>=0,"height");
   for(let i of a)if(!mark[i]&&!high[i]&&ht>=H){high[i]=1;stats.firstHigh++}
   let labels=new Set(a.map(i=>prev[i])),top=[...labels].some(p=>p>=Q),med=[...labels].some(p=>p>=J);
   if(a.length>=kappa){
    for(let i of a)if(!mark[i]){
     if(!high[i]){ck(ht<H,"low mark");if(top){ck(reset(tt,C),"top V reset");kind[i]=1;stats.VTop++;stats.VTopMixed+=labels.has(0)||[...labels].some(p=>p>0&&p<Q)}
      else if(!reset(tt,C)&&med){ck(!labels.has(0)&&labels.size>=2,"nonreset distinct");kind[i]=2;stats.VNonresetMedium++}
      else{kind[i]=3;stats.VOther++}
     }
     mark[i]=1;stats.markV++;
    }
   }
  }
 }
 for(let b=cell(2*X);b<=cell(7*X-2);b++){
  let m=admit.get(b)||0;if(!m)continue;let boundary=b*L,lo=Math.max(2*X,boundary+2),hi=Math.min(7*X-2,boundary+L),stopCell=mode==='stopped'&&m>=T;if(stopCell)stats.terminalCells++;
  for(let C=lo;C<=hi;C+=2){
   let arr=[],V=new Map(),i=head[C/2];head[C/2]=-1;
   while(i>=0){let j=next[i];arr.push(i);if(!V.has(t[i]))V.set(t[i],[]);V.get(t[i]).push(i);i=j}
   if(!arr.length)continue;
   markV(C,arr,V);
   if(stopCell){for(let i of arr){if(!mark[i]){if(high[i])stats.terminalUnmarkedHigh++;else{stats.terminalUnmarkedLow++;ck(V.get(t[i]).length<kappa,"unmarked V cap")}}finish(i,1)}continue}
   let r=Math.min(spf[C-1],spf[C+1]),groups=new Map(),A=new Map();if(r>R0)stats.roughC++;
   for(let i of arr){let [n,p]=hit(t[i],C,K[i]);if(!p){finish(i,spf[C-1]===C-1&&spf[C+1]===C+1?3:4);continue}
    ck(n-t[i]<=2*r&&r<=p,"wait");
    if(!groups.has(p))groups.set(p,[]);groups.get(p).push([i,n]);let key=n*B+p;if(!A.has(key))A.set(key,{p,n,ids:[]});A.get(key).ids.push(i)
   }
   let topAtC=false;
   for(let {p,n,ids} of A.values()){
    if(ids.length>=kappa){
     let top=ids.some(i=>prev[i]>=Q);if(top)topAtC=true;
     for(let i of ids)if(!mark[i]){
      ck(V.get(t[i]).length<kappa,"parent cap");
      if(!high[i]){
       ck(2*t[i]-C<H,"low A mark");
       if(r>R0){kind[i]=4;stats.ALong++}
       else if(top){let wit=ids.find(j=>prev[j]>=Q);ck(Math.abs(t[i]-t[wit])<2*r,"reverse interval");ck(reset(t[wit],C),"top A reset");kind[i]=5;stats.ATop++}
       else{kind[i]=6;stats.AOther++}
      }
      mark[i]=1;stats.markA++;
     }
    }
   }
   stats.topC+=topAtC;
   for(let [p,a] of groups){
    if(mode==='stopped'&&p>=Y&&a.length>=Math.ceil(cap/p)){stats.terminalKeys++;for(let [i,n] of a){if(!mark[i]){if(high[i])stats.terminalUnmarkedHigh++;else{stats.terminalUnmarkedLow++;ck(A.get(n*B+p).ids.length<kappa,"unmarked A cap")}}finish(i,2)}continue}
    for(let [i,n] of a){
     let C1=C+p-1,h0=2*t[i]-C,h1=2*n-C1,unmarked=!mark[i]&&!high[i];ck(h1>=0,"post height");
     if(unmarked){
      ck(A.get(n*B+p).ids.length<kappa&&h0<H,"pre cap");
      if(p>2*H+2){ck(8*r>=p,"large label roughness");stats.largePriorEvents++;if(reset(n,C1))stats.largePriorReset++;else stats.largePriorNonreset++;if(!largePrior[i]){largePrior[i]=1;stats.largePrior++}}
      if(!largePrior[i]){let C0=2*(X+2*i+1)-2;ck((BigInt(C1)-1n)/barrier===(BigInt(C0)-1n)/barrier,"premark barrier");stats.barrierChecks++}
      if(p>H){
       if(h1>=H){ck(!reset(n,C1)&&h1>=(n%2?6:0)+2*p&&4*r>=3*p-1-h0,"large crossing");stats.largeCross++}
       else{ck(reset(n,C1),"large noncross reset");stats.largeReset++}
      }
      if(h1<H&&!reset(n,C1)&&p>=J){ck(h1>=(n%2?6:0)+2*p,"medium arrival height");if(!nonresetMedium[i]){nonresetMedium[i]=1;stats.mediumNonreset++}}
     }
     t[i]=n;prev[i]=p;stats.events++;add(i,C1,cell(C1)!==b)
    }
   }
  }
 }
 for(let i=0;i<N;i++)if(terminal[i]===1||terminal[i]===2){if(high[i])stats.stoppedFirstHigh++;else if(mark[i]){stats.stoppedMarkedLow++;if([1,2,4,5].includes(kind[i])||nonresetMedium[i]||largePrior[i])stats.stoppedMarkedExcluded++;else stats.stoppedMarkedResidual++}else stats.stoppedLowUnmarked++}
 if(mode==='full')for(let i=0;i<N;i++){if(high[i])stats.fullFirstHigh++;else if(mark[i]){stats.fullMarked++;if([1,2,4,5].includes(kind[i])||nonresetMedium[i]||largePrior[i])stats.fullExcluded++;else stats.fullResidual++}else{stats.fullUnmarkedLow++;if(terminal[i]===4&&!largePrior[i])stats.fullUnmarkedLowNonTwin++;}}
 if(mode==='full')ck(stats.fullFirstHigh+stats.fullExcluded+stats.fullResidual+stats.fullUnmarkedLow===N,"full partition");
 ck(stats.stop+stats.twin+stats.bad===N,"conservation");
 ck(stats.stop===stats.stoppedFirstHigh+stats.stoppedMarkedExcluded+stats.stoppedMarkedResidual+stats.stoppedLowUnmarked,"joint partition");
 ck(stats.markV+stats.markA<=N,"first marks");return stats;
}
for(const x of process.argv.slice(2).map(Number))for(const mode of ['stopped','full'])console.log(JSON.stringify(audit(x,11,mode)));
