// Root-slice sieve prerequisites and finite-label first-exit packet comparison.
function audit(X,W){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,spf=new Int32Array(7*X+4),ps=[];
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i<=Math.min(W,B)&&i>2)ps.push(i);if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)},cell=C=>Math.floor((C-1)/W);
 let D=2n;for(let p of ps)D*=BigInt(p);ck(D%BigInt(W)===0n,"period contains cell");
 const phases=new Map(),stats={X,W,B,N,D:String(D),fullExits:0,noExit:0,largeExits:0,veryLargeExits:0,lowerExits:0,lowerTerminal:0,phaseChecks:0,terminalChecks:0,roughChecks:0,congruenceChecks:0,candidateRoots:0,candidatePairs:0,largeDistinctKeys:0,largeMaxPacket:0,fullExitMaxP:0,largeExitMaxP:0,lowerTerminalMaxGain:0,lowerTerminalMaxTime:0,actualMaxLocalGain:0,actualMaxLocalHeight:0,largeMassByBand:[0,0,0],candidatesByBand:[0,0,0],largeExitGainSum:0,largeExitTimeSum:0};
 const keys=new Map(),threshold=10*W+14, Z=Math.min(B,Math.max(threshold+1,32*W)),fullPackets=new Map(),cutPackets=new Map(),sharedPackets=new Map();let mismatch=0,cutExits=0;const key=(c,C,n,p)=>[c,C,n,p].join('/'),inc=(map,k)=>map.set(k,(map.get(k)||0)+1);
 function next(t,C,lim){
  let n=Infinity,p=0,sgn=0,r=Infinity;
  for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(q>lim)break;r=Math.min(r,q);let u=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(u<n||(u===n&&q<p)){n=u;p=q;sgn=s}while(v%q===0)v/=q}}
  return {n,p,sgn,r};
 }
 function lower(M){
  let t=M+2,C=2*M-2,c=cell(C),events=0;
  for(;;){let e=next(t,C,Math.min(W,B));if(!e.p)return {kind:0,g:C-(2*M-2),dt:t-(M+2),events};let C1=C+e.p-1;if(cell(C1)!==c)return {kind:1,g:C-(2*M-2),dt:t-(M+2),events,p:e.p};t=e.n;C=C1;events++;}
 }
 function truncated(M,lim){let t=M+2,C=2*M-2,c=cell(C);for(;;){let e=next(t,C,lim);if(!e.p)return null;let C1=C+e.p-1;if(cell(C1)!==c)return {key:key(c,C,e.n,e.p),p:e.p,n:e.n};t=e.n;C=C1;}}
 function band(p){return p<32*W?0:p<128*W?1:2}
 for(let i=0;i<N;i++){
  let M=X+2*i+1,C0=2*M-2,t0=M+2,K=Math.floor((7*M-1)/4),c=cell(C0),phase=String(BigInt(M)%D),low=lower(M),prev=phases.get(phase);
  if(prev){ck(JSON.stringify(prev)===JSON.stringify(low),"root-slice periodicity");stats.phaseChecks++}else phases.set(phase,low);
  if(low.kind===1)stats.lowerExits++;else{
   stats.lowerTerminal++;stats.lowerTerminalMaxGain=Math.max(stats.lowerTerminalMaxGain,low.g);stats.lowerTerminalMaxTime=Math.max(stats.lowerTerminalMaxTime,low.dt);
  }
  let candidates=new Set();
  if(low.kind===0){let C=C0+low.g,r=next(t0+low.dt,C,B).r;
   for(let s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;if(p>threshold&&8*r>p){candidates.add(p);stats.candidatePairs++;stats.candidatesByBand[band(p)]++;ck((C+s)%p===0,"candidate divisor");}while(v%p===0)v/=p;}}
   if(candidates.size)stats.candidateRoots++;
  }
  let C=C0,t=t0,events=0,found=false,actual=null;const cut=truncated(M,Z);if(cut&&cut.n<=K){cutExits++;inc(cutPackets,cut.key)}
  for(;;){
   let e=next(t,C,B);if(e.n>K||!e.p)break;
   let C1=C+e.p-1;
   if(cell(C1)!==c){
    found=true;actual={key:key(c,C,e.n,e.p),p:e.p};inc(fullPackets,actual.key);stats.fullExits++;stats.fullExitMaxP=Math.max(stats.fullExitMaxP,e.p);
    let g=C-C0,dt=t-t0,h=2*t-C;
    ck(g>=0&&g<W&&dt<=3*g&&h===6+2*dt-g&&h<=6+5*W,"local prefix bound");
    stats.actualMaxLocalGain=Math.max(stats.actualMaxLocalGain,g);stats.actualMaxLocalHeight=Math.max(stats.actualMaxLocalHeight,h);
    if(e.p>threshold){
     stats.largeExits++;stats.largeMassByBand[band(e.p)]++;stats.largeExitMaxP=Math.max(stats.largeExitMaxP,e.p);
     ck(e.n-t>2*W&&8*e.r>e.p,"large rough wait");stats.roughChecks++;
     ck(low.kind===0&&low.g===g&&low.dt===dt&&low.events===events,"lower terminal match");stats.terminalChecks++;
     ck(candidates.has(e.p),"candidate coverage");
     ck(mod(2*M-2+low.g+e.sgn,e.p)===0,"root congruence");stats.congruenceChecks++;
     let key=[c,C,e.n,e.p].join("/");keys.set(key,(keys.get(key)||0)+1);stats.largeExitGainSum+=g;stats.largeExitTimeSum+=dt;
     if(e.p>128*W)stats.veryLargeExits++;
    }
    break;
   }
   ck(e.p<=W&&C1-C<W,"internal prime");C=C1;t=e.n;events++;
  }
  if(!found)stats.noExit++;const cv=cut&&cut.n<=K?cut:null;if((actual?.key??null)!==(cv?.key??null)){mismatch++;ck(actual&&actual.p>Z,'only super-cutoff exit differs')}else if(actual)inc(sharedPackets,actual.key);
 }
 stats.Z=Z;stats.cutExits=cutExits;stats.cutMismatches=mismatch;stats.packetComparison=[1,2,4,8,16].map(k=>{const calc=m=>[...m.values()].reduce((s,x)=>s+Math.min(k,x),0),large=m=>[...m.values()].filter(x=>x>k).reduce((s,x)=>s+x,0);let a=calc(fullPackets),b=calc(cutPackets),c=calc(sharedPackets),u=large(fullPackets),v=large(cutPackets);ck(a-c<=mismatch&&b-c<=mismatch&&Math.abs(a-b)<=mismatch,'cap comparison');ck(Math.abs(u-v)<=(k+1)*mismatch,'tail comparison');return {k,fullCap:a,cutCap:b,sharedCap:c,fullLarge:u,cutLarge:v}});stats.largeDistinctKeys=keys.size;stats.largeMaxPacket=Math.max(0,...keys.values());stats.phaseCount=phases.size;
 ck(stats.fullExits+stats.noExit===N&&stats.largeExits<=stats.candidateRoots,"partition");
 return stats;
}
for(const x of process.argv.slice(2).map(Number))for(const W of [2,6,30,210])console.log(JSON.stringify(audit(x,W)));
