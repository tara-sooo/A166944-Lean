// Exact canonical reentry from reset states, and root-free deficit bounds.
function audit(N=150000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)spf[j]=i}
 function gcd(a,b){while(b)[a,b]=[b,a%b];return Math.abs(a)}
 const mod=(a,b)=>(a%b+b)%b;
 function tick(n,H){let e=n%2?-1:1,g=gcd(e===1?n:n-2,H-e);if(g===1)return 0;let p=spf[g];return p*p<=H+1?p:0}
 function next(t,H){let best=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}}return best}
 const root=(t,H)=>H%4===0&&2*t-H===6;
 function predict(H){let b=[];while(H%3===2||H%5===1){b.push(H%3===2?3:5);H+=4;if(b.length>2)throw Error("blocks")}return b}
 function resetCheck(H){let t=H/2,b=predict(H),expected=b.flatMap(p=>p===3?[3,3]:[0,5]).concat([0,0,0]);
 for(let p0 of expected){let p=tick(++t,H);if(p!==p0)throw Error("reset tick");if(p)H+=p-1}
 if(!root(t,H))throw Error("root");return {blocks:b.length,ticks:expected.length,word:expected,H,t}}
 let s={N,steps,abstractResets:0,abstractTicks:0,blockHistogram:[0,0,0],table:[],paths:0,events:0,terminal:0,truncated:0,rootReentries:0,rootsOnEvent:0,rootsOnQuiet:0,rootsOnTerminalPlateau:0,evenResets:0,oddResets:0,smallDeficitChecks:0,nonresetChecks:0,rootlessIntervals:0,rootlessGainChecks:0,sharpRootFreeChecks:0,generalIntervalChecks:0,boundedDeficitIntervalChecks:0,highResetChecks:0,highResetInjectionChecks:0,largestRootFree:null,example:null};
 for(let r=0;r<15;r++){let H=60+4*r,v=resetCheck(H);s.table.push({Hmod60:H%60,blocks:predict(H),ticks:v.ticks,newHmod60:v.H%60})}
 for(let H=24;H<=Math.min(200000,cap-100);H+=4){let v=resetCheck(H);s.abstractResets++;s.abstractTicks+=v.ticks;s.blockHistogram[v.blocks]++}
 function barrier(R,G){let K=2;for(let p=3;p<=R&&p<=cap;p+=2)if(spf[p]===p){K*=p;if(K>=G)return G}return K}
 function checkBlock(ev,A,B,tEnd,Hstart,Hend){if(B<=A||Hstart<24)return;let G=Hend-Hstart,D=0,lowGain=0,lateGain=0;
 for(let k=A;k<B;k++){let z=ev[k];D=Math.max(D,z.d);if(z.n<tEnd-7){if(z.p>=5&&z.D===0)throw Error("early reset "+JSON.stringify({z,tEnd,Hstart,Hend,A,B}));if(z.p>Math.max(3,Math.floor(D/2)))throw Error("label");lowGain+=z.p-1;}else lateGain+=z.p-1}
 let R=Math.max(3,Math.floor(D/2)),K=barrier(R,G);
 if(lowGain>K||G!==lowGain+lateGain||lateGain>8*Math.floor(Math.sqrt(Hend+1)))throw Error("root-free gain");
 // Stronger bound: with no interior root, at most one high reset;
 // only 3/5 gains up to 8 can follow it before the next root.
 let RR=Math.max(5,Math.floor(D/2)),KK=barrier(RR,G),ix=-1,tail=0;
 for(let k=A;k<B;k++){let z=ev[k];if(z.p>RR){if(z.D!==0||ix!==-1)throw Error("root-free high reset");ix=k;}else if(ix!==-1)tail+=z.p-1;}
 if(tail>8||G>KK+Math.floor(Math.sqrt(Hend+1))+8)throw Error("sharp root-free bound");
 s.sharpRootFreeChecks++;
 s.rootlessIntervals++;s.rootlessGainChecks++;
 if(!s.largestRootFree||G>s.largestRootFree.G)s.largestRootFree={G,D,R,lowGain,lateGain,Hstart,Hend,events:B-A};
 }
 function general(ev,roots,i,j){if(i>=j||ev[i].H<24)return;
 let Hstart=ev[i].H,Hend=ev[j-1].Z,tstart=ev[i].t,tend=ev[j-1].n,G=Hend-Hstart,C=Math.floor(Math.sqrt(Hend+1)),Nroot=roots.filter(r=>r.t>tstart&&r.t<=tend).length,D=0;
 for(let k=i;k<j;k++)D=Math.max(D,ev[k].d);
 for(let R of [5,7,11,13,17,Math.max(5,Math.floor(D/2))]){
  let K=barrier(R,G),m0=0,m1=0,V1=0,U=0,V0=0,run=0;
  for(let k=i;k<j;k++){let z=ev[k],g=z.p-1;if(z.p<=R){run+=g;U+=g;if(run>K)throw Error("low run");}else{run=0;if(z.D===0){m0++;V0+=g}else{m1++;V1+=g;if(z.d<2*z.p)throw Error("nonreset d");}}}
  if(m0>Nroot+1||G!==U+V0+V1||U>K*(m0+m1+1)||G>K+(K+C)*(Nroot+1+m1))throw Error("root/count inequality");
  if((R-1)*G>(R-1)*(K+(K+C)*(Nroot+1))+(R-1+K)*V1)throw Error("weighted inequality");
  if(R>=D/2){if(m1||G>K+(K+C)*(Nroot+1))throw Error("bounded deficit count");s.boundedDeficitIntervalChecks++}
  s.generalIntervalChecks++;
 }
 }
 for(let M=5;M<=N;M+=2){
  let H=2*M-2,t=M+2,ev=[],roots=[{t,H,index:0}],lastHigh=null;
  for(let i=0;i<steps;i++){
   if(H+Math.sqrt(H+1)+30>=cap){s.truncated++;break}
   let a=next(t,H);if(!a){s.terminal++;let rt=H/2+3;if(H%4===0&&rt>t)s.rootsOnTerminalPlateau++;break}
   let n=t+a.w,rt=H/2+3;
   if(H%4===0&&t<rt&&rt<n){roots.push({t:rt,H,index:ev.length});s.rootsOnQuiet++;s.rootReentries++;if(lastHigh){if(rt-lastHigh.n>7)throw Error("high root deadline");s.highResetInjectionChecks++;lastHigh=null}}
   let Z=H+a.p-1,d=2*n-Z,D=d-3*(1-a.e),z={...a,H,t,n,Z,d,D};ev.push(z);s.events++;
   if(d===2||d===4||d<0)throw Error("post deficit");s.smallDeficitChecks++;
   if(a.p>=5){if(D<0||D%(2*a.p))throw Error("D");if(D!==0){if(a.p>d/2)throw Error("nonreset");s.nonresetChecks++}}
   if(D===0){if(a.e===1){s.evenResets++;if(Z%4||d)throw Error("even reset");if(Z>=24)resetCheck(Z)}else{s.oddResets++;if(!root(n,Z))throw Error("odd reset")}
    if(a.p>7&&Z>=24){if(lastHigh)throw Error("two high resets without root");lastHigh={n,Z,p:a.p};s.highResetChecks++}
   }
   H=Z;t=n;
   if(root(t,H)){roots.push({t,H,index:ev.length});s.rootReentries++;s.rootsOnEvent++;if(lastHigh){if(t-lastHigh.n>7)throw Error("high root deadline");s.highResetInjectionChecks++;lastHigh=null}}
   if(lastHigh&&t-lastHigh.n>7)throw Error("missed root");
  }
  if(!ev.length)continue;s.paths++;
  for(let j=1;j<roots.length;j++){let a=roots[j-1],b=roots[j];checkBlock(ev,a.index,b.index,b.t,a.H,b.H)}
  let a=roots.at(-1);checkBlock(ev,a.index,ev.length,t,a.H,H);general(ev,roots,0,ev.length);if(ev.length>=4)general(ev,roots,Math.floor(ev.length/2),ev.length);
  if(roots.length>=4&&!s.example)s.example={M,roots:roots.slice(0,8),events:ev.length};
 }
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||150000),Number(process.argv[3]||180)),null,2));
