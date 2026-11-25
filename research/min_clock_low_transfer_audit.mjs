// LOW-block clock compression and small non-LOW transfer.
// Run: node research/min_clock_low_transfer_audit.mjs 1024 4096 16384 65536 262144
function audit(X,mode='analytic'){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,u=Math.log(B),ell=Math.log(u),G=2*H+B+6,U=7*X+4;
 const ok=(x,m)=>{if(!x)throw Error(m);};
 ok(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(U);
 for(let p=2;p<U;p++)if(!spf[p]){spf[p]=p;if(p*p<U)for(let j=p*p;j<U;j+=p)if(!spf[j])spf[j]=p;}
 const y=mode==='wide'?5:mode==='diagnostic'?3:Math.max(3,Math.floor(Math.sqrt(ell)));
 let L=2;for(let p=3;p<=y;p+=2)if(spf[p]===p)L*=p;
 const Z=mode==='wide'?Math.min(B,31):mode==='diagnostic'?Math.min(B,13):Math.min(B,L*L);
 const k=mode==='wide'?2:mode==='diagnostic'?1:Math.max(1,Math.floor(Math.sqrt(y)));
 const bcap=1.5*L,margin=3*L+2*Z+2,spanCap=2*k*Z+(2*k+1)*L,coreMargin=3*spanCap+2;
 const clockWidth=mode==='analytic'?Math.ceil(u**4):mode==='wide'?32:16;
 const sourceWidth=mode==='analytic'?B/u**.125:B/4;
 const sigma=mode==='analytic'?Math.max(1,Math.floor(B/(L*L*k*k))):mode==='wide'?6:4;
 const tau=mode==='analytic'?Math.floor(u**3):mode==='wide'?4:2;
 const lo=X,hi=7*X/2-1,len=hi+1,r=new Int32Array(len);
 let S0=0,SZ=0,nR=0;for(let j=lo;j<=hi;j++){const q=Math.min(spf[2*j-1],spf[2*j+1]);if(q<=B){r[j]=q;S0+=q;nR++;if(q<=Z)SZ+=q;}}
 function hit(t,C,K){let T=K+1,P=0;for(const side of [-1,1]){
  let v=C+side;while(v>1){const p=spf[v];if(p>B)break;
   const m=2*p,rs=side===-1?0:p+2,w=t+1+(rs-(t+1)%m+m)%m;
   if(p>2&&(w<T||(w===T&&w<=K&&p<P))){T=w;P=p;}while(v%p===0)v/=p;}
 }return [T,P];}
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a;};
 const paths=[],full=new Float64Array(len),small=new Float64Array(len),large=new Float64Array(len),low=new Float64Array(len),comp=new Float64Array(len),transfer=new Float64Array(len),destN=new Int32Array(len),smallN=new Int32Array(len),basic=new Float64Array(len),core=new Float64Array(len);
 const cellMap=new Map(),stateMap=new Map(),key=(t,C)=>t*U+C;
 const smallAnchorW=new Map(),lowDest=new Map(),lowPhys=new Map(),anchorMass=new Map();
 let R=0,Rs=0,Rl=0,Rlow=0,tailLow=0,events=0,literal=0,twins=0,selected=0,largeEvents=0,smallEvents=0,lowEvents=0,blocks=0,positiveBlocks=0,blockMax=0,weightMax=0,postCount=0;
 const cellId=e=>e.C+':'+Math.floor((e.t-e.C/2)/clockWidth)+':'+Math.floor((e.M-X)/sourceWidth);
 for(let M=X+1;M<2*X;M+=2){
  const s=M+2,K=Math.floor((7*M-1)/4),path=[],non=[];
  let t=s,C=2*M-2,rg=0,sw=0,acc=0,gain=0;
  while(t<s+H){
   const [v,p]=hit(t,C,K);
   if(X<=1024){
    let vv=K+1,pp=0;for(let n=t+1;n<=K;n++){const d=gcd(n%2?n-2:n,n%2?C+1:C-1);if(d>1&&spf[d]<=B){vv=n;pp=spf[d];break;}}
    ok(v===vv&&p===pp,'literal MIN');literal++;
   }
   if(!p){ok(!r[C/2]&&spf[C-1]===C-1&&spf[C+1]===C+1,'terminal twin');twins++;break;}
   const q=r[C/2],D=C+p-1,dur=Math.max(0,Math.min(v-s,H)-Math.max(t-s,a)),cost=dur/2,w=dur/(2*q);
   ok(C<=2*t&&D<=2*v&&v-t<=2*q&&q<=p&&2*v-D<=12*B+6,'clock/gain/deficit');
   const e={M,s,t,C,v,D,p,q,cost,w,ix:path.length,anchor:v+':'+D+':'+p};path.push(e);
   R+=cost;rg+=cost;sw+=p;full[C/2]+=w;events++;
   if(p<=y){lowEvents++;Rlow+=cost;low[C/2]+=w;acc+=cost;gain+=p-1;ok(gain<L&&acc<=bcap,'LOW block');}
   else{
    non.push(e);e.nix=non.length-1;postCount++;comp[C/2]+=(cost+acc)/(q+bcap);
    ok(cost+acc<=q+bcap,'compressed capacity');
    if(gain){blocks++;positiveBlocks+=+(acc>0);blockMax=Math.max(blockMax,gain);weightMax=Math.max(weightMax,acc);}
    gain=0;acc=0;
    if(p<=Z){smallEvents++;Rs+=cost;small[C/2]+=w;smallN[C/2]++;const c=cellId(e);e.cell=c;
     let row=cellMap.get(c);if(!row){row={n:0,times:new Map()};cellMap.set(c,row);}
     row.n++;row.times.set(t,(row.times.get(t)||0)+1);
     const rr=smallAnchorW.get(e.anchor)||{q,w:0};ok(rr.q===q,'anchor pre-horizon');rr.w+=w;smallAnchorW.set(e.anchor,rr);
    }else{largeEvents++;Rl+=cost;large[C/2]+=w;}
   }
   t=v;C=D;
  }
  ok(C-(2*M-2)<=G&&rg<=B&&sw<=1.5*G,'root budgets');selected+=sw;tailLow+=acc;
  paths.push({M,s,path,non});
 }
 let Rcomp=0,Ecomp=0,Scomp=0,Efull=0,Esmall=0,Elarge=0,Elow=0,EsmallAnchor=0;
 for(let j=lo;j<=hi;j++){const q=r[j];Efull+=q*full[j]**2;Esmall+=q*small[j]**2;Elarge+=q*large[j]**2;Elow+=q*low[j]**2;
  if(comp[j]){Rcomp+=(q+bcap)*comp[j];Ecomp+=(q+bcap)*comp[j]**2;Scomp+=q+bcap;}
 }
 for(const z of smallAnchorW.values())EsmallAnchor+=z.q*z.w*z.w;
 const eps=1e-6*Math.max(1,Efull,Rcomp);
 ok(Math.abs(R-Rs-Rl-Rlow)<=eps&&Math.abs(R-tailLow-Rcomp)<=eps,'exact linear compression');
 ok(tailLow<=N*bcap&&Rcomp**2<=Scomp*Ecomp+1e-6*Math.max(1,Rcomp**2),'compressed certificate');
 ok(EsmallAnchor<=Esmall+eps,'event-key energy subset');
 let basicCost=0,basicTail=0,basicBig=0,basicTrim=0,basicBlocks=0,targetWait=0,maxDestDist=0,coreCost=0,coreEnd=0,coreBig=0,coreThinProjected=0,coreThinCell=0,coreTrim=0,coreBlocks=0,coreNeighborChecks=0,coreMaxSpan=0,coreMinProjected=Infinity,coreMinCell=Infinity,coreMinDistinctTimes=Infinity,corePhysicalThick=0,coreClockSpread=0;
 let thinProjected=0,thinCell=0,thinCells=0;for(const n of smallN)if(n<=sigma)thinProjected+=n;
 for(const row of cellMap.values())if(row.n<=tau){thinCell+=row.n;thinCells++;}
 for(const {M,s,path,non} of paths){
  let l=0;
  for(let j=0;j<=non.length;j++){
   const next=non[j],end=next?next.ix:path.length,es=path.slice(l,end);
   l=end+1;if(!es.length)continue;
   let cost=0,gain=0;for(const e of es){ok(e.p<=y,'block membership');cost+=e.cost;gain+=e.p-1;}
   ok(gain<L&&cost<=bcap,'full block cap');
   if(!next){basicTail+=cost;}else if(next.p>Z){basicBig+=cost;}else{
    let z=0;for(const e of es){
     const dur=Math.max(0,Math.min(e.v,s+H-margin)-Math.max(e.t,s+a)),b=dur/2;
     ok(b<=e.cost+1e-9,'trim');if(!b)continue;
     ok(next.C-e.C<L&&next.C>e.C&&next.t>=s+a&&next.v<=s+H,'destination full slab');
     maxDestDist=Math.max(maxDestDist,next.C-e.C);
     const w=b/e.q;basic[e.C/2]+=w;z+=b;
     const id=e.C+':'+next.C,old=lowDest.get(id)||{C:e.C,D:next.C,q:e.q,w:0};old.w+=w;lowDest.set(id,old);
     const ph=key(e.t,e.C),v0=lowPhys.get(ph)||{q:e.q,w:0,anchor:next.anchor};
     ok(v0.anchor===next.anchor,'same physical LOW state same destination event');v0.w+=w;lowPhys.set(ph,v0);
    }
    basicTrim+=cost-z;
    if(z){basicBlocks++;basicCost+=z;targetWait+=next.cost;transfer[next.C/2]+=z;destN[next.C/2]++;
     ok(next.cost===(next.v-next.t)/2&&next.cost>=.5,'full nonLOW clock');
     const old=anchorMass.get(next.anchor)||{q:next.q,n:0};old.n++;anchorMass.set(next.anchor,old);
    }
   }
   // Optional two-sided persistent small-event core, using frozen groups.
   if(j<k||j+k>non.length){coreEnd+=cost;continue;}
   const ns=non.slice(j-k,j+k);ok(ns.length===2*k,'neighbor count');
   if(ns.some(e=>e.p>Z)){coreBig+=cost;continue;}
   ok(ns.every(e=>e.p>y&&e.cell),'small neighbor membership');
   if(ns.some(e=>smallN[e.C/2]<=sigma)){coreThinProjected+=cost;continue;}
   if(ns.some(e=>cellMap.get(e.cell).n<=tau)){coreThinCell+=cost;continue;}
   const first=ns[0],last=ns[ns.length-1],span=last.D-first.C;
   ok(span<=spanCap&&last.v-first.t<=3*span,'two-sided small-event span');
   let z=0;for(const e of es){const dur=Math.max(0,Math.min(e.v,s+H-coreMargin)-Math.max(e.t,s+a+coreMargin));if(dur){ok(first.t>=s+a&&last.v<=s+H,'two-sided actual full waits');core[e.C/2]+=dur/(2*e.q);z+=dur/2;}}
   coreTrim+=cost-z;if(!z)continue;
   coreBlocks++;coreCost+=z;coreMaxSpan=Math.max(coreMaxSpan,span);
   for(const e of ns){const row=cellMap.get(e.cell);coreNeighborChecks++;coreMinProjected=Math.min(coreMinProjected,smallN[e.C/2]);coreMinCell=Math.min(coreMinCell,row.n);coreMinDistinctTimes=Math.min(coreMinDistinctTimes,row.times.size);
    const mx=Math.max(...row.times.values());if(mx>Math.sqrt(tau))corePhysicalThick++;else{ok(row.times.size>Math.sqrt(tau),'thin states imply clock spread');coreClockSpread++;}
   }
  }
 }
 let Eb=0,Ecore=0,Et=0,ST=0,n2=0,linearCheck=0,nbound=0,fullDestEnergy=0,sameDestEnergy=0,samePhysEnergy=0,anchorN2=0,EtTarget=0,maxN=0;
 for(let j=lo;j<=hi;j++){const q=r[j];Eb+=q*basic[j]**2;Ecore+=q*core[j]**2;linearCheck+=transfer[j];Et+=transfer[j]**2/bcap;if(transfer[j])ST+=bcap;n2+=destN[j]**2;maxN=Math.max(maxN,destN[j]);ok(destN[j]<=2*q*small[j]+1e-7,'destination count dominated by full small weight');}
 for(const row of lowDest.values())sameDestEnergy+=row.q*row.w**2;
 for(const row of lowPhys.values())samePhysEnergy+=row.q*row.w**2;
 for(const [id,row] of anchorMass){anchorN2+=row.n**2;const a=smallAnchorW.get(id);ok(a&&row.n<=2*row.q*a.w+1e-7,'physical event mass dominated by full small wait');}
 let local=0;for(let j=lo;j<=hi;j++)if(destN[j])for(let h=Math.max(lo,j-L/2+1);h<=Math.min(hi,j+L/2-1);h++)local+=destN[j]*destN[h];
 ok(Math.abs(basicCost+basicTail+basicBig+basicTrim-Rlow)<=eps&&Math.abs(linearCheck-basicCost)<=eps,'basic low partition');
 ok(basicTail<=N*bcap+eps&&basicBig<=largeEvents*bcap+eps&&basicTrim<=N*margin/2+eps,'basic deletion bounds');
 ok(basicCost<=2*bcap*targetWait+eps&&targetWait<=Rs+eps,'linear small-event transfer');
 ok(Rs*Rs<=SZ*Esmall+1e-6*Math.max(1,Rs*Rs),'small sieve Cauchy');
 ok(basicCost**2<=ST*Et+1e-6*Math.max(1,basicCost**2),'transferred energy Cauchy');
 ok(Et<=bcap*n2+eps&&sameDestEnergy<=bcap*n2+eps&&Eb<=L/2*sameDestEnergy+eps&&Eb<=bcap*local+eps,'projected local transfer energy');
 ok(samePhysEnergy<=bcap*anchorN2+eps&&anchorN2<=4*Z*EsmallAnchor+eps,'physical next event energy');
 ok(n2<=4*Z*Esmall+eps&&Eb<=3*L*L*Z*Esmall+eps,'low energy transfer bound');
 ok(Math.abs(coreEnd+coreBig+coreThinProjected+coreThinCell+coreTrim+coreCost-Rlow)<=eps,'two-sided budget partition');
 ok(coreEnd<=2*k*N*bcap+eps&&coreBig<=2*k*largeEvents*bcap+eps&&coreThinProjected<=2*k*thinProjected*bcap+eps&&coreThinCell<=2*k*thinCell*bcap+eps&&coreTrim<=N*coreMargin+eps,'two-sided deletion bounds');
 ok(coreNeighborChecks===2*k*coreBlocks&&corePhysicalThick+coreClockSpread===coreNeighborChecks,'clock dichotomy');
 const nz=x=>Number.isFinite(x)?x:null;
 return {X,B,mode,y,L,Z,k,margin,coreMargin,clockWidth,sourceWidth,sigma,tau,N,events,literal,twins,selected,lowEvents,smallEvents,largeEvents,blocks,positiveBlocks,blockMax,weightMax,R,Rs,Rl,Rlow,tailLow,Rcomp,Ecomp,Scomp,S0,SZ,Efull,Esmall,Elarge,Elow,EsmallAnchor,basicCost,basicTail,basicBig,basicTrim,basicBlocks,targetWait,maxDestDist,maxN,n2,local,Eb,Et,ST,sameDestEnergy,samePhysEnergy,anchorN2,cellCount:cellMap.size,thinCells,thinProjected,thinCell,coreCost,coreEnd,coreBig,coreThinProjected,coreThinCell,coreTrim,coreBlocks,coreNeighborChecks,coreMaxSpan,coreMinProjected:nz(coreMinProjected),coreMinCell:nz(coreMinCell),coreMinDistinctTimes:nz(coreMinDistinctTimes),corePhysicalThick,coreClockSpread,Ecore};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536,262144])for(const mode of ['analytic','diagnostic','wide'])console.log(JSON.stringify(audit(X,mode)));
