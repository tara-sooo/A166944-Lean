// Time-weighted outgoing-prime coupling and wait/gain entropy on synchronized actual MIN trajectories.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=4000005,spf=new Int32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)if(!spf[a])spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const f=x=>x?x*Math.log(x):0,F=x=>Math.log1p(x)+2*Math.log1p(Math.log1p(x));
 let out={roots:0,events:0,segments:0,tailChecks:0,penaltyChecks:0,entropyChecks:0,thresholdChecks:0,rows:[]};
 for(let R of [12000,48000,192000,480000,1000000,2000000]){
  let S=Math.sqrt(2*R+1),L=Math.log(S),T=Math.ceil(S),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nr=(hi-lo)/6+1;
  const d=q=>Math.log(S/Math.min(S,q)),c=x=>2*Math.log(L/(L-x))+F(x),C=2/Math.log(3)+3;
  let tails=[0,0.25,0.5,1,2,3,4,5],tailCounts=tails.map(()=>0),cuts=[5,13,31,Math.ceil(S**0.5),Math.ceil(S**0.75),Math.ceil(S/8),Math.ceil(S/4)].filter(x=>x>=3).sort((a,b)=>a-b);
  let thresholds=[...new Set(cuts)].map(Y=>({Y,smallTime:0,smallGain:0,smallFirstGain:0,smallRepeatGain:0,largeWaitSmallQ:0,lowQ:0}));
  let endpoints=new Map(),endW=new Map(),diff=new Float64Array(T+1),pDiff=new Float64Array(T+1),stats={R,S,T,W,nr,meanN:0,meanLogN:0,meanGain:0,meanD:0,meanProxyD:0,meanPenalty:0,meanProxyPenalty:0,meanWaitEntropy:0,meanGainEntropy:0,terminalFraction:0,terminalPenalty:0,meanExcess:0,meanConditionalBound:0,meanDurationBound:0};
  for(let A=lo;A<=hi;A+=6){
   let l=lo+Math.floor((A-lo)/W)*W,n0=3-l/2,end=n0+T,a=A,n=3-A/2,ne=0,G=0,len=0,D=0,P=0,PD=0,PP=0,Hw=0,Hg=0,gAll=0,seg=[],seen=new Set(),sm=thresholds.map(()=>[0,0,0,0,0,0]);
   for(;;){
    let e=next(a,n),fire=n+e.w,begin=Math.max(n,n0),stop=Math.min(fire,end),duration=Math.max(0,stop-begin),terminal=fire>end;
    if(duration){
     let q=Math.min(spf[a-1]||a-1,spf[a+1]||a+1),v=d(q),r=terminal?0:d(e.p),p=terminal?S:e.p;
     ck(v>=r-1e-10&&duration<=2*q&&(!terminal? q<=e.p:true),"coupling");out.segments++;
     len+=duration;D+=duration*v;P+=duration*c(v);PD+=duration*r;PP+=duration*c(r);Hw-=f(duration/T);
     diff[begin-n0]+=c(v);diff[stop-n0]-=c(v);pDiff[begin-n0]+=c(r);pDiff[stop-n0]-=c(r);
     if(terminal){stats.terminalFraction+=duration/T;stats.terminalPenalty+=duration*c(v)/T}
     for(let i=0;i<tails.length;i++)if(v-r>tails[i]+1e-12)tailCounts[i]+=duration/T;
     seg.push({q,p,duration,v,r,terminal});
    }
    if(terminal)break;
    let g=e.p-1;G+=g;ne++;Hg+=g/T*Math.log(Math.max(1,T/g));gAll+=g;out.events++;
    for(let i=0;i<thresholds.length;i++){let Y=thresholds[i].Y;if(e.p<Y){sm[i][1]+=g;if(seen.has(e.p))sm[i][3]+=g;else sm[i][2]+=g;}}
    seen.add(e.p);a-=g;n=fire;
   }
   ck(len===T&&G<=3*T+6,"time/gain");
   for(let t of tails){let v=seg.reduce((s,x)=>s+(x.v-x.r>t+1e-12?x.duration:0),0)/T;ck(v<=Math.min(1,(3*G+2*S)/T*Math.exp(-t))+1e-9,"tail");out.tailChecks++}
   let E=(D-PD)/T,B=1+Math.log(Math.max(1,(3*G+2*S)/T));ck(E<=B+1e-8&&(P-PP)/T<=C*E+1e-8&&(P-PP)/T>=-1e-8,"penalty");
   ck(D/T<=Math.log(2*S/T)+Hw+1e-8&&Hw<=Math.log(ne+1)+1e-8,"duration entropy");out.penaltyChecks++;
   for(let i=0;i<thresholds.length;i++){let Y=thresholds[i].Y;for(let x of seg){if(!x.terminal&&x.p<Y)sm[i][0]+=x.duration;if(x.q<Y){sm[i][5]+=x.duration;if(x.terminal||x.p>=Y)sm[i][4]+=x.duration}}
    ck(sm[i][0]<=3*sm[i][1]+1e-8&&sm[i][1]===sm[i][2]+sm[i][3],"small gain");let Z=Math.sqrt(Y*T),bound=3*G/T; // independent low-q/high-label estimate at z=Y/4
    let zz=Y/4,occ=seg.reduce((s,x)=>s+(x.q<zz?x.duration:0),0);ck(occ/T<=3*sm[i][1]/T+2*zz*(1+G/(Y-1))/T+1e-8,"threshold");
    out.thresholdChecks++;for(let j=0;j<6;j++)thresholds[i][["smallTime","smallGain","smallFirstGain","smallRepeatGain","largeWaitSmallQ","lowQ"][j]]+=sm[i][j]/T;
   }
   stats.meanN+=ne;stats.meanLogN+=Math.log1p(ne);stats.meanGain+=G/T;stats.meanD+=D/T;stats.meanProxyD+=PD/T;stats.meanPenalty+=P/T;stats.meanProxyPenalty+=PP/T;stats.meanWaitEntropy+=Hw;stats.meanGainEntropy+=Hg;stats.meanExcess+=E;stats.meanConditionalBound+=B;stats.meanDurationBound+=Math.log(2*S/T)+Hw;
   endpoints.set(a,(endpoints.get(a)||0)+1);let k=l+":"+a;endW.set(k,(endW.get(k)||0)+1);out.roots++;
  }
  for(let k of Object.keys(stats))if(!["R","S","T","W","nr"].includes(k))stats[k]/=nr;
  let LE=[...endpoints.values()].reduce((s,v)=>s+f(v),0)/nr,LEW=[...endW.values()].reduce((s,v)=>s+f(v),0)/nr,pmin=Infinity,ppmin=Infinity,v=0,b=0,mean=0,proxy=0;
  for(let t=0;t<T;t++){v+=diff[t];b+=pDiff[t];pmin=Math.min(pmin,v/nr);ppmin=Math.min(ppmin,b/nr);mean+=v/nr/T;proxy+=b/nr/T}
  ck(Math.abs(mean-stats.meanPenalty)<1e-8&&Math.abs(proxy-stats.meanProxyPenalty)<1e-8&&LEW<=LE+1e-8,"entropy/time");out.entropyChecks++;
  stats.Lend=LE;stats.LendWindow=LEW;stats.meanScore=LE+stats.meanPenalty;stats.proxyScore=LE+stats.meanProxyPenalty;stats.minPenalty=pmin;stats.minProxyPenalty=ppmin;stats.tail=tails.map((t,i)=>({t,rate:tailCounts[i]/nr}));stats.thresholds=thresholds.map(x=>Object.fromEntries(Object.entries(x).map(([k,v])=>[k,k==="Y"?v:v/nr])));out.rows.push(stats);
 }return out
}
console.log(JSON.stringify(audit(),null,2));
