// Time-randomized MIN channel: conditional entropy and exact departure-phase loss.
// node research/min_local_negative_dwell_phase_entropy_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+5),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){const out=[];while(n>1){let p=spf[n]||n;out.push(p);while(n%p===0)n/=p}return out}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},f=x=>x?x*Math.log(x):0,add=(m,k,v)=>m.set(k,(m.get(k)||0)+v);
 const q=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1);
 let rows=[];
 for(let R of Rs){
  let S=Math.sqrt(2*R+1),T=Math.ceil(S),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
  let occ=new Map(),ends=new Map(),phaseF=0,rootH=0,rootCost=0,terminal=0,phaseCount=0,checks=0,events=0,segments=0,condK=0,condEnd=0,meanKL=0;
  let lowPhaseH=0;
  for(let l=lo;l<=hi;l+=W){
   let n0=3-l/2,end=n0+T,phase=new Map(),positions=new Map();
   for(let A=l;A<=Math.min(hi,l+W-6);A+=6){
    let a=A,n=3-A/2,seen=0,trace=[];
    for(;;){
     let e=next(a,n),fire=n+e.w,dt=Math.max(0,Math.min(fire,end)-Math.max(n,n0)),last=fire>end;
     if(dt){
      let w=dt/T,t=Math.min(1,2*q(a)/T),key=a+":"+(last?"T":fire);
      ck(w<=t+1e-12,"dwell cap");seen+=dt;rootH-=f(w);rootCost-=w*Math.log(t);meanKL+=w*Math.log(t/w);
      add(occ,a,w);add(positions,a,w);trace.push({key,w,a,start:Math.max(n,n0),stop:Math.min(fire,end)});segments++;
      if(last)terminal+=w;
     }
     if(last)break;
     a-=e.p-1;n=fire;events++;
    }
    ck(seen===T&&A-a<=3*T+6,"gain/time");add(ends,a,1);
    for(let e of trace){
     let z=phase.get(e.key)||{m:0,y:a,x:e.a,start:e.start,stop:e.stop};
     ck(z.y===a&&z.x===e.a&&z.stop===e.stop,"phase determines endpoint");
     z.m+=e.w;z.start=Math.min(z.start,e.start);phase.set(e.key,z);checks++;
    }
   }
   let localF=0,localPosF=0;let byX=new Map();
   for(let z of phase.values()){localF+=f(z.m);let a=byX.get(z.x)||[];a.push(z);byX.set(z.x,a)}
   for(let [x,ps] of byX){
    ps.sort((a,b)=>a.start-b.start);let duration=0,m=0;
    for(let i=0;i<ps.length;i++){let z=ps[i];ck(i===0||ps[i-1].stop<=z.start,"disjoint phase intervals");duration+=z.stop-z.start;m+=z.m;checks++}
    ck(duration<=T&&Math.abs(m-positions.get(x))<1e-8,"phase duration/mass");
    localPosF+=f(m);
   }
   ck(localPosF>=localF-1e-6,"phase entropy");
   condK+=localPosF;phaseF+=localF;phaseCount+=phase.size;
  }
  let occF=[...occ.values()].reduce((s,x)=>s+f(x),0),endF=[...ends.values()].reduce((s,x)=>s+f(x),0);
  let total=[...occ.values()].reduce((s,x)=>s+x,0);ck(Math.abs(total-N)<1e-6*N,"root mass");
  const Hroot=rootH/N,HAX=Hroot+occF/N,HAphase=Hroot+phaseF/N,Hphase=(occF-phaseF)/N,Lend=endF/N,Hwindow=(occF-condK)/N,HphaseW=(condK-phaseF)/N;
  ck(HAphase<=Lend+1e-8&&HAphase>=-1e-8&&Hphase>=-1e-8&&Math.abs(HAX-HAphase-Hphase)<1e-8,"phase chain rule");
  let cap=0,badCap=0,used=0,usedBad=0,KL=0;
  for(let a=2*Math.ceil((lo-3*T-6)/2);a<=hi;a+=2){let t=Math.min(1,2*q(a)/T);cap+=t;if(q(a)<=S)badCap+=t;if(occ.has(a)){used+=t;if(q(a)<=S)usedBad+=t;}}
  for(let [x,m] of occ){let v=m/N;KL+=v*Math.log(v*used/Math.min(1,2*q(x)/T));}
  ck(KL>=-1e-8&&Math.abs(HAX-(Math.log(N/used)+KL+meanKL/N))<1e-8,"capacity KL identity");
  rows.push({R,T,N,events,segments,checks,phaseCount,Lend,Hroot,HAX,HAphase,Hphase,Hwindow,HphaseW,phaseUpper:Lend+Hphase,capacityLower:Math.log(N/used),KL,slack:meanKL/N,cap,badCap,used,usedBad,reqCapacity:N*Math.exp(-HAX),terminal:terminal/N});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000,1000000,2000000]),null,2));
