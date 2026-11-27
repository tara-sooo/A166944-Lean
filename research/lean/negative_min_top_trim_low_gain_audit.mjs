// Finite controls for whole-root trimming and low-band gain criterion. Proxy parameters only.
// Run: node research/lean/negative_min_top_trim_low_gain_audit.mjs
function audit(){
 const ok=(h,m)=>{if(!h)throw Error(m)},mod=(a,b)=>((a%b)+b)%b;
 const sp=new Int32Array(240002);for(let p=2;p<sp.length;p++)if(!sp[p]){sp[p]=p;if(p*p<sp.length)for(let j=p*p;j<sp.length;j+=p)if(!sp[j])sp[j]=p}
 function factors(n){const a=[];while(n>1){let p=sp[n];ok(p>0,"factor range");a.push(p);while(n%p===0)n/=p}return a}
 const qmin=x=>Math.min(...factors(x-1),...factors(x+1));
 const rows=[];
 for(const [R,T,M,Y,U,H] of [[12000,96,4,24,12,12],[48000,192,8,48,16,16],[96000,384,16,96,24,24]]){
  const lo=Math.ceil(R/6)*6,W=6*Math.floor(T/6),roots=[],keys=new Map(),siteWindows=new Map(),slowCounts=new Map(),longBins=new Map();
  let ticks=0,events=0,capChecks=0,births=0,lowBlocks=0,trimmed=0,trimLife=0,rawLife=0,lowGain=0,lowWait=0,highWait=0,finalIdle=0,shortIdle=0,longIdle=0,fastHigh=0,terminalRough=0,slowRough=0,rootGainChecks=0,lowBlockCount=0,actualMaxK=0;
  const windows=Math.floor((2*R-lo)/W)+1;
  for(let J=0;J<windows;J++){
   const a0=lo+J*W,a1=Math.min(2*R,a0+W-6),obs=3-a0/2,end=obs+T-1,all=[];
   const birthMap=new Map();for(let A=a0;A<=a1;A+=6){let r={A,x:A,birth:3-A/2,last:3-A/2,events:[],life:0,lastAlive:3-A/2-1};birthMap.set(r.birth,r);all.push(r);roots.push(r)}
   let active=[];
   for(let n=3-a1/2;n<=end;n++){
    const proposals=[];
    for(const r of active){let p=0;const even=n%2===0;
     for(const v of factors(even?r.x+1:r.x-1))if(v>2&&mod(n,2*v)===(even?0:v+2)){p=v;break}
     const y=r.x-(p? p-1:0);proposals.push({r,p,y,source:r.x});
    }
    if(birthMap.has(n)){const r=birthMap.get(n);proposals.push({r,p:0,y:r.x,source:r.x});births++}
    const bins=new Map();for(const b of proposals){if(!bins.has(b.y))bins.set(b.y,[]);bins.get(b.y).push(b)}
    active=[];
    for(const [x,bs] of bins){
     bs.sort((a,b)=>a.r.A-b.r.A);const kept=bs.slice(0,M);ok(kept.length<=M,"full cap");capChecks++;
     for(const {r,p,y,source} of kept){
      if(p){const w=n-r.last;ok(w>=1&&w<=2*p,"completed wait");ok(p<=2*(n-r.birth)+7,"label height bound");ok(y>=r.A-2*(n-r.birth)-6,"gain height bound");r.events.push({p,w,n,source,y});r.last=n;events++}
      r.x=y;r.lastAlive=n;active.push(r);if(n>=obs){r.life++;ticks++}
     }
    }
   }
   for(const r of all){
    if(!r.life)continue;
    rawLife+=r.life;const high=r.events.filter(e=>e.p>=Y);actualMaxK=Math.max(actualMaxK,high.length);ok(high.length<=Math.floor((3*T+6)/(Y-1)),"high count");
    const slow=high.filter(e=>e.w>=U);
    for(const e of slow){ok(qmin(e.source)*2>=e.w,"slow roughness");slowRough++;let key=e.source+","+e.n+","+e.p;let m=keys.get(key)||new Map();m.set(J,(m.get(J)||0)+1);keys.set(key,m)}
    if(slow.length){trimmed++;trimLife+=r.life;const e=slow[0],k=e.source+","+e.n+","+e.p;let m=slowCounts.get(k)||new Map();m.set(J,(m.get(J)||0)+1);slowCounts.set(k,m);continue}
    let g=0,w=0,lg=0,lw=0,hw=0,blocks=0;
    const flush=()=>{ok(8*w<=17*g+264,"new potential low block");if(g||w){lowBlocks++;blocks++}lg+=g;lw+=w;g=w=0};
    for(const e of r.events){if(e.p>=Y){flush();hw+=e.w;fastHigh++;ok(e.w<U,"retained fast high")}else{g+=e.p-1;w+=e.w}}
    flush();ok(blocks<=high.length+1,"low blocks");lowBlockCount+=blocks;ok(8*lw<=17*lg+264*(high.length+1),"low telescope");rootGainChecks++;
    const idle=Math.max(0,r.lastAlive-Math.max(obs,r.last+1)+1);
    ok(r.life<=lw+hw+idle+1,"prefix accounting");lowGain+=lg;lowWait+=lw;highWait+=hw;finalIdle+=idle;
    if(idle<H)shortIdle+=idle;else{ok(2*qmin(r.x)>=idle,"terminal roughness");terminalRough++;longIdle+=idle;
     let js=siteWindows.get(r.x)||new Set();js.add(J);siteWindows.set(r.x,js);
     for(let n=Math.max(obs,r.last+1);n<=r.lastAlive;n++){const k=J+","+r.x+","+n;longBins.set(k,(longBins.get(k)||0)+1)}
    }
   }
  }
  let kappa=0;for(const m of keys.values()){kappa=Math.max(kappa,m.size);for(const v of m.values())ok(v<=M,"per-key source cap")}
  for(const m of slowCounts.values())for(const v of m.values())ok(v<=M,"first slow root charge");
  for(const s of siteWindows.values())kappa=Math.max(kappa,s.size);
  for(const v of longBins.values())ok(v<=M,"long idle bin cap");
  const kBound=Math.floor((3*T+6)/(Y-1)),windowBound=Math.ceil((3*T+6)/W)+2;
  ok(kappa<=windowBound,"window count");ok(trimmed<=windowBound*M*keys.size,"remove root union bound");ok(trimLife<=T*trimmed,"trim whole life");ok(longIdle<=windowBound*M*T*siteWindows.size,"long idle mass bound");
  ok(8*(rawLife-trimLife)<=17*lowGain+264*lowBlockCount+8*(highWait+finalIdle+roots.length),"aggregate exact low bound");
  ok(8*rawLife<=17*lowGain+264*roots.length*(kBound+1)+8*(roots.length*kBound*U+roots.length*(H+1)+windowBound*M*T*(siteWindows.size+keys.size)),"aggregate crude bound");
  rows.push({R,T,M,Y,U,H,roots:roots.length,births,windows,ticks,events,capChecks,rootGainChecks,lowBlocks,rawLife,trimmed,trimLife,slowKeys:keys.size,slowRough,terminalRough,longSites:siteWindows.size,longBins:longBins.size,longIdle,shortIdle,lowGain,lowWait,highWait,fastHigh,kappa,actualMaxK});
 }
 return rows;
}
console.log(JSON.stringify(audit(),null,2));
