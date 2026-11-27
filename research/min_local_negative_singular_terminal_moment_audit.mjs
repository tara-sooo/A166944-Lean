// Restricted low-only singular-height terminal-map moments on exact CRT periods.
// node research/min_local_negative_singular_terminal_moment_audit.mjs
function audit(zs){
 const primes=[3,5,7,11,13,17,19,23],mod=(a,b)=>(a%b+b)%b,ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 let rows=[];
 for(let z of zs){
  let ps=primes.filter(p=>p<=z),Q=2*ps.reduce((a,p)=>a*p,1),period=2*Q;
  let eligible=new Uint16Array(period);
  for(let i=0;i<ps.length;i++){let p=ps[i];for(let x=1;x<period;x+=p)if(x%2===0)eligible[x]|=1<<(2*i+1);for(let x=p-1;x<period;x+=p)if(x%2===0)eligible[x]|=1<<(2*i);}
  let mass=new Uint32Array(period/2),m0=new Uint32Array(period/2),m3=new Uint32Array(period/2),events=0,checks=0,gain=0,maxGain=0,maxEvents=0,violations=[0,0],examples=[],prev=[null,null],crossed=0,roughStarts=0;
  let hist=new Map(),total=0;
  for(let v=0;v<period;v+=4){
   for(let h of [0,3]){
    let x=v,n=h-v/2,k=0;
    if(!eligible[x])roughStarts++;
    for(;;){
     let bits=eligible[x];if(!bits)break;
     let p=Infinity,w=Infinity;
     for(let i=0;i<ps.length;i++){let r=ps[i];for(let j=0;j<2;j++)if(bits&(1<<(2*i+j))){let d=mod((j===0?0:r+2)-n,2*r)||2*r;if(d<w||d===w&&r<p){p=r;w=d;}}}
     ck(Number.isFinite(p),"eligible calendar");let y=x-p+1;
     ck(Math.floor(x/Q)===Math.floor(y/Q)&&n+w+y/2>=0,"cell and height");
     for(let a=x-2;a>y;a-=2)if(!eligible[a])crossed++;
     x=y;n+=w;k++;events++;
    }
    ck(x>=0&&x<=v&&v-x<Q&&!eligible[x],"terminal");
    let j=h===0?0:1;if(prev[j]!==null&&x<prev[j]){violations[j]++;if(examples.length<3)examples.push({h,v,previousV:v-4,previousTerminal:prev[j],terminal:x});}prev[j]=x;
    mass[x/2]++;(h===0?m0:m3)[x/2]++;gain+=v-x;maxGain=Math.max(maxGain,v-x);maxEvents=Math.max(maxEvents,k);total++;checks++;
   }
  }
  let K=0,K00=0,K33=0,K03=0,maxMass=0,support=0,meanLog=0,checkN=0;
  for(let i=0;i<mass.length;i++){let m=mass[i];if(!m)continue;checkN+=m;K+=m*m;K00+=m0[i]**2;K33+=m3[i]**2;K03+=m0[i]*m3[i];maxMass=Math.max(maxMass,m);support++;meanLog+=m*Math.log(m);hist.set(m,(hist.get(m)||0)+1);}
  ck(K===K00+K33+2*K03&&checkN===total&&total===Q,"moment ledger");
  rows.push({z,Q,period,starts:total,events,checks,collisionPerPeriod:K/period,meanFiber:K/total,H:meanLog/total,K00:K00/period,K33:K33/period,K03:K03/period,maxMass,support,meanGain:gain/total,maxGain,maxEvents,monotonicityViolations:violations,crossedRoughCenters:crossed,roughStarts,examples});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[3,5,7,11,13,17]),null,2));
