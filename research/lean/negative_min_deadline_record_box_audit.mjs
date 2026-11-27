// Independent literal-tick audit of deadline clipping, record pair energy,
// box-local repeats, and separated supports. Finite data, not asymptotics.
function audit(Rs=[12000,48000,192000]){
 const ck=(b,m)=>{if(!b)throw Error(m);checks++};
 let checks=0,rows=[];
 const gcd=(a,b)=>{a=Math.abs(a);while(b){let t=a%b;a=b;b=t}return a};
 const spf=new Int32Array(2*Math.max(...Rs)+32);
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 const lpf=n=>spf[n]||n;
 for(const R of Rs){
  const T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
  const z=5,Y=47,H=Math.max(32,Math.floor(T/3)),D=3,w=13,M=8,budget=3;
  let S=0,Q=0,V=0,rawQ=0,pairQ=0,uncapped=0,capped=0,deadlineCost=0,clippedCost=0,first=0,repeated=0,globalRepeated=0,pairs=0,ticks=0,events=0,sparseRuns=0,sparseEvents=0,escapeChecks=0;
  let alph=[new Set([3,5])],bounds=[29],adds=[31,97,307];
  for(let p of adds){alph.push(new Set([...alph.at(-1),p]));bounds.push(2*bounds.at(-1)+p-1)}
  for(let l=lo;l<=hi;l+=W){
   let start=3-l/2,end=start+T,maxA=Math.min(hi,l+W-6),paths=[];
   for(let A=l;A<=maxA;A+=6){
    const birth=3-A/2,K=end-birth,age0=start-birth,xx=new Int32Array(K+1),pp=new Int32Array(K),ff=new Int32Array(K+1),peak=new Int32Array(K+1),profit=new Int32Array(K),suf=new Int32Array(K+1),rep=new Int32Array(K+1);
    let x=A,seen=new Set(),allSeen=new Set(),index=-1,boxMap=new Map(),lastP=new Map(),deadline=K,es=[];
    for(let i=0;i<K;i++){
     let n=birth+i,fire=n+1,g=fire%2===0?gcd(fire,x+1):gcd(fire-2,x-1),p=g>1?lpf(g):0;
     xx[i]=x;pp[i]=p;ticks++;let b=Math.floor((birth-(3-R)+i)/H)-Math.floor((birth-(3-R))/H)+Math.floor(A/H)-Math.floor(x/H);
     ck(b>=index,'box monotone');if(b!==index){seen=new Set();boxMap.set(b,[Math.floor((birth-(3-R)+i)/H),Math.floor(x/H)]);index=b}
     let coords=boxMap.get(b);ck(coords[0]===Math.floor((birth-(3-R)+i)/H)&&coords[1]===Math.floor(x/H),'same box');
     let charge=z<p&&p<Y?1:0,rc=0;
     if(charge){
      if(allSeen.has(p))globalRepeated++;allSeen.add(p);
      if(seen.has(p)){repeated++;rc=1;let a=lastP.get(p);ck(a.b===b&&i-a.i<H&&a.x-x<H&&2*(p-1)<=a.x-x,'local repeat gap');}
      else{first++;seen.add(p)}
     }
     rep[i+1]=rep[i]+rc;if(rep[i+1]>budget&&deadline===K)deadline=i;
     if(p){events++;es.push({p,x,i});lastP.set(p,{x,i,b});x-=p-1}
     ff[i+1]=ff[i]+(i>=age0?D:0)-w*charge;
     peak[i+1]=Math.max(peak[i],ff[i+1]);profit[i]=peak[i+1]-peak[i];
     ck(profit[i]>=0&&profit[i]<=D,'record profit bounds');
    }
    xx[K]=x;suf[K]=ff[K];for(let i=K-1;i>=0;i--)suf[i]=Math.max(ff[i],suf[i+1]);
    ck(H*(index+1)<=3*K+6+3*H,'box bound');
    let nf=0,nr=0,ls=new Map();
    for(let i=0;i<K;i++){
     let p=pp[i];if(!(z<p&&p<Y))continue;
     let key=Math.floor((birth-(3-R)+i)/H)+':'+Math.floor(xx[i]/H)+':'+p;
     if(ls.has(key))nr++;else nf++;ls.set(key,i);
    }
    ck(nr===rep[K]&&nf+nr===es.filter(e=>z<e.p&&e.p<Y).length&&H*nf<=Y*(3*K+6+3*H),'box partition');
    for(let j=0;j<alph.length;j++){
     let gain=0,count=0,run=false;
     for(let e of [...es,{p:0}]){
      if(alph[j].has(e.p)){gain+=e.p-1;run=true;if(j&&e.p===adds[j-1])count++}
      else if(run){ck(gain<=bounds[j]&&count<=1,'separated support');sparseRuns++;sparseEvents+=count;gain=0;count=0;run=false}
     }
    }
    let prev=new Map();
    for(let j=0;j<es.length;j++){
     let e=es[j];if(e.p>=31&&prev.has(e.p)){let h=prev.get(e.p);ck(es.slice(h+1,j).some(a=>30%a.p!==0),'repeat escape');escapeChecks++}prev.set(e.p,j)
    }
    deadlineCost+=rep[deadline];paths.push({A,birth,K,age0,xx,pp,ff,peak,profit,suf,rep,deadline,dead:false,clipEnd:K});
   }
   let joined=new Map(),pairActual=new Map();
   for(let n=paths[paths.length-1].birth;n<end;n++){
    let bins=new Map(),eligible=new Map();
    for(let j=0;j<paths.length;j++){
     let a=paths[j],i=n-a.birth;if(i<0)continue;let x=a.xx[i];
     if(n>=start){let b=bins.get(x)||[];b.push(j);bins.set(x,b)}
     if(i<a.deadline){let b=eligible.get(x)||[];b.push(j);eligible.set(x,b);if(n>=start)uncapped++}
     else if(!a.dead){a.dead=true;a.clipEnd=i}
    }
    for(let b of eligible.values()){
     b.sort((i,j)=>(paths[j].birth+paths[j].deadline)-(paths[i].birth+paths[i].deadline)||paths[i].A-paths[j].A);
     for(let h=0;h<b.length;h++){
      let a=paths[b[h]],i=n-a.birth;
      if(h<M){ck(!a.dead,'deadline resurrection');if(n>=start)capped++}
      else if(!a.dead){a.dead=true;a.clipEnd=i}
     }
     ck(b.filter(j=>!paths[j].dead).length===Math.min(M,b.length),'exact deadline clip')
    }
    if(n>=start)for(let b of bins.values()){
     let weights=b.map(j=>paths[j].profit[n-paths[j].birth]),local=0;
     for(let t=0;t<D;t++){let m=weights.filter(v=>v>t).length;S+=m;Q+=m*m;V+=Math.min(M,m);local+=m*m}
     rawQ+=D*b.length*b.length;
     let pq=0;
     for(let h=0;h<b.length;h++)for(let k=h;k<b.length;k++){
      let i=b[h],j=b[k],a=paths[i],bb=paths[j],key=i*paths.length+j,m=Math.min(weights[h],weights[k]),factor=i===j?1:2;
      pq+=factor*m;
      if(!joined.has(key)){
       let ia=n-a.birth,ib=n-bb.birth;
       ck(a.suf[ia]-a.ff[ia]===bb.suf[ib]-bb.ff[ib],'common suffix peak');
       let value=Math.max(0,a.suf[ia]-a.ff[ia]-Math.max(a.peak[ia]-a.ff[ia],bb.peak[ib]-bb.ff[ib]));
       joined.set(key,factor*value);pairs++;
      }
      pairActual.set(key,(pairActual.get(key)||0)+factor*m)
     }
     ck(local===pq,'threshold square pair identity')
    }
   }
   for(let a of paths){ck(a.clipEnd<=a.deadline&&a.rep[a.clipEnd]<=budget,'deadline prefix cost');clippedCost+=a.rep[a.clipEnd]}
   for(let [k,v] of joined){ck(pairActual.get(k)===v,'first-contact future profit');pairQ+=v}
  }
  ck(Q===pairQ&&Q<=rawQ,'pair energy total');
  ck(BigInt(M)*BigInt(S)**2n<=BigInt(V)*(BigInt(M-1)*BigInt(S)+BigInt(Q)),'sharp moment');
  ck(clippedCost<=deadlineCost,'monotone expense');
  rows.push({R,N,T,H,D,w,M,budget,ticks,events,pairs,S,Q,V,rawQ,uncapped,capped,deadlineCost,clippedCost,first,repeated,globalRepeated,sparseRuns,sparseEvents,escapeChecks,netFraction:V/(N*D*T),recordFraction:S/(N*D*T),recordEnergy:Q/(N*D*T),rawEnergy:rawQ/(N*D*T)})
 }
 return {checks,rows};
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000]),null,2));
