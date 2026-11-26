// First-appearance prime lift laws for negative-time inverse fibers.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(m)},mod=(x,p)=>(x%p+p)%p,N=300000,Kmax=8192,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let x=p*p;x<=N+2;x+=p)if(!spf[x])spf[x]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
 const C=Array.from({length:Kmax+1},(_,k)=>k?fs(k%2?k+2:k):[]);
 function e(k){return k%2?1:-1}
 function step(a,k){let p=C[k].find(p=>mod(a-e(k),p)===0);return p?a-p+1:a}
 function inverse(S,k){let V=new Set();for(let b of S){if(step(b,k)===b)V.add(b);for(let p of C[k])if(step(b+p-1,k)===b)V.add(b+p-1)}return V}
 let stats={roots:0,dead:0,alive:0,maxDeath:0,firstTickDeaths:0,recycledDeaths:0,singlePrimeDeaths:0,multiPrimeDeaths:0,singletonDeaths:0,multipleDeaths:0,newPrimeChecks:0,recycledSingleChecks:0,multiCoverChecks:0,reverseTicks:0,firstRecovery:0,erasedAtQ:0,deathByType:{},maxDeathExample:null,recoveryExamples:[],periodChecks:[]};
 for(let p=1009;p<=N;p+=2)if(!spf[p]&&spf[p-2]){
  stats.roots++;let q=spf[p-2],S=new Set([p-1]),K=Math.min(Kmax,(p-1)/2-4),dead=false;
  for(let k=1;k<=K;k++){
   let ps=C[k],V=inverse(S,k);stats.reverseTicks++;
   let fresh=ps.length===1&&k===ps[0]-2;
   if(ps.length===1){let r=ps[0],n0=0,n1=0;for(let x of S){if(mod(x-e(k),r)===0)n0++;if(mod(x-e(k)-1,r)===0)n1++}
    ck(V.size===S.size-n0+n1,"single prime count");ck((V.size===0)===(n0===S.size),"single prime extinction");if(fresh)stats.newPrimeChecks++;else stats.recycledSingleChecks++;
   }
   if(k===q-2){ck(S.has(p-1),"stationary through first q");if(V.size){stats.firstRecovery++;if(stats.recoveryExamples.length<6)stats.recoveryExamples.push({p,q,k,prior:[...S],after:[...V]})}else stats.erasedAtQ++}
   if(!V.size){
    dead=true;stats.dead++;if(fresh)stats.firstTickDeaths++;else stats.recycledDeaths++;if(ps.length===1)stats.singlePrimeDeaths++;else stats.multiPrimeDeaths++;if(S.size===1)stats.singletonDeaths++;else stats.multipleDeaths++;
    ck([...S].every(x=>ps.some(r=>mod(x-e(k),r)===0)),"extinction cover");if(ps.length>1)stats.multiCoverChecks++;
    let tag=(fresh?"new":"old")+"/"+(ps.length===1?"single":"multi")+"/"+(S.size===1?"width1":"width>1");stats.deathByType[tag]=(stats.deathByType[tag]||0)+1;
    if(k>stats.maxDeath){stats.maxDeath=k;stats.maxDeathExample={p,q,k,ps,prior:[...S]}}break;
   }
   S=V;
  }if(!dead)stats.alive++;
 }
 // Exact lift laws on every residue class of the preceding suffix at first appearance.
 for(let p of [3,5,7,11,13,17]){
  let k=p-2, Q=2;for(let r=3;r<p;r+=2)if(!spf[r])Q*=r;
  let fibers=Array.from({length:Q/2},()=>[]);
  for(let x=0;x<Q;x+=2){let b=x;for(let j=k-1;j>=1;j--)b=step(b,j);let r=mod(b,Q);fibers[r/2].push(x-b);}
  let rstat={p,k,Q,nonempty:0,monoresidue:0,multiresidue:0,lost:0,conditionalPrimeLost:0,varianceNumerator:0,meanChecks:0,varianceChecks:0,extinctionChecks:0,translationChecks:0,maxWidth:0};
  for(let r=0;r<Q;r+=2){let offsets=fibers[r/2],W=offsets.length;if(!W)continue;rstat.nonempty++;rstat.maxWidth=Math.max(rstat.maxWidth,W);
   let n=Array(p).fill(0);for(let d of offsets)n[mod(d,p)]++;
   let mono=n.some(x=>x===W);if(mono)rstat.monoresidue++;else rstat.multiresidue++;
   let sum=0,varnum=0,loss=0,primeLoss=0,calc=0;
   for(let j=0;j<p;j++){let b=r+Q*j,S=new Set(offsets.map(d=>b+d)),V=inverse(S,k),t=mod(1-b,p);
    ck(V.size===W-n[t]+n[(t+1)%p],"lift width");sum+=V.size;varnum+=(V.size-W)**2;
    if(!V.size){loss++;if(mod(b+1,p)!==0)primeLoss++}
    rstat.translationChecks++;
   }
   for(let j=0;j<p;j++)calc+=(n[(j+1)%p]-n[j])**2;
   ck(sum===p*W,"mean");ck(varnum===calc&&calc<=2*W*W,"variance");ck(loss===(mono?1:0),"extinction");
   rstat.meanChecks++;rstat.varianceChecks++;rstat.extinctionChecks++;rstat.lost+=loss;rstat.conditionalPrimeLost+=primeLoss;rstat.varianceNumerator+=varnum;
  }
  ck(rstat.lost===rstat.monoresidue,"aggregate");stats.periodChecks.push(rstat)
 }
 return stats
}
console.log(JSON.stringify(audit(),null,2));
