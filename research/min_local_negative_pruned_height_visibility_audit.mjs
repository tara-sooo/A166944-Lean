// First-merger record-height visibility for pairs with common subsequent slow high firings.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p;
 const N=1000000,spf=new Uint32Array(N+3);for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let x=p*p;x<=N+2;x+=p)if(!spf[x])spf[x]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let [d,e] of [[a+1,0],[a-1,2]])for(let r of fs(d)){let t=mod((e===0?0:r+2)-n,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}}return {p,w}}
 let out={roots:0,events:0,highSlowIncidences:0,highSlowKeys:0,pairIncidences:0,uniquePrunedPairs:0,firstMergeSearchSteps:0,weightedEnergyChecks:0,lowHistoryChecks:0,capacityChecks:0,recordChecks:0,gridWitnessChecks:0,dropChecks:0,rows:[]};
 for(let R of [3000,12000,48000,192000,480000]){
  let T=Math.ceil(8*Math.sqrt(2*R+1)),Y=Math.ceil(T/16),K=Math.floor(Math.sqrt(T)),J=Math.max(6,6*Math.floor(Math.log(R)**2/Math.log(Math.log(R))/6)),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nr=(hi-lo)/6+1;
  let paths=[],prefixes=[],keys=new Map(),row={R,T,Y,K,J,roots:nr,meanGain:0,meanHighSlowGain:0,meanHighCredit:0,energy:0,weightedEnergy:0,capacity:0,highSlowKeys:0,highSlowIncidences:0,pairIncidences:0,prunedPairs:0,birth:0,idle:0,jumpJump:0,lowHistory:0,bothPastJ:0,firstHighArrival:0,firstBothHighArrival:0,firstLongIdle:0,firstShortIdleSmall:0,firstShortIdleLarge:0,firstSmallBoth:0,firstMergeMaxGainSum:0,firstMergeMinGainSum:0,firstMergeDistanceMax:0,firstMergeSites:0,visiblePairs:0,gridPairs:0,recycledPairs:0,lowMergeRecycled:0,highMergeRecycled:0,visibleGain:0,gridGain:0,totalPairGain:0,maxPastSum:0,mergeHeightSum:0,byBand:[]};
  let totalGain=0,totalSlow=0,totalCredit=0;
  for(let k=0;k<nr;k++){let A=lo+6*k,a=A,n=3-A/2,end=n+T,ar=[],pre=[],maxPre=3,p0=0,w0=0;
   while(true){let e=next(a,n),f=n+e.w;ar.push(a,n,Math.min(f-1,end),p0,w0);pre.push(maxPre);if(f>end)break;
    if(e.p>=Y&&4*e.w>=e.p){let key=a+":"+f,E=keys.get(key)||{a,n:f,p:e.p,roots:[]};E.roots.push(k);keys.set(key,E);totalSlow+=e.p-1;totalCredit+=Math.max(0,4*e.w-e.p+1);out.highSlowIncidences++}
    maxPre=Math.max(maxPre,f+a/2);a-=e.p-1;n=f;p0=e.p;w0=e.w;out.events++;
   }
   paths.push(ar);prefixes.push(pre);totalGain+=A-a;out.roots++;
  }
  row.meanGain=totalGain/nr;row.meanHighSlowGain=totalSlow/nr;row.meanHighCredit=totalCredit/nr;
  let pairGain=new Map(),firstSites=new Set(),bands=new Map(),diag=0;
  for(let E of keys.values()){
   let g=E.p-1,m=E.roots.length;row.highSlowKeys++;row.highSlowIncidences+=m;row.energy+=m*m;row.weightedEnergy+=g*m*m;row.capacity+=g;diag+=g*m;out.highSlowKeys++;
   let band=2**Math.floor(Math.log2(E.p)),B=bands.get(band)||{Y:band,keys:0,incidences:0,pairs:0,energy:0,weightedEnergy:0};B.keys++;B.incidences+=m;B.pairs+=m*(m-1)/2;B.energy+=m*m;B.weightedEnergy+=g*m*m;bands.set(band,B);
   for(let i=0;i<m;i++)for(let j=i+1;j<m;j++){
    let u=E.roots[i],v=E.roots[j],id=u*nr+v;ck(u<v,"ordered roots");row.pairIncidences++;out.pairIncidences++;
    if(pairGain.has(id)){let rec=pairGain.get(id);rec.g+=g;rec.max=Math.max(rec.max,E.n+E.a/2);if(rec.past<E.n+E.a/2)rec.visGain+=g;if(E.n+E.a/2-rec.past>=Math.max(1,Math.floor(Y/8)))rec.gridGain+=g;continue}
    let rec={g,max:E.n+E.a/2,past:0,h:0,g1:0,g2:0,visGain:0,gridGain:0};pairGain.set(id,rec);let ar=paths[u],br=paths[v],i0=0,j0=0,found=false;
    while(i0<ar.length&&j0<br.length){
     out.firstMergeSearchSteps++;
     if(ar[i0]===br[j0]&&Math.max(ar[i0+1],br[j0+1])<=Math.min(ar[i0+2],br[j0+2])){found=true;break}
     if(ar[i0+2]<br[j0+2])i0+=5;else j0+=5;
    }
    ck(found,"pair common path");let b=ar[i0],s1=ar[i0+1],s2=br[j0+1],n=Math.max(s1,s2),p1=ar[i0+3],p2=br[j0+3],g1=lo+6*u-b,g2=lo+6*v-b;
    ck(n<E.n&&g1>=0&&g2>=g1&&g2-g1===6*(v-u),"first merge before shared high event");row.prunedPairs++;out.uniquePrunedPairs++;firstSites.add(b+":"+n);
    let h=n+b/2,past1=Math.max(prefixes[u][i0/5],h),past2=Math.max(prefixes[v][j0/5],h),past=Math.max(past1,past2),preE=E.n+E.a/2,d=Math.max(1,Math.floor(Y/8));
    rec.past=past;rec.h=h;rec.g1=g1;rec.g2=g2;rec.visGain=past<preE?g:0;rec.gridGain=preE-past>=d?g:0;
    ck(g1>=2*(past1-h)&&g2>=2*(past2-h),"gain pays earlier height drop");out.dropChecks++;
    row.maxPastSum+=past;row.mergeHeightSum+=h;
    row.firstMergeMaxGainSum+=g2;row.firstMergeMinGainSum+=g1;row.firstMergeDistanceMax=Math.max(row.firstMergeDistanceMax,g2-g1);
    if(g1<=J){row.lowHistory++;ck(g1<=J,"low history");out.lowHistoryChecks++}else row.bothPastJ++;
    if((s1===n&&p1===0)||(s2===n&&p2===0))row.birth++;
    else if(s1===s2){ck(p1!==p2&&p1&&p2,"distinct jump branches");row.jumpJump++}
    else {row.idle++;let age=Math.abs(s1-s2),old=s1<s2?p1:p2;if(age>=K)row.firstLongIdle++;else if(old>=Y)row.firstShortIdleLarge++;else row.firstShortIdleSmall++}
    if(Math.max(p1,p2)>=Y)row.firstHighArrival++;else row.firstSmallBoth++;
    if(Math.min(p1,p2)>=Y)row.firstBothHighArrival++;
   }
  }
  let pg=0,d=Math.max(1,Math.floor(Y/8));for(let v of pairGain.values()){ck(v.g<=2*T+6,"pair gain cap");pg+=v.g;row.totalPairGain+=v.g;row.visibleGain+=v.visGain;row.gridGain+=v.gridGain;
   if(v.max>v.past){row.visiblePairs++;ck(v.visGain>0,"visible gain");}else{row.recycledPairs++;if(v.h<=Y/8){row.lowMergeRecycled++;ck(Math.max(v.g1,v.g2)>=2*(v.past-v.h),"recycled prior gain");}else row.highMergeRecycled++}
   if(v.max-v.past>=d){row.gridPairs++;let H=d*(Math.floor(v.past/d)+1);ck(H>v.past&&H<=v.max&&v.gridGain>0,"height grid witness");out.gridWitnessChecks++}
   out.recordChecks++;out.weightedEnergyChecks++}
   ck(row.visiblePairs+row.recycledPairs===row.prunedPairs&&row.lowMergeRecycled+row.highMergeRecycled===row.recycledPairs,"record partition");
  ck(diag===totalSlow&&row.weightedEnergy===diag+2*pg&&row.weightedEnergy<=(2*T+6)*(nr+2*row.prunedPairs),"weighted energy decomposition");out.weightedEnergyChecks++;
  ck(totalSlow**2<=row.capacity*row.weightedEnergy+1,"weighted Cauchy");out.capacityChecks++;
  ck(row.birth+row.idle+row.jumpJump===row.prunedPairs&&row.lowHistory+row.bothPastJ===row.prunedPairs&&row.firstLongIdle+row.firstShortIdleLarge+row.firstShortIdleSmall===row.idle,"pair partition");
  row.firstMergeSites=firstSites.size;row.meanFirstMergeMaxGain=row.firstMergeMaxGainSum/Math.max(1,row.prunedPairs);row.meanFirstMergeMinGain=row.firstMergeMinGainSum/Math.max(1,row.prunedPairs);row.byBand=[...bands.values()].sort((a,b)=>a.Y-b.Y);out.rows.push(row)
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
