// Exact event-state DP comparison: Pareto record-count/minimum-gain witnesses versus literal per-root calendar. Finite verification only.
function paretoAudit(){
  const assert=(v,m)=>{if(!v)throw Error(m)};
  const mod=(x,m)=>((x%m)+m)%m;
  const f=new Int32Array(384100);
  for(let p=2;p<f.length;p++)if(!f[p]){f[p]=p;if(p*p<f.length)for(let x=p*p;x<f.length;x+=p)if(!f[x])f[x]=p;}
  const factors=x=>{let a=[];while(x>1){let p=f[x];assert(p>0,"factor range");a.push(p);while(x%p===0)x/=p;}return a;};
  function next(x,h){
    const n=h-x/2;let w=Infinity,p=0;
    for(const s of [1,-1])for(const q of factors(x+s)){
      let d=mod((s===1?0:q+2)-n,2*q);if(!d)d=2*q;
      if(d<w||(d===w&&q<p)){w=d;p=q;}
    }
    return {w,p};
  }
  function direct(R,H,B){
    let m=new Map(),inc=0;
    for(let A=6*Math.ceil(R/6);A<=2*R;A+=6){
      let x=A,h=3,M=3,k=0;
      while(A-x<=B){
        const {w,p}=next(x,h);
        if(h+w-1>=H){
          inc++;
          let a=m.get(x);
          if(!a)m.set(x,{minA:A,kAtMinA:k,minK:k,AAtMinK:A});
          else {
            if(A<a.minA){a.minA=A;a.kAtMinA=k;}
            if(k<a.minK||(k===a.minK&&A<a.AAtMinK)){a.minK=k;a.AAtMinK=A;}
          }
          break;
        }
        x-=p-1;h+=w-(p-1)/2;
        assert(h>=0&&h<H,"direct height");
        if(h>M){M=h;k++;}
      }
    }
    return {m,inc};
  }
  const dominates=(a,b)=>a.A<=b.A&&a.M>=b.M&&a.k<=b.k;
  function runGraph(R,H,B,mode){
    const lo=2*Math.floor((R-B)/2),hi=2*R,arr=new Array((hi-lo)/2+1),sinks=new Map();
    let offers=0,discarded=0,removed=0,strictRecordDominance=0,strictMaxDominance=0,states=0,labels=0,maxFrontier=0,terminalOffers=0;
    function add(x,h,b){
      assert(x>=lo&&x<=hi&&x%2===0&&h<H&&b.A-x<=B&&b.M>=h,"label domain");
      const i=(x-lo)/2;let bin=arr[i];if(!bin){bin=new Map();arr[i]=bin;}
      let list=bin.get(h);if(!list){list=[];bin.set(h,list);}
      offers++;
      if(mode==="minA"){
        if(list.length&&list[0].A<=b.A){discarded++;return;}
        removed+=list.length;list.length=0;list.push(b);return;
      }
      for(const a of list)if(dominates(a,b)){
        discarded++;if(a.k<b.k)strictRecordDominance++;if(a.M>b.M)strictMaxDominance++;return;
      }
      for(let i=list.length-1;i>=0;i--)if(dominates(b,list[i])){
        if(b.k<list[i].k)strictRecordDominance++;if(b.M>list[i].M)strictMaxDominance++;
        list.splice(i,1);removed++;
      }
      list.push(b);maxFrontier=Math.max(maxFrontier,list.length);
    }
    for(let x=hi;x>=lo;x-=2){
      if(x>=R&&x%6===0)add(x,3,{A:x,M:3,k:0});
      const bin=arr[(x-lo)/2];if(!bin)continue;
      for(const [h,list] of bin){
        states++;labels+=list.length;
        if(mode!=="minA")for(let i=0;i<list.length;i++)for(let j=0;j<list.length;j++)if(i!==j)assert(!dominates(list[i],list[j]),"frontier antichain");
        const {w,p}=next(x,h);
        if(h+w-1>=H){
          for(const b of list){
            terminalOffers++;
            let old=sinks.get(x);if(old===undefined||b.k<old)sinks.set(x,b.k);
          }
          continue;
        }
        const y=x-p+1,h2=h+w-(p-1)/2;
        assert(y<x&&h2>=0&&h2<H,"graph event");
        if(y<lo)continue;
        for(const b of list){
          if(b.A-y>B)continue;
          add(y,h2,{A:b.A,M:Math.max(b.M,h2),k:b.k+(h2>b.M?1:0)});
        }
      }
      arr[(x-lo)/2]=undefined;
    }
    return {sinks,offers,discarded,removed,strictRecordDominance,strictMaxDominance,states,labels,maxFrontier,terminalOffers};
  }
  const rows=[];let sinkChecks=0,minAncestorDiff=0,minAncestorGraphDiff=0,strictRecord=0,strictMax=0,totalOffers=0,totalPruned=0;
  let example=null;
  for(const R of [12000,48000,192000]){
    const H=Math.floor(R**.4);
    for(const B of [2*H,4*H]){
      const d=direct(R,H,B),a=runGraph(R,H,B,"pareto"),b=runGraph(R,H,B,"minA");
      assert(d.m.size===a.sinks.size&&b.sinks.size===d.m.size,"sink size");
      let ad=0,bd=0;
      for(const [x,z] of d.m){
        assert(a.sinks.get(x)===z.minK,"exact minimum record count");
        assert(b.sinks.get(x)>=z.minK,"min A graph upper");
        sinkChecks++;
        if(z.kAtMinA!==z.minK){
          ad++;
          if(!example)example={R,H,B,x,...z,graphMinAOnly:b.sinks.get(x)};
        }
        if(b.sinks.get(x)!==z.minK)bd++;
      }
      minAncestorDiff+=ad;minAncestorGraphDiff+=bd;
      strictRecord+=a.strictRecordDominance;strictMax+=a.strictMaxDominance;
      totalOffers+=a.offers;totalPruned+=a.discarded+a.removed;
      rows.push({R,H,B,sinks:d.m.size,successfulRoots:d.inc,minAncestorDiff:ad,minAncestorGraphDiff:bd,states:a.states,labels:a.labels,offers:a.offers,discarded:a.discarded,removed:a.removed,maxFrontier:a.maxFrontier,strictRecordDominance:a.strictRecordDominance,strictMaxDominance:a.strictMaxDominance});
    }
  }
  assert(minAncestorDiff>0&&minAncestorGraphDiff>0&&strictRecord>0&&strictMax>0,"nonvacuous dominance");
  return {sinkChecks,minAncestorDiff,minAncestorGraphDiff,strictRecord,strictMax,totalOffers,totalPruned,example,rows};
}
console.log(JSON.stringify(paretoAudit(),null,2));
