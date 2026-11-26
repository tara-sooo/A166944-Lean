// Exact clock-block reverse forest, height/gain pruning, and terminal marked-prime tails.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=2100000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let a=p*p;a<=N+2;a+=p)spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function clocks(a){return [...fs(a+1).map(p=>({p,c:0})),...fs(a-1).map(p=>({p,c:p+2}))]}
 function next(a,v){let p=Infinity,w=Infinity;for(let c of clocks(a)){let t=mod(c.c-v,2*c.p)||2*c.p;if(t<w||t===w&&c.p<p){p=c.p;w=t}}return {p,w}}
 function prev(a,u){let d=0;for(let c of clocks(a)){let r=mod(a/2+c.c,2*c.p),t=u-mod(u-r,2*c.p);d=Math.max(d,t)}return d}
 function twin(a){return (spf[a-1]||a-1)===a-1&&(spf[a+1]||a+1)===a+1}
 let z={roots:0,events:0,successes:0,controls:0,blockNodes:0,branchCandidates:0,priorityRejected:0,heightRejected:0,budgetRejected:0,duplicateChecks:0,birthChecks:0,exactBasinChecks:0,prunedNodes:0,prunedCandidates:0,prunedPriorityRejected:0,prunedHeightRejected:0,prunedBudgetRejected:0,tailKeys:0,tailIncidences:0,tailCongruenceChecks:0,tailMultiplicityChecks:0,tailDistinctChecks:0,emptyControls:0,tailCRTControls:0,tailCRTRechecks:0,tailSieveControls:0,tailSieveRemainderChecks:0,maxTailProduct:0,repeatedTailControls:0,repeatedTailIncidences:0,repeatedBadTailIncidences:0,repeatedCongruenceChecks:0,repeatedAdjacentExcluded:0,repeatedResidueChecks:0,repeatedCandidateChecks:0,rows:[]};
 for(let R of [3000,12000,48000,192000,480000,1000000]){
  let H=4*Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),L=Math.floor(H/4),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),basins=new Map(),row={R,H,L,roots:0,success:0,badSuccess:0,badCenters:0,reverseCenters:0,nodes:0,prunedNodes:0,maxNodes:0,maxMass:0,tail:[]};
  for(let A=lo;A<=hi;A+=6){let a=A,h=3,v=3-A/2,path=[];while(true){let e=next(a,v);if(h+e.w>H){let ar=basins.get(a)||[];ar.push({A,path});basins.set(a,ar);row.success++;z.successes++;break}
   if(A-a+e.p-1>L)break;path.push({p:e.p,b:a,a:a-e.p+1,h:h+e.w-(e.p-1)/2,n:v+e.w});a-=e.p-1;v+=e.w;h+=e.w-(e.p-1)/2;z.events++;
  }row.roots++;z.roots++}
  let bad=[...basins].filter(([a])=>!twin(a));row.badCenters=bad.length;row.badSuccess=bad.reduce((s,[a,ar])=>s+ar.length,0);
  // All bad endpoints for six slabs, plus a deterministic sample of twins.
  let controls=[...bad,...[...basins].filter(([a])=>twin(a)).filter((_,i)=>i%41===0)];
  let empty=0;for(let a=2*Math.ceil((R-L)/2);a<=hi;a+=2){if(basins.has(a)||twin(a)||Math.min(...fs(a-1),...fs(a+1))<=9*H/32-7)continue;if(empty++%29===0){controls.push([a,[]]);z.emptyControls++;}}
  for(let [a0,ar] of controls){
   let bound=Math.min(hi,a0+L),expected=ar.map(r=>r.A).sort((a,b)=>a-b);
   function reverse(prune){
    let stack=[[a0,H]],seen=new Set(),birth=[],nodes=0,candidates=0,pr=0,hr=0,br=0;
    while(stack.length){let [a,u]=stack.pop(),d=prev(a,u),key=a+":"+d;
     ck(!seen.has(key),{a0,a,u,d,prune});seen.add(key);nodes++;z.duplicateChecks++;
     if(a>=lo&&a<=hi&&a%6===0&&d<=3&&3<=u){birth.push(a);z.birthChecks++}
     for(let [m,side] of [[a,0],[a-2,1]])for(let p of fs(m)){
      if(p===2)continue;let b=a+p-1,g=(p-1)/2;if(b>bound)continue;
      let r=mod(a/2+(side===0?0:p+2),2*p);
      for(let h=d+mod(r-d,2*p);h<=u;h+=2*p){
       candidates++;
       let pre=h+g,prevH=pre-1;
       if(pre>H||prevH<0){hr++;continue}
       if(prune&&(4*h>44+7*(bound-a)||35*(bound-a+10)<18*pre)){br++;continue}
       let n=h-a/2;
       let win=Infinity;for(let c of clocks(b))if(mod(n-c.c,2*c.p)===0)win=Math.min(win,c.p);
       if(win!==p){pr++;continue}
       ck(n-1===prevH-b/2,"time equation");
       stack.push([b,prevH])
      }
     }
    }
    birth.sort((a,b)=>a-b);ck(new Set(birth).size===birth.length,"unique births");
    ck(JSON.stringify(birth)===JSON.stringify(expected),{R,a0,prune,birth,expected});z.exactBasinChecks++;
    if(prune){z.prunedNodes+=nodes;z.prunedCandidates+=candidates;z.prunedPriorityRejected+=pr;z.prunedHeightRejected+=hr;z.prunedBudgetRejected+=br}
    else{z.blockNodes+=nodes;z.branchCandidates+=candidates;z.priorityRejected+=pr;z.heightRejected+=hr;z.budgetRejected+=br}
    return nodes
   }
   let n=reverse(false),m=reverse(true);ck(m<=n,"pruning");row.nodes+=n;row.prunedNodes+=m;row.maxNodes=Math.max(row.maxNodes,n);row.maxMass=Math.max(row.maxMass,ar.length);row.reverseCenters++;z.controls++;
  }
  // Terminal k marks, with fixed low-only suffix gains <=16.
  // Scale ranges for finite diagnostics (not asymptotic exponent tests).
  for(let [Y,U] of [[7,14],[11,22],[17,34],[23,46],[31,62],[47,94]]){
   for(let k of [1,2,3]){
    let endpoints=new Map(),badEndpoints=new Set(),badStarts=new Set(),goodMass=0,badMass=0,tailCount=0,distinctTail=new Set(),maxPaths=0;
    for(let [a,ar] of basins){
     for(let root of ar){let path=root.path,marks=[],d=0,valid=true,shift=0,cur=a,idx=path.length-1;
      for(;idx>=0&&marks.length<k;idx--){
       let e=path[idx];ck(e.a===cur,"path continuity");
       if(e.p<=5){shift+=e.p-1;ck(shift<=16,"low-run cap");cur=e.b;continue}
       if(e.p<Y||e.p>=U||marks.some(m=>m.p===e.p)){valid=false;break}
       ck(e.a===a+d+shift,"offset");
       ck(e.a%e.p===0||mod(e.a-2,e.p)===0,"tail divisibility");z.tailCongruenceChecks++;
       marks.push({p:e.p,shift,side:e.a%e.p===0?0:2});d+=shift+e.p-1;shift=0;cur=e.b;
      }
      if(!valid||marks.length!==k)continue;
      ck(cur===a+d,"tail start");
      let q=0;if(!twin(a)){for(let n of [a-1,a+1]){let f=fs(n);if(f.length>1||f[0]!==n){q=f[0];break}}ck(q>0,"composite neighbor")}
      let key=JSON.stringify([a,marks]);distinctTail.add(key);let st=endpoints.get(a)||new Set();st.add(key);endpoints.set(a,st);
      
      if(q){badEndpoints.add(a);badStarts.add(cur);badMass++;
       if(!marks.some(m=>m.p===q)){
        let f=fs(a-1),e=f.includes(q)?-1:1; // a+e=q*m
        let P=marks.reduce((s,m)=>s*m.p,1),r0=(a+e)/q,offset=0;
        for(let m of marks){offset+=m.shift;ck(mod(q*r0-e+offset-m.side,m.p)===0,"terminal CRT");offset+=m.p-1;z.tailCRTRechecks++}
        // Independent CRT reconstruction using a bounded integer search
        // on small products, and elementary CRT remainder checks for
        // the two shifted forms in the progression.
        if(P<=15000&&z.tailCRTControls<3000){
         let rs=mod(r0,P),nq=0;
         for(let r=0;r<P;r++){let ok=true,dd=0;for(let m of marks){dd+=m.shift;if(mod(q*r-e+dd-m.side,m.p)!==0){ok=false;break}dd+=m.p-1}if(ok){nq++;ck(r===rs,"unique CRT residue")}}
         ck(nq===1,"CRT one");z.tailCRTControls++;z.maxTailProduct=Math.max(z.maxTailProduct,P);
         for(let l of [5,7,11,13,17])if(l!==q&&P%l!==0){
          let n=127,cnt=0,nu=0;function blocked(t){let m=rs+P*t;return mod(m,l)===0||mod(q*m-2*e,l)===0}
          for(let t=0;t<l;t++)if(blocked(t))nu++;ck(nu===2,"two residues");
          for(let t=0;t<n;t++)if(blocked(t))cnt++;ck(Math.abs(cnt-n*2/l)<=2+1e-8,"sieve remainder");z.tailSieveRemainderChecks++;
         }z.tailSieveControls++;
        }
       }
      }else goodMass++;
      z.tailIncidences++;
     }
    }
    for(let [a,st] of endpoints){maxPaths=Math.max(maxPaths,st.size);let D=2*9*Math.ceil(Math.log(2*R+30)/Math.log(Y));ck(st.size<=D**k,"tail branching");z.tailMultiplicityChecks++}
    ck(badStarts.size<=distinctTail.size&&badEndpoints.size<=distinctTail.size,"tail support");z.tailDistinctChecks++;z.tailKeys+=distinctTail.size;
    row.tail.push({Y,U,k,goodMass,badMass,badEndpoints:badEndpoints.size,badStarts:badStarts.size,distinctTail:distinctTail.size,maxPaths});
   }
  }
  // Allow repeated marks. A repeat in the same constant-ratio band
  // forces a congruence for another intervening distinct prime.
  row.repeats=[];
  for(let Y of [19,23,31,47])for(let k of [2,3,4,5]){
   let repeat=0,badRepeat=0,repeatKeys=new Set();
   for(let [a,ar] of basins)for(let root of ar){
    let marks=[],shift=0,off=0,valid=true;
    for(let i=root.path.length-1;i>=0&&marks.length<k;i--){
     let e=root.path[i];if(e.p<=5){shift+=e.p-1;ck(shift<=16,"low gap");continue}
     if(e.p<Y||e.p>=2*Y){valid=false;break}
     off+=shift;ck(e.a===a+off,"repeat offset");marks.push({p:e.p,d:shift,c:e.a%e.p===0?0:2,off});off+=e.p-1;shift=0
    }
    if(!valid||marks.length!==k||new Set(marks.map(m=>m.p)).size===k)continue;
    repeat++;z.repeatedTailIncidences++;if(!twin(a)){badRepeat++;z.repeatedBadTailIncidences++}
    repeatKeys.add(JSON.stringify([a,marks]));
    for(let i=0;i<k;i++)for(let j=i+1;j<k;j++)if(marks[i].p===marks[j].p){
     const p=marks[i].p;
     ck(mod(marks[j].off-marks[i].off-marks[j].c+marks[i].c,p)===0,"repeat congruence");z.repeatedCongruenceChecks++;
     ck(j>i+1,"adjacent repeat impossible");z.repeatedAdjacentExcluded++;
     let r=marks.slice(i+1,j).find(m=>m.p!==p)?.p;ck(r!==undefined,"intervening label");
     let coef=0,constant=marks[i].c-marks[j].c;
     for(let l=i;l<j;l++){if(marks[l].p===r)coef++;else constant+=marks[l].p;constant-=1;constant+=marks[l+1].d;}
     ck(coef>0&&coef<p&&mod(coef*r+constant,p)===0,"linear repeat constraint");z.repeatedResidueChecks++;
     let candidates=0;for(let rr=Y;rr<2*Y;rr++)if(mod(coef*rr+constant,p)===0)candidates++;
     ck(candidates<=2,"constant choices");z.repeatedCandidateChecks++;
    }
   }
   z.repeatedTailControls++;row.repeats.push({Y,k,repeat,badRepeat,distinct:repeatKeys.size})
  }
  z.rows.push(row)
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
