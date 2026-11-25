// Cohort turnover and fixed-cut arithmetic audit. Node usage: node research/min_unified_a1_cohort_cut_audit.mjs [X ...]
function audit(Xs=[4096,16384,65536]){
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(x,m)=>(x%m+m)%m;
 const max=7*Math.max(...Xs)+100,spf=new Int32Array(max+1);for(let p=2;p<=max;p++)if(!spf[p])for(let j=p;j<=max;j+=p)if(!spf[j])spf[j]=p;
 const factors=n=>{let f=[];while(n>1){let p=spf[n];f.push(p);while(n%p===0)n/=p}return f};
 const lag=(s,h,I,f,J)=>{let r=mod((2*h+1)*s+6*(I-J),f);let a=mod(r*((f+1)/2),f);return mod(a,2)===mod(I-J,2)?a:a+f};
 const results=[];
 for(const X of Xs){let B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),tags=[],slots=new Map(),events=0,negative=0,positive=0,fixed=0,rivals=0,unit=0,reset=0;
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let tag=tags.length,es=[],C=2*M-2,t=M+2;
   while(C-(2*M-2)<T){let p=0,w=Infinity,I=0;for(let j=0;j<2;j++)for(let f of factors(C-1+2*j)){if(f*f>C+1)continue;let v=mod((j?f+2:0)-t,2*f)||2*f;if(v<w||v===w&&f<p){p=f;w=v;I=j}}
    if(!p)break;let J=C+p-1,n=t+w,d=2*t-C,dp=2*n-J,h=(dp-6*I)/(2*p),key=C+"/"+n+"/"+p;
    if(!slots.has(key))slots.set(key,{C,J,n,p,I,h,members:new Set(),succ:null});let slot=slots.get(key);slot.members.add(tag);let e={slot,C,J,p,w,I,h,d,dp,a1:p>=47&&p>=5*d+15&&h===1};
    if(d>dp){ok(p>=5&&Number.isInteger(h)&&h>=0,"decrease");if(w===1)unit++;if(h===0)reset++;
     for(let b=dp+2;b<=d;b+=2){let h0=Math.floor((b-6*I-1)/(2*p)),r=b-6*I-2*p*h0;ok(h===h0&&r>=2&&r<=p-3&&w<=(p-1-r)/2,"fixed cut");ok(mod(C-(1-2*I+p*(2*I-2*h-1)),4*p)===0,"horizon residue");fixed++}
     for(let k=0;k<2;k++)for(let f of factors(C-1+2*k)){if(f===p||f*f>C+1)continue;let a=lag(p,h,I,f,k),exact=mod(n-(k?f+2:0),2*f);ok(a===exact&&!(a===0&&f<p)&&!(a>0&&a<w),"rival lag");rivals++}
    }
    es.push(e);C=J;t=n;events++;
   }tags.push(es)
  }
  for(let es of tags)for(let k=0;k+1<es.length;k++){let s=es[k].slot,f=es[k+1].slot;ok(s.succ===null||s.succ===f,"unique next slot");s.succ=f}
  for(let s of slots.values())if(s.succ){let f=s.succ,r=[...s.members].filter(i=>f.members.has(i)).length;ok(r>0,"survivor");negative+=r*Math.log(s.members.size/r);positive+=r*Math.log(f.members.size/r)}
  // Positive increments for joining tags from each predecessor (new roots start at first exit cohort; account for initial mass).
  let initial=tags.reduce((a,es)=>a+(es.length?Math.log(es[0].slot.members.size):0),0);positive+=initial;ok(negative<=tags.length+1e-6&&positive<=tags.length*Math.log(tags.length)+negative+1e-6,"entropy budget");
  const configs=[{Y:47,A:4,eps:.2,R:7,l:2},{Y:67,A:16,eps:.05,R:7,l:2},{Y:47,A:16,eps:1,R:7,l:2}];
  let controls=[];
  for(let cfg of configs){let {Y,A,eps,R,l}=cfg,dem=0,pending=0,late=0,unstable=0,stable=0,relays=0,matched=0,partnerLoss=0,dominant=new Map(),cohortTests=0,changes=0;
   let totalMark=0;
   for(let ti=0;ti<tags.length;ti++){let es=tags[ti],pend=[],variation=[0],markWeight=0;
    for(let k=0;k<es.length;k++){if(k){let a=es[k-1].slot,b=es[k].slot,r=[...a.members].filter(i=>b.members.has(i)).length;variation[k]=variation[k-1]+Math.log(a.members.size/r)+Math.log(b.members.size/r)}
     let e=es[k],x=5*(e.d+3),xp=5*(e.dp+3);
     if(xp<x){let remain=[];for(let m of pend){let lo=Math.max(xp,m.lo),hi=Math.min(x,m.hi);if(hi<=lo){remain.push(m);continue}let len=hi-lo;if(lo>m.lo)remain.push({...m,hi:lo});matched+=len;
       if(e.C-es[m.k].J>=A*m.p){late+=len;continue}
       let j=k;if(e.p<=R){while(j>0&&es[j-1].p<=R)j--;let end=k;while(end+1<es.length&&es[end+1].p<=R)end++;if(j===0||es[end].J-es[j].C>=4*l){late+=len;continue}j--;relays+=len}
       let src=es[m.k].slot,dst=es[j].slot;ok(j>=m.k,"causal");
       let v=variation[j]-variation[m.k];let a=src.members,b=dst.members,r=[...a].filter(i=>b.has(i)).length,dist=a.size+b.size-2*r;
       ok(dist<=a.size*Math.exp(v)*v+1e-6&&dist<=b.size*Math.exp(v)*v+1e-6,"symmetric difference");
       cohortTests++;if(dist>0)changes++;
       if(v>eps){unstable+=len;continue}
       stable+=len;partnerLoss+=len*(a.size-r)/a.size;
       if(Math.exp(eps)*eps<.5){ok(r>b.size/2,"dominance");for(let y=lo+1;y<=hi;y++){let key=dst.C+"/"+dst.n+"/"+dst.p+"/"+y;let old=dominant.get(key);ok(old===undefined||old===src,"unique dominant mark");dominant.set(key,src)}}
     }pend=remain}
     if(e.a1&&e.p>=Y){ok(!pend.some(z=>Math.min(z.hi,5*e.p)>Math.max(z.lo,e.p)),"disjoint marks");pend.push({lo:e.p,hi:5*e.p,k,p:e.p});dem+=4*e.p;markWeight+=4*e.p}
    }
    pending+=pend.reduce((s,m)=>s+m.hi-m.lo,0);totalMark+=markWeight
   }
   ok(dem===pending+matched&&matched===late+unstable+stable,"partition");ok(partnerLoss<=Math.exp(eps)*eps*stable+1e-6,"partner loss");
   // Every unstable source interval lies within A*B+B of a positive variation increment.
   ok(unstable*eps<=5*(A*B+2*B)*(positive+negative)+1e-5,"global variation halo");
   controls.push({cfg,dem,pending,matched,late,unstable,stable,relays,partnerLoss,dominant:dominant.size,cohortTests,changes});
  }
  results.push({X,N:tags.length,events,slots:slots.size,negative,positive,fixed,rivals,unit,reset,controls})
 }
 // Abstract deterministic cohort histories: merges, retirements, and simultaneous turnover with equal sizes.
 const seq=[new Set([0,1,2,3]),new Set([0,1]),new Set([0,1,4,5]),new Set([0,1,4,5,6,7]),new Set([0,4,5,6,7])];
 let v=0,ratios=[];for(let j=1;j<seq.length;j++){let a=seq[j-1],b=seq[j],r=[...a].filter(i=>b.has(i)).length;v+=Math.log(a.size/r)+Math.log(b.size/r);ratios.push({a:a.size,b:b.size,r,v})}
 ok(seq[0].size===seq[2].size&&[...seq[0]].filter(i=>seq[2].has(i)).length===2&&ratios[1].v>1,"equal size turnover");
 // Unit-wait abstract fixed-cut saturation controls, no canonical-ancestry claim.
 let abstract=0;for(let s of [5,7,11,13])for(let I of [0,1]){let h=(s*s-1)/2,b=2*s*h+6*I+2;for(let C=2*s*s;C<Math.min(max,20000);C+=2){if(mod(C-(1-2*I+s*(2*I-2*h-1)),4*s))continue;let n=(C+s-1+2*s*h+6*I)/2;ok(n%2===I&&b>2*s*h+6*I,"abstract phase");for(let f of factors(C-1+2*I))if(f<s)ok(lag(s,h,I,f,I)!==0,"unit saturation");abstract++}}
 return {results,turnover:ratios,abstract};
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
