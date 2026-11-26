// Multi-source roughness, broad terminal-prime bands, and dimension checks.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=2100000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let a=p*p;a<=N+2;a+=p)spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,v){let p=Infinity,w=Infinity,q=Infinity,c=0;for(let [d,e] of [[a+1,0],[a-1,2]])for(let r of fs(d)){q=Math.min(q,r);let t=mod((e===0?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;c=e}}return {p,w,q,c}}
 function twin(a){return (spf[a-1]||a-1)===a-1&&(spf[a+1]||a+1)===a+1}
 let z={roots:0,events:0,successes:0,badSuccesses:0,slowEventChecks:0,allTailControls:0,tailIncidences:0,badTailIncidences:0,slowSourceChecks:0,shiftSeparationChecks:0,crtCongruenceChecks:0,repeatedTailChecks:0,goodPrimeResidueChecks:0,degeneratePrimeChecks:0,crtProgressionChecks:0,crtRemainderChecks:0,degreeControls:0,rows:[]};
 for(let R of [3000,12000,48000,192000,480000,1000000]){
  const H=4*Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),L=Math.floor(H/4),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),basins=new Map(),row={R,H,L,success:0,bad:0,depthHist:{},controls:[]};
  for(let A=lo;A<=hi;A+=6){let a=A,h=3,v=3-A/2,path=[];
   while(true){let e=next(a,v);if(h+e.w>H){let ar=basins.get(a)||[];ar.push({A,path});basins.set(a,ar);row.success++;z.successes++;if(!twin(a)){row.bad++;z.badSuccesses++;}break}
    if(A-a+e.p-1>L)break;ck(e.w<=2*e.q,"wait cap");if(e.w>=e.p/4){ck(e.q>=e.p/8,"slow source");z.slowEventChecks++}
    path.push({p:e.p,w:e.w,q:e.q,c:e.c,b:a,a:a-e.p+1});a-=e.p-1;v+=e.w;h+=e.w-(e.p-1)/2;z.events++;
   }z.roots++;
  }
  // Fixed finite bands, deliberately broader than a dyadic band.
  for(let [Y,U] of [[7,32],[11,64],[17,128],[31,256]])for(let k of [1,2,3,4]){
   let counts=Array.from({length:k+1},()=>({all:0,bad:0,keys:new Set(),badKeys:new Set(),starts:new Set()})),words=new Map(),minCut=Infinity;
   for(let [a,ar] of basins)for(let root of ar){
    let marks=[],d=0,off=0,valid=true;
    for(let i=root.path.length-1;i>=0&&marks.length<k;i--){
     let e=root.path[i];if(e.p<=5){d+=e.p-1;ck(d<=16,"low wall");continue}
     if(e.p<Y||e.p>=U){valid=false;break}
     off+=d;ck(e.a===a+off&&mod(a+off-e.c,e.p)===0,"arrival congruence");z.crtCongruenceChecks++;
     const slow=e.w>=e.p/4;
     marks.push({p:e.p,d,c:e.c,off,source:e.b-a,slow,w:e.w});off+=e.p-1;d=0;
    }
    if(!valid||marks.length!==k)continue;
    let bad=!twin(a),s=marks.filter(x=>x.slow).length,key=JSON.stringify([a,marks.map(({p,d,c,slow})=>({p,d,c,slow}))]);
    let cnt=counts[s];cnt.all++;cnt.keys.add(key);if(bad){cnt.bad++;cnt.badKeys.add(key);cnt.starts.add(a+off);z.badTailIncidences++}z.tailIncidences++;
    if(new Set(marks.map(m=>m.p)).size!==k)z.repeatedTailChecks++;
    let shifts=[-1,1],sources=[0];
    for(let m of marks){ck(m.source===m.off+m.p-1&&m.source>sources.at(-1)+2,"source separation");sources.push(m.source);z.shiftSeparationChecks++;if(m.slow){shifts.push(m.source-1,m.source+1);ck(Math.min(...fs(a+m.source-1),...fs(a+m.source+1))>=m.w/2,"slow rough forms");z.slowSourceChecks++}}
    ck(new Set(shifts).size===2*(s+1),"distinct forms");
    // Inspect selected small CRT progressions independently. Actual forms
    // need not be sifted at all tested primes in these finite controls.
    if(bad&&z.degreeControls<10000){
     let q=Infinity,e=0;
     for(let sg of [-1,1]){let n=a+sg,f=fs(n);if(f[0]!==n&&f[0]<q){q=f[0];e=sg}}
     ck(q<Infinity,"composite");
     let ps=[...new Set(marks.map(m=>m.p))],P=ps.reduce((x,y)=>x*y,1);
     if(!ps.includes(q)&&P<1000000){
      let m0=(a+e)/q,rr=mod(m0,P);
      for(let m of marks)ck(mod(q*rr-e+m.off-m.c,m.p)===0,"CRT progression");
      z.crtProgressionChecks++;
      for(let l of [3,5,7,11,13,17,19,23,29,31]){
       if(l===q||P%l===0)continue;
       let coll=false;for(let i=0;i<shifts.length;i++)for(let j=i+1;j<shifts.length;j++)if(mod(shifts[i]-shifts[j],l)===0)coll=true;
       let residues=new Set();for(let t=0;t<l;t++)if(shifts.some(c=>mod(q*(rr+P*t)-e+c,l)===0))residues.add(t);
       if(!coll){ck(residues.size===shifts.length,"dimension");z.goodPrimeResidueChecks++}else{ck(residues.size<shifts.length,"degenerate");z.degeneratePrimeChecks++}
       let n=53,count=0;for(let t=0;t<n;t++)if(residues.has(t%l))count++;ck(Math.abs(count-n*residues.size/l)<=residues.size+1e-8,"remainder");z.crtRemainderChecks++;
      }z.degreeControls++;
     }
    }
   }
   z.allTailControls++;row.controls.push({Y,U,k,counts:counts.map(({all,bad,keys,badKeys,starts},s)=>({s,all,bad,keys:keys.size,badKeys:badKeys.size,starts:starts.size}))});
  }
  // Broad coverage profile: last non-low event, no imposed band.
  for(let [a,ar] of basins)for(let root of ar){
   let non=root.path.filter(e=>e.p>5),last=non.at(-1),key=last?`${Math.floor(Math.log2(last.p))}:${last.w>=last.p/4?"slow":"fast"}`:"none";
   let p=row.depthHist[key]||[0,0];p[twin(a)?0:1]++;row.depthHist[key]=p;
  }
  z.rows.push(row);
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
