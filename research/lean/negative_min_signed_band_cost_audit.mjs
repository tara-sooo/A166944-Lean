// Finite exact integer signed-cost and Pareto checks; score uses floating point. The mod2310 block bound is inherited, not recertified here.
function audit(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 const mod=(a,b)=>((a%b)+b)%b;
 const f=new Int32Array(384100);
 for(let p=2;p<f.length;p++)if(!f[p]){f[p]=p;if(p*p<f.length)for(let x=p*p;x<f.length;x+=p)if(!f[x])f[x]=p;}
 function next(x,h){
   let n=h-x/2,w=Infinity,p=0,s=0;
   for(const e of [1,-1]){let v=x+e;while(v>1){const q=f[v];let d=mod((e===1?0:q+2)-n,2*q);if(!d)d=2*q;if(d<w||(d===w&&q<p)){w=d;p=q;s=e;}while(v%q===0)v/=q;}}
   return {w,p,s};
 }
 const cost=(p,Y)=>p>=Y?-4*(p-1):13*(p-1)-Math.max(0,p-281);
 let roots=0,success=0,eventChecks=0,slowChecks=0,ledgerChecks=0,blockChecks=0,selectedKeys=0,dpChecks=0,offers=0,pruned=0,tradeoffs=0,scoreChecks=0;
 const rows=[];
 for(const R of [12000,48000,192000]){
  const H=Math.floor(R**.4),B=4*H,lo=2*Math.floor((R-B)/2),hi=2*R;
  for(const Y of [Math.max(5,Math.floor(H/4)),Math.floor(H/2),H]){
   const sinks=new Map();
   let ns=0,ne=0,slow=0,blocks=0,localRoots=0;
   for(let A=6*Math.ceil(R/6);A<=2*R;A+=6){
    localRoots++;let x=A,h=3,C=0,wt=0,gl=0,gt=0,wl=0,slack=0,m=0,blockG=0,blockW=0,blockSlack=0,keys=[];
    function close(){
     assert(24*blockW<=51*blockG+790-3*blockSlack,"certified block bound");
     blockChecks++;blocks++;blockG=blockW=blockSlack=0;
    }
    while(A-x<=B){
     const {w,p,s}=next(x,h);
     if(h+w-1>=H){
       close();const I=H-h;
       assert(I<w&&I<2*Math.min(f[x-1],f[x+1]),"terminal idle");
       assert(H-3===wl+wt+I-(gl+gt)/2&&A-x===gl+gt,"exact split ledger");
       assert(C===13*gl-slack-4*gt,"signed cost");
       // Multiply H-3 <= C/8 + Wtop+I + (395/12)(m+1) by 24.
       assert(24*(H-3)<=3*C+24*(wt+I)+790*(m+1),"signed height inequality");
       ledgerChecks++;ns++;
       const val={A,C,wt,I,m,gl,gt,keys};
       const prev=sinks.get(x);
       if(!prev||C<prev.C)sinks.set(x,val);
       break;
     }
     const n=h+w-x/2,source=x;
     x-=p-1;h+=w-(p-1)/2;ne++;
     assert(h>=0&&h<H,"height");
     C+=cost(p,Y);
     if(p>=Y){
       close();m++;gt+=p-1;wt+=w;
       keys.push({key:[x,h,p,s].join(","),p,w,source,n});
       if(w>=Math.max(2,Math.floor(Math.sqrt(Y)))){
        assert(2*Math.min(f[source-1],f[source+1])>=w,"rough source");slow++;
       }
     }else{
       gl+=p-1;wl+=w;const a=Math.max(0,p-281);slack+=a;
       blockG+=p-1;blockW+=w;blockSlack+=a;
     }
    }
   }
   const seen=new Set();let sumWt=0,sumI=0,score=0,highGain=0,staticCount=0,lower=0;
   for(const [x,a] of sinks){
    sumWt+=a.wt;sumI+=a.I;highGain+=a.gt;
    for(const q of a.keys){assert(!seen.has(q.key),"distinct sinks disjoint keys");seen.add(q.key);selectedKeys++;}
    const S=Math.max(0,Math.min(1,(8*(H-3)-a.C)/(8*H)));
    assert(S<=(a.wt+a.I+(395/12)*(a.m+1))/H+1e-12,"soft score bound");
    score+=S;scoreChecks++;
    if(Math.min(f[x-1],f[x+1])>=4*H&&x>=R){staticCount++;assert(a.C<=0,"stationary birth score");}
    if(a.C<=0)lower++;
   }
   // Exact event-graph DP, hard gain budget, signed accumulated cost.
   const arr=new Array((hi-lo)/2+1),out=new Map();
   function add(x,h,a){
    if(a.A-x>B||x<lo)return;
    const i=(x-lo)/2;let bin=arr[i];if(!bin){bin=new Map();arr[i]=bin;}
    let list=bin.get(h);if(!list){list=[];bin.set(h,list);}
    offers++;
    for(const b of list)if(b.A<=a.A&&b.C<=a.C){pruned++;return;}
    for(let j=list.length-1;j>=0;j--)if(a.A<=list[j].A&&a.C<=list[j].C){list.splice(j,1);pruned++;}
    if(list.length)tradeoffs++;
    list.push(a);
   }
   for(let x=hi;x>=lo;x-=2){
    if(x>=R&&x%6===0)add(x,3,{A:x,C:0});
    const bin=arr[(x-lo)/2];if(!bin)continue;
    for(const [h,list] of bin){
     const {w,p}=next(x,h);
     if(h+w-1>=H){
      for(const a of list){const v=out.get(x);if(v===undefined||a.C<v)out.set(x,a.C);}
     }else{
      const y=x-p+1,h2=h+w-(p-1)/2;
      for(const a of list)add(y,h2,{A:a.A,C:a.C+cost(p,Y)});
     }
    }
    arr[(x-lo)/2]=undefined;
   }
   assert(out.size===sinks.size,"sink sizes");
   for(const [x,a] of sinks){assert(out.get(x)===a.C,"signed minimum cost");dpChecks++;}
   roots+=localRoots;success+=ns;eventChecks+=ne;slowChecks+=slow;
   rows.push({R,H,Y,roots:localRoots,success:ns,distinct:sinks.size,events:ne,slow,blocks,selectedTopKeys:seen.size,sumWt,sumI,highGain,score,staticCount,nonpositiveCost:lower});
  }
 }
 assert(slowChecks>0&&selectedKeys>0&&tradeoffs>0&&pruned>0,"nonvacuity");
 return {roots,success,eventChecks,slowChecks,ledgerChecks,blockChecks,selectedKeys,dpChecks,offers,pruned,tradeoffs,scoreChecks,rows};
}
console.log(JSON.stringify(audit(),null,2));
