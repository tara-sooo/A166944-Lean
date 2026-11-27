// Budgeted anchor-priority capped flow and threshold averaging. Verify reset residents, short-anchor collisions,
// same-prime exclusion, and protected-loss charging, with exact full path replay.
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+5),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const q=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1);
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 const add=(m,k,v=1)=>m.set(k,(m.get(k)||0)+v);
 let rows=[];
 for(let R of Rs){
  let T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
  let specs=[[.5,4,4,64],[.25,8,16,128],[.125,8,32,256]].map(([f,B,M,budget])=>({budget,protectedBudget:0,otherBudget:0,thresholdMeasure:0,thresholdBound:0,P:Math.max(11,Math.ceil(f*T)),B,M,d:.6,young:Math.max(1,3*(M-2)-1),events:0,merges:0,reset0:0,reset3:0,resident3:0,movingPairs:0,short:0,singular:0,samePrime:0,long:0,youngMixed:0,shortKeys:0,singularKeys:0,longKeys:0,youngKeys:0,protectedDeaths:0,highDeaths:0,youngDeaths:0,unprotectedDeaths:0,highInternalDeaths:0,highPairBound:0,youngMixedBound:0,protectedTicks:0,liveTicks:0,ret:0,anchorEvents:0,anchorTokens:0,checks:0,sourceTests:0,targetTests:0}));
  let literalEvents=0,rootCheck=0;const eventCost=(p,x,P)=>p>=P?0:p>5&&p<47?8:p>=47&&q(x)>=p**.5/2?2*q(x):0;
  for(let l=lo;l<=hi;l+=W){
   let maxA=Math.min(hi,l+W-6),start=3-maxA/2,n0=3-l/2,end=n0+T;
   const full=new Map();
   for(let A=l;A<=maxA;A+=6){let a=A,n=3-A/2;for(;;){let e=next(a,n),t=n+e.w;if(t>end)break;a-=e.p-1;n=t;literalEvents++;}full.set(A,a);}
   for(let c of specs){
    // Compute the exact measure of thresholds b in [budget,2budget)
    // whose first crossing lies at a protected poststate. No simulation
    // of the cap is needed for this upper bound, since deletion cannot
    // alter a surviving trajectory.
    for(let A=l;A<=maxA;A+=6){
     let x=A,n=3-A/2,cost=0,anchor=null,measure=0,protInc=0,anchors=0;
     for(;;){let e=next(x,n),t=n+e.w;if(t>end)break;let y=x-e.p+1,inc=eventCost(e.p,x,c.P);
      if(e.p>=c.P){anchor=q(x)>=e.p**c.d/2?y:null;anchors+=+(anchor!==null);}
      let protectedNow=(anchor!==null&&anchor-y<=c.B)||t-(3-A/2)<=c.young;
      if(protectedNow){protInc+=inc;measure+=Math.max(0,Math.min(2*c.budget,cost+inc)-Math.max(c.budget,cost));}
      cost+=inc;x=y;n=t;
     }
     ck(measure<=Math.min(c.budget,protInc)&&anchors*(c.P-1)<=3*T+6,"threshold measure");
     c.thresholdMeasure+=measure;c.thresholdBound+=Math.min(c.budget,protInc);
    }
    let active=new Map(),buckets=new Map(),pairSeen=new Set(),longSeen=new Set(),youngSeen=new Set(),dead=new Set();
    let P=c.P,B=c.B,M=c.M,D=Math.ceil(P**c.d)+3*B+4;
    function status(t,x,n){
     if(t.anchor&&t.anchor.x-x>=0&&t.anchor.x-x<=B)return 2;
     if(n-(3-t.A/2)<=c.young)return 1;
     return 0;
    }
    function sched(a,n,v){let e=next(a,n),t=n+e.w;if(t<=end){let b=buckets.get(t)||[];b.push({a,p:e.p,v});buckets.set(t,b);}}
    function close(a,v,n){let l=Math.max(n0,v.tick),r=Math.min(end,n);if(r>l){c.liveTicks+=(r-l)*v.tokens.length;for(let t of v.tokens){
      if(t.anchor&&t.anchor.x-a<=B)c.protectedTicks+=r-l;else c.protectedTicks+=Math.max(0,Math.min(r,3-t.A/2+c.young+1)-l);
    }}}
    for(let n=start;n<=end;n++){
     let arrivals=new Map();function push(a,g){let v=arrivals.get(a)||[];v.push(g);arrivals.set(a,v);}
     for(let e of buckets.get(n)||[]){
      let v=active.get(e.a);if(v!==e.v)continue;
      close(e.a,v,n);active.delete(e.a);let x=e.a-e.p+1,h=n+x/2,sg=n%2===0?0:2;
      ck(h>=0&&mod(x-sg,e.p)===0&&mod(h-(sg?3:0),e.p)===0,"arrival pin");
      let rough=e.p>=P&&q(e.a)>=e.p**c.d/2;
      let anchor={id:e.a+":"+n,p:e.p,x,h,n,sg,src:e.a};
      if(rough){c.anchorEvents++;c.anchorTokens+=v.tokens.length;}
      let tokens=[];
      for(let t of v.tokens){
       let u={A:t.A,cost:t.cost+eventCost(e.p,e.a,P),anchor:e.p>=P?(rough?anchor:null):t.anchor};
       if(u.cost>c.budget){ck(!dead.has(u.A),"budget death");dead.add(u.A);if(status(u,x,n))c.protectedBudget++;else c.otherBudget++;}
       else tokens.push(u);
      }
      if(tokens.length)push(x,{tokens,p:e.p,arr:n,source:e.a});c.events++;c.checks++;
     }
     let A=2*(3-n);if(A>=l&&A<=maxA&&A%6===0)push(A,{tokens:[{A,cost:0,anchor:null}],p:0,birth:true,arr:n});
     for(let [x,gs] of arrivals){
      let old=active.get(x),h=n+x/2,sing=n%2===0?h===0:h===3;
      if(old){close(x,old,n);gs.push({tokens:old.tokens,p:0,idle:true,arr:old.arr,last:old.last});}
      if(n%2===0&&h===0){ck(!old&&gs.every(g=>g.p>0),"no height-zero resident/birth");c.reset0++;}
      if(n%2!==0&&h===3){c.reset3++;if(old){ck(old.arr===n-3&&old.last.every(p=>p>0)&&mod(x,4)===0,"height-three resident at reset zero");c.resident3++;}}
      let groups=gs.map(g=>({...g,high:g.tokens.filter(t=>status(t,x,n)===2),young:g.tokens.filter(t=>status(t,x,n)===1)}));
      if(gs.length>1)c.merges++;
      let H=groups.filter(g=>g.high.length),highCount=H.reduce((s,g)=>s+g.high.length,0),youngCount=groups.reduce((s,g)=>s+g.young.length,0);
      ck(youngCount<=M,"young total bound");
      let hp=Math.max(0,highCount-M),yp=Math.min(youngCount,Math.max(0,highCount+youngCount-M));c.highInternalDeaths+=hp;
      let pairBound=0;
      for(let i=0;i<H.length;i++)for(let j=i+1;j<H.length;j++){
       let a=H[i].high[0].anchor,b=H[j].high[0].anchor;
       if(H[i].idle){[a,b]=[b,a];}
       ck(!H[i].idle||!H[j].idle,"unique resident");
       let E=a.x-x,F=b.x-x;ck(E>=0&&F>=0&&E<=B&&F<=B&&a.id!==b.id,"distinct anchored groups");
       ck(n-a.n<=3*B,"moving anchor age");
       if(!H[i].idle&&!H[j].idle){ck(n-b.n<=3*B,"second moving age");c.movingPairs++;}
       let key=[a.id,b.id].sort().join("|");ck(!pairSeen.has(key),"anchor pair first merge");pairSeen.add(key);pairBound+=M;
       if(n-b.n<=D){
        ck(Math.abs(a.h-b.h)<=D+B/2,"height gap");c.short++;
        let ca=a.sg?3:0,cb=b.sg?3:0,ka=(a.h-ca)/a.p,kb=(b.h-cb)/b.p;
        ck(Number.isInteger(ka)&&Number.isInteger(kb)&&ka>=0&&kb>=0,"height multipliers");
        if(2*B+4<Math.min(a.p,b.p)&&D+B/2+3<Math.min(a.p,b.p)){
         ck(a.p!==b.p,"same-prime close anchors impossible");
         ck((ka===0)===(kb===0),"no mixed singular regular");
        }else if(a.p===b.p)c.samePrime++;
        if(ka===0&&kb===0){c.singular++;c.singularKeys++;let delta=E-F-a.sg+b.sg;ck(mod(x+E-a.sg,a.p)===0&&mod(x+F-b.sg,b.p)===0,"singular spatial pins");
         if(a.p!==b.p){let u=(x+E-a.sg)/a.p,v=(x+F-b.sg)/b.p;ck(a.p*u-b.p*v===delta,"shifted hyperbola");
          for(let ell of [7,11,13,17,19,23,29,31])if(ell<Math.min(a.p**c.d,b.p**c.d)/2&&ell!==a.p&&ell!==b.p){ck([a.src-1,a.src+1,b.src-1,b.src+1].every(z=>mod(z,ell)!==0),"two sources rough");c.sourceTests++;}
         }
        }
       }else{
        ck(H[i].idle||H[j].idle,"long needs resident");
        ck(n-b.n-3*B<=2*q(x),"resident long roughness");
        ck(q(x)>=P**c.d/2,"long resident rough");
        let k=a.id+":"+x;ck(!longSeen.has(k),"long incoming anchor/position unique");longSeen.add(k);c.long++;
        for(let ell of [7,11,13,17,19,23,29,31])if(ell<Math.min(a.p**c.d,P**c.d)/2){ck([a.src-1,a.src+1,x-1,x+1].every(z=>mod(z,ell)!==0),"source and resident rough");c.targetTests++;}
       }
       c.checks++;
      }
      ck(hp<=pairBound,"high internal loss covered");c.highPairBound+=pairBound;
      if(highCount&&youngCount){
       c.youngMixed++;c.youngMixedBound+=youngCount;
       let a=H[0].high[0].anchor;ck(h<=c.young+3&&a.h<=h+B/2,"young contact anchor height");
       if(a.p>c.young+3+B/2+3)ck(a.h===(a.sg?3:0),"young contact singular");
       youngSeen.add(a.id+":"+x);
      }
      let list=gs.flatMap(g=>g.tokens);list.sort((a,b)=>status(b,x,n)-status(a,x,n)||a.A-b.A);
      let del=list.slice(M);let hdel=0,ydel=0,udel=0;
      for(let t of del){ck(!dead.has(t.A),"one death");dead.add(t.A);let s=status(t,x,n);hdel+=+(s===2);ydel+=+(s===1);udel+=+(s===0);}
      ck(hdel===hp&&ydel===yp,"priority exact losses");
      c.highDeaths+=hdel;c.youngDeaths+=ydel;c.unprotectedDeaths+=udel;c.protectedDeaths+=hdel+ydel;
      let tokens=list.slice(0,M),v={tokens,tick:n,arr:old?old.arr:n,last:old?old.last:gs.map(g=>g.p)};
      active.set(x,v);sched(x,n,v);
     }
    }
    c.shortKeys+=pairSeen.size-longSeen.size;c.longKeys+=longSeen.size;c.youngKeys+=youngSeen.size;
    let keep=0;for(let [x,v] of active){close(x,v,end);keep+=v.tokens.length;for(let t of v.tokens){ck(full.get(t.A)===x&&!dead.has(t.A),"surviving root path");rootCheck++;}}
    ck(keep+dead.size===full.size,"root mass ledger");c.ret+=keep;
   }
  }
  for(let c of specs){ck(c.ret+c.protectedDeaths+c.unprotectedDeaths+c.protectedBudget+c.otherBudget===N&&c.highDeaths<=c.highPairBound&&c.youngDeaths<=c.youngMixedBound,"global ledger");}
  rows.push({R,N,T,literalEvents,rootCheck,controls:specs.map(c=>({...c,ret:c.ret/N,protectedBudget:c.protectedBudget/N,otherBudget:c.otherBudget/N,averageProtectedThresholdDeaths:c.thresholdMeasure/(c.budget*N),averageThresholdUpper:c.thresholdBound/(c.budget*N),protectedDeaths:c.protectedDeaths/N,highDeaths:c.highDeaths/N,youngDeaths:c.youngDeaths/N,unprotectedDeaths:c.unprotectedDeaths/N,live:c.liveTicks/(N*T),protectedLive:c.protectedTicks/(N*T),highPairBound:c.highPairBound/N,youngMixedBound:c.youngMixedBound/N}))});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000]),null,2));
