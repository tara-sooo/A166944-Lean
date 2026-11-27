// Late-tail entropy: synchronized clock-pruned factor ranks and asynchronous early-prefix separation.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=4000005,spf=new Int32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)if(!spf[a])spf[a]=p;
 function fs(n){let v=[];while(n>1){let p=spf[n]||n;v.push(p);while(n%p===0)n/=p}return v}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const f=x=>x?x*Math.log(x):0,add=(m,k,v=1)=>m.set(k,(m.get(k)||0)+v),sumF=m=>[...m.values()].reduce((s,v)=>s+f(v),0);
 let out={roots:0,events:0,tailControls:0,reverseDecodes:0,clockPinChecks:0,rankChecks:0,kraftChecks:0,entropyChecks:0,rows:[]};
 for(let R of [12000,48000,192000,480000,1000000,2000000]){
  let S=Math.sqrt(2*R+1),T=Math.ceil(S),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nr=(hi-lo)/6+1,B=3*T+6;
  let cuts=[{type:"sync",t:0},{type:"sync",t:Math.floor(T/4)},{type:"sync",t:Math.floor(T/2)},{type:"sync",t:Math.floor(3*T/4)},{type:"early",t:Math.floor(Math.log(R))},{type:"early",t:Math.floor(Math.log(R)**1.5)},{type:"early",t:Math.min(T,Math.floor(Math.log(R)**2))}];
  if(R>=1000000)cuts=cuts.filter(c=>c.type==="early"||c.t===Math.floor(T/2));
  let data=cuts.map(c=>({...c,counts:new Map(),ends:new Map(),joint:new Map(),paths:new Map(),totalN:0,changed:0,tailGain:0,tailLowGain:0}));
  let ends=new Map(),endsW=new Map();
  for(let A=lo;A<=hi;A+=6){
   let l=lo+Math.floor((A-lo)/W)*W,n0=3-l/2,end=n0+T,a=A,n=3-A/2,birth=n,events=[];
   for(;;){let e=next(a,n),fire=n+e.w;if(fire>end)break;let b=a-e.p+1;events.push({p:e.p,n:fire,b});a=b;n=fire;out.events++}
   add(ends,a);add(endsW,l+":"+a);out.roots++;
   for(let d of data){
    let cut=d.type==="sync"?n0+d.t:birth+d.t;if(cut>end)cut=end;
    let i=0;while(i<events.length&&events[i].n<=cut)i++;let x=i?events[i-1].b:A,tail=events.slice(i),y=a,j=d.type==="sync"?l:0,k=j+":"+y+":"+x;
    add(d.counts,j+":"+x);add(d.ends,j+":"+y);add(d.joint,k);
    // Store distinct actual event words, not just x: early cuts need not have a common clock.
    let word=tail.map(e=>e.p).join(","),pk=k+":"+word;let v=d.paths.get(pk);
    if(v){v.m++;if(d.type==="sync")ck(v.cut===cut&&v.end===end,"same clock")}else d.paths.set(pk,{x,y,j,cut,end,tail,m:1,word});
    d.totalN+=tail.length;d.changed+=+(tail.length>0);d.tailGain+=x-y;out.tailControls++;
   }
  }
  let Lend=sumF(ends)/nr,LendW=sumF(endsW)/nr,rows=[];
  for(let d of data){
   let Lx=sumF(d.counts)/nr,Ly=sumF(d.ends)/nr,Hxy=(sumF(d.ends)-sumF(d.joint))/nr;
   ck(Hxy>=-1e-8&&Lx+Hxy>=Ly-1e-8,"chain");if(d.type==="sync")ck(Math.abs(Lx+Hxy-Ly)<1e-8,"sync equality");out.entropyChecks++;
   let ys=[3,13,31,Math.floor(T/8),B+1].filter((v,i,a)=>v>=3&&a.indexOf(v)===i);
   let results=[];
   for(let Y of ys){
    let counts=new Map(),classMass=new Map(),rec=[],rankSum=0,prunedSum=0,meanK=0,meanLow=0,changedMass=0;
    for(let v of d.paths.values()){
     let gaps=[0],high=[];for(let i=v.tail.length-1;i>=0;i--){let e=v.tail[i];if(e.p<=Y)gaps[gaps.length-1]+=(e.p-1)/2;else {high.push(e);gaps.push(0)}}
     let key=gaps.join(","),cl=String(mod(v.y,210)),key2=cl+":"+key;
     add(counts,key2,v.m);add(classMass,cl,v.m);
     let x=v.y,rank=0,rankP=0,upper=v.end,low=gaps.reduce((s,n)=>s+n,0),choices=[],prunedChoices=[];
     for(let i=0;i<high.length;i++){
      let e=high[i];x+=2*gaps[i];if(gaps[i])upper--;
      ck(x===e.b,"target reverse");
      let maxP=Math.min(hi,v.y+B)-x+1,all=[...new Set([...fs(x),...fs(x-2)])].filter(p=>p>Y&&p<=maxP).sort((a,b)=>a-b);
      ck(all.includes(e.p),"rank");out.rankChecks++;
      rank+=Math.log(all.length);choices.push(all.indexOf(e.p));
      if(d.type==="sync"){
       let cand=all.map(p=>{let c=x%p===0?0:p+2,n=upper-mod(upper-c,2*p);return {p,n}}).filter(z=>z.n>v.cut&&z.n+x/2>=0);
       let j=cand.findIndex(z=>z.p===e.p);ck(j>=0&&e.n<=cand[j].n&&e.n>v.cut,"clock rank");out.clockPinChecks++;
       rankP+=Math.log(cand.length);prunedChoices.push(j);upper=cand[j].n-1;
      }else{rankP+=Math.log(all.length);prunedChoices.push(all.indexOf(e.p))}
      x+=e.p-1;
     }
     x+=2*gaps.at(-1);ck(x===v.x,"reverse x");out.reverseDecodes++;
     rec.push({v,key,key2,cl,rank,rankP,word:key+"|"+choices.join(","),wordP:key+"|"+prunedChoices.join(",")});
     rankSum+=v.m*rank;prunedSum+=v.m*rankP;meanK+=v.m*high.length;meanLow+=v.m*low*2;changedMass+=v.m*+(v.tail.length>0);
    }
    let E=0,EP=0,gapCost=0,weights=new Map(),weightP=new Map();
    for(let r of rec){
     let pi=counts.get(r.key2)/classMass.get(r.cl),c=-Math.log(pi),u=c+r.rank,up=c+r.rankP;E+=r.v.m*u;EP+=r.v.m*up;gapCost+=r.v.m*c;
     let key=r.v.j+":"+r.v.y,k=weights.get(key)||new Map(),k2=weightP.get(key)||new Map();k.set(r.word,Math.exp(-u));k2.set(r.wordP,Math.exp(-up));weights.set(key,k);weightP.set(key,k2);
    }
    for(let [key,k] of weights){let w=[...k.values()].reduce((s,v)=>s+v,0),wp=[...weightP.get(key).values()].reduce((s,v)=>s+v,0);ck(w<=1+1e-8&&wp<=1+1e-8,"Kraft");out.kraftChecks++}
    ck(E/nr>=Hxy-1e-8&&EP/nr>=Hxy-1e-8&&EP<=E+1e-7,"code");out.entropyChecks++;
    results.push({Y,gapCost:gapCost/nr,rankCost:rankSum/nr,clockRankCost:prunedSum/nr,code:E/nr,clockCode:EP/nr,meanHigh:meanK/nr,meanLowGain:meanLow/nr,gapClasses:counts.size});
   }
   rows.push({type:d.type,t:d.t,Lx,Ly,Hxy,chain:Lx+Hxy,earlyGainCap:d.type==="early"?Math.log(1+Math.floor((2*d.t+6)/6)):null,tailEvents:d.totalN/nr,tailChanged:d.changed/nr,tailGain:d.tailGain/nr,results});
  }
  out.rows.push({R,T,nr,Lend,LendW,cuts:rows});
 }return out
}
console.log(JSON.stringify(audit(),null,2));
