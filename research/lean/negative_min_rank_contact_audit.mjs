// Independent event-driven verification of capped cumulative retention.
function audit(Rs){
 const mod=(a,b)=>(a%b+b)%b,ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 const spf=new Int32Array(2*Math.max(...Rs)+10);
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(x,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let r of fs(x-s)){let d=mod((s===-1?0:r+2)-n,2*r)||2*r;if(d<w||d===w&&r<p){p=r;w=d}}return {p,w}}
 const q=x=>Math.min(spf[x-1]||x-1,spf[x+1]||x+1),choose=n=>n*(n-1)/2;
 let rows=[];
 for(let R of Rs){
  let T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
  let specs=[[4,32],[16,128],[64,256]].map(([M,b])=>({M,b,selected:0,events:0,pairs:0,pairTicks:0,live:0,loss:0,allCheapTicks:0,cheapPairTicks:0,cheapLive:0,cheapLoss:0,cheapBudgetLoss:0,fullCheapFinal:0,cheapDeaths:0,cheapPolicyCost:0,checks:0,cohortBound:0,cheapBound:0}));
  for(let l=lo;l<=hi;l+=W){
   let maxA=Math.min(hi,l+W-6),start=3-maxA/2,n0=3-l/2,end=n0+T;
   let traces=new Map(),births=new Map(),fires=new Map();
   const cost=(p,x)=>p>5&&p<47?8:p>=47&&p<T/2&&4*q(x)**2>=p?2*q(x):0;
   for(let A=l;A<=maxA;A+=6){
    let x=A,n=3-A/2,total=0;births.set(n,A);
    for(;;){let e=next(x,n),t=n+e.w;if(t>end)break;
     let g=fires.get(t)||[];g.push({A,x,y:x-e.p+1,cost:cost(e.p,x)});fires.set(t,g);
     total+=cost(e.p,x);x-=e.p-1;n=t;
    }
    traces.set(A,{total,y:x});
   }
   for(let c of specs){
    let full=new Map(),alive=new Map(),fixedAlive=new Map(),fixedDead=new Set(),cheapDead=new Set(),costs=new Map();
    let pairTicks=0,cheapPairTicks=0,live=0,cheapLive=0,allCheap=0,loss=0,cheapLoss=0,budgetLoss=0,pairs=0,selected=0,policyCost=0;
    const rank=(a,b)=>costs.get(a)-costs.get(b)||a-b;
    for(let [A,t] of traces)if(t.total<=c.b)selected++;
    c.selected+=selected;
    function insert(map,x,ids){if(!ids.length)return;let v=map.get(x)||[];v.push(...ids);map.set(x,v)}
    for(let n=start;n<=end;n++){
     let moves=new Map(),b=fires.get(n)||[],affected=new Set(),prevPairs=0;
     for(let e of b){
      let a=moves.get(e.x)||{y:e.y,cost:e.cost,ids:[]};ck(a.y===e.y&&a.cost===e.cost,"common firing");a.ids.push(e.A);moves.set(e.x,a);
     }
     for(let [x,m] of moves){
      let v=full.get(x)||[];ck(v.length===m.ids.length&&m.ids.every(A=>v.includes(A)),"full physical group no split");
      let a=alive.get(x)||[],f=fixedAlive.get(x)||[];
      for(let A of v)costs.set(A,costs.get(A)+m.cost);
      for(let A of a)policyCost+=m.cost;
      full.delete(x);alive.delete(x);fixedAlive.delete(x);
      m.a=a.filter(A=>{if(costs.get(A)>c.b){ck(!cheapDead.has(A),"one budget death");cheapDead.add(A);budgetLoss+=Math.max(0,end-Math.max(n,n0));return false;}return true;});
      m.f=f;affected.add(m.y);
     }
     let incoming=new Map();
     for(let [x,m] of moves){let v=incoming.get(m.y)||[];v.push(m.ids);incoming.set(m.y,v);insert(full,m.y,m.ids);insert(alive,m.y,m.a);insert(fixedAlive,m.y,m.f);c.events++;}
     if(births.has(n)){let A=births.get(n);costs.set(A,0);let v=incoming.get(A)||[];v.push([A]);incoming.set(A,v);insert(full,A,[A]);insert(alive,A,[A]);if(traces.get(A).total<=c.b)insert(fixedAlive,A,[A]);affected.add(A);}
     for(let x of affected){
      let v=full.get(x),a=alive.get(x)||[],f=fixedAlive.get(x)||[];
      let fixed=v.filter(A=>traces.get(A).total<=c.b).sort((a,b)=>a-b),cheap=v.filter(A=>costs.get(A)<=c.b).sort(rank);
      let gs=incoming.get(x)||[],s=gs.reduce((s,g)=>s+g.filter(A=>traces.get(A).total<=c.b).length,0);
      let pairNew=choose(fixed.length)-choose(fixed.length-s)-gs.reduce((s,g)=>s+choose(g.filter(A=>traces.get(A).total<=c.b).length),0);
      ck(pairNew>=0,"nonnegative new pairs");pairs+=pairNew;pairTicks+=pairNew*Math.max(0,end-Math.max(n,n0));
      a.sort(rank);f.sort((a,b)=>a-b);
      for(let A of a.slice(c.M)){ck(!cheapDead.has(A),"no reactivation");cheapDead.add(A);cheapLoss+=Math.max(0,end-Math.max(n,n0));}
      for(let A of f.slice(c.M)){ck(!fixedDead.has(A),"no fixed reactivation");fixedDead.add(A);loss+=Math.max(0,end-Math.max(n,n0));}
      let aa=a.slice(0,c.M),ff=f.slice(0,c.M);alive.set(x,aa);fixedAlive.set(x,ff);
      ck(aa.length===Math.min(c.M,cheap.length)&&aa.every((A,i)=>A===cheap[i]),"exact cheap priority rank optimum");
      ck(ff.length===Math.min(c.M,fixed.length)&&ff.every((A,i)=>A===fixed[i]),"exact fixed rank optimum");c.checks+=2;
     }
     if(n>=n0&&n<end){
      let s=0,cs=0,lp=0,cp=0;
      for(let [x,v] of full){
       let f=v.filter(A=>traces.get(A).total<=c.b).length,cheap=v.filter(A=>costs.get(A)<=c.b).length;
       let fr=(fixedAlive.get(x)||[]).length,cr=(alive.get(x)||[]).length;
       ck(fr===Math.min(f,c.M)&&cr===Math.min(cheap,c.M),"all ticks optimal");c.checks++;
       live+=fr;cheapLive+=cr;allCheap+=cheap;s+=f;cs+=cheap;lp+=choose(f);cp+=choose(cheap);
      }
      ck(s===selected,"all roots born by n0");c.pairTicks+=lp;cheapPairTicks+=cp;
     }
    }
    ck(selected*T===live+loss&&traces.size*T===cheapLive+cheapLoss+budgetLoss,"time loss identity");
    ck(c.M*loss<=pairTicks&&c.M*(allCheap-cheapLive)<=cheapPairTicks,"weighted pair charge");
    ck(policyCost<=traces.size*(c.b+2*T),"budget overshoot");c.checks+=3;
    c.live+=live;c.loss+=loss;c.pairs+=pairs;c.allCheapTicks+=allCheap;c.cheapPairTicks+=cheapPairTicks;c.cheapLive+=cheapLive;c.cheapLoss+=cheapLoss;c.cheapBudgetLoss+=budgetLoss;c.cheapPolicyCost+=policyCost;
    c.fullCheapFinal += [...traces.values()].filter(v=>v.total<=c.b).length;
    c.cohortBound+=pairTicks; 
   }
  }
  for(let c of specs){
   ck(c.cohortBound===c.pairTicks,"integrated pair moment equals first-contact weights");
   const nt=N*T,s=c.selected*T,sp=c.allCheapTicks;
   c.fixedLower=s?c.M*s*s/((c.M-1)*s+s+2*c.pairTicks):0;
   c.cheapLower=sp?c.M*sp*sp/((c.M-1)*sp+sp+2*c.cheapPairTicks):0;
   ck(c.fixedLower<=c.live+1e-6&&c.cheapLower<=c.cheapLive+1e-6,"Cauchy Schwarz lower bound");
  }
  rows.push({R,N,T,controls:specs.map(c=>({...c,selected:c.selected/N,live:c.live/(N*T),loss:c.loss/(N*T),cheapLive:c.cheapLive/(N*T),allCheapTicks:c.allCheapTicks/(N*T),cheapLoss:c.cheapLoss/(N*T),cheapBudgetLoss:c.cheapBudgetLoss/(N*T),fixedLower:c.fixedLower/(N*T),cheapLower:c.cheapLower/(N*T),pairTicks:c.pairTicks/(N*T),cheapPairTicks:c.cheapPairTicks/(N*T)}))});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000]),null,2));
