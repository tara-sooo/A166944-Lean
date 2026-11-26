// Relay packing energy and bandwise CRT capacity (exact finite controls).
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(x,p)=>(x%p+p)%p;
 const N=600000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let x=p*p;x<=N+2;x+=p)spf[x]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
 function next(a,v){let p=Infinity,w=Infinity,e=0,q=Infinity;for(let [b,s] of [[a+1,-1],[a-1,1]])for(let r of fs(b)){q=Math.min(q,r);let t=mod((s===-1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e,q}}
 let s={roots:0,events:0,blocks:0,negativeBlocks:0,positivePhaseBlocks:0,bandControls:0,groups:0,repeatedGroups:0,groupsWithPositiveCost:0,distinctPairs:0,samePairs:0,crtChecks:0,capacityChecks:0,energyChecks:0,weightedChecks:0,globalChecks:0,syntheticChecks:0,syntheticNontrivial:0,maxGroup:0,maxExcess:0,positiveExcessControls:0,rows:[]};
 // Exact packing lower bound, tested separately from actual trajectories.
 for(let c=1;c<=40;c++)for(let n=0;n<=240;n++){
  let E=0;for(let i=0;i<n;i++)E+=2*Math.floor(i/c);
  let m=Math.floor(n/c),r=n%c;
  ck(E===c*m*(m-1)+2*m*r,"packing exact");ck(E+1e-9>=n*n/c-n,"packing lower");
  s.syntheticChecks++;if(n>c)s.syntheticNontrivial++;
 }
 function check(arr,R,T,U,row){
  if(!arr.length)return;
  let D=R,S=Math.sqrt(2*R+1),groups=new Map(),prev=null,Eg=0,low=0,WL=0,Wdistinct=0,Wsame=0,Gdistinct=0,Gsame=0,Wend=0,Whigh=0,breaks=0,J=0;
  function end(){if(prev)Wend+=prev.w;prev=null;Eg=0}
  for(let x of arr){
   ck(x.q<=S,"non twin slab");
   if(x.p>=U){end();breaks++;continue}
   if(x.p<T){low+=x.p-1;WL+=x.w;if(prev)Eg+=x.p-1;continue}
   Whigh+=x.w;
   if(prev){
    let p=prev.p,r=x.p,E=Eg,e=prev.e,f=x.e;
    ck(x.a===prev.a-p+1-E&&E%2===0,"relay arithmetic");
    if(p===r){ck(E>=p-1,"same-label cost");Wsame+=prev.w;Gsame+=E;s.samePairs++}
    else{
     ck(mod(prev.a-e,p)===0&&mod(prev.a-(p-1+E+f),r)===0,"pair CRT");s.crtChecks++;
     let key=[p,r,e,f].join(":"),g=groups.get(key);if(!g){g={p,r,e,f,list:[]};groups.set(key,g)}
     g.list.push({a:prev.a,E,w:prev.w});Wdistinct+=prev.w;Gdistinct+=E;s.distinctPairs++
    }
   }
   prev=x;Eg=0
  }end();
  let A=0,B=0,energy=0,exact=0;
  for(let g of groups.values()){
   let {p,r,list}=g,n=list.length,c=Math.floor((D-1)/(2*p*r))+1,t=Math.min(p,S),E=list.reduce((a,x)=>a+x.E,0),W=list.reduce((a,x)=>a+x.w,0),cnt=new Map();
   for(let x of list){let old=cnt.get(x.E)||[];for(let a of old)ck(mod(a-x.a,2*p*r)===0,"CRT gap");old.push(x.a);cnt.set(x.E,old)}
   for(let a of cnt.values()){ck(a.length<=c,"capacity");s.capacityChecks++}
   let m=Math.floor(n/c),r0=n%c,packing=c*m*(m-1)+2*m*r0;
   ck(E>=packing&&E+1e-9>=n*n/c-n,"energy lower");s.energyChecks++;
   let cost=Math.max(0,W-2*t*c)**2/(4*t*t*c);
   ck(cost<=E+1e-7&&W<=2*t*(c+Math.sqrt(c*E))+1e-7,"weighted energy");s.weightedChecks++;
   A+=t*c;B+=t*t*c;energy+=cost;exact+=2*t*(c+Math.sqrt(c*E));
   s.groups++;if(n>=2)s.repeatedGroups++;if(packing>0)s.groupsWithPositiveCost++;s.maxGroup=Math.max(s.maxGroup,n);J++;
  }
  ck(Whigh===Wdistinct+Wsame+Wend&&Gsame+Gdistinct<=low,"partition");
  ck(Wsame<=2.5*Gsame+1e-8&&Wend<=2*Math.min(U,S)*(breaks+1)+1e-8,"same and end");
  ck(Wdistinct<=exact+1e-7&&exact<=2*A+2*Math.sqrt(B*Gdistinct)+1e-6,"global Cauchy");
  let excess=Math.max(0,Wdistinct-2*A);
  if(B>0)ck(excess*excess/(4*B)<=Gdistinct+1e-7,"aggregate lower");
  ck(energy<=Gdistinct+1e-7,"group positive-part energy");
  if(excess>0){s.positiveExcessControls++;s.maxExcess=Math.max(s.maxExcess,excess)}
  ck(Whigh+WL<=5.5*low+2*A+2*Math.sqrt(B*low)+2*Math.min(U,S)*(breaks+1)+1e-6,"full band bound");
  if(isFinite(U)&&U<=2*T){
   ck(A<=J*(D/(2*T)+2*T)+1e-7,"band A");ck(B<=J*(2*D+4*T*T)+1e-7,"band B");
  }
  s.globalChecks++;s.bandControls++;row.controls++;row.groups+=J;row.same+=Gsame;row.relay+=Gdistinct;row.wait+=Whigh;row.excess+=excess;
 }
 for(let R of [10000,40000,120000,250000]){
  let row={R,roots:0,events:0,blocks:0,controls:0,groups:0,same:0,relay:0,wait:0,excess:0};
  // Canonical negative prefixes, plus explicitly arbitrary clock phases
  // (including positive times), to exercise longer noncanonical blocks.
  for(let mode of [0,1,2,3]){
   for(let A=Math.ceil((2*R-150)/6)*6;A<2*R;A+=6){
    let a=A,v=mode===0?-A/2+3:mode===1?0:mode===2?17:Math.floor(A/5),block=[];
    function flush(){if(!block.length)return;s.blocks++;row.blocks++;if(mode===0)s.negativeBlocks++;else s.positivePhaseBlocks++;
     for(let T of [5,11,23,Math.max(5,Math.floor(Math.sqrt(R)/4)),Math.floor(Math.sqrt(R))]){
      check(block,R,T,Infinity,row);check(block,R,T,2*T,row)
     }block=[]
    }
    while(a>=R){
     let x=next(a,v);if(mode===0&&v+x.w>-1)break;
     if(x.q>Math.sqrt(a+1))flush();else block.push({a,v,...x});
     v+=x.w;a-=x.p-1;s.events++;row.events++;
    }flush();s.roots++;row.roots++;
   }
  }s.rows.push(row)
 }
 return s
}
console.log(JSON.stringify(audit(),null,2));
