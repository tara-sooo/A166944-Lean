// Exact static walls, wall-cell gain budgets and bounded-height escape controls.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,P=[3,5,7,11,13,17,19,23,29],rows=[],tables=new Map();
 function allowed(x,p){let r=mod(-x,p);return r<=(p-3)/2}
 let stats={localWallChecks:0,crtLifts:0,gapChecks:0,rootGapChecks:0,actualBlocks:0,actualEvents:0,lowRuns:0,cellBudgetChecks:0,nontrivialCellImprovement:0,heightRoots:0,heightTicks:0,heightChecks:0,heightRows:[],wallPotentialChecks:0,neutralChecks:0,wallDropChecks:0,tailBudgetChecks:0,oneSidedRechargeChecks:0,exactRechargeChecks:0,rechargeRows:[],rows};
 for(let p of P)for(let r=0;r<p;r++){
  let cross=false;for(let d=0;d<(p-1)/2;d++)if(mod(2*(r+d)-1,p)===0||mod(2*(r+d)+1,p)===0)cross=true;
  ck(allowed(r,p)===!cross,"local exact wall");stats.localWallChecks++;
 }
 let Q=1,w=[0];
 for(let p of P){
  let a=[];for(let r of w)for(let k=0;k<p;k++)if(allowed(r+Q*k,p))a.push(r+Q*k);Q*=p;a.sort((a,b)=>a-b);w=a;
  ck(w.length===P.filter(q=>q<=p).reduce((a,q)=>a*(q-1)/2,1),"CRT count");stats.crtLifts+=w.length;
  let max=0,sum=0,hist=new Map();for(let i=0;i<w.length;i++){let d=(i+1===w.length?Q:w[i+1])-w[i];max=Math.max(max,d);sum+=d*(d-1)/2;hist.set(d,(hist.get(d)||0)+1);stats.gapChecks++}
  ck([...hist].reduce((a,[d,n])=>a+d*n,0)===Q,"period gaps");
  let row={p,Q,walls:w.length,maxGap:max,meanGap:Q/w.length,meanDistance:sum/Q,density:w.length/Q,tail:[1,2,4,8].map(k=>{let B=Math.ceil(k*Q/w.length);return {B,mass:[...hist].reduce((a,[d,n])=>a+Math.max(d-B,0)*n,0)/Q}})};
  rows.push(row);tables.set(p,{Q,w,max,hist});
 }
 function wall(x,t){let r=mod(x,t.Q),lo=0,hi=t.w.length;while(lo+1<hi){let m=(lo+hi)>>1;if(t.w[m]<=r)lo=m;else hi=m}return x-r+t.w[lo]}
 function gapFromWall(x,t){let r=mod(x,t.Q),lo=0,hi=t.w.length;while(lo+1<hi){let m=(lo+hi)>>1;if(t.w[m]<=r)lo=m;else hi=m}return (hi===t.w.length?t.Q:t.w[hi])-t.w[lo]}
 // Full-period one-sided wall-distance recharge profiles.
 for(let z of [3,5,7,11]){
  let t=tables.get(z),d=Array.from({length:t.Q},(_,x)=>x-wall(x,t)),row={z,Q:t.Q,M:t.max,classes:0,exactSmallShifts:0,zeroShifts:0};
  for(let s=0;s<t.Q;s++){let mx=0,sum=0;for(let x=0;x<t.Q;x++){let diff=d[(x+s)%t.Q]-d[x];ck(diff<=Math.min(s,t.max-1),"one-sided recharge");mx=Math.max(mx,diff);sum+=diff;stats.oneSidedRechargeChecks++}
   ck(sum===0,"zero mean shift");if(s<t.max){ck(mx===s,"exact short upward shift");row.exactSmallShifts++;stats.exactRechargeChecks++}
   if(mx===0)row.zeroShifts++;row.classes++;
  }ck(row.zeroShifts===1,"only neutral full-period shift");stats.rechargeRows.push(row);
 }
 const N=400000,spf=new Uint32Array(N+3);for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)if(!spf[n])spf[n]=p;
 function fs(n){n=Math.abs(n);let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function event(a,v){let p=Infinity,w=Infinity;for(let [d,e] of [[a+1,-1],[a-1,1]])for(let r of fs(d)){let t=mod((e===-1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}}return {p,w}}
 for(let R of [10000,40000,120000,180000])for(let mode of [0,1])for(let A=2*R-180;A<2*R;A+=6){
  let a=A,v=mode?17:3-A/2,arr=[];while(a>=R){let x=event(a,v);if(!mode&&v+x.w>-1)break;arr.push({a,p:x.p,b:a-x.p+1});v+=x.w;a-=x.p-1;stats.actualEvents++}
  if(!arr.length)continue;stats.actualBlocks++;
  for(let z of [3,5,7,11,13,17,19,23,29]){
   let t=tables.get(z),low=0,high=0,run=null,used=new Map(),recharge=0,positive=0,drop=0;
   const distance=x=>x-wall(x,t);
   for(let x of arr){let aa=x.a/2,bb=x.b/2,d=distance(bb)-distance(aa),C=wall(aa,t)-wall(bb,t);ck(C>=0&&d===bb-aa+C,'wall drop');stats.wallDropChecks++;drop+=C;if(x.p<=z)ck(C===0,'low drop');if(x.p>z){ck(d<=Math.min(mod(-(x.p-1)/2,t.Q),t.max-1),"actual recharge cap");stats.oneSidedRechargeChecks++;recharge+=d;positive+=Math.max(0,d);if((x.p-1)%(2*t.Q)===0){ck(d===0,'neutral');stats.neutralChecks++;}high++;if(run!==null){stats.lowRuns++;run=null}continue}
    let a=x.a/2,b=x.b/2,J=wall(a,t);ck(b>=J,"no cross");stats.rootGapChecks++;
    if(run===null)run=J;else ck(run===J||a===run,"same cell");
    low+=a-b;used.set(J,(used.get(J)||0)+a-b);
   }
   if(run!==null)stats.lowRuns++;
   let caps=[...used].map(([J,g])=>{let c=gapFromWall(J,t);ck(g<=c,"cell capacity");return c});
   ck(used.size<=high+1&&low<=caps.reduce((a,b)=>a+b,0)&&low<=t.max*(high+1),"global cell cap");stats.cellBudgetChecks++;
   let top=arr[0].a/2,bottom=arr.at(-1).b/2;ck(low===distance(top)-distance(bottom)+recharge&&low<=distance(top)+positive&&drop===wall(top,t)-wall(bottom,t),'wall potential telescope');stats.wallPotentialChecks++;
   for(let B of [0,Math.ceil(t.Q/t.w.length),Math.ceil(2*t.Q/t.w.length)]){
    let tail=0,j=wall(bottom,t);while(j<top){let d=gapFromWall(j,t),len=Math.max(0,Math.min(top,j+d)-Math.max(bottom,j));tail+=Math.max(0,len-B);j+=d}
    ck(low<=B*(high+1)+tail,'tail cell budget');stats.tailBudgetChecks++;
   }
   if(caps.reduce((a,b)=>a+b,0)<t.max*(high+1))stats.nontrivialCellImprovement++;
  }
 }
 function tick(t,h,j){let b=h+1,n=3-3*j+t,e=mod(n,2)===0?-1:1,p=0;for(let q of fs(e===-1?2*b+1:2*b-5)){if(mod(n-(e===-1?0:q+2),2*q)===0){p=q;break}}return b-(p?(p-1)/2:0)}
 for(let H=4;H<=8;H++){
  let z=P.filter(p=>p<=2*H+1).at(-1),tab=tables.get(z),per=2*tab.Q/3,row={H,z,period:per,mean:0,max:0,meanWallBound:0,maxWallBound:0};
  for(let j=0;j<per;j++){let h=3,t=0,J=wall(3*j,tab),B=3*j-J+H-3;
   while(h<H){h=tick(++t,h,j);ck(t<=B,"escape wall time");stats.heightTicks++}
   row.mean+=t;row.max=Math.max(row.max,t);row.meanWallBound+=B;row.maxWallBound=Math.max(row.maxWallBound,B);stats.heightRoots++;stats.heightChecks++;
  }row.mean/=per;row.meanWallBound/=per;stats.heightRows.push(row)
 }
 return stats
}
console.log(JSON.stringify(audit(),null,2));
