// Thickened pinned-cut neighborhoods: actual MIN corridors and cumulative deficit budget.
function audit(N=60000){
 const lim=2000000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i%2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function factors(x){ok(x>0&&x<lim,"range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g;z={H,p,w,d,dp,g,Z:H+g}}}return z}
 const cfg=[5,7,11].map(S=>{let K=2*pr.filter(p=>p<=S).reduce((a,p)=>a*p,1);return {S,K,V:Math.min(S*S,Math.floor((K-1)/2)),R:5*S,baseR:pr.find(p=>p>S)}});
 const st={roots:0,events:0,cap:0,configs:cfg,offsetControls:0,roughOffsets:0,translationChecks:0,moderateCrossings:0,sievedCrossings:0,pending:0,completed:0,witnessCorridors:0,cleanCorridors:0,cleanEvents:0,fastChecks:0,highDropChecks:0,localBudgetChecks:0,globalBudgetChecks:0,nonoverlapChecks:0,cleanSieved:0,witnessSieved:0,maxCleanLength:0,positiveCleanHigh:0,syntheticHighDrop:0,examples:[],witnessExamples:[]};
 function cutOK(J,S,R,V){for(let p of pr){if(p>V)break;if(p>S&&p<=R&&(J%p%2!==0||J%p>p-3))return false;if(p>R&&[1,p-1].includes(J%p))return false}return true}
 function rough(H,S){return !pr.some(p=>p<=S&&((H-1)%p===0||(H+1)%p===0))}
 for(let {S,V,K,R} of cfg){for(let u=2;u<=V;u+=2){let f=pr.find(p=>p<=S&&((u-1)%p===0||(u+1)%p===0));if(!f){ok(u>=4&&spf[u-1]===u-1&&spf[u+1]===u+1&&u-1>S,"offset twins");st.roughOffsets++}st.offsetControls++;for(let J of [K*100,K*101,K*103])for(let sign of [-1,1]){let H=J+sign*u;ok(rough(H,S)===!f,"translation");st.translationChecks++}}
  for(let p of pr.filter(p=>p>R&&p<4*R))for(let w=1;w<=2*S;w++){ok(R*(p-1-2*w)>=(R-4*S)*(p-1),"synthetic drop");st.syntheticHighDrop++}
 }
 function inspect(rows,{S,V,K,R,baseR},root){
  if(!rows.length||rows[0].H+1<S*S)return;
  let end=rows.at(-1).Z,Pminus=rows.reduce((a,z)=>a+Math.max(0,z.d-z.dp),0),Pplus=rows.reduce((a,z)=>a+Math.max(0,z.dp-z.d),0),Glow=rows.filter(z=>z.p<=R).reduce((a,z)=>a+z.g,0);
  let prevEnd=-1,lastJ=-Infinity,cleanCount=0,paidLow=0,paidNeg=0,paidG=0;
  for(let i=0;i<rows.length;i++){let z=rows[i];if(z.p<=S||z.p>V)continue;let J=Math.ceil(z.H/K)*K;if(J>=z.Z||J===z.H)continue;
   // Strict crossings of the pinned lattice, a superset of the surviving hybrid cuts.
   let sieved=z.p>baseR&&cutOK(J,S,baseR,V);
   st.moderateCrossings++;if(sieved)st.sievedCrossings++;ok(z.H<J&&J<z.Z&&J-lastJ>=K,"spacing");lastJ=J;
   if(J+V>end){st.pending++;continue}
   let j=i;while(rows[j].Z<J+V)j++;ok(i>prevEnd,"disjoint");prevEnd=j;st.nonoverlapChecks++;st.completed++;
   let G=0,L=0,D=0,pp=0,witness=null,high=0;
   for(let k=i;k<=j;k++){let e=rows[k],u=Math.abs(e.H-J);ok(u>0&&u<=V&&e.H<J+V,"corridor offset");G+=e.g;if(e.p<=R)L+=e.g;D+=Math.max(0,e.d-e.dp);pp+=Math.max(0,e.dp-e.d);
    if(rough(e.H,S)){ok(u>=4&&spf[u-1]===u-1&&spf[u+1]===u+1&&u-1>S,"actual offset twin");witness={root,J,H:e.H,p:e.p,q:[u-1,u+1]};continue}
    ok(e.w<=2*S,"fast");st.fastChecks++;
    if(e.p>R){ok(R*(e.d-e.dp)>=(R-4*S)*e.g,"high loss");st.highDropChecks++;high++}
   }
   ok(G>=V,"corridor gain");
   if(witness){st.witnessCorridors++;if(sieved)st.witnessSieved++;if(st.witnessExamples.length<3)st.witnessExamples.push(witness);continue}
   st.cleanCorridors++;if(sieved)st.cleanSieved++;st.cleanEvents+=j-i+1;st.maxCleanLength=Math.max(st.maxCleanLength,j-i+1);if(high)st.positiveCleanHigh++;
   ok((R-4*S)*(G-L)<=R*D,"local budget");st.localBudgetChecks++;
   cleanCount++;paidLow+=L;paidNeg+=D;paidG+=G;
   if(st.examples.length<3&&(high||sieved))st.examples.push({root,S,V,K,R,baseR,J,sieved,start:z.H,end:rows[j].Z,labels:rows.slice(i,j+1).map(a=>a.p),waits:rows.slice(i,j+1).map(a=>a.w),gain:G,lowGain:L,negative:D,positive:pp})
  }
  ok(paidG>=V*cleanCount&&paidLow<=Glow&&paidNeg<=Pminus&&Pminus<=Pplus+rows[0].d,"aggregate budget");
  ok((R-4*S)*V*cleanCount<=(R-4*S)*Glow+R*(Pplus+rows[0].d),"global budget");st.globalBudgetChecks++;
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
  for(let c of cfg)inspect(rows,c,M)
 }
 ok(st.completed&&st.cleanCorridors&&st.witnessCorridors&&st.syntheticHighDrop&&st.globalBudgetChecks,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
