// CRT universal barrier Fourier estimates and exact interval-count sweep.
function audit(Y){
 const ps=[];for(let p=3;p<Y;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 let P=1,positions=[0],beta=1,gamma=1,delta=1,maxLocalRatio=0,checks=0;
 const ck=(b,m)=>{if(!b)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 for(let p of ps){
  let m=(p-1)/2,c=Math.min(1,1/(m*Math.sin(Math.PI/p)));
  for(let k=1;k<p;k++){let re=0,im=0;for(let x=0;x<m;x++){re+=Math.cos(2*Math.PI*k*x/p);im+=Math.sin(2*Math.PI*k*x/p)}let r=Math.hypot(re,im)/m;ck(r<=c+1e-12,"local Fourier bound");maxLocalRatio=Math.max(maxLocalRatio,r/c);checks++;}
  beta*=c*c+(1-c*c)/p;gamma*=c+(1-c)/p;delta*=m/p;
  let nxt=[];for(let x of positions)for(let j=0;j<p;j++){let v=x+P*j;if(v%p<m)nxt.push(v)}
  P*=p;positions=nxt.sort((a,b)=>a-b);ck(positions.length===Math.round(P*delta),"CRT count");
 }
 let gaps=[],maxGap=0,meanForward=0;for(let i=0;i<positions.length;i++){let g=(positions[i+1]??P)-positions[i];gaps.push(g);maxGap=Math.max(maxGap,g);meanForward+=g*(g-1)/(2*P)}
 const density=positions.length/P;
 const Rs=[...new Set([1,Math.ceil(1/density),Math.ceil(4/density),Math.ceil(16/density),Math.ceil(P*beta),Math.ceil(2*P*beta),Math.floor(P/2),P].map(x=>Math.max(1,Math.min(P,x))))].sort((a,b)=>a-b);
 const results=[];
 for(let R of Rs){
  let count=0;for(let b of positions){if(b<R)count++;else break;}
  const mean=R*density,events=[];
  for(let b of positions){let add=mod(b-R+1,P),sub=mod(b+1,P);if(add)events.push([add,1]);if(sub)events.push([sub,-1]);}
  events.sort((a,b)=>a[0]-b[0]);
  let prev=0,total=0,variance=0,no=0,maxDisc=0,minCount=Infinity,maxCount=0;
  function acc(len){if(!len)return;total+=len*count;variance+=len*(count/mean-1)**2/P;if(count===0)no+=len;maxDisc=Math.max(maxDisc,Math.abs(count/mean-1));minCount=Math.min(minCount,count);maxCount=Math.max(maxCount,count);}
  for(let j=0;j<events.length;){let x=events[j][0];acc(x-prev);while(j<events.length&&events[j][0]===x)count+=events[j++][1];prev=x;}
  acc(P-prev);
  let gapNo=gaps.reduce((s,g)=>s+Math.max(0,g-R),0);
  ck(no===gapNo&&Math.abs(total-P*mean)<Math.max(1,1e-12*P*mean),"interval sweep conservation");
  let varBound=2*P*beta/R,discBound=P*gamma*(1+Math.log(P))/R;
  ck(variance<=varBound+1e-8&&maxDisc<=discBound+1e-8&&no/P<=variance+1e-8,"Fourier global bound");
  results.push({R,mean,variance,varBound,noBarrier:no/P,maxDisc,discBound,minCount,maxCount});
 }
 return {Y,P,barriers:positions.length,density,beta,gamma,varianceScale:2*P*beta,deterministicScale:P*gamma*(1+Math.log(P)),meanGap:1/density,maxGap,meanForward,checks,maxLocalRatio,results}
}
for(const Y of [5,7,11,13,17,19,23,29])console.log(JSON.stringify(audit(Y)));
