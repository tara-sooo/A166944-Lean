// Unweighted reset-excursion lengths and time-cut crossing counts, common cutoff.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),K=Math.floor((7*X-1)/4),spf=new Int32Array(7*X+4),L=210;
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=b=>{if(!b)throw Error("assertion")},start=X+3,J0=5*X/4+2,J1=3*X/2;
 const C0=t=>2*t-(t%2?6:0);
 function hit(t,C){let u=K+1,q=0;for(let s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let h=t+1+(((s===-1?0:p+2)-t-1)%(2*p)+2*p)%(2*p);if(h<u||(h===u&&p<q)){u=h;q=p}while(v%p===0)v/=p}}return [u,q]}
 const d=Array.from({length:3},()=>new Int32Array(K+2)),count=[0,0,0],cost=[0,0,0],span=[0,0,0],terminal=[0,0,0],termTwin=[0,0,0],earlySinks=[0,0,0],earlyTwin=[0,0,0],earlyCost=[0,0,0];let maxOneP=0,oneLarge=0,oneLargeReset=0,oneLargeRough=0;
 for(let s=start;s<=K;s++){
  let t=s,C=C0(s),c=0,h=0,p1=0,r1=0,t1=0,postH1=0,preGain=0,reset=false;
  for(;;){let [u,p]=hit(t,C);if(!p)break;let r=Math.min(spf[C-1],spf[C+1]);ck(u-t<=2*r);if(p>7){h++;if(h===1){p1=p;r1=r;t1=u;preGain=C-C0(s);ck(preGain<L&&2*(t1-s)>=p1-7)}}C+=p-1;t=u;c+=r;if(h===1&&p===p1&&t===t1)postH1=2*t-C;if(C===C0(t)){reset=true;break}}
  let a=Math.min(2,h);count[a]++;cost[a]+=c;span[a]+=t-s;d[a][s]++;d[a][t]--;
  if(!reset){terminal[a]++;let twin=spf[C-1]===C-1&&spf[C+1]===C+1;if(twin)termTwin[a]++;if(s<=J0){earlySinks[a]++;earlyCost[a]+=c;if(twin)earlyTwin[a]++}}
  if(h===1){ck(c<=p1+3*L&&t-s<=2*p1+6*L);maxOneP=Math.max(maxOneP,p1);if(p1>2*L+10){oneLarge++;if(reset){ck(postH1===(t1%2?6:0)&&t===t1);oneLargeReset++}}if(p1>=12*L+14){ck(r1>=p1/8);oneLargeRough++}}
 }
 let cur=[0,0,0],sum=[0,0,0],max=[0,0,0],min=[Infinity,Infinity,Infinity];
 for(let j=start;j<K;j++){for(let a=0;a<3;a++){cur[a]+=d[a][j];if(j>=J0&&j<=J1){sum[a]+=cur[a];max[a]=Math.max(max[a],cur[a]);min[a]=Math.min(min[a],cur[a])}}}
 return {X,B,K,vertices:K-start+1,J0,J1,count,cost,span,terminal,termTwin,earlySinks,earlyTwin,earlyCost,maxOneP,oneLarge,oneLargeReset,oneLargeRough,cutMean:sum.map(x=>x/(J1-J0+1)),cutMax:max,cutMin:min,multiSpanRatio:span[2]/(X*B)};
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
