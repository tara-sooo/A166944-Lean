// Exact conditional prime-priority and integer reset-start first-exit checks.
function audit(X,W){
 const B=Math.ceil(Math.sqrt(7*X)),Z0=10*W+14,K=Math.floor((7*X-1)/4),spf=new Int32Array(7*X+2*B+20);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i;}
 const mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)},cell=C=>Math.floor((C-1)/W);
 function next(t,C,lim){let n=Infinity,p=0,b=0,r=Infinity;for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(q>lim)break;r=Math.min(r,q);let bb=s===-1?0:6,u=t+2*q-mod(t-(bb===0?0:q+2),2*q);if(u<n||(u===n&&q<p)){n=u;p=q;b=bb;}while(v%q===0)v/=q;}}return {n,p,b,r};}
 function block(u,lim){let t=u,C=2*u-(u%2?6:0),c=cell(C),cost=0,events=0;for(;;){let a=next(t,C,lim);if(!a.p)return {exit:false,t,C,cost,events};let C1=C+a.p-1,h=2*a.n-C1;ck(h>=0,'height');cost+=a.r;events++;if(cell(C1)!==c)return {exit:true,t,C,cost,events,p:a.p,n:a.n,r:a.r,b:a.b,h};t=a.n;C=C1;}}
 let z={X,W,B,Z0,origins:0,terminal:0,exit:[0,0],tailExit:[0,0],tailWait:[0,0],tailGain:[0,0],totalCost:0,totalElapsed:0,checks:0};
 for(let u=X+3;u<=K;u++){
  let a=block(u,B),C0=2*u-(u%2?6:0);z.origins++;ck(a.C-C0<W&&a.t-u<=3*(a.C-C0),'internal gain');z.totalCost+=a.cost;z.totalElapsed+=(a.exit?a.n:a.t)-u;
  if(!a.exit){z.terminal++;continue;}let j=a.h===a.b?0:1;z.exit[j]++;
  if(a.p>8*Z0){let d=block(u,Math.min(Z0,B));ck(!d.exit&&d.C===a.C&&d.t===a.t&&d.events===a.events-1,'cutoff '+JSON.stringify({u,a,d}));let h=2*a.t-a.C,k=mod(a.C+a.p-1,4)===0?1:3;ck(2*(a.n-a.t)===k*a.p-1+a.b-h&&a.h===a.b+(k-1)*a.p,'priority');ck(a.r>a.p/8,'roughness');z.tailExit[j]++;z.tailWait[j]+=a.n-a.t;z.tailGain[j]+=a.p-1;z.checks++;}
 }
 ck(z.terminal+z.exit[0]+z.exit[1]===z.origins,'partition');return z;
}
function priority(W,Z,d){
 const Z0=10*W+14,ps=[];for(let p=3;p<=Z;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 let keys=[],rho0=1,rho=1,rhos=new Map(),tail=Math.max(8*Z0,Math.floor(Math.sqrt(Z)));
 for(let p of ps){rho*=1-2/p;rhos.set(p,rho);if(p<=Z0){rho0=rho;continue;}let a=(d+p-1)%4===0?1:3;for(let b of [0,6])keys.push({p,a,b,s:a*p+b});}
 keys.sort((x,y)=>x.s-y.s||x.p-y.p);let seen=new Map(),prod=1,total=0,gain=[0,0],wait=[0,0],prob=[0,0],min=Infinity,max=0;
 for(let x of keys){let n=seen.get(x.p)||0,pr=prod/(1-n/x.p)/x.p;total+=pr;prod*=(1-(n+1)/x.p)/(1-n/x.p);seen.set(x.p,n+1);if(x.p>tail){let j=x.a===1?0:1,q=pr/(rhos.get(x.p)/rho0/x.p);min=Math.min(min,q);max=Math.max(max,q);prob[j]+=pr;gain[j]+=pr*(x.p-1);wait[j]+=pr*(x.s-1)/2;}}
 if(Math.abs(total+prod-1)>1e-9||Math.abs(prod-rho/rho0)>1e-9)throw Error('probability conservation');
 return {W,Z,d,tail,none:prod,nonresetGainShare:gain[1]/(gain[0]+gain[1]),nonresetRawWaitShare:wait[1]/(wait[0]+wait[1]),minRatio:min,maxRatio:max};
}
const rows=[],periodic=[];for(let X of [16384,65536,262144])for(let W of [2,6,30])rows.push(audit(X,W));for(let Z of [4096,16384,65536])for(let W of [2,6,30])for(let d of [0,2])periodic.push(priority(W,Z,d));console.log(JSON.stringify({rows,periodic},null,2));
