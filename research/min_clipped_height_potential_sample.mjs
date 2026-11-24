// Fixed-seed CRT sampling of entire LOW paths, clipped leak and quantiles.
function clipSample(Y,N=8192){
 const ps=[];for(let p=3;p<Y;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 let rng=(0x71b2439d^Y)>>>0;
 function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let lim=4294967296-4294967296%p,x;do{x=u32()}while(x>=lim);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),ds=[],caps=[Y,Math.floor(Y*Math.sqrt(Math.log(Y))),Math.floor(Y*Math.log(Y))],P=[5,11,31].filter(p=>p<Y);
 let rows=caps.map(K=>({K,tail:0,leak:0,small:P.map(P=>({P,leak:0,tail:0}))})),sum=0,stepsum=0,maxsteps=0;
 for(let j=0;j<N;j++){
  let parity=uni(2);for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let v=uni(p);t[i]=v%2===parity?v:v+p}
  let el=0,gain=0,steps=0,d=0,first=0,fd=0;
  for(;;){let w=Infinity,p0=0;for(let i=0;i<ps.length;i++){let p=ps[i],cc=(c[i]+gain)%p;if(cc!==1&&cc!==p-1)continue;let ph=cc===1?0:p+2,b=(t[i]+el-ph)%(2*p);if(b<0)b+=2*p;let f=2*p-b;if(f<w||(f===w&&p<p0)){w=f;p0=p}}if(!p0)break;
   if(!steps){first=p0;fd=2*w-p0+1}
   el+=w;gain+=p0-1;d=Math.max(d,2*el-gain);if(++steps>20000)throw Error("guard")
  }
  ds.push(d);sum+=d;stepsum+=steps;maxsteps=Math.max(maxsteps,steps);
  for(let a of rows){let v=Math.max(0,Math.min(Math.max(0,fd),d-a.K));a.tail+=d>a.K;a.leak+=v;for(let z of a.small)if(first&&first<z.P){z.leak+=v;z.tail+=d>a.K}}
 }
 ds.sort((a,b)=>a-b);for(let a of rows){a.tailCount=a.tail;a.tail/=N;a.leak/=N;for(let z of a.small){z.tail/=N;z.leak/=N}}
 return {Y,N,mean:sum/N,meanRatio:sum/N/(Y*Math.log(Y)),q50:ds[Math.ceil(.5*N)-1],q90:ds[Math.ceil(.9*N)-1],q99:ds[Math.ceil(.99*N)-1],max:ds.at(-1),meanSteps:stepsum/N,maxsteps,rows}
}
for(const Y of process.argv.slice(2).map(Number))console.log(JSON.stringify(clipSample(Y)));
