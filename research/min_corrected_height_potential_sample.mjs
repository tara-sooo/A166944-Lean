// Fixed-seed CRT-residue Monte Carlo; truncated gamma, not a proof or tail bound.
function sampled(Y,N=8192){
 const ps=[];for(let p=3;p<Y;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const qs=[],cum=[];let mass=0;
 for(let q=Y;q<=32*Y;q++){if(q<2)continue;let ok=true;for(let d=2;d*d<=q;d++)if(q%d===0){ok=false;break}if(ok){qs.push(q);mass+=1/q**2;cum.push(mass)}}
 let rng=(0x4b1d3457^Y)>>>0;
 function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){const limit=4294967296-4294967296%p;let x;do{x=u32()}while(x>=limit);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length);
 let maxEvents=0;
 function walk(gain){
  let el=0,steps=0,drift=0,peak=-Infinity,r0=0,g0=0;
  for(;;){
   let w=Infinity,p0=0,r=0,g=Infinity;
   for(let i=0;i<ps.length;i++){
    let p=ps[i],cc=(c[i]+gain)%p;
    if(cc!==1&&cc!==p-1)continue;
    if(!r)r=p;
    let ph=cc===1?0:p+2,back=(t[i]+el-ph)%(2*p);if(back<0)back+=2*p;
    let f=2*p-back;if(f<w||(f===w&&p<p0)){w=f;p0=p}if(back<g)g=back;
   }
   if(!r){maxEvents=Math.max(maxEvents,steps);return {D:Math.max(0,peak),U:peak,r:r0,g:g0,steps}}
   if(steps===0){r0=r;g0=g}
   gain+=p0-1;el+=w;drift+=2*w-p0+1;peak=Math.max(peak,drift);if(++steps>20000)throw Error("sample path guard exceeded");
  }
 }
 function add(acc,x){acc[0]+=x;acc[1]+=x*x;}
 let a=[0,0],gamma=[0,0],tail=[0,0],ev=[0,0],nonzero=0,largest=0,checks=0;
 for(let j=0;j<N;j++){
  let parity=uni(2);
  for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let v=uni(p);t[i]=v%2===parity?v:v+p}
  let x=(u32()/4294967296)*mass,lo=0,hi=qs.length-1;while(lo<hi){let m=(lo+hi)>>1;if(cum[m]>x)hi=m;else lo=m+1}let q=qs[lo],before=walk(0),after=walk(q-1),z=Math.max(0,after.D-q+1),v=0;
  if(!before.r)v=z;else if(before.g)v=Math.max(0,after.D-q+1+Math.min(2*before.g,-before.U)-4*before.r);
  if(v>z)throw Error("tail domination");
  add(a,before.D);add(gamma,v*mass);add(tail,z*mass);add(ev,before.steps);largest=Math.max(largest,before.D,after.D);if(v)nonzero++;checks++;
 }
 function stat(a){let m=a[0]/N,sd=Math.sqrt(Math.max(0,(a[1]-N*m*m)/(N-1)));return {mean:m,se:sd/Math.sqrt(N)}}
 let A=stat(a),G=stat(gamma),TT=stat(tail);
 return {Y,N,maxQ:32*Y,primeCount:ps.length,weightMass:mass,A,A_ratio:A.mean/(Y*Math.log(Y)),gammaTruncated:G,tailTruncated:TT,events:stat(ev),maxEvents,largest,nonzero,checks}
}
for(const Y of process.argv.slice(2).map(Number)) console.log(JSON.stringify(sampled(Y)));
