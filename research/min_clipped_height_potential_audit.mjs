// Exhaustive clipped potential and exact leakage support identity.
function clipExact(Y){
 const ps=[];for(let p=3;p<Y;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const L=2*ps.reduce((s,p)=>s*p,1),n=L/2,states=n*L;
 if(L>2310)throw Error("exact limit");
 const D=new Uint16Array((n+1)*L),delta=new Int16Array(states),after=new Uint16Array(states),label=new Uint8Array(states);
 const ck=(b,m)=>{if(!b)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 let mean=0,max=0;
 for(let i=n-1;i>=0;i--){
  let C=2*i,eligible=ps.filter(p=>(C-1)%p===0||(C+1)%p===0);
  for(let t=0;t<L&&eligible.length;t++){
   let w=L+1,p0=0;for(let p of eligible){let ph=(C-1)%p===0?0:p+2,f=1+mod(ph-t-1,2*p);if(f<w||(f===w&&p<p0)){w=f;p0=p}}
   let k=i*L+t,j=(i+(p0-1)/2)*L+mod(t+w,L);
   label[k]=p0;delta[k]=2*w-p0+1;after[k]=D[j];D[k]=Math.max(0,delta[k]+after[k]);mean+=D[k];max=Math.max(max,D[k]);
  }
 }
 let caps=[...new Set([0,Y,2*Y,Math.floor(Y*Math.sqrt(Math.log(Y))),Math.floor(Y*Math.log(Y)),max])].sort((a,b)=>a-b);
 let rows=[];
 for(let K of caps){
  let P=[...new Set([5,7,11,Y])].filter(p=>p<=Y).sort((a,b)=>a-b),s={K,tail:0,meanTruncated:0,leak:0,leakOnTail:0,small:P.map(P=>({P,leak:0,tail:0,raw:0})),maxLeak:0};
  for(let k=0;k<states;k++){
   const d=D[k],p=label[k],v=p?Math.max(0,delta[k]+Math.min(K,after[k])-Math.min(K,d)):0;
   ck(v<=Math.max(0,delta[k])&&(!v||d>K),"clip leak support");ck(v===Math.max(0,Math.min(Math.max(0,delta[k]),d-K)),"exact clip leak");
   s.tail+=d>K;s.meanTruncated+=Math.min(d,K);s.leak+=v;s.maxLeak=Math.max(s.maxLeak,v);
   if(d>K)s.leakOnTail+=Math.max(0,delta[k]);
   for(let a of s.small)if(p&&p<a.P){a.leak+=v;if(d>K){a.tail++;a.raw+=Math.max(0,delta[k])}}
  }
  for(let a of s.small){ck(a.leak<=a.raw&&a.raw<=4*a.P*a.tail,"small");a.leak/=states;a.raw/=states;a.tail/=states}
  s.tail/=states;s.meanTruncated/=states;s.leak/=states;s.leakOnTail/=states;rows.push(s)
 }
 return {Y,L,states,mean:mean/states,max,rows};
}
for(const Y of process.argv.slice(2).map(Number))console.log(JSON.stringify(clipExact(Y)));
