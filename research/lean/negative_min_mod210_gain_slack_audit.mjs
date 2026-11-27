// Exact integer potential certificate mod 210, plus actual MIN event audit.
// Run: node research/lean/negative_min_mod210_gain_slack_audit.mjs
function audit(){
 const Q=210,N=Q*Q/2,A=13,B=6,P=97;
 const ok=(h,m)=>{if(!h)throw Error(m)};
 const mod=(x,q)=>((x%q)+q)%q;
 const primes=n=>{let a=new Uint8Array(n+1),p=[];for(let i=2;i<=n;i++)if(!a[i]){p.push(i);if(i*i<=n)for(let j=i*i;j<=n;j+=i)a[j]=1}return p};
 const ps=primes(P).filter(p=>p>2),big=ps.filter(p=>p>7),base=[3,5,7];
 const idx=(x,n)=>mod(x,Q)/2*Q+mod(n,Q);
 const wait=(x,n,p)=>{let c=mod(x+1,p)===0?0:mod(x-1,p)===0?p+2:-1;return c<0?Infinity:mod(c-n,2*p)||2*p};
 const w0=new Int16Array(N),p0=new Int16Array(N);
 for(let i=0;i<N;i++){let x=2*Math.floor(i/Q),n=i%Q,best=32767,label=0;for(const p of base){let w=wait(x,n,p);if(w<best){best=w;label=p}}w0[i]=best;p0[i]=label}
 function edges(i,fn){let x=2*Math.floor(i/Q),n=i%Q;const p=p0[i];if(p)fn(idx(x-p+1,n+w0[i]),w0[i],p);for(const p of big){let mx=Math.min(2*p,w0[i]-1);for(let w=1;w<=mx;w++)fn(idx(x-p+1,n+w),w,p)}}
 const F=new Int32Array(N),inQ=new Uint8Array(N).fill(1),queue=Array.from({length:N},(_,i)=>i);let head=0,updates=0;
 while(head<queue.length){const i=queue[head++];inQ[i]=0;edges(i,(j,w,p)=>{let v=F[i]+B*w-A*(p-1);if(v>F[j]){F[j]=v;updates++;ok(v<=100000,"potential growth");if(!inQ[j]){inQ[j]=1;queue.push(j)}}});ok(head<2000000,"queue termination")}
 let min=Infinity,max=-Infinity;for(const f of F){min=Math.min(min,f);max=Math.max(max,f)}ok(min===0&&max===80,"range");ok((A-2*B)*(P+1)-A>=max-min,"universal tail");
 let tested=0,zero=0;const adj=Array.from({length:N},()=>[]),zps=new Set();
 // Independent all-wait verification, recompute priority from residue representatives rather than w0 table.
 for(let x=0;x<Q;x+=2)for(let n=0;n<Q;n++){
  const i=idx(x,n);let wsmall=15,small=0;
  for(let t=1;t<=14;t++){for(const p of base){const c=n+t;if(c%2===0?mod(x+1,p)===0&&mod(c,2*p)===0:mod(x-1,p)===0&&mod(c,2*p)===p+2){wsmall=t;small=p;break}}if(small)break}
  const verify=(p,w)=>{const j=idx(x-p+1,n+w),s=F[j]-F[i]-B*w+A*(p-1);ok(s>=0,"finite edge certificate");tested++;if(s===0){zero++;adj[i].push([j,p,w]);zps.add(p)}};
  if(small)verify(small,wsmall);
  for(const p of big){const mx=small?Math.min(2*p,wsmall-1):2*p;for(let w=1;w<=mx;w++)verify(p,w)}
 }
 // Find a zero-slack cycle of the relaxation. It is not asserted to be an actual orbit.
 const color=new Uint8Array(N),parent=new Int32Array(N).fill(-1),pe=new Array(N);let cycle=null;
 for(let i=0;i<N&&!cycle;i++)if(!color[i]){
  const st=[[i,0]];color[i]=1;
  while(st.length&&!cycle){let top=st[st.length-1],v=top[0];if(top[1]>=adj[v].length){color[v]=2;st.pop();continue}const e=adj[v][top[1]++],[j,p,w]=e;if(!color[j]){parent[j]=v;pe[j]=[v,j,p,w];color[j]=1;st.push([j,0])}else if(color[j]===1){cycle=[[v,j,p,w]];let u=v;while(u!==j){ok(parent[u]>=0,"cycle parent");cycle.push(pe[u]);u=parent[u]}cycle.reverse()}}
 }
 ok(cycle,"zero cycle exists");let cw=0,cg=0;for(const [i,j,p,w] of cycle){cw+=w;cg+=p-1;ok(F[j]-F[i]===B*w-A*(p-1),"cycle equality")}ok(B*cw===A*cg,"optimality in relaxation");
 // Exact literal recurrence, with two scales per slab. Validate completed-block telescope, and finite twin witness.
 const Rmax=384000,sp=new Int32Array(2*Rmax+2);for(let p=2;p<sp.length;p++)if(!sp[p]){sp[p]=p;if(p*p<sp.length)for(let j=p*p;j<sp.length;j+=p)if(!sp[j])sp[j]=p}
 function factors(n){const a=[];while(n>1){let p=sp[n];a.push(p);while(n%p===0)n/=p}return a}
 const rows=[];let eventChecks=0,tailChecks=0,strictWitnesses=0;
 for(const R of [12000,48000,192000,384000]){
  const S=Math.sqrt(2*R+1),T=Math.ceil(8*S),K=Math.floor(Math.sqrt(R)/Math.log(R)),H=4*K;
  let roots=0,nonTwin=0,mean=0,meanNon=0,highSlack=0,lowWitness=0,nearLow=0;
  for(let x0=Math.ceil(R/6)*6;x0<=2*R;x0+=6){
   let x=x0,n=3-x0/2,t=0,G=0,W=0,f0=F[idx(x,n)],slack=0,large=0,seenNear=false;
   roots++;
   while(t<T){
    let w=Infinity,p=0;for(const v of [...new Set([...factors(x-1),...factors(x+1)])]){let z=wait(x,n,v);if(z<w||(z===w&&v<p)){w=z;p=v}}
    if(!seenNear&&t+w>H){if(G<=Math.floor(3*H/13)&&H-t>2*K)nearLow++;seenNear=true}
    if(t+w>T)break;
    let y=x-p+1,n1=n+w,s=F[idx(y,n1)]-F[idx(x,n)]-B*w+A*(p-1);
    ok(s>=0,"actual potential");if(p>=94){ok(s>=p-93,"tail slack");tailChecks++;large+=p-93}
    slack+=s;G+=p-1;W+=w;eventChecks++;ok(B*W===A*G+F[idx(y,n1)]-f0-slack,"exact slack telescope");ok(slack>=large,"cumulative tail slack");x=y;n=n1;t+=w;
   }
   const twin=sp[x-1]===x-1&&sp[x+1]===x+1;
   if(!twin){nonTwin++;meanNon+=G/T;ok(A*G>=B*(T-2*S)-(max-min)+large-1e-8,"non-twin gain lower with tail slack")}
   if(A*G<B*(T-2*S)-(max-min)){ok(twin,"strict finite witness");strictWitnesses++;lowWitness++}
   mean+=G/T;highSlack+=large/T;
  }
  rows.push({R,T,K,roots,nonTwin,meanGain:mean/roots,meanNonTwinGain:nonTwin?meanNon/nonTwin:null,meanTailSlack:highSlack/roots,strictWitnesses:lowWitness,nearLow});
 }
 return {states:N,range:[min,max],updates,queuePops:head,finiteEdges:tested,zeroEdges:zero,zeroLabels:[...zps].sort((a,b)=>a-b),relaxedCycle:{length:cycle.length,W:cw,G:cg},eventChecks,tailChecks,strictWitnesses,rows};
}
console.log(JSON.stringify(audit(),null,2));
