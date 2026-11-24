// Exact directed threshold ledger, elapsed clock weights and local peak localization.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=x=>{if(!x)throw Error("assertion")},gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return a};
 function hit(t,C,K){let u=K+1,q=0;for(let s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let m=2*p,r=s===-1?0:p+2,h=t+1+((r-t-1)%m+m)%m;if(h<u||(h===u&&p<q)){u=h;q=p}while(v%p===0)v/=p}}return [u,q]}
 const L=210,lambda=Math.sqrt(Math.log(B)),thresholds=[1,8,16,32,64,128,256,512,1024,2048].filter(u=>u<=B+315);
 const data=[0,1].map(mode=>({mode,total:0,initial:0,forest:0,last:0,cycle:0,originSurplus:0,near:[2,8,32,B/lambda].map(f=>({factor:f,peak:0,near:0,peakCount:0,nearCount:0})),layers:thresholds.map(u=>({u,beta:0,D:0,sinkless:0,tailBeta:0,tailD:0}))}));
 let R=0,E=0,events=0,literal=0;
 for(let M=X+1;M<2*X;M+=2){
  let t=M+2,C=2*M-2,K=Math.floor((7*M-1)/4),a=[],initial=[0,0],lowGain=0;
  for(;;){let [u,p]=hit(t,C,K);if(X<=1024){let v=K+1,q=0;for(let j=t+1;j<=K;j++){let g=gcd(j%2?j-2:j,C+(j%2?1:-1));if(g>1&&spf[g]<=B){v=j;q=spf[g];break}}ck(u===v&&p===q);literal++}if(!p)break;
   let r=Math.min(spf[C-1],spf[C+1]),dt=u-t;ck(dt<=2*r);R+=r;E+=dt;events++;
   if(p<=7){lowGain+=p-1;if(a.length){a.at(-1).w[0]+=r;a.at(-1).w[1]+=dt}else{initial[0]+=r;initial[1]+=dt}}else{ck(lowGain<L);lowGain=0;a.push({p,C,w:[r,dt]})}C+=p-1;t=u;ck(C<=2*t)
  }ck(lowGain<L);
  let labels=[...new Set(a.map(e=>e.p))],ids=a.map(e=>labels.indexOf(e.p)),groups=labels.map(()=>[]);for(let i=0;i<a.length;i++)groups[ids[i]].push(i);
  for(let s of data){
   const m=s.mode,w=a.map(e=>e.w[m]),total=initial[m]+w.reduce((x,y)=>x+y,0);s.total+=total;s.initial+=initial[m];if(!a.length)continue;
   s.last+=w.at(-1);let edges=[];for(let i=0;i+1<a.length;i++)edges.push([ids[i],ids[i+1],w[i]]);
   edges.sort((a,b)=>b[2]-a[2]);let par=labels.map((_,i)=>i),root=i=>{while(par[i]!==i)i=par[i];return i},rejected=[];
   for(let [u,v,z] of edges){if(root(u)===root(v)){s.cycle+=z;rejected.push(z)}else{par[root(v)]=root(u);s.forest+=z}}
   let outMax=Array(labels.length).fill(0),originRejected=[];for(let [u,v,z] of edges){if(!outMax[u])outMax[u]=z;else{originRejected.push(z);s.originSurplus+=z}}
   for(let layer of s.layers){
    let beta=rejected.filter(z=>z>=layer.u).length,D=originRejected.filter(z=>z>=layer.u).length;
    let pa=labels.map((_,i)=>i),rt=i=>{while(pa[i]!==i)i=pa[i];return i},out=Array(labels.length).fill(0),active=Array(labels.length).fill(false),n=0;
    for(let [u,v,z] of edges)if(z>=layer.u){pa[rt(v)]=rt(u);out[u]++;active[u]=active[v]=true;n++}
    let comps=new Map();for(let j=0;j<labels.length;j++)if(active[j]){let k=rt(j);comps.set(k,(comps.get(k)||0)+ +(out[j]===0))}
    let sinkless=[...comps.values()].filter(z=>!z).length,sinks=[...comps.values()].reduce((a,b)=>a+b,0);
    ck(beta===n-active.filter(Boolean).length+comps.size);ck(beta-D===comps.size-sinks&&beta<=D+sinkless);
    layer.beta+=beta;layer.D+=D;layer.sinkless+=sinkless;layer.tailBeta+=rejected.reduce((a,z)=>a+Math.max(0,z-layer.u+1),0);layer.tailD+=originRejected.reduce((a,z)=>a+Math.max(0,z-layer.u+1),0)
   }
   for(let g of groups){
    const p=a[g[0]].p;
    for(let n of s.near){let T=Math.ceil((p+315)*n.factor),peaks=[];
     for(let i of g){let better=g.some(j=>j!==i&&Math.abs(a[j].C-a[i].C)<=T&&(w[j]>w[i]||(w[j]===w[i]&&j<i)));if(better){n.near+=w[i];n.nearCount++}else{n.peak+=w[i];n.peakCount++;peaks.push(i)}}
     for(let j=1;j<peaks.length;j++)ck(a[peaks[j]].C-a[peaks[j-1]].C>T)
    }
   }
  }
 }
 ck(data[0].total===R&&data[1].total===E);for(let s of data){ck(s.total===s.initial+s.forest+s.last+s.cycle);for(let n of s.near)ck(n.near+n.peak+s.initial===s.total);ck(s.layers[0].tailBeta===s.cycle&&s.layers[0].tailD===s.originSurplus)}
 return {X,B,R,E,events,literal,data};
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
