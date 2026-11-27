// Coarse inverse code: compress adjacent-cell exits and encode nonadjacent source-cell ranks.
// node research/min_local_negative_coarse_prefix_code_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+5),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},add=(m,k,v=1)=>m.set(k,(m.get(k)||0)+v),f=x=>x?x*Math.log(x):0;
 let rows=[];
 for(let R of Rs){
  const S=Math.sqrt(2*R+1),T=Math.ceil(S),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1,B=2*T+6,L=Math.log(S);
  const q=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1),weight=a=>{let t=Math.log(Math.min(S,q(a))),d=L-t;return Math.exp(-2*Math.log(L/t)-Math.log1p(d)-2*Math.log1p(Math.log1p(d)))};
  let stats=[6,30,210].map(Q=>({Q,M:Q/6,candidates:new Map(),controls:[[.5,.75],[.25,.75],[.125,.75],[.25,.5],[.25,.9]].map(([stop,adj])=>({stop,adj,cellMass:new Map(),posMass:new Map(),rootBest:0,all:0,meanVisited:0,checks:0}))}));
  function candidates(s,j){
   let c=s.candidates.get(j);if(c)return c;
   let arr=new Set(),Q=s.Q;
   for(let b=Math.max(4,j*Q);b<(j+1)*Q&&b<=hi;b+=2)
    for(let p of [...fs(b),...fs(b-2)])if(p>Q&&p-1<=B){let a=b+p-1,i=Math.floor(a/Q);if(a<=hi&&i>j+1)arr.add(i);}
   c=[...arr].sort((a,b)=>a-b);s.candidates.set(j,c);return c;
  }
  let checks=0,events=0;
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,end=n+T,path=[A];
   for(;;){let e=next(a,n),fire=n+e.w;if(fire>end)break;a-=e.p-1;n=fire;path.push(a);events++}
   for(let s of stats){
    let cell=x=>Math.floor(x/s.Q),groups=[];
    for(let x of path){let j=cell(x),g=groups.at(-1);if(!g||g.j!==j)groups.push({j,best:x});else if(q(x)>q(g.best))g.best=x;}
    for(let c of s.controls){
     let k=c.stop/s.M,best=0;
     for(let i=0;i<groups.length;i++){
      let {j,best:x}=groups[i];
      if(i){let prev=groups[i-1].j,can=candidates(s,j),a=can.length?c.adj:1;
       if(prev===j+1)k*=(1-c.stop)*a;
       else {ck(can.includes(prev),"source");k*=(1-c.stop)*(1-a)/can.length;}
      }
      add(c.cellMass,j,k);add(c.posMass,x,k);let w=k*weight(x);c.all+=w;best=Math.max(best,w);c.meanVisited++;checks++;
     }
     c.rootBest+=best;
    }
   }
  }
  let cap=0;for(let a=2*Math.ceil((lo-B)/2);a<=hi;a+=2)if(q(a)<=S)cap+=weight(a);
  let output=[];
  for(let s of stats)for(let c of s.controls){
   let maxMass=0,support=0,cert=0;
   for(let [j,k] of c.cellMass){ck(k<=1+1e-8,"cell capacity");maxMass=Math.max(k,maxMass);checks++}
   for(let [x,k] of c.posMass){ck(k<=1+1e-8,"position capacity");support+=weight(x);cert+=k*weight(x);checks++}
   ck(Math.abs(cert-c.all)<=1e-7*N&&c.rootBest<=cert+1e-8&&cert<=support+1e-8,"certificate");
   output.push({Q:s.Q,stop:c.stop,adj:c.adj,meanVisited:c.meanVisited/N,maxMass,rootBest:c.rootBest,all:cert,support,ratio:cert/cap});
  }
  rows.push({R,N,events,checks,cap,output});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000,1000000,2000000]),null,2));
