// Signed boundary flux moments on shifted primorial grids, actual Negative MIN.
// node research/min_local_negative_boundary_flux_moments_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+5),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const f=x=>x?x*Math.log(x):0,add=(m,k,v)=>m.set(k,(m.get(k)||0)+v),ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 const rows=[];
 for(let R of Rs){
  let T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1,ends=new Map(),checks=0,jumps=0;
  const grids=[6,30,210].map(q=>{
   let start=Math.floor((lo-3*T-6)/q)-2,end=Math.ceil(hi/q)+3,len=end-start+1;
   return {q,start,end,band:[new Float64Array(len),new Float64Array(len),new Float64Array(len)],F:new Float64Array(len),barriers:0,intervals:0};
  });
  const range=(arr,l,r,m)=>{if(l<=r){arr[l]+=m;arr[r+1]-=m}};
  for(let l=lo;l<=hi;l+=W){
   let maxA=Math.min(hi,l+W-6),start=3-maxA/2,n0=3-l/2,end=n0+T,active=new Map(),buckets=new Map();
   const sched=(a,n,v)=>{let e=next(a,n),t=n+e.w;if(t<=end){let b=buckets.get(t)||[];b.push({a,p:e.p,v});buckets.set(t,b)}};
   for(let n=start;n<=end;n++){
    let arrivals=new Map();
    for(let e of buckets.get(n)||[]){
     let v=active.get(e.a);if(v!==e.v)continue;active.delete(e.a);let b=e.a-e.p+1;add(arrivals,b,v.m);jumps++;
     for(let g of grids){
      let L=Math.floor(b/g.q)+1-g.start,U=Math.floor(e.a/g.q)-g.start;
      if(g.q%e.p===0){ck(L>U,"primorial barrier");g.barriers++}
      if(L<=U){ck(L>=0&&U+1<g.F.length,"grid bounds");range(g.band[e.p<=31?0:e.p<=127?1:2],L,U,v.m);g.intervals++;}
     }
    }
    let A=2*(3-n);if(A>=l&&A<=maxA&&A%6===0)add(arrivals,A,1);
    for(let [a,m] of arrivals){m+=active.get(a)?.m||0;let z={m};active.set(a,z);sched(a,n,z)}
   }
   for(let [a,v] of active)add(ends,a,v.m);
  }
  ck([...ends.values()].reduce((s,m)=>s+m,0)===N,"mass");
  const fine=[...ends.values()].reduce((s,m)=>s+f(m),0)/N;
  const output=[];
  for(let g of grids){
   let initial=new Float64Array(g.F.length),final=new Float64Array(g.F.length);
   for(let A=lo;A<=hi;A+=6)initial[Math.floor(A/g.q)-g.start]++;
   for(let [a,m] of ends)final[Math.floor(a/g.q)-g.start]+=m;
   let prefix=0;
   for(let k=0;k<g.F.length;k++){
    ck(prefix===g.band.reduce((s,a)=>s+a[k],0),"event vs endpoint flux");g.F[k]=prefix;
    prefix+=final[k]-initial[k];
    for(let a of g.band)if(k+1<a.length)a[k+1]+=a[k];
    checks++;
   }
   ck(prefix===0,"flux ends");
   for(let k=0;k<g.F.length;k++){ck(g.F[k]===g.band.reduce((s,a)=>s+a[k],0),"band flux");checks++}
   let widths=[g.q,2*g.q,4*g.q,7*g.q,11*g.q].filter(Q=>Q<=2*T);
   for(let Q of widths){
    let K=Q/g.q,M=Q/6,controls=[];
    for(let shift=0;shift<K;shift++){
     let row={shift,entropy:0,energy:0,posEnergy:0,posFrac:0,absFrac:0,fracMoment:0,coarseMoment:0,bandPos:[0,0,0],bandFrac:[0,0,0],mass:0};
     for(let k=mod(shift-g.start,K);k<g.F.length;k+=K){
      let a=0,m=0;for(let j=k;j<Math.min(k+K,g.F.length);j++){a+=initial[j];m+=final[j]}
      let F0=g.F[k],F1=g.F[k+K]||0,d=F1-F0;
      ck(a+d===m,"cell flux derivative");ck(a<=M,"initial cap");checks++;
      let pos=Math.max(0,d);row.mass+=m;row.entropy+=f(m);row.energy+=d*d;row.absFrac+=Math.abs(d)**1.5;row.posEnergy+=pos*pos;row.posFrac+=pos**1.5;row.fracMoment+=m**1.5;row.coarseMoment+=m*m;
      for(let i=0;i<3;i++){let e=Math.max(0,(g.band[i][k+K]||0)-g.band[i][k]);row.bandPos[i]+=e*e;row.bandFrac[i]+=e**1.5;}
     }
     // If the first grid boundary lies beyond array start, all omitted cells are empty for these widths?
     // Handle padded left boundary explicitly, using its zero exterior flux.
     let first=mod(shift-g.start,K);
     if(first){let a=0,m=0;for(let j=0;j<first;j++){a+=initial[j];m+=final[j]}let d=g.F[first],pos=Math.max(0,d);
      ck(a+d===m&&a<=M,"left partial cell");checks++;row.mass+=m;row.entropy+=f(m);row.energy+=d*d;row.absFrac+=Math.abs(d)**1.5;row.posEnergy+=pos*pos;row.posFrac+=pos**1.5;row.fracMoment+=m**1.5;row.coarseMoment+=m*m;for(let i=0;i<3;i++){let e=g.band[i][first];row.bandPos[i]+=e*e;row.bandFrac[i]+=e**1.5}
     }
     ck(row.mass===N,"coarse mass");row.entropy/=N;
     row.bound2=Math.log(M)+2*Math.log1p(Math.sqrt(row.posEnergy/(N*M)));
     row.bound15=Math.log(M)+3*Math.log1p((row.posFrac/(N*Math.sqrt(M)))**(2/3));
     row.sharp2=Math.log(M)+Math.log(1+row.energy/(N*M)+4*M/N);
     row.sharp15=Math.log(M)+2*Math.log(1+row.absFrac/(N*Math.sqrt(M))+3*M/N);
     row.sharpPos2=Math.log(M)+Math.log(2+row.posEnergy/(N*M)+4*M/N);
     row.sharpPos15=Math.log(M)+2*Math.log(2+row.posFrac/(N*Math.sqrt(M))+3*M/N);
     row.actualRenyi2=Math.log(row.coarseMoment/N);
     row.actualRenyi15=2*Math.log(row.fracMoment/N);
     ck(fine<=row.entropy+1e-8&&row.entropy<=row.actualRenyi2+1e-8&&row.entropy<=row.actualRenyi15+1e-8&&row.actualRenyi2<=row.bound2+1e-8&&row.actualRenyi15<=row.bound15+1e-8,"moment bounds");
     ck(row.actualRenyi2<=Math.min(row.sharp2,row.sharpPos2)+1e-8&&row.actualRenyi15<=Math.min(row.sharp15,row.sharpPos15)+1e-8,"Taylor bounds");
     ck(Math.sqrt(row.posEnergy)<=row.bandPos.reduce((s,x)=>s+Math.sqrt(x),0)+1e-6,"band Minkowski");
     controls.push(row);
    }
    const avg=controls.reduce((s,c)=>s+c.posEnergy,0)/K,avgFrac=controls.reduce((s,c)=>s+c.posFrac,0)/K;
    let best=controls.reduce((a,b)=>a.bound2<b.bound2?a:b),best15=controls.reduce((a,b)=>a.bound15<b.bound15?a:b);
    let avgBound2=Math.log(M)+2*Math.log1p(Math.sqrt(avg/(N*M))),avgBound15=Math.log(M)+3*Math.log1p((avgFrac/(N*Math.sqrt(M)))**(2/3));
    ck(best.bound2<=avgBound2+1e-8&&best15.bound15<=avgBound15+1e-8,"shift averaging");
    output.push({q:g.q,Q,K,M,bestShift:best.shift,coarseEntropy:best.entropy,ratio2:best.posEnergy/(N*M),ratio15:best15.posFrac/(N*Math.sqrt(M)),bestBound2:best.bound2,bestBound15:best15.bound15,avgBound2,avgBound15,actualRenyi2:best.actualRenyi2,actualRenyi15:best.actualRenyi15,sharp2:best.sharp2,sharp15:best15.sharp15,sharpPos2:best.sharpPos2,sharpPos15:best15.sharpPos15,absEnergy:best.energy/(N*M),absFrac:best15.absFrac/(N*Math.sqrt(M))});
   }
  }
  rows.push({R,T,N,fine,jumps,checks,barriers:grids.reduce((s,g)=>s+g.barriers,0),intervals:grids.reduce((s,g)=>s+g.intervals,0),output});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000,1000000,2000000]),null,2));
