// Short-slab distinct-label merger budget, all actual original tags.
// Run: node research/min_clock_slab_merge_ledger.mjs 1024 4096 16384 65536 262144
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,Q=Math.ceil(B/Math.sqrt(Math.log(B)));
 const check=(x,m)=>{if(!x)throw Error(m)};
 check(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(7*X+4);
 for(let p=2;p<spf.length;p++)if(!spf[p]){
  spf[p]=p;if(p*p<spf.length)for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 }
 function hit(t,C,K){
  let T=K+1,P=0;
  for(const side of [-1,1]){
   let v=C+side;while(v>1){const p=spf[v];if(p>B)break;
    const m=2*p,res=side===-1?0:p+2,u=t+1+(res-(t+1)%m+m)%m;
    if(p>2&&(u<T||(u===T&&u<=K&&p<P))){T=u;P=p;}
    while(v%p===0)v/=p;
   }
  }return [T,P];
 }
 const V=new Map(),costs=new Float64Array(N),key=(t,C)=>t*(7*X+4)+C;
 function get(t,C){
  const k=key(t,C);let v=V.get(k);
  if(!v){v={t,C,rep:0,weight:0,root:0,edges:new Map()};V.set(k,v)}
  return v;
 }
 function visit(v,M,weight){check(M>=v.rep,'source order');v.rep=M;v.weight=weight;}
 let R=0,events=0,finished=0;
 for(let M=X+1;M<2*X;M+=2){
  const s=M+2,C0=2*M-2,K=Math.floor((7*M-1)/4);
  let t=s,C=C0,cost=0,v=get(t,C);
  v.root=M;visit(v,M,0);
  while(t<s+H){
   const [u,p]=hit(t,C,K);
   if(!p){check(spf[C-1]===C-1&&spf[C+1]===C+1,'terminal twin');finished++;break;}
   const r=Math.min(spf[C-1],spf[C+1]),dur=Math.max(0,Math.min(u-s,H)-Math.max(t-s,a));
   check(u-t<=2*r&&C<=2*t,'wait and invariant');
   visit(v,M,dur/2);cost+=dur/2;events++;
   const w=get(u,C+p-1);
   w.edges.set(key(t,C),{M,p,cost,enter:dur/2});
   visit(w,M,0);t=u;C+=p-1;v=w;
  }
  check(cost<=B,'per-source slab cost');costs[(M-X-1)/2]=cost;R+=cost;
 }
 let rep=0,same=0,sameCost=0,mixed=0,mixedCost=0,root=0,rootCost=0;
 const out=[Q,11].map(Q=>({Q,pairs:0,resetPairs:0,nonresetPairs:0,vertices:0,demotions:0,cost:0,rootDemotions:0,rootCost:0}));
 const demoted=new Set();
 const cutoffs=[Q,Math.ceil(Math.log(B)**2),11].map(y=>({y,all:0,groupWinner:0,sameLoser:0,groupEvents:0}));
 function suffix(e){const x=costs[(e.M-X-1)/2]-e.cost;check(x>=0,'suffix cost');return x;}
 function demote(e){check(!demoted.has(e.M),'single demotion');demoted.add(e.M);return suffix(e);}
 for(const v of V.values()){
  rep+=v.weight;
  const groups=new Map();
  for(const e of v.edges.values()){
   if(!groups.has(e.p))groups.set(e.p,[]);
   groups.get(e.p).push(e);
  }
  const winners=[];
  for(const g of groups.values()){
   g.sort((b,c)=>c.M-b.M);winners.push(g[0]);
   for(const o of cutoffs)if(g[0].p>=o.y){o.groupEvents++;o.groupWinner+=g[0].enter;for(const e of g)o.all+=e.enter;for(const e of g.slice(1))o.sameLoser+=e.enter;}
   for(const e of g.slice(1)){same++;sameCost+=demote(e);}
  }
  winners.sort((b,c)=>c.M-b.M);
  const eps=v.t%2?6:0,def=2*v.t-v.C-eps;
  check(def>=-6&&def<=2*(H+2*B)+6,'short deficit strip');
  for(const e of winners){
   check((v.t-(v.t%2?2:0))%e.p===0&&(v.C+(v.t%2?2:0))%e.p===0,'incoming arithmetic');
  }
  for(const o of out){
   let n=0;
   for(let i=0;i<winners.length;i++)for(let j=0;j<i;j++){
    const p=winners[i].p,q=winners[j].p;
    check(def%(2*p*q)===0,'pair divisor of deficit');
    if(Math.max(p,q)>=o.Q){
     n++;o.pairs++;if(def===0)o.resetPairs++;else{o.nonresetPairs++;check(2*p*q<=2*(H+2*B)+6,'nonreset product bound');}
    }
   }
   if(v.root&&winners.some(e=>e.p>=o.Q)){o.rootDemotions++;o.rootCost+=suffix(winners[0]);}
   if(n){
    o.vertices++;check(winners.length-1<=n,'large-label pair domination');
    o.demotions+=winners.length-1;
    for(const e of winners.slice(1))o.cost+=suffix(e);
   }
  }
  for(const e of winners.slice(1)){mixed++;mixedCost+=demote(e);}
  if(v.root&&winners.length){check(v.root>winners[0].M,'root largest');root++;rootCost+=demote(winners[0]);}
  check(v.rep===(v.root||winners[0]?.M),'representative order');
 }
 check(rep+sameCost+mixedCost+rootCost===R,'exact slab ledger');
 for(const o of out)check(o.demotions<=o.pairs&&o.cost<=B*o.demotions&&o.rootCost<=B*o.rootDemotions,'large mixed bound');
 for(const o of cutoffs)check(o.all===o.groupWinner+o.sameLoser,'representative entering cost identity');
 return {X,B,Q,events,vertices:V.size,finished,R,rep,same,sameCost,mixed,mixedCost,root,rootCost,out,cutoffs};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536,262144])console.log(JSON.stringify(audit(X)));
