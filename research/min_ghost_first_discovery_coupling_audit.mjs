// Exact conditional bad-residue product and first-discovery count audit.
function discoveryAudit(Y,Z){
 const ps=[];for(let p=3;p<Y;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const low=ps.filter(p=>p<Z),hi=ps.filter(p=>p>=Z),L=2*ps.reduce((a,p)=>a*p,1),l=2*low.reduce((a,p)=>a*p,1);
 if(L>2310||!hi.length)throw Error("limit");
 const mod=(a,b)=>(a%b+b)%b,ck=(x,m)=>{if(!x)throw Error(m)};
 function walk(C,t,alphabet){
  let G=0,E=0,D=0,events=[];
  for(;;){let w=Infinity,p=0;
   for(let q of alphabet){let c=mod(C+G,q);if(c!==1&&c!==q-1)continue;let ph=c===1?0:q+2,f=1+mod(ph-t-E-1,2*q);if(f<w||(f===w&&q<p)){w=f;p=q}}
   if(!p)break;
   events.push({p,G,E,w});E+=w;G+=p-1;D=Math.max(D,2*E-G);
   ck(events.length<1000,"termination");
  }return {G,E,D,events};
 }
 const Ts=[4,8,16,32,64,128],base=new Map(),out=Ts.map(T=>({T,matchNumer:0,matchActual:0,fullTail:0,lowTail:0,baseShortDiff:0,unionBudget:0,firsts:new Array(hi.length+1).fill(0),factorialMoments:new Array(hi.length+1).fill(0)}));
 let fullMatchNumer=0,fullMatchActual=0,checks=0,meanBad=0;
 const factor=hi.reduce((a,p)=>a*p*p,1),states=L*L/2;
 function bad(C,t,lowPath,q,T,terminal){
  const b=new Uint8Array(q*q);let count=0;
  function at(G,e){
   const even=mod(t+e,2)===0,c=mod((even?1:-1)-G,q),v=mod((even?0:2)-e,q),k=c*q+v;
   if(!b[k]){b[k]=1;count++}
  }
  for(let ev of lowPath.events){
   for(let e=ev.E+1;e<ev.E+ev.w&&e<=T;e++)at(ev.G,e);
   if(ev.E+ev.w>T)break;
  }
  if(terminal){
   for(let sign of [-1,1])for(let v=0;v<q;v++){let k=mod(sign-lowPath.G,q)*q+v;if(!b[k]){b[k]=1;count++}}
  }else if(lowPath.E<T){
   for(let e=lowPath.E+1;e<=T;e++)at(lowPath.G,e)
  }
  return count
 }
 for(let C=0;C<l;C+=2)for(let t=0;t<l;t++){
  let p=walk(C,t,low),full=1,bb=hi.map(q=>bad(C,t,p,q,Infinity,true));for(let i=0;i<hi.length;i++){ck(bb[i]<=Math.min(hi[i]**2,p.E+2*hi[i]),"bad complete");full*=hi[i]**2-bb[i];}fullMatchNumer+=full;
  let vals=Ts.map((T,j)=>{let x=1,bs=hi.map(q=>bad(C,t,p,q,T,false));for(let i=0;i<hi.length;i++){ck(bs[i]<=Math.min(T,hi[i]**2),"time slots");x*=hi[i]**2-bs[i];}out[j].matchNumer+=x;
   if(p.E>T)out[j].lowTail+=factor;
   else out[j].unionBudget+=factor*hi.reduce((s,q,i)=>s+bb[i]/q**2,0);
   return x;
  });
  base.set(C*l+t,p);meanBad+=bb.reduce((s,v,i)=>s+v/hi[i]**2,0)
 }
 function choose(n,k){let a=1;for(let j=1;j<=k;j++)a=a*(n-j+1)/j;return a}
 for(let C=0;C<L;C+=2)for(let t=0;t<L;t++){
  let p=walk(C,t,ps),b=base.get((C%l)*l+t%l),first=p.events.find(e=>e.p>=Z),match=!first;
  if(match){ck(p.E===b.E&&p.G===b.G&&p.D===b.D,"complete agreement");fullMatchActual++;}
  for(let j=0;j<Ts.length;j++){
   let z=out[j],T=z.T,k=new Set(p.events.filter(e=>e.p>=Z&&e.E+e.w<=T).map(e=>e.p)).size;
   if(!k)z.matchActual++;
   if(p.E>T){z.fullTail++;if(b.E<=T){ck(!!first&&first.E+first.w<=T+2*Y,"first disruption");z.baseShortDiff++;}}
   for(let s=1;s<=hi.length;s++){if(k>=s)z.firsts[s]++;z.factorialMoments[s]+=choose(k,s)}
  }
  checks++;
 }
 ck(checks===states&&fullMatchNumer===fullMatchActual,"full product");
 let W=hi.reduce((s,q)=>s+1/q**2,0);
 for(let z of out){
  ck(z.matchActual===z.matchNumer&&z.fullTail<=z.lowTail+z.baseShortDiff&&z.baseShortDiff<=z.unionBudget+1e-7,"time product and coupling");
  z.bounds=z.firsts.map((_,k)=>k?Math.min(1,choose(z.T,k)*W**k):1);
  let elementary=[1,...hi.map(()=>0)];for(let q of hi)for(let k=hi.length;k>=1;k--)elementary[k]+=elementary[k-1]/q**2;
  z.sharpBounds=elementary.map((e,k)=>Math.min(1,choose(z.T,k)*e*Array.from({length:k},(_,j)=>j+1).reduce((a,b)=>a*b,1)));
  for(let k=1;k<=hi.length;k++){ck(z.firsts[k]/states<=z.sharpBounds[k]+1e-12,"discovery bound");ck(z.factorialMoments[k]/states<=choose(z.T,k)*elementary[k]*Array.from({length:k},(_,j)=>j+1).reduce((a,b)=>a*b,1)+1e-12,"moment bound")}
  z.matchProb=z.matchActual/states;z.fullTailProb=z.fullTail/states;z.lowTailProb=z.lowTail/states;z.firstProb=z.firsts.map(x=>x/states);
 }
 return {Y,Z,L,l,hi,states,baseStates:l*l/2,W,fullMatchNumer,fullMatchActual,fullMatchProb:fullMatchActual/states,meanBad:meanBad/(l*l/2),checks,out}
}
for(const a of process.argv.slice(2)){const [Y,Z]=a.split(':').map(Number);console.log(JSON.stringify(discoveryAudit(Y,Z)));}
