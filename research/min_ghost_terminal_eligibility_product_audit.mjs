// Full rectangle terminal-eligibility product and lifetime comparison.
function terminalAudit(Z){
 const ps=[];for(let p=3;p<Z;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const L=2*ps.reduce((a,b)=>a*b,1),states=L*L/2,mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)};
 if(L>2310)throw Error("exact limit");
 const lower=[5,7,11].filter(P=>P<Z).map(P=>{
  let k=ps.findIndex(p=>p>=P),M=2*ps.slice(0,k).reduce((a,b)=>a*b,1),extra=ps.slice(k);
  let prod=extra.reduce((x,p)=>x*(1-2/p),1),sum=extra.reduce((x,p)=>x+1/p**2,0);
  return {P,k,M,extra,prod,sum,cache:[],rows:[4,8,16,32,64].map(v=>({v,low:0,upper:0,joint:0,div:0,disagree:0,lateBlock:0}))}
 });
 function trace(C,t,k){let e=0,g=0,es=[];for(;;){let w=Infinity,p0=0;for(let i=0;i<k;i++){let p=ps[i],cc=mod(C+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<p0)){w=f;p0=p}}if(!p0)return {e,g,es};e+=w;g+=p0-1;es.push([e,p0]);if(g>=L)throw Error("barrier");}}
 for(let a of lower)for(let C=0;C<a.M;C+=2)for(let t=0;t<a.M;t++)a.cache[C/2*a.M+t]=trace(C,t,a.k);
 for(let C=0;C<L;C+=2)for(let t=0;t<L;t++){
  let b=trace(C,t,ps.length);
  for(let a of lower){
   let low=a.cache[(C%a.M)/2*a.M+t%a.M],quiet=a.extra.every(p=>![1,p-1].includes(mod(C+low.g,p))),j=0;
   while(j<low.es.length&&j<b.es.length&&low.es[j][0]===b.es[j][0]&&low.es[j][1]===b.es[j][1])j++;
   let first=Math.min(low.es[j]?.[0]??Infinity,b.es[j]?.[0]??Infinity);
   for(let r of a.rows){let A=low.e<=r.v,B=b.e<=r.v,E=A&&quiet,D=first<=r.v;
    ck(D||B===E,"terminal equivalence off divergence");r.low+=A;r.upper+=B;r.joint+=E;r.div+=D;r.disagree+=B!==E;r.lateBlock+=A&&!quiet&&!D;
   }
  }
 }
 for(let a of lower){delete a.cache;for(let r of a.rows){ck(Math.abs(r.joint-r.low*a.prod)<1e-5,"exact independent eligibility");ck(Math.abs(r.upper-r.joint)<=r.disagree&&r.disagree<=r.div,"coupling");ck(r.div/states<=r.v*a.sum+1e-10,"union");r.upperProb=r.upper/states;r.lowerProb=r.low/states;r.productPrediction=r.joint/states;r.errorBound=Math.min(1,r.v*a.sum)}}
 return {Z,L,states,lower}
}
for(const z of process.argv.slice(2).map(Number))console.log(JSON.stringify(terminalAudit(z)));
