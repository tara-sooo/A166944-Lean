// Per-label deletion comparison over complete seed periods.
function audit(){
 const ck=(a,m)=>{if(!a)throw Error(m)},mod=(x,m)=>(x%m+m)%m;
 function next(u,v,A){let p=Infinity,w=Infinity;for(let r of A){let s=mod(u,r)===1?1:mod(u,r)===r-1?-1:0;if(!s)continue;let z=mod((s===1?0:r+2)-v,2*r)||2*r;if(z<w||z===w&&r<p){p=r;w=z}}return {p,w}}
 function walk(X,A){let u=X,v=X/2+3,used=new Set(),steps=0;for(;;){let z=next(u,v,A);if(!isFinite(z.p))return {u,v,used,steps,G:u-X};used.add(z.p);u+=z.p-1;v+=z.w;steps++}}
 const all=[3,5,7,11,13,17];let rows=[];
 for(let y of [5,7,11,13,17]){
  let A=all.filter(p=>p<=y),P=4*A.reduce((a,b)=>a*b,1),N=P/6,base=P,full=[],s={y,P,N,fullSteps:0,sumG:0,sumG2:0,distinctGainSum:0,usageLower:0,gainLower:0,gain2Lower:0,deleteControls:0,deletionSteps:0,rows:[]};
  for(let X=base;X<base+P;X+=6){let a=walk(X,A);full.push(a);s.fullSteps+=a.steps;s.sumG+=a.G;s.sumG2+=a.G*a.G;for(let p of a.used)s.distinctGainSum+=p-1;}
  ck(full.length===N,"period");
  for(let p of A.filter(p=>p!==3)){
   let B=A.filter(q=>q!==p),period=P/p,cache=[],used=0,forced=0,preempt=0;
   for(let X=base;X<base+period;X+=6){let a=walk(X,B);cache.push(a);s.deletionSteps+=a.steps}
   for(let i=0;i<N;i++){
    let k=Math.floor(i/cache.length),a=cache[i%cache.length],u=a.u+period*k,eligible=mod(u,p)===1||mod(u,p)===p-1;
    if(full[i].used.has(p))used++;
    if(eligible){forced++;ck(full[i].used.has(p),"forced use")}
    else if(full[i].used.has(p))preempt++;
    s.deleteControls++;
   }
   ck(forced===2*N/p&&used===forced+preempt,"exact forced count");
   s.usageLower+=2/p;s.gainLower+=2*(p-1)/p;s.gain2Lower+=2*(p-1)**2/p;
   s.rows.push({p,forced,used,other:preempt})
  }
  ck(s.sumG>=s.distinctGainSum&&s.distinctGainSum+1e-6>=N*s.gainLower&&s.sumG2+1e-6>=N*s.gain2Lower,"moment lower");
  s.meanG=s.sumG/N;s.meanG2=s.sumG2/N;rows.push(s)
 }
 return rows;
}
console.log(JSON.stringify(audit(),null,2));
