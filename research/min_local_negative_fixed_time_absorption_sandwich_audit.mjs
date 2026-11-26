// Fixed-time gain vs restricted absorption, pathwise sandwich and coherent formal sampling.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(m)},mod=(a,p)=>(a%p+p)%p,MAX=65536,Z=2*MAX+20,spf=new Uint32Array(Z+1),pr=[];
 for(let p=2;p*p<=Z;p++)if(!spf[p])for(let n=p*p;n<=Z;n+=p)spf[n]=p;
 for(let p=3;p<=Z;p+=2)if(!spf[p])pr.push(p);
 let seed=0x9b07d4af;function u32(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0}
 function uniform(n){let M=Math.floor(4294967296/n)*n,x;do{x=u32()}while(x>=M);return x%n}
 const V=y=>pr.filter(p=>p>=5&&p<=y).reduce((s,p)=>s*(1-2/p),1);
 let z={environments:0,tickChecks:0,restrictedTicks:0,physicalTicks:0,sandwichChecks:0,absorptionComparisons:0,stablePathChecks:0,roughnessChecks:0,physicalRoots:0,physicalSandwichChecks:0,formal:[],physical:[]};
 function tick(res,par,t,G,cut){let b=3+t-G/2,np=mod(3+t-par,2),f=Math.abs(np?2*b-5:2*b+1);
  while(f>1){let p=spf[f]||f;if(p<=cut&&mod(res[p]-G+(np?-1:1),p)===0)return p-1;while(f%p===0)f/=p}return 0
 }
 function rough(res,G,cut){for(let p of pr){if(p>cut)break;if(mod(res[p]-G-1,p)===0||mod(res[p]-G+1,p)===0)return false}return true}
 function restricted(res,par,cut,L,physical=false){
  let G=0,t=0,maxT=Math.floor(9*L/4+8);
  if(rough(res,G,cut))return {ok:true,G,t};
  for(t=1;t<=maxT;t++){let g=tick(res,par,t,G,cut);if(physical)z.physicalTicks++;else z.restrictedTicks++;G+=g;if(G>L)return {ok:false,G,t};
   if(g&&rough(res,G,cut))return {ok:true,G,t};}
  return {ok:false,G,t}
 }
 function full(res,par,T,physical=false){let G=0,W=0;for(let t=1;t<=T;t++){let g=tick(res,par,t,G,2*T+7);if(g){G+=g;W=t}if(physical)z.physicalTicks++;else z.tickChecks++;ck(G<=2*t+6,"gain cap")}
  return {G,W}
 }
 const caps=T=>[Math.floor(T/32),Math.floor(T/16),Math.floor(T/Math.max(16,Math.log(T)**2))].filter((v,i,a)=>a.indexOf(v)===i&&v>=6);
 function check(res,par,T,gs,stats,physical=false){
  const a=full(res,par,T,physical);
  for(let [i,L] of gs.entries()){
   let ym=Math.floor((T-9*L/4-9)/2),yp=2*T+7,lo=restricted(res,par,yp,L,physical),hi=restricted(res,par,ym,L,physical);
   ck(ym>=2*Math.floor(9*L/4+8)+7,"cutoff locality");ck(9*L/4+8<=T,"arrival time");
   let mid=a.G<=L;
   ck(!lo.ok||mid,"lower sandwich");ck(!mid||hi.ok,"upper sandwich");
   if(mid){ck(a.G===hi.G&&a.W===hi.t,"same absorption");ck(rough(res,a.G,ym),"rough last idle");z.roughnessChecks++}
   if(lo.ok){ck(a.G===lo.G&&a.W===lo.t,"same full prefix");z.stablePathChecks++}
   if(physical)z.physicalSandwichChecks++;else z.sandwichChecks++;
   let s=stats[i];s.lo+=+lo.ok;s.mid+=+mid;s.hi+=+hi.ok;s.n++;
  }
  return a.G
 }
 for(let [T,n] of [[256,2048],[1024,1536],[4096,1024],[16384,384],[65536,96]]){
  let gs=caps(T),stats=gs.map(L=>({L,ym:Math.floor((T-9*L/4-9)/2),yp:2*T+7,n:0,lo:0,mid:0,hi:0})),sum=0,sq=0;
  for(let i=0;i<n;i++){
   let res=new Int32Array(2*T+8),par=uniform(2);
   for(let p of pr){if(p>2*T+7)break;res[p]=p===3?0:uniform(p)}
   let g=check(res,par,T,gs,stats);sum+=g;sq+=g*g;z.environments++;
  }
  z.formal.push({T,n,meanGain:sum/n,meanRatio:sum/n/T,meanSquare:sq/n,stats:stats.map(s=>({...s,loRatio:s.lo/n,midRatio:s.mid/n,hiRatio:s.hi/n,Vratio:V(s.ym)/V(s.yp)}))});
 }
 // Independent physical integer checks, sampled canonical roots.
 for(let R of [12000,48000,192000,1000000]){
  let T=Math.ceil(8*Math.sqrt(2*R+1)),gs=caps(T),stats=gs.map(L=>({L,ym:Math.floor((T-9*L/4-9)/2),yp:2*T+7,n:0,lo:0,mid:0,hi:0})),sum=0,n=0;
  for(let A=6*Math.ceil(R/6);A<=2*R;A+=6*97){
   let res=new Int32Array(2*T+8),par=mod(A/2,2);for(let p of pr){if(p>2*T+7)break;res[p]=mod(A,p)}
   let g=check(res,par,T,gs,stats,true);sum+=g;n++;z.physicalRoots++;
  }
  z.physical.push({R,T,n,meanGain:sum/n,meanRatio:sum/n/T,stats});
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
