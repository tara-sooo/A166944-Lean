// Fresh-prime renewal entropy cost: exact mixing, geometric displacement bound.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p;
 const primes=[3,5,7,11,13,17,19,23,29,31,37],out={oldRoots:0,oldExitChecks:0,activeNodes:0,resetExcursions:0,repeatedFreshEdges:0,chainChecks:0,energyChecks:0,entropyChecks:0,directLiftChecks:0,fullPeriodRoots:0,rows:[]};
 function cut(a,h,H,P){let d=0,n=h-a/2,k=0;while(true){let p=0,w=Infinity;
  for(let q of P)for(let e of [-1,1])if(mod(a-e,q)===0){let t=mod((e===-1?0:q+2)-n,2*q)||2*q;if(t<w||t===w&&q<p){p=q;w=t}}
  if(h+w>=H)return {d,k,a};
  a-=p-1;d+=p-1;n+=w;h+=w-(p-1)/2;k++;ck(h>=0,"height");
 }}
 for(let p of [11,13,17,19]){
  let b=(p-1)/2,P=primes.filter(q=>q<p),Q=P.reduce((x,y)=>x*y,1),L=4*Q,M=L/6,NP=[...P,p],L2=L*p,u=new Int32Array(L/2),oldE=0,oldFirstE=0,first=new Int32Array(L/2);
  for(let j=0;j<M;j++){
   let A=6*j,x=cut(A,3,b,P),y=cut(A,3,b+1,P);u[mod(y.a,L)/2]++;first[mod(x.a,L)/2]++;out.oldRoots++;
  }
  for(let m of u)oldE+=m*m;for(let m of first)oldFirstE+=m*m;
  // Activate at the last (idle) tick of the old exit to height b+1.
  let active=[],lift=new Map(),nodes=new Map();
  for(let x=0;x<L/2;x++)if(mod(b-x,2)===0){
   let a=2*x;while(mod(a,p)!==p-1)a+=L;ck(a<L2,"unique lift");active.push(x);lift.set(x,a);out.activeNodes++;
   let n=b-a/2;ck(n%2===0,"even");let old=cut(a,b-1,b+1,P); // This auxiliary start is not used for the renewal map.
   if(u[x]){let t=cut(a,b,b+1,P);ck(t.d===0,"old even record exits");out.oldExitChecks++}
   let v=cut(a-p+1,0,b+1,P),c=a-p+1-v.d,y=mod(c,L)/2,s=mod(c,p),again=mod(b-c/2,2)===0&&s===p-1;
   if(again){ck(v.d>=p+1&&mod(v.d,p)===1,"repeat cost");out.repeatedFreshEdges++}
   nodes.set(x,{c,y,s,again,oldGain:v.d});out.resetExcursions++;
  }
  let memo=new Map(),maxChain=0;
  function resolve(x){let stack=[],seen=new Set(),z=x;
   while(!memo.has(z)){
    ck(!seen.has(z),"cycle");seen.add(z);let v=nodes.get(z);ck(v,"node");stack.push(z);
    if(!v.again){memo.set(z,{a:mod(v.c,L2),k:1});stack.pop();break}z=v.y;
   }
   while(stack.length){let v=stack.pop(),r=memo.get(z);memo.set(v,{a:r.a,k:r.k+1});z=v}
   return memo.get(x);
  }
  const fl=x=>x?x*Math.log(x):0,geom=x=>fl(1+x)-fl(x);let oldH=0;for(let m of u)oldH+=fl(m);let incoming=new Map(),removedH=0,weightedIndex=0,removed=0,mass=0,weightedFirings=0,repeatMass=0,initialEnergy=0;
  for(let x of active){let z=resolve(x);maxChain=Math.max(maxChain,z.k);let m=u[x];out.chainChecks++;if(!m)continue;
   ck(!(mod(b-z.a/2,2)===0&&mod(z.a,p)===p-1),"terminal nonactive");incoming.set(z.a,(incoming.get(z.a)||0)+m);removed+=m*m;removedH+=fl(m);let D=mod(lift.get(x)-z.a,L2);ck(D>=p-1,'positive lifted displacement');weightedIndex+=m*Math.floor(D/(4*p));mass+=m;weightedFirings+=m*z.k;if(z.k>1)repeatMass+=m;
  }
  let add=0,cross=0,incE=0,baseMass=0,crossH=0,incH=0;for(let [a,m] of incoming){add+=m;let base=u[mod(a,L)/2];cross+=2*base*m;incE+=m*m;baseMass+=base;crossH+=fl(base+m)-fl(base)-fl(m);incH+=fl(m);}
  let internalH=incH-removedH,deltaH=(crossH+internalH)/(p*M),crossBound=mass*geom(baseMass/mass),intBound=mass*geom(weightedIndex/mass);ck(internalH>=-1e-7&&crossH<=crossBound+1e-7&&internalH<=intBound+1e-7,'entropy bounds');out.entropyChecks++;ck(add===mass,"mass");let predicted=p*oldE-removed+cross+incE;ck(predicted>=p*oldE,"energy monotone");out.energyChecks++;
  // Direct full period for p<=17; deterministic subsample for p=19.
  let full=p<=17?new Int32Array(L2/2):null,step=full?1:97,counts=0;
  for(let j=0;j<M*p;j+=step){
   let A=6*j,base=cut(A,3,b+1,P),actual=cut(A,3,b+1,NP),x=mod(base.a,L)/2;
   let act=mod(b-base.a/2,2)===0&&mod(base.a,p)===p-1,predict=act?resolve(x).a:mod(base.a,L2);
   ck(predict===mod(actual.a,L2),{p,A,predict,actual:actual.a});out.directLiftChecks++;if(full){full[mod(actual.a,L2)/2]++;out.fullPeriodRoots++}counts++;
  }
  if(full){let e=0,hh=0;for(let x=0;x<full.length;x++){
   let a=2*x,i=mod(a,L)/2,act=mod(b-a/2,2)===0&&mod(a,p)===p-1,pred=(act?0:u[i])+(incoming.get(a)||0);ck(full[x]===pred,{p,a,actual:full[x],pred});e+=full[x]*full[x];hh+=fl(full[x]);out.energyChecks++}ck(e===predicted,"exact energy");ck(Math.abs(hh/(p*M)-oldH/M-deltaH)<1e-9,'exact entropy');out.entropyChecks++}
  out.rows.push({p,b,M,oldFirst:oldFirstE/M,oldExit:oldE/M,newExit:predicted/(p*M),oldEntropy:oldH/M,newEntropy:oldH/M+deltaH,deltaH,crossEntropy:crossH/(p*M),internalEntropy:internalH/(p*M),baseRatio:baseMass/mass,meanDisplacementIndex:weightedIndex/mass,entropyUpper:(crossBound+intBound)/(p*M),oldDelta:(oldE-oldFirstE)/M,freshDelta:(predicted-p*oldE)/(p*M),freshScaled:(cross+incE-removed)/M,activatedMass:mass/(p*M),activatedEnergy:removed/(p*M),repeatMass,weightedFirings,activeNodes:active.length,positiveActive:active.filter(x=>u[x]>0).length,terminalKeys:incoming.size,maxChain,counts,cross,incE,removed});
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
