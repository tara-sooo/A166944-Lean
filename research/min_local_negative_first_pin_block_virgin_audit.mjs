// First-pin exact first-use law and p-virgin stationary-block deletion equality at common height cuts.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,f=x=>x?x*Math.log(x):0,phi=(a,b)=>f(a+b)-f(a)-f(b);
 const P=[3,5,7,11,13],M=2*P.filter(p=>p>3).reduce((a,b)=>a*b,1),L=6*M;
 let z={fullRoots:0,deletedRoots:0,ticks:0,sourceTests:0,firstPins:0,blockLifts:0,prunedBlocks:0,firstChecks:0,repeatChecks:0,blockChecks:0,massChecks:0,entropyChecks:0,rows:[]};
 function run(A,Q,H,hook){
  let a=A,h=3,n=3-A/2,G=0,count=0;
  for(;;){let b=h+1,s=mod(n+1,2)?1:-1,v=Math.abs(s===-1?2*b+1:2*b-5),q=1;for(let p of Q)if(v%p===0&&mod(a-s,p)===0){q=p;break}
   if(hook)hook({a,h,n,G,b,s,v,q,count});
   z.ticks++;n++;a-=q-1;G+=q-1;h=b-(q-1)/2;count+=+(q!==1);
   if(h===H)return {a,h,n,G,count};ck(h<H&&h>=0,"height");
  }
 }
 function add(m,k,v=1){m.set(k,(m.get(k)||0)+v)}
 for(let H of [16,32,64])for(let p of [5,7,11,13]){
  const old=P.filter(q=>q!==p),m=M/p,l=6*m;
  let S=new Map(),B=new Map(),Bs=new Map(),actualS=new Map(),actualB=new Map(),actualFirst=new Map(),predFirst=new Map(),predVirgin=new Map(),raw=0,distinct=0,blocks=0,pruned=0,fullN=0,deletedN=0,actualRepeat=0,firstTotal=0,repeatBound=0,sourcePoint=0,basePoint=0,predS=new Map(),predSmall=new Map(),actSmall=new Map(),smallEntropy=0,smallMass=0,entropy=0,unprunedEntropy=0,prunedEntropy=0;
  function lift(a,r){let k=0;while(mod(a+k*l-r,p))k++;ck(k<p,"lift");return a+k*l}
  const key=(a,h)=>mod(a,L)+":"+h;
  for(let j=0;j<m;j++){
   let A=6*j,seen=new Set(),entrySeen=new Set(),entryA=A,entryH=3,entryG=0,entryQ=0;
   function endBlock(h){
    blocks++;for(let r of [0,2]){let a=lift(entryA,r),root=mod(a+entryG,p);add(B,key(a,h));z.blockLifts++;if(!entrySeen.has(root)){add(Bs,key(a,h));if(entryQ>0&&entryQ<p)add(predSmall,key(a,h));pruned++;z.prunedBlocks++}}
   }
   let ret=run(A,old,H,v=>{
    if(v.q!==1)endBlock(v.h);
    if(v.v%p===0&&(v.q===1||v.q>p)){
     raw++;z.sourceTests++;let r=mod(v.G+v.s,p);
     if(!seen.has(r)){seen.add(r);distinct++;z.firstPins++;
      let a=lift(v.a,v.s),root=mod(a+v.G,L);predFirst.set(root,{a:mod(a-p+1,L),h:v.b-(p-1)/2,G:v.G});firstTotal++;let target=a-p+1,h=v.b-(p-1)/2,n=h-target/2,w=Infinity;for(let q of old)for(let e of [-1,1])if(mod(target-e,q)===0){let t=mod((e===-1?0:q+2)-n,2*q)||2*q;w=Math.min(w,t)}add(predS,key(target,Math.min(H,h+w-1)));z.massChecks++;
     }
    }
    if(v.q!==1){entryA=v.a-v.q+1;entryQ=v.q;entryG=v.G+v.q-1;entryH=v.b-(v.q-1)/2;entrySeen=new Set(seen)}
   });
   endBlock(H);deletedN+=ret.count;z.deletedRoots++;
  }
  for(let j=0;j<M;j++){
   let A=6*j,virgin=true,entryVirgin=true,entryA=A,entryP=0,previous=null,np=0;
   function endBlock(h){let k=key(entryA,h);if(entryVirgin&&[0,2].includes(mod(entryA,p))){add(actualB,k);if(entryP>0&&entryP<p)add(actSmall,k)}if(entryP===p&&entryVirgin===false&&firstEntry)add(actualS,k)}
   let firstEntry=false;
   let ret=run(A,P,H,v=>{
    if(v.q!==1){
     endBlock(v.h);
     firstEntry=virgin&&v.q===p;entryP=v.q;entryA=v.a-v.q+1;
     if(v.q===p){
      np++;if(previous!==null){let gap=v.G-previous-(p-1);ck(gap>=p-1,"repeat gap");z.repeatChecks++}previous=v.G;
      if(virgin){let x={a:mod(entryA,L),h:v.b-(p-1)/2,G:v.G};actualFirst.set(A,x);virgin=false}
     }
     entryVirgin=virgin;
    }
   });
   endBlock(H);fullN+=ret.count;actualRepeat+=Math.max(0,np-1);
   if(np){repeatBound+=Math.floor(Math.max(0,ret.G-(p-1))/(2*p-2));ck(np-1<=Math.floor(Math.max(0,ret.G-(p-1))/(2*p-2)),"repeat budget")}
   z.fullRoots++;
  }
  for(let j=0;j<M;j++){let A=6*j;ck(JSON.stringify(actualFirst.get(A))===JSON.stringify(predFirst.get(A)),{H,p,A,actual:actualFirst.get(A),pred:predFirst.get(A)});z.firstChecks++}
  for(let k of new Set([...actualB.keys(),...Bs.keys(),...B.keys()])){ck((actualB.get(k)||0)===(Bs.get(k)||0)&& (Bs.get(k)||0)<=(B.get(k)||0),{H,p,k,a:actualB.get(k),b:Bs.get(k)});z.blockChecks++}
  for(let k of new Set([...predS.keys(),...actualS.keys()])){ck((predS.get(k)||0)===(actualS.get(k)||0),'source block equality');z.blockChecks++}
  for(let k of new Set([...predSmall.keys(),...actSmall.keys()])){ck((predSmall.get(k)||0)===(actSmall.get(k)||0),'smaller virgin block equality');z.blockChecks++}
  for(let [k,a] of actualS){smallEntropy+=phi(a,actSmall.get(k)||0);smallMass+=actSmall.get(k)||0;let b=actualB.get(k)||0;entropy+=phi(a,b);if(b){sourcePoint+=a;basePoint+=b}unprunedEntropy+=phi(a,B.get(k)||0);prunedEntropy+=phi(a,Bs.get(k)||0);z.massChecks++}
  ck([...actualS.values()].reduce((a,b)=>a+b,0)===firstTotal,"source count");ck(entropy<=phi(firstTotal,pruned)+1e-6&&prunedEntropy<=unprunedEntropy+1e-6&&actualRepeat<=repeatBound,"bounds");z.entropyChecks++;
  z.rows.push({H,p,period:M,oldPeriod:m,rawTests:raw/m,distinctPins:distinct/m,firstFraction:firstTotal/M,oldBlocks:blocks/m,prunedVirginBlocks:pruned/M,unprunedVirginBlocks:2*blocks/M,fullEvents:fullN/M,oldEvents:deletedN/m,repeat:actualRepeat/M,repeatBound:repeatBound/M,matchedSource:sourcePoint/M,matchedBase:basePoint/M,entropy:entropy/M,smallerVirginEntropy:smallEntropy/M,matchedSmallerMass:smallMass/M,unprunedPointBound:unprunedEntropy/M,prunedAggregate:phi(firstTotal,pruned)/M,unprunedAggregate:phi(firstTotal,2*blocks)/M})
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
