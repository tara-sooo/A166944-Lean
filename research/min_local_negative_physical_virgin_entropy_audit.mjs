// Physical first-use p and p-virgin idle mass: exact deleted-path CRT lift upper certificate.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,f=x=>x?x*Math.log(x):0,phi=(a,b)=>f(a+b)-f(a)-f(b);
 const P=[3,5,7,11,13],M=2*P.filter(p=>p>3).reduce((a,b)=>a*b,1),L=6*M;
 let z={fullRoots:0,deletedRoots:0,ticks:0,sourceLiftChecks:0,baseLiftChecks:0,pointwiseChecks:0,entropyChecks:0,rows:[]};
 for(let T of [24,40,64])for(let p of [5,7,11,13]){
  let old=P.filter(q=>q!==p),m=M/p,l=6*m,src=new Map(),base=new Map(),actS=new Map(),actB=new Map(),srcCount=0,baseCount=0,actualSrc=0,actualBase=0;
  function winner(a,n,b,Q){let s=mod(n,2)?1:-1,v=Math.abs(s===-1?2*b+1:2*b-5);for(let q of Q)if(v%q===0&&mod(a-s,q)===0)return q;return 1}
  function lift(a,desired){let k=0;while(mod(a+k*l-desired,p))k++;ck(k<p,"unique");return a+k*l}
  function add(map,a,h){let key=mod(a,L)+":"+h;map.set(key,(map.get(key)||0)+1)}
  for(let j=0;j<m;j++){
   let a=6*j,n=3-a/2,h=3;
   for(let t=1;t<=T;t++){
    let b=h+1; n++;let s=mod(n,2)?1:-1,v=Math.abs(s===-1?2*b+1:2*b-5),q=winner(a,n,b,old);
    if(v%p===0&&(q===1||q>p)){
     let x=lift(a,s),hh=b-(p-1)/2;ck(hh>=0&&mod(x-s,p)===0&&mod(n-(x-a)/2-(s===-1?0:p+2),2*p)===0,"source lift");add(src,x-p+1,hh);srcCount++;z.sourceLiftChecks++;
    }
    if(q===1&&mod(b-(s===-1?0:3),p)===0){
     let x=lift(a,s+1);ck(mod(n-(x-a)/2-(s===-1?0:p+2),2*p)===0,"base lift");add(base,x,b);baseCount++;z.baseLiftChecks++;
    }
    a-=q-1;h=b-(q-1)/2;z.ticks++;
   }z.deletedRoots++;
  }
  for(let j=0;j<M;j++){
   let a=6*j,n=3-a/2,h=3,virgin=true;
   for(let t=1;t<=T;t++){
    let b=h+1;n++;let s=mod(n,2)?1:-1,q=winner(a,n,b,P);
    if(virgin&&q===p){add(actS,a-p+1,b-(p-1)/2);actualSrc++;virgin=false}
    if(virgin&&q===1&&mod(a-s-1,p)===0&&mod(b-(s===-1?0:3),p)===0){add(actB,a,b);actualBase++}
    a-=q-1;h=b-(q-1)/2;z.ticks++;
   }z.fullRoots++;
  }
  let A=0,B=0,H=0,keys=0;
  for(let k of new Set([...actS.keys(),...actB.keys()])){
   let a=actS.get(k)||0,b=actB.get(k)||0;ck(a<=(src.get(k)||0)&&b<=(base.get(k)||0),{T,p,k,a,b,ps:src.get(k),pb:base.get(k)});z.pointwiseChecks++;
   if(a&&b){A+=a;B+=b;H+=phi(a,b);keys++}
  }
  ck(actualSrc<=srcCount&&actualBase<=baseCount&&H<=phi(A,B)+1e-7&&phi(A,B)<=phi(srcCount,baseCount)+1e-7,"entropy");z.entropyChecks++;
  z.rows.push({T,p,period:M,oldPeriod:m,sourceMean:srcCount/m,baseMean:baseCount/m,actualFirst:actualSrc/M,actualVirginBase:actualBase/M,collisionKeys:keys,collisionSource:A/M,collisionBase:B/M,entropy:H/M,bound:phi(srcCount,baseCount)/M,matchedBound:phi(A,B)/M});
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
