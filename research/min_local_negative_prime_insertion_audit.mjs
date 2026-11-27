// Exact largest-prime insertion, short-fiber Euler identity, and regular subensemble.
// node research/min_local_negative_prime_insertion_audit.mjs
function audit(){
 const mod=(a,b)=>(a%b+b)%b,ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 function next(x,n,ps){let p=Infinity,w=Infinity,e=0;
  for(let q of ps)for(let s of [-1,1])if(mod(x-s,q)===0){
   let d=mod((s===-1?0:q+2)-n,2*q)||2*q;
   if(d<w||d===w&&q<p){p=q;w=d;e=s}
  }
  return {p,w,e}
 }
 function run(v,h,ps,trace=false){
  let x=v,n=h-v/2,ev=[],k=0;const Q=2*ps.reduce((a,b)=>a*b,1);
  for(;;){let e=next(x,n,ps);if(!Number.isFinite(e.p))break;
   let y=x-e.p+1;ck(Math.floor(x/Q)===Math.floor(y/Q)&&n+e.w+y/2>=0,"restricted cell and height");
   if(trace)ev.push({x,n,...e});x=y;n+=e.w;k++;ck(v-x<Q&&k<=Q/2,"termination");
  }
  return {x,n,k,g:v-x,h:n+x/2,ev};
 }
 function moment(a){let s=0;for(let m of a)s+=m*m;return s}
 function init(ps){
  let F=4*ps.reduce((a,b)=>a*b,1),N=F/2,keep=new Uint8Array(N).fill(1);return {ps,F,keep};
 }
 function add(old,p,zero=false){
  const {ps,F,keep}=old,qs=[...ps,p],F1=F*p,N=F/2,N1=F1/2,B=zero?0:Math.min(p-3,Math.floor(Math.log(p)**2),F/2);
  const oldMass=new Uint32Array(F/2),baseFull=new Uint32Array(F/2),newMass=new Uint32Array(F1/2),goodMass=new Uint32Array(F1/2),badMass=new Uint32Array(F1/2),newKeep=new Uint8Array(N1);
  const goodArrival=new Map(),moved=new Map(),targetBase=new Map(),gainOld=new Uint32Array(N),endOld=new Uint32Array(N),gainNew=new Uint32Array(N1),endNew=new Uint32Array(N1);
  let early=0,terminal=0,unchanged=0,repeat=0,regular=0,highHeight=0,postLong=0,oldTailEvents=0,oldHeightBad=0,eligibleTerminal=0,retOld=0,retNew=0,keptBad=0,keptReg=0,keptIdle=0,checks=0,events=0,oldEvents=0;
  let predCount=0;
  for(let v=0;v<F;v+=4)for(let hi=0;hi<2;hi++){
   let h=3*hi,id=v/2+hi,o=run(v,h,ps,true);
   gainOld[id]=o.g;endOld[id]=o.x/2;oldEvents+=o.k;baseFull[o.x/2]++;
   if(keep[id]){retOld++;oldMass[o.x/2]++;}
   if(6*o.g+7>=p)oldTailEvents+=o.k;
   if(o.h>(p-3)/2)oldHeightBad++;
   let actualEarlyLifts=0,actualTerminalLifts=0;
   for(let j=0;j<p;j++){
    let shift=j*F,root=v+shift,idx=root/2+hi,first=-1,wait=0,sign=0;
    // The old trace is known at the base residue; check the two p-pins.
    for(let i=0;i<=o.ev.length;i++){
     let x=(i<o.ev.length?o.ev[i].x:o.x)+shift,n=(i<o.ev.length?o.ev[i].n:o.n)-shift/2;
     for(let e of [-1,1])if(mod(x-e,p)===0){
      let w=mod((e===-1?0:p+2)-n,2*p)||2*p;
      if(i===o.ev.length||w<o.ev[i].w){first=i;wait=w;sign=e;break;}
     }
     if(first!==-1)break;
    }
    let a=run(root,h,qs,true),at=a.ev.findIndex(e=>e.p===p),pc=a.ev.filter(e=>e.p===p).length;
    events+=a.k;gainNew[idx]=a.g;endNew[idx]=a.x/2;newMass[a.x/2]++;
    ck(at===first,"first added-prime index");checks++;
    if(first===-1){ck(a.x===o.x+shift&&a.g===o.g&&a.k===o.k,"unaffected exact translation");unchanged++;}
    else{
     predCount++;let e=a.ev[at];ck(e.w===wait&&e.e===sign&&e.x===(at<o.k?o.ev[at].x:o.x)+shift,"first added-prime phase");checks++;
     if(at<o.k){early++;actualEarlyLifts++;ck(6*o.g+7>=p,"early height necessary");}
     else{terminal++;actualTerminalLifts++;ck(at===o.k,"old terminal insertion");}
     if(pc>1)repeat++;
    }
    let good=false;
    if(first===o.k){
     let e=a.ev[at],v1=e.x-p+1,h1=e.n+e.w+v1/2,tail=run(v1,h1,ps,false);
     if(o.h>(p-3)/2)highHeight++;
     else{
      ck([0,3,p,p+3].includes(h1),"low entry height determines postheight");
      if(tail.g>B)postLong++;
      else{
       ck(pc===1&&a.x===tail.x&&a.k===o.k+1+tail.k,"regular one-prime insertion");
       good=true;regular++;
      }
     }
    }
    if(keep[id]&&(first===-1||good)){
     newKeep[idx]=1;retNew++;goodMass[a.x/2]++;
     if(first===-1)keptIdle++;
     else{
      keptReg++;let key=o.x+":"+sign,v=moved.get(key)||{m:0,target:a.x,base:o.x/2,source:o.x+shift};
      ck(v.target===a.x,"terminal fiber and sign determine full new target");v.m++;moved.set(key,v);
      let f=goodArrival.get(a.x)||new Set();f.add(key);goodArrival.set(a.x,f);
     }
    }else if(keep[id]){keptBad++;badMass[a.x/2]++;}
   }
   ck(actualEarlyLifts<=2*o.k&&actualTerminalLifts<=2,"first deviation lift counts");
   if(p>6*o.g+7)ck(actualEarlyLifts===0&&actualTerminalLifts===2,"exact short-path lift law");
   checks++;
  }
  ck(predCount===early+terminal&&unchanged+early+terminal===N1,"first event partition");
  ck(early<=2*oldTailEvents&&terminal<=2*N&&retNew+keptBad===retOld*p,"retained mass ledger");
  let cross=0,moveSquares=0,moveActual=0;
  for(let v of moved.values()){
   ck(v.m<=oldMass[v.base],"old terminal source mass");
   cross+=v.m*oldMass[mod(v.target,F)/2];moveSquares+=v.m*v.m;
   let y=mod(v.target,F),s=targetBase.get(y)||0;targetBase.set(y,s+1);
  }
  for(let [x,s] of goodArrival){ck(s.size<=2,"at most two incoming regular terminal signs");let m=0;for(let k of s)m+=moved.get(k).m;moveActual+=m*m;}
  for(let n of targetBase.values())ck(n<=2*(Math.floor(B/2)+1),"base target multiplicity");
  let K0=moment(oldMass)/F,Kfull0=moment(baseFull)/F,K1=moment(newMass)/F1,Kg=moment(goodMass)/F1,Kb=moment(badMass)/F1;
  let factor=1+(4*Math.sqrt(Math.floor(B/2)+1)+4)/p,exactBound=K0+(2*cross+moveActual)/F1;
  ck(moveSquares<=2*moment(oldMass)&&moveActual<=2*moveSquares&&Kg<=exactBound+1e-10&&exactBound<=K0*factor+1e-10,"regular moment recursion");
  let zeroBound=null,g0=0,g1=0,mg0=0,mg1=0,firstGain=0,maxKept=0,lambda=1/17;
  if(zero){
   let flow=new Int32Array(F1/2);
   for(let y=0;y<flow.length;y++)flow[y]=oldMass[y%(F/2)];
   let seen=new Set();
   for(let v of moved.values()){
    ck(v.target===v.source-p+1&&!seen.has(v.target)&&mod(v.source-1,p)*mod(v.source+1,p)===0,"zero-relay unique target");
    ck(mod(v.target-1,p)!==0&&mod(v.target+1,p)!==0,"target not outgoing");
    seen.add(v.target);flow[v.source/2]-=v.m;flow[v.target/2]+=v.m;
   }
   for(let y=0;y<flow.length;y++)ck(flow[y]>=goodMass[y],"baseline minus move plus arrival dominates");
   zeroBound=K0*(1+4/p);
   ck(Kg<=moment(flow)/F1+1e-10&&moment(flow)/F1<=K0+2*cross/F1+1e-10&&K0+2*cross/F1<=zeroBound+1e-10,"improved zero-relay recursion");
   for(let i=0;i<N;i++)if(keep[i]){g0+=gainOld[i];mg0+=Math.exp(lambda*gainOld[i]);}
   for(let i=0;i<N1;i++)if(newKeep[i]){g1+=gainNew[i];mg1+=Math.exp(lambda*gainNew[i]);maxKept=Math.max(maxKept,gainNew[i]);}
   ck(g1<=p*g0+2*(p-1)*retOld&&mg1<=(p+2*Math.expm1(lambda*(p-1)))*mg0+1e-6,"selected gain and exponential moment recursion");
  }
  const Ds=[0,1,2,4,6,8,12,15,20].filter(D=>p>6*D+7);
  let short=[];
  for(let D of Ds){
   let a=new Uint32Array(F/2),b=new Uint32Array(F1/2),n0=0,n1=0;
   for(let i=0;i<N;i++)if(gainOld[i]<=D){a[endOld[i]]++;n0++;}
   for(let i=0;i<N1;i++)if(gainNew[i]<=D){b[endNew[i]]++;n1++;}
   ck(n1===(p-2)*n0&&moment(b)===(p-2)*moment(a),"exact short mass and moment Euler identity");
   for(let y=0;y<F/2;y++)if(a[y])for(let j=0;j<p;j++){
    let v=2*y+j*F,ok=mod(v-1,p)!==0&&mod(v+1,p)!==0;
    ck(b[v/2]===(ok?a[y]:0),"exact short terminal fiber lift");
   }
   short.push({D,n0,n1,K0:moment(a)/F,K1:moment(b)/F1});
  }
  let out={p,F,F1,N1,B,zeroBound,meanSelectedGain:g1/N1,mgfSelected:mg1/N1,maxKept,checks,events,oldEvents,early:early/N1,terminal:terminal/N1,repeat:repeat/N1,regular:regular/N1,highHeight:highHeight/N1,postLong:postLong/N1,earlyBound:2*oldTailEvents/N1,retOld:retOld/N,retNew:retNew/N1,keptIdle:keptIdle/N1,keptReg:keptReg/N1,keptBad:keptBad/N1,Kfull0,K1,K0,Kg,Kb,exactBound,regularBound:K0*factor,short};
  return {ps:qs,F:F1,keep:newKeep,out};
 }
 let a=init([3]),rows=[];for(let p of [5,7,11,13,17]){a=add(a,p);rows.push(a.out)}
 let b=init([3,5]),sparse=[];for(let p of [101,103]){b=add(b,p);sparse.push(b.out)}
 let c=init([3]),zero=[];for(let p of [5,7,11,13,17]){c=add(c,p,true);zero.push(c.out)}
 return {rows,sparse,zero};
}
if(typeof console!=="undefined")console.log(JSON.stringify(audit(),null,2));
