// Exact high-alphabet deletion exposure, first-winner product and idle-height toll identity.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p;
 const N=1000010,spf=new Uint32Array(N+1),pr=[];
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)spf[a]=p;
 for(let p=3;p<=N;p+=2)if(!spf[p])pr.push(p);
 const fs=n=>{let a=[];n=Math.abs(n);while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a};
 let out={periodRoots:0,liftedRoots:0,productChecks:0,firstLawChecks:0,occupationChecks:0,zeroThreeChecks:0,actualRoots:0,firstEventChecks:0,stopChecks:0,period:[],physical:[]};
 function make(T,high){
  let hs=new Set(high),B=Array.from({length:T+6},(_,b)=>{if(b<1)return [[],[]];return [fs(2*b+1).filter(p=>hs.has(p)),fs(2*b-5).filter(p=>hs.has(p))]});
  let pref=[0];for(let b=0;b<B.length;b++)pref.push(pref.at(-1)+B[b].flat().reduce((s,p)=>s+1/p,0));
  return {B,pref,range:(l,r)=>r<l?0:pref[r+1]-pref[l]}
 }
 function path(A,T,low,high,table,J=Infinity){
  let a=A,n=3-A/2,h=3,t=0,G=0,record=3,tests=[],D=new Map(),first=null,remain=1,law=new Map(),idle=0,toll=0,small=0,mid=0,rec=0,recRepeat=0,below=0,stopped=false;
  while(t<T){
   let b=h+1,nt=n+1,par=mod(nt,2),sg=par?1:-1,fac=par?2*b-5:2*b+1,p=1;
   for(let q of fs(fac))if(low(q)&&mod(a-sg,q)===0){p=q;break}
   if(p===1){
    idle+=table.range(b,b);
    if(G<=J)for(let q of table.B[b][par]){
     let pin=mod(G+sg,q),d=D.get(q)||new Set();
     if(d.has(pin))continue;
     let prob=remain/(q-d.size);remain-=prob;d.add(pin);D.set(q,d);
     let key=(t+1)+":"+q;law.set(key,prob);tests.push({t:t+1,q,pin,b,record:b>=record,newRecord:b>record,G});
     if(b>record)rec+=1/q;else if(b===record)recRepeat+=1/q;else below+=1/q;
     if(!first&&mod(A,q)===pin)first={t:t+1,p:q,b,G,record:b>=record};
    }
   }else{
    let k=(p-1)/2,v=table.range(b+1-k,b-1);
    toll+=v;if(p<=31)small+=v;else if(p<=127)mid+=v;
    if(p===3){ck(v===0,"3 toll");out.zeroThreeChecks++}
    a-=p-1;G+=p-1;
   }
   record=Math.max(record,b);h=b-(p-1)/2;n=nt;t++;
   if(G>J){stopped=true;break}
  }
  let base=h+1>=4?table.range(4,h): -table.range(h+1,3);
  ck(Math.abs(idle-base-toll)<1e-8,"occupation");out.occupationChecks++;
  let prod=1;for(let [q,d] of D)prod*=1-d.size/q;
  ck(Math.abs(prod-remain)<1e-10,"product");out.productChecks++;
  return {G,remain,law,tests,first,idle,base,toll,small,mid,rec,recRepeat,below,stopped,t};
 }
 function full(A,T,low,high,J=Infinity){
  let a=A,h=3,n=3-A/2,G=0,record=3,first=null;
  for(let t=1;t<=T;t++){
   let b=h+1; n++;let par=mod(n,2),sg=par?1:-1,p=1;
   for(let q of fs(par?2*b-5:2*b+1))if((low(q)||high(q))&&mod(a-sg,q)===0){p=q;break}
   if(high(p)&&!first)first={t,p,b,G,record:b>=record};
   record=Math.max(record,b);G+=p-1;a-=p-1;h=b-(p-1)/2;if(G>J)break;
  }return {G,first}
 }
 for(let [T,P,Q] of [[12,[3,5],[7,11,13]],[22,[3,5,7],[11,13,17]],[34,[3,5,7],[11,13,17]]]){
  let M=2*P.filter(p=>p>=5).reduce((s,p)=>s*p,1),K=Q.reduce((s,p)=>s*p,1),low=p=>P.includes(p),high=p=>Q.includes(p),table=make(T,Q),sum=0,actual=0,meanToll=0,meanExposure=0,lowG=0,fullG=0,firstBelow=0;
  for(let j=0;j<M;j++){
   let A=6*j,r=path(A,T,low,high,table),count=0,m=new Map();out.periodRoots++;sum+=1-r.remain;meanToll+=r.toll;meanExposure+=r.idle;lowG+=r.G;
   for(let k=0;k<K;k++){let B=A+6*M*k,x=full(B,T,low,high);out.liftedRoots++;fullG+=x.G;if(x.first){count++;let key=x.first.t+":"+x.first.p;m.set(key,(m.get(key)||0)+1);firstBelow+=+!x.first.record}}
   ck(Math.abs(count/K-(1-r.remain))<1e-10,{T,j,count,prob:1-r.remain});out.productChecks++;actual+=count;
   for(let key of new Set([...m.keys(),...r.law.keys()])){ck(Math.abs((m.get(key)||0)/K-(r.law.get(key)||0))<1e-10,"law");out.firstLawChecks++}
  }
  out.period.push({T,P,Q,M,K,prob:sum/M,actual:actual/(M*K),meanToll:meanToll/M,meanExposure:meanExposure/M,lowG:lowG/M,fullG:fullG/(M*K),firstBelow});
 }
 for(let R of [12000,48000,192000,480000])for(let div of [4,8,16]){
  let T=Math.ceil(8*Math.sqrt(2*R+1)),Y=Math.ceil(T/div),Q=pr.filter(p=>p>Y&&p<=2*T+7),low=p=>p<=Y,high=p=>p>Y,table=make(T,Q),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),step=Math.max(1,Math.ceil((hi-lo)/6/384));
  let row={R,T,Y,div,n:0,first:0,firstBelow:0,firstRecord:0,proxy:0,lowGain:0,fullGain:0,idleExposure:0,base:0,toll:0,smallToll:0,mediumToll:0,recordExposure:0,repeatRecordExposure:0,belowExposure:0,stopProxy:0,stopFirst:0,stopJ:Math.floor(Math.sqrt(T))};
  for(let A=lo;A<=hi;A+=6*step){
   let r=path(A,T,low,high,table),f=full(A,T,low,high);
   ck(JSON.stringify(r.first)===JSON.stringify(f.first),{A,R,Y,fromDeleted:r.first,full:f.first});out.firstEventChecks++;
   let s=path(A,T,low,high,table,row.stopJ),g=full(A,T,low,high,row.stopJ);
   ck(JSON.stringify(s.first)===JSON.stringify(g.first),"stopped first event");out.stopChecks++;
   row.n++;out.actualRoots++;row.first+=+!!f.first;row.firstBelow+=+(!!f.first&&!f.first.record);row.firstRecord+=+(!!f.first&&f.first.record);
   row.proxy+=1-r.remain;row.lowGain+=r.G;row.fullGain+=f.G;row.idleExposure+=r.idle;row.base+=r.base;row.toll+=r.toll;row.smallToll+=r.small;row.mediumToll+=r.mid;row.recordExposure+=r.rec;row.repeatRecordExposure+=r.recRepeat;row.belowExposure+=r.below;row.stopProxy+=1-s.remain;row.stopFirst+=+!!g.first;
  }
  for(let k of ["first","firstBelow","firstRecord","proxy","lowGain","fullGain","idleExposure","base","toll","smallToll","mediumToll","recordExposure","repeatRecordExposure","belowExposure","stopProxy","stopFirst"])row[k]/=row.n;
  out.physical.push(row);
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
