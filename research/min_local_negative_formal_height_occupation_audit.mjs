// Coherent formal CRT samples: idle-height local times, downward interval overlap and top-alphabet exposure.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=131100,spf=new Uint32Array(N+1),pr=[];
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)spf[a]=p;
 for(let p=3;p<=N;p+=2)if(!spf[p])pr.push(p);
 function fs(n){let a=[];n=Math.abs(n);while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 const factor=Array.from({length:N+1},(_,i)=>i%2?fs(i):[]);
 let seed=0x5e912b87;function u32(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0}function rnd(n){let m=Math.floor(4294967296/n)*n,x;do{x=u32()}while(x>=m);return x%n}
 let z={paths:0,tickChecks:0,heightChecks:0,productChecks:0,firstChecks:0,threeChecks:0,intervalOverlapChecks:0,rows:[]};
 for(let T of [256,1024,4096,16384,65536])for(let div of [4,8]){
  let Y=Math.ceil(T/div),Ns=T<=4096?512:T<=16384?256:96,high=pr.filter(p=>p>Y&&p<=2*T+7),bmax=T+3,weight=new Float64Array(bmax+3),opp=new Uint8Array(bmax+3),B=0;
  for(let h=1;h<=bmax;h++){for(let p of [...factor[2*h+1],...factor[Math.abs(2*h-5)]])if(p>Y){weight[h]+=1/p;opp[h]=1}B+=opp[h]}
  let row={T,Y,div,Ns,B,prob:0,first:0,lowGain:0,fullGain:0,base:0,toll:0,smallToll:0,mediumToll:0,meanIdleSq:0,meanDropSq:0,meanSmallSq:0,meanMediumSq:0,maxLocal:0,meanMaxLocal:0,preJ:0,preJactual:0,J:Math.floor(T**.75),firstAtRecord:0};
  for(let i=0;i<Ns;i++){
   let parity=rnd(2),res=new Int32Array(N+1).fill(-1);res[3]=0;
   function aMod(p){if(res[p]<0)res[p]=rnd(p);return res[p]}
   let L=new Int32Array(bmax+3),df=new Int32Array(bmax+4),ds=new Int32Array(bmax+4),dm=new Int32Array(bmax+4),seen=new Map(),remaining=1,stRemain=1,G=0,h=3,first=null,record=3,intervals=[];
   for(let t=1;t<=T;t++){
    let b=h+1,par=mod(3-parity+t,2),s=par?1:-1,ff=factor[Math.abs(par?2*b-5:2*b+1)],p=1;
    for(let q of ff)if(q<=Y&&mod(aMod(q)-G-s,q)===0){p=q;break}
    if(p===1){L[b]++;
     for(let q of ff)if(q>Y){
      let pin=mod(G+s,q),d=seen.get(q)||new Set();if(d.has(pin))continue;
      let f=1-1/(q-d.size);remaining*=f;if(G<=row.J)stRemain*=f;
      d.add(pin);seen.set(q,d);
      if(!first&&aMod(q)===pin)first={t,q,b,G,record:b>=record};
     }
    }else{let l=b+1-(p-1)/2,r=b-1;if(l<=r){df[l]++;df[r+1]--;if(p<=31){ds[l]++;ds[r+1]--}if(p<=127){dm[l]++;dm[r+1]--}if(T===256&&i<8)intervals.push([l,r]);}if(p===3){ck(l>r,"3 interval");z.threeChecks++}G+=p-1}
    record=Math.max(record,b);h=b-(p-1)/2;z.tickChecks++;
   }
   let prod=1;for(let [p,d] of seen)prod*=1-d.size/p;ck(Math.abs(prod-remaining)<1e-10,"product");z.productChecks++;
   let D=0,S=0,M=0,local=0,drop=0,small=0,medium=0,mx=0,toll=0,st=0,mt=0,base=0;
   for(let b=1;b<=bmax;b++){D+=df[b];S+=ds[b];M+=dm[b];let f=h>=3?(b>=4&&b<=h?1:0):(b>=h+1&&b<=3?-1:0);
    ck(L[b]===f+D,{T,b,L:L[b],f,D});z.heightChecks++;local+=L[b]**2;drop+=D**2;small+=S**2;medium+=M**2;mx=Math.max(mx,L[b]);toll+=D*weight[b];st+=S*weight[b];mt+=M*weight[b];base+=f*weight[b];
   }
   if(T===256&&i<8){let v=0;for(let [l,r] of intervals)for(let [s,t] of intervals)v+=Math.max(0,Math.min(r,t)-Math.max(l,s)+1);ck(v===drop,"overlap");z.intervalOverlapChecks++}
   let g=0,hh=3,rec=3,actual=null;
   for(let t=1;t<=T;t++){let b=hh+1,par=mod(3-parity+t,2),s=par?1:-1,p=1;
    for(let q of factor[Math.abs(par?2*b-5:2*b+1)])if(mod(aMod(q)-g-s,q)===0){p=q;break}
    if(p>Y&&!actual)actual={t,q:p,b,G:g,record:b>=rec};rec=Math.max(rec,b);g+=p-1;hh=b-(p-1)/2;
   }
   ck(JSON.stringify(actual)===JSON.stringify(first),{T,actual,first});z.firstChecks++;
   row.prob+=1-remaining;row.first+=+!!actual;row.lowGain+=G;row.fullGain+=g;row.base+=base;row.toll+=toll;row.smallToll+=st;row.mediumToll+=mt;row.meanIdleSq+=local;row.meanDropSq+=drop;row.meanSmallSq+=small;row.meanMediumSq+=medium;row.maxLocal=Math.max(row.maxLocal,mx);row.meanMaxLocal+=mx;row.preJ+=1-stRemain;row.preJactual+=+(!!actual&&actual.G<=row.J);row.firstAtRecord+=+(!!actual&&actual.record);z.paths++;
  }
  for(let key of ["prob","first","lowGain","fullGain","base","toll","smallToll","mediumToll","meanIdleSq","meanDropSq","meanSmallSq","meanMediumSq","meanMaxLocal","preJ","preJactual","firstAtRecord"])row[key]/=Ns;
  row.dropRatio=row.meanDropSq/(T*Math.log(T));row.smallRatio=row.meanSmallSq/T;row.mediumRatio=row.meanMediumSq/T;z.rows.push(row);
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
