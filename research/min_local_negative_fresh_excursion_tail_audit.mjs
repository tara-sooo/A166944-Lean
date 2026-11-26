// Actual finite-slab fresh-prime excursion transport, short-injection and long-tail energy split.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=1000010,spf=new Uint32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)spf[a]=p;
 const fs=n=>{let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a};
 function cut(a,h,H,pmax){let n=h-a/2,d=0,k=0;
  while(true){ck(a>=0&&a+1<=N,"domain");let p=0,w=Infinity;
   for(let e of [-1,1])for(let q of fs(Math.abs(a-e)))if(q<=pmax){let t=mod((e===-1?0:q+2)-n,2*q)||2*q;if(t<w||t===w&&q<p){p=q;w=t}}
   if(h+w>=H)return {a,d,k};a-=p-1;d+=p-1;n+=w;h+=w-(p-1)/2;k++;
  }
 }
 function bridge(a){let x=a,h=0,t=0;
  while(h!==3||x%6!==0){let b=h+1,n=b-x/2,p=1;
   for(let q of fs(Math.abs(n%2===0?2*b+1:2*b-5)))if(q<=5&&mod(x+(n%2===0?1:-1),q)===0){p=q;break}
   x-=p-1;h=b-(p-1)/2;t++;ck(t<=8&&a-x<=10,"bridge");
  }return {a:x,g:a-x};
 }
 let z={slabs:0,roots:0,directChecks:0,activatedSources:0,bridgeChecks:0,repeatChecks:0,shortInjectivityChecks:0,energyChecks:0,rows:[]};
 for(let R of [48000,192000,480000])for(let p of [23,47,97,193,389,769]){
  let b=(p-1)/2,lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),M=(hi-lo)/6+1,U=new Map(),oldList=[],direct=new Map(),E=0,E2=0,G=0,maxGain=0;
  for(let A=lo;A<=hi;A+=6){let x=cut(A,3,b+1,p-1),y=cut(A,3,b+1,p);U.set(x.a,(U.get(x.a)||0)+1);direct.set(y.a,(direct.get(y.a)||0)+1);oldList.push([A,x.a,y.a]);G+=x.d;maxGain=Math.max(maxGain,x.d);z.roots++}
  let act=a=>mod(b-a/2,2)===0&&mod(a,p)===p-1,activated=[...U].filter(([a])=>act(a)),memo=new Map(),incoming=new Map(),shortIn=new Map(),longIn=new Map(),removed=0,removedShort=0,removedLong=0,shortMass=0,longMass=0,repeatMass=0,maxChain=0,maxD=0,seedMin=lo;
  function resolve(a){if(memo.has(a))return memo.get(a);let u=a,chain=[],d0=-1;
   while(true){let x=cut(u-p+1,0,b+1,p-1),B=bridge(u-p+1),y=cut(B.a,3,b+1,p-1);
    ck(y.a===x.a,"canonical bridge old exit");seedMin=Math.min(seedMin,B.a);z.bridgeChecks++;maxD=Math.max(maxD,x.d);if(d0<0)d0=x.d;chain.push({u,d:x.d});
    if(!act(x.a)){u=x.a;break}ck(x.d>=p+1&&mod(x.d,p)===1,"repeat gain");z.repeatChecks++;u=x.a;
   }
   let v={a:u,k:chain.length,d:d0};memo.set(a,v);return v
  }
  for(let [a,m] of activated){let x=resolve(a);maxChain=Math.max(maxChain,x.k);let short=x.d<=p;
   if(short){ck(x.k===1&&!shortIn.has(x.a),"short injective");shortIn.set(x.a,m);removedShort+=m*m;shortMass+=m;z.shortInjectivityChecks++}
   else{longIn.set(x.a,(longIn.get(x.a)||0)+m);removedLong+=m*m;longMass+=m}
   if(x.k>1)repeatMass+=m;incoming.set(x.a,(incoming.get(x.a)||0)+m);removed+=m*m;z.activatedSources++;
  }
  let pred=new Map(U);for(let [a,m] of activated)pred.delete(a);for(let [a,m] of incoming)pred.set(a,(pred.get(a)||0)+m);
  ck(pred.size===direct.size,"size");
  for(let [a,m] of pred){ck(direct.get(a)===m,"mass");E2+=m*m;z.energyChecks++}
  for(let m of U.values())E+=m*m;
  let crossS=0,crossL=0,collSL=0,longE=0;for(let [a,m] of shortIn)crossS+=2*(U.get(a)||0)*m;
  for(let [a,m] of longIn){crossL+=2*(U.get(a)||0)*m;collSL+=2*(shortIn.get(a)||0)*m;longE+=m*m}
  ck(E2-E===crossS+crossL+collSL+longE-removedLong,"split energy");
  for(let [A,x,y] of oldList){ck((act(x)?resolve(x).a:x)===y,"root prediction");z.directChecks++}
  z.rows.push({R,p,b,M,oldEnergy:E/M,newEnergy:E2/M,delta:(E2-E)/M,oldMeanGain:G/M,maxGain,activatedSources:activated.length,shortMass,longMass,repeatMass,maxChain,maxD,shortCross:crossS,longCross:crossL,mixedCollision:collSL,longInternal:longE-removedLong,removedShort,removedLong,seedMin});
  z.slabs++;
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
