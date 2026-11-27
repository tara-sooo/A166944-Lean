// Actual low-gain cohorts: compatible used-p return capacity, large plus-to-three bridge, and short p-q-p relays.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=4000005,spf=new Int32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)if(!spf[a])spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity,s=0;for(let e of [-1,1])for(let q of fs(a-e)){let d=mod((e===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d;s=e}}return {p,w,s}}
 const f=x=>x?x*Math.log(x):0,phi=(a,b)=>f(a+b)-f(a)-f(b);
 let out={roots:0,events:0,selected:0,compatibleChecks:0,largeChecks:0,relayChecks:0,bridgeMixChecks:0,rows:[]};
 for(let R of [12000,48000,192000,480000,1000000,2000000]){
  let K=Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),T=4*K,J=Math.floor(T/5),H=Math.floor(3+T-J/2),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),ns=0,blocks=new Map(),Y=Math.max(5,Math.ceil(J/8)),ds=[0,4,8,16],sets=ds.map(D=>({D,roots:0,motifs:0,keys:new Set(),pairs:new Set()}));
  let r={R,K,T,J,Y,ns:0,meanEvents:0,usedLower:0,usedLowerCap:0,usedAll:0,usedAllCap:0,largeFirst:0,largeUsedLower:0,largeBridges:0,largeBridgeMix:0,largeBridgeEntropy:0,largeBridgeKeys:0,macroRepeat:0,oneRelay:0,shortRepeat:0,otherRepeat:0};
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,end=n+T,G=0,path=[];
   for(;;){let e=next(a,n);if(n+e.w>end)break;path.push({a,n:n+e.w,G,p:e.p,s:e.s});a-=e.p-1;G+=e.p-1;n+=e.w;out.events++}
   out.roots++;if(G>J)continue;ns++;out.selected++;r.meanEvents+=path.length;
   let seen=new Map(),macro=path.map((e,i)=>e.p>=Y?i:-1).filter(i=>i>=0),used=new Map();
   for(let i=0;i<path.length;i++){let e=path[i],p=e.p,b=e.a-p+1,u=i+1<path.length?path[i+1].n-1:H-b/2,key=b+":"+u;
    let v=blocks.get(key)||{a:b,u,first:new Map(),bridges:new Map()};blocks.set(key,v);
    if(p>=5&&!seen.has(p)){
     seen.set(p,i);if(p>J/3+1){r.largeFirst++;let t=v.first.get(p)||{m:0,n:e.n,s:e.s};t.m++;v.first.set(p,t);ck(e.s===t.s,"first sign")}
    }
    for(let [q,j] of seen)if(j<i&&[0,2].includes(mod(b,q))){
     let t=used.get(q)||{all:0,low:0,repeat:0};t.all++;if(p<q)t.low++;if(p===q)t.repeat++;used.set(q,t);
     if(q>J/3+1&&p<q){ck(p===3&&i===j+1&&path[j].s===1&&e.G-path[j].G===q-1&&mod(b,q)===0,"bridge");r.largeBridges++;r.largeUsedLower++;out.largeChecks++;let x=v.bridges.get(q)||{m:0,n:e.n,firstN:path[j].n};x.m++;v.bridges.set(q,x)}
    }
   }
   for(let [p,j] of seen){let e=path[j],D=G-e.G-(p-1),rem=D%(2*p),C=2*Math.floor(D/(2*p))+(rem>=(e.s===1?2:2*p-2)?1:0),x=used.get(p)||{all:0,low:0,repeat:0};ck(x.all<=C&&x.low<=C-x.repeat,"compatible cap");out.compatibleChecks++;r.usedAll+=x.all;r.usedAllCap+=C;r.usedLower+=x.low;r.usedLowerCap+=C-x.repeat}
   let last=new Map(),hit=sets.map(()=>false);
   for(let k=0;k<macro.length;k++){let i=macro[k],e=path[i],p=e.p;if(last.has(p)){r.macroRepeat++;let k0=last.get(p);if(k===k0+2){r.oneRelay++;let j=macro[k0],m=macro[k0+1],x=path[j],q=path[m].p,d1=path[m].G-x.G-(p-1),d2=e.G-path[m].G-(q-1),D=d1+d2,c=x.s+1-e.s;ck(q!==p&&mod(q-1+D-c,p)===0&&(q-1+D-c)/p%2===1,"relay congruence");out.relayChecks++;
      if(D<=16)r.shortRepeat++;for(let l=0;l<sets.length;l++)if(D<=sets[l].D){let st=sets[l];st.motifs++;st.keys.add([x.a,p,q,d1,d2,x.s,path[m].s,e.s].join(":"));st.pairs.add(p+":"+q);hit[l]=true}
     }else r.otherRepeat++}last.set(p,k)}
   for(let l=0;l<sets.length;l++)sets[l].roots+=+hit[l];
  }
  for(let v of blocks.values())for(let [p,b] of v.bridges){let a=v.first.get(p);if(!a)continue;ck(a.s===-1&&mod(a.n,2*p)===0&&mod(b.firstN,2*p)===p+2&&b.n-b.firstN<=6&&Math.abs(a.n-b.n)>=p-8,"bridge clock separation");
   let q=Math.min(fs(v.a-1)[0],fs(v.a+1)[0]);ck(2*q>Math.abs(a.n-b.n),"stationary length");
   out.bridgeMixChecks++;r.largeBridgeMix+=b.m;r.largeBridgeEntropy+=phi(a.m,b.m);r.largeBridgeKeys++;
  }
  r.ns=ns;for(let k of Object.keys(r))if(!["R","K","T","J","Y","ns","largeBridgeKeys"].includes(k))r[k]/=ns;
  r.relays=sets.map(s=>({D:s.D,roots:s.roots,motifs:s.motifs,keys:s.keys.size,pairs:s.pairs.size,rate:s.roots/ns}));out.rows.push(r)
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
