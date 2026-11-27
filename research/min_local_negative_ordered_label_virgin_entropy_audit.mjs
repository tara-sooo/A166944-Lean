// Ordered label entropy telescoping and virgin/used/repeated split on actual selected cohorts.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=4000005,spf=new Int32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)if(!spf[a])spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const f=x=>x?x*Math.log(x):0,phi=(a,b)=>f(a+b)-f(a)-f(b);
 let z={roots:0,events:0,selected:0,blocks:0,labelSplits:0,virginChecks:0,entropyChecks:0,rows:[]};
 for(let R of [12000,48000,192000,480000,1000000,2000000]){
  let K=Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),T=4*K,J=Math.floor(T/5),H=Math.floor(3+T-J/2),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nr=(hi-lo)/6+1,blocks=new Map(),endpoints=new Map(),ns=0,primeBits=new Map(),idx=0,nu=0,first=0,repeatCount=0,three=0,firstGt3=0,repeatGt3=0,repeatCap=0,repeatActualGainCap=0;
  for(let p=3;p<=J+1;p+=2)if(!spf[p])primeBits.set(p,1n<<BigInt(idx++));
  for(let A=lo;A<=hi;A+=6){let a=A,n=3-A/2,end=n+T,path=[],labels=[];
   for(;;){let e=next(a,n);if(n+e.w>end)break;path.push({a,u:n+e.w-1});a-=e.p-1;n+=e.w;labels.push(e.p);z.events++}
   z.roots++;if(A-a>J)continue;path.push({a,u:H-a/2});ns++;z.selected++;endpoints.set(a,(endpoints.get(a)||0)+1);
   let used=0n,G=0,counts=new Map(),firstG=new Map();nu+=labels.length;for(let p of labels){if(!counts.has(p))firstG.set(p,G);counts.set(p,(counts.get(p)||0)+1);G+=p-1}ck(G===A-a,'gain');three+=counts.get(3)||0;ck((counts.get(3)||0)<=2*(labels.length-(counts.get(3)||0)),'3 run');first+=counts.size;repeatCount+=labels.length-counts.size;for(let [p,m] of counts)if(p>=5){firstGt3++;repeatGt3+=m-1;let b=Math.floor((J-firstG.get(p)-(p-1))/(2*(p-1))),d=Math.floor((G-firstG.get(p)-(p-1))/(2*(p-1)));ck(m-1<=d&&d<=b,'repeat cap');repeatCap+=b;repeatActualGainCap+=d;}
   for(let i=1;i<path.length;i++){let p=labels[i-1],bit=primeBits.get(p),fresh=(used&bit)===0n,key=path[i].a+":"+path[i].u;let v=blocks.get(key)||{a:path[i].a,groups:[]};v.groups.push({p,fresh,used});blocks.set(key,v);used|=bit}
  }
  let totals={exact:0,virgin:0,used:0,repeat:0,firstMass:0,virginMass:0,usedMass:0,repeatMass:0,smallMass:0,exactFirstMix:0,exactRepeatMix:0},byP=new Map(),blockLabels=0;
  for(let v of blocks.values()){
   z.blocks++;let map=new Map();for(let e of v.groups){let l=map.get(e.p)||[];l.push(e);map.set(e.p,l)}
   let M=v.groups.length,E=f(M)-[...map.values()].reduce((s,l)=>s+f(l.length),0),F=0;
   for(let [p,l] of map){if(p<5)continue;
    let A=l.filter(x=>x.fresh).length,Q=l.length-A,B0=0,B1=0;
    for(let e of v.groups)if(e.p<p){if(e.used&primeBits.get(p))B1++;else B0++}
    let B=B0+B1;
    if(B){ck([0,2].includes(mod(v.a,p)),"target pin");z.virginChecks++}
    const ex=phi(A+Q,B),v0=phi(A,B0),v1=phi(A,B1),r=phi(Q,B);
    ck(ex<=v0+v1+r+1e-8,"split");z.labelSplits++;F+=ex;
    let o=byP.get(p)||{p,exact:0,virgin:0,used:0,repeat:0,firstMass:0,virginMass:0,usedMass:0,repeatMass:0,smallMass:0,exactFirstMix:0,exactRepeatMix:0};
    let vals={exact:ex,virgin:v0,used:v1,repeat:r,firstMass:B?A:0,virginMass:A?B0:0,usedMass:A?B1:0,repeatMass:B?Q:0,smallMass:Q?B:0,exactFirstMix:phi(A,B),exactRepeatMix:phi(Q,B)};
    for(let k of Object.keys(totals)){totals[k]+=vals[k];o[k]+=vals[k]}byP.set(p,o);
   }
   ck(Math.abs(E-F)<1e-8,"telescope");z.entropyChecks++;blockLabels+=E;
  }
  let bound=0;for(let o of byP.values())bound+=phi(o.firstMass,o.virginMass)+phi(o.firstMass,o.usedMass)+phi(o.repeatMass,o.smallMass);
  ck(blockLabels<=totals.virgin+totals.used+totals.repeat+1e-7&&totals.virgin+totals.used+totals.repeat<=bound+1e-7,"global");let L=[...endpoints.values()].reduce((s,m)=>s+f(m),0)/ns;
  z.rows.push({R,K,T,J,ns,L,nu:nu/ns,first:first/ns,repeatCount:repeatCount/ns,three:three/ns,firstGt3:firstGt3/ns,repeatGt3:repeatGt3/ns,repeatCap:repeatCap/ns,repeatActualGainCap:repeatActualGainCap/ns,aggregateUpper:bound/ns,...Object.fromEntries(Object.entries(totals).map(([k,v])=>[k,v/ns])),byP:[...byP.values()].sort((a,b)=>a.p-b.p).map(o=>Object.fromEntries(Object.entries(o).map(([k,v])=>[k,k==="p"?v:v/ns])))})
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
