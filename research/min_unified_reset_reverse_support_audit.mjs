// Actual reset reverse graph, ordered-pair capacity, shifted root roughness and flat nonreset controls.
function audit(Xs=[4096,16384,65536]){
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b,lim=7*Math.max(...Xs)+100;
 let spf=new Int32Array(lim+1);for(let p=2;p<=lim;p++)if(!spf[p])for(let j=p;j<=lim;j+=p)spf[j]=p;
 let out=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,tags=[],events=0;
  const key=(C,t)=>C+"/"+t,phase=(C,t)=>C%4===0&&(2*t-C===0||2*t-C===6);
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let C0=2*M-2,C=C0,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity;for(let I=0;I<2;I++){let v=C-1+2*I;while(v>1){let f=spf[v];while(v%f===0)v/=f;if(f*f>C+1)continue;let r=mod((I?f+2:0)-t,2*f)||2*f;if(r<w||r===w&&f<p){p=f;w=r}}}if(!p)break;
    let J=C+p-1,n=t+w,I=n%2,d=2*t-C,dp=2*n-J,e={C,t,J,n,p,w,g:p-1,d,dp,I,reset:dp===6*I};path.push(e);events++;C=J;t=n;
   }tags.push({M,C0,F:C,tf:t,path})
  }
  let N=tags.length;
  for(let Y of [...new Set([7,17,31,Math.max(7,Math.floor(Math.sqrt(H)))])]){
   let P=B,cut=4,graph=new Map(),vis=new Map(),rootSet=new Set(tags.map(t=>key(t.C0,t.M+2))),edgeCount=0,rootPrefix=0,rootGain=0,pureWitness=0,pureTargets=0,maxIn=0,rootArrivalChecks=0,resetPhaseChecks=0,seedChecks=0,seedNear=0,seedTargets=0,seedMax=0,resetGain=0,resetCount=0,firstGain=0,closeGain=0,tailGain=0,Rw=0,tupleChecks=0,pairChecks=0,maxSupport=0,supportSq=0,capacity=0,roughChecks=0,rootNear=0,rootFirst=0,rootShiftChecks=0,firstAgeSum=0,flatChecks=0,flatRuns=0,flatGain=0;
   const factorCount=n=>{let k=0;while(n>1){let p=spf[n];ok(p>0,"factor range");if(p>=Y&&p<=P)k++;while(n%p===0)n/=p}return k};
   const node=(C,t)=>{let id=key(C,t);if(!graph.has(id))graph.set(id,{id,C,t,ins:new Set(),next:null});return graph.get(id)};
   const put=(v,seed,depth,pure)=>{if(!vis.has(v.id))vis.set(v.id,{seeds:new Map(),pure:[]});let q=vis.get(v.id),z=q.seeds.get(seed)||{n:0,depth};ok(z.depth===depth,"deterministic suffix depth");z.n++;q.seeds.set(seed,z);if(pure)q.pure.push(depth)};
   for(let t of tags){let root=node(t.C0,t.M+2),seed=root.id,depth=0,pure=true;put(root,seed,depth,pure);
    let firstHigh=t.path.find(e=>e.p>=Y&&4*e.w>=e.g);
    if(firstHigh){let a=firstHigh.C-t.C0;firstAgeSum+=a;if(a<=Math.ceil(Math.log(X)**2))rootNear++;if(a===0)rootFirst++;
     ok(a%2===0&&firstHigh.C-1===2*t.M+a-3&&firstHigh.C+1===2*t.M+a-1,"shifted root forms");
     for(let f=3;9*f<firstHigh.g;f+=2)if(spf[f]===f){ok((firstHigh.C-1)%f!==0&&(firstHigh.C+1)%f!==0,"rough root shift");rootShiftChecks++}
    }
    let list=t.path.filter(e=>e.reset&&e.p>=Y&&e.p<=P);
    if(list.length){let S=[...new Set(list.map(e=>e.p))],s=S.length,ss=S.reduce((z,p)=>z+p-1,0),recip=S.reduce((z,p)=>z+1/p,0),G=t.F-t.C0,F=list.reduce((z,e)=>z+e.g,0),pairs=new Map(),relay=0,close=0,tail=0;
     maxSupport=Math.max(maxSupport,s);supportSq+=s*s;resetGain+=F;resetCount+=list.length;firstGain+=list[0].g;
     for(let j=1;j<list.length;j++){let a=list[j-1],b=list[j],E=b.C-a.J;
      ok(E>=0&&E%2===0,"reset relay");relay+=E;Rw+=b.p*E;
      if(E>cut){tail+=b.g;continue}
      ok(a.p!==b.p,"close reset distinct labels");ok(mod(a.C-(1-2*a.I),a.p)===0&&mod(a.C+a.p-1+E-(1-2*b.I),b.p)===0,"reset pair CRT");
      let k=[a.p,b.p,E,a.I,b.I].join("/"),q=pairs.get(k)||{a:a.p,b:b.p,n:0,first:a.C,last:a.C};ok(q.n===0||(a.C-q.last)%(a.p*b.p)===0,"repeated reset pair progression");q.n++;q.last=a.C;pairs.set(k,q);pairChecks++;close+=b.g;
      if(b.g>=2*(6+5*E)){ok(4*b.w>=b.g,"automatic long reset successor");for(let f=3;9*f<b.g;f+=2)if(spf[f]===f){ok((b.C-1)%f!==0&&(b.C+1)%f!==0,"rough reset successor");roughChecks++}}
     }
     let bound=4*(cut+1)*((s-1)*ss+G*(s-1)*recip);
     for(let q of pairs.values()){ok(q.n<=1+G/(q.a*q.b),"reset pair occurrence capacity");tupleChecks++}
     ok(close<=bound+1e-7&&relay<=G-F&&F===list[0].g+close+tail,"support capacity and partition");
     closeGain+=close;tailGain+=tail;capacity+=bound;
    }
    for(let j=0;j<t.path.length;j++){
     let e=t.path[j],a=phase(e.C,e.t),b=phase(e.J,e.n);
     if(b){ok(e.reset&&mod(e.J+2*e.I,e.p)===0,"reset predecessor factor");ok(!rootSet.has(key(e.J,e.n)),"no completed event into prime-root state");rootArrivalChecks++}
     let high=a&&b&&e.p>=Y&&e.p<=P;
     if(high){ok(e.p%4===1&&e.reset,"reset phase transition");let u=node(e.C,e.t),v=node(e.J,e.n);if(u.next===null){u.next=v.id;v.ins.add(u.id);edgeCount++}else ok(u.next===v.id,"deterministic reset successor");
      depth++;if(pure){rootGain+=e.g;pureWitness++;if(j===0)rootPrefix++}put(v,seed,depth,pure);resetPhaseChecks++;
     }else{pure=false;depth=0;seed=key(e.J,e.n);if(b)put(node(e.J,e.n),seed,0,false)}
    }
    // Flat high nonreset controls, with fixed ordinary d>6.
    for(let j=0;j<t.path.length;){let e=t.path[j];if(e.d!==e.dp||e.d<=6||e.p<Y){j++;continue}let k=j+1;while(k<t.path.length&&t.path[k].d===e.d&&t.path[k].dp===e.d&&t.path[k].p>=Y)k++;
     let q=t.path.slice(j,k),S=[...new Set(q.map(z=>z.p))],s=S.length,G=q.reduce((a,z)=>a+z.g,0),pairs=new Map();
     for(let n=0;n<q.length;n++){let z=q[n];ok(z.w*2===z.g&&((z.d-6*z.I)/2)%z.p===0,"flat high factor");if(n){let a=q[n-1];ok(a.p!==z.p,"flat distinct labels");let id=a.p+"/"+z.p,old=pairs.get(id)||{n:0,a:a.p,b:z.p,last:a.C};ok(!old.n||(a.C-old.last)%(a.p*z.p)===0,"flat pair spacing");old.last=a.C;old.n++;pairs.set(id,old);flatChecks++}}
     ok(G<=P+S.reduce((v,p)=>v+S.filter(r=>r!==p).reduce((z,r)=>z+(r-1)*(1+G/(p*r)),0),0)+1e-7,"flat local capacity");if(Y>=2*s*s)ok(G<=2*(1+s*(s-1))*P,"flat gain bound");flatRuns++;flatGain+=G;j=k;
    }
   }
   let dcap=Math.max(2,2*Math.floor(Math.log(7*X+2)/Math.log(Y)));
   for(let v of graph.values()){let I=(2*v.t-v.C)/6;ok(I===0||I===1,"phase vertex");ok(v.ins.size<=2*factorCount(v.C+2*I)&&v.ins.size<=dcap,"reverse divisor capacity");maxIn=Math.max(maxIn,v.ins.size);if(rootSet.has(v.id))ok(v.ins.size===0,"root leaf");
    let q=vis.get(v.id);if(!q)continue;
    if(q.pure.length){ok(q.pure.reduce((s,k)=>s+dcap**(-k),0)<=1+1e-8,"Kraft root bound");pureTargets++}
    let b=Math.max(...[...q.seeds.values()].map(z=>z.n));seedMax=Math.max(seedMax,b);seedTargets++;
    for(let k=0;k<=3;k++){let n=0,cap=0;for(let j=0;j<=k;j++)cap+=dcap**j;for(let z of q.seeds.values())if(z.depth<=k)n+=z.n;ok(n<=b*cap,"short reset suffix seed packing");seedNear+=n;seedChecks++}
   }
   ok(resetGain===firstGain+closeGain+tailGain&&tailGain<=Rw/(cut+1)+1e-7,"aggregate reset pair bound");
   out.push({X,focus,N,events,Y,P,H,dcap,vertices:graph.size,edgeCount,rootPrefix,rootGain,pureWitness,pureTargets,maxIn,rootArrivalChecks,resetPhaseChecks,seedChecks,seedNear,seedTargets,seedMax,resetGain,resetCount,firstGain,closeGain,tailGain,Rw,tupleChecks,pairChecks,maxSupport,supportSq,capacity,roughChecks,rootNear,rootFirst,rootShiftChecks,firstAgeSum,flatChecks,flatRuns,flatGain});
  }
 }
 return out
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
