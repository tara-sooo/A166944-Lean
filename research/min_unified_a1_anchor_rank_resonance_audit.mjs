// Actual prime-root controls for the A1 arrival-anchor correction, induced ranks and comparable-support leaves.
function audit(Xs=[4096,16384,65536]){
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(x,m)=>(x%m+m)%m;
 const lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1);
 for(let p=2;p<=lim;p++)if(!spf[p])for(let j=p;j<=lim;j+=p)spf[j]=p;
 const res=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),tags=[],slots=new Map(),nodes=[],events=0,reaches=0;
  const node=()=>{let n={id:nodes.length,members:new Set(),next:null};nodes.push(n);return n};
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let id=tags.length,C=2*M-2,C0=C,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity,I=0;for(let k=0;k<2;k++){let z=C-1+2*k;while(z>1){let q=spf[z];while(z%q===0)z/=q;if(q*q>C+1)continue;let v=mod((k?q+2:0)-t,2*q)||2*q;if(v<w||v===w&&q<p){p=q;w=v;I=k}}}if(!p)break;
    let n=t+w,J=C+p-1,d=2*t-C,dp=2*n-J,h=(dp-6*I)/(2*p),a1=p>=47&&p>=5*d+15&&h===1,key=C+"/"+p+"/"+n;
    if(!slots.has(key))slots.set(key,{node:node(),C,J,p,n,I,h,early:null,arr:new Map()});
    let s=slots.get(key);s.node.members.add(id);s.arr.set(id,{w,d,a1});
    if(a1){if(!s.early)s.early=node();s.early.members.add(id)}
    path.push({s,C,J,p,w,I,d,dp,h,a1,t,n});C=J;t=n;events++;
   }if(C-C0>=T)reaches++;tags.push(path)
  }
  function edge(a,b){ok(!a.next||a.next===b,"expanded unique successor");a.next=b}
  let mixed=0,early=0,mixedTags=0,allMarkWeight=0,mixedExample=null,waitChecks=0,rawPairs=0;
  for(let s of slots.values())if(s.early){early++;edge(s.early,s.node);let a=s.early.members.size,b=s.node.members.size;
   ok(a<=b&&[...s.early.members].every(i=>s.node.members.has(i)),"early subset");
   if(a<b){mixed++;mixedTags+=a;if(!mixedExample||a/b<mixedExample.early/mixedExample.full)mixedExample={C:s.C,p:s.p,n:s.n,early:a,full:b,arr:[...s.arr.values()].slice(0,10)}}
   for(let row of s.arr.values()){ok(2*row.w<=3*s.p+5,"h1 wait cap");waitChecks++}
   allMarkWeight+=a*s.p;rawPairs+=a*b
  }
  let chains=tags.map(path=>path.flatMap(e=>e.a1?[e.s.early,e.s.node]:[e.s.node]));
  let neg=0,pos=0,last=0,retired=0;
  for(let chain of chains){for(let j=1;j<chain.length;j++)edge(chain[j-1],chain[j]);if(chain.length){pos+=Math.log(chain[0].members.size);last+=Math.log(chain.at(-1).members.size)}}
  const v=new Map();for(let a of nodes)if(a.next){let b=a.next,r=[...a.members].filter(i=>b.members.has(i)).length;ok(r>0,"survivors");let loss=a.members.size-r;retired+=loss;let x=Math.log(a.members.size/r),y=Math.log(b.members.size/r);neg+=r*x;pos+=r*y;v.set(a.id,x+y)}
  ok(neg<=retired+1e-7&&retired<=tags.length&&Math.abs(pos-neg-last)<1e-6&&pos+neg<=tags.length*(Math.log(tags.length)+2)+1e-6,"expanded variation");
  let controls=[];
  for(let eps of [.1,.25]){let dom=new Map(),src=new Map(),checks=0,matched=0,unstable=0,stable=0,partnerLoss=0,rankCount=0,rankCut=0,slotLevelMass=0,markLevelMass=0;
   for(let i=0;i<tags.length;i++){let path=tags[i],chain=chains[i],prefix=new Map(),sum=0;for(let j=0;j<chain.length;j++){prefix.set(chain[j].id,sum);if(j+1<chain.length)sum+=v.get(chain[j].id)}
    let pend=[];
    for(let e of path){if(e.dp<e.d){let next=[];for(let m of pend){let lo=Math.max(m.lo,5*(e.dp+3)),hi=Math.min(m.hi,5*(e.d+3));if(hi<=lo){next.push(m);continue}let len=hi-lo;matched+=len;if(lo>m.lo)next.push({...m,hi:lo});
      let variation=prefix.get(e.s.node.id)-prefix.get(m.s.early.id);if(variation>eps){unstable+=len;continue}
      let A=m.s.early.members,S=e.s.node.members,r=[...A].filter(j=>S.has(j)).length,delta=Math.exp(eps)*eps;
      ok(A.size+S.size-2*r<=Math.min(A.size,S.size)*Math.exp(variation)*variation+1e-6,"early/provider overlap");stable+=len;partnerLoss+=len*(m.s.node.members.size-r)/m.s.node.members.size;checks++;
      ok(r>S.size/2,"early dominance");for(let y=lo+1;y<=hi;y++){let key=e.s.node.id+"/"+y,sk=m.s.node.id+"/"+y,old=dom.get(key),oldV=src.get(sk);
       ok(!old||old.m===m.s,"unique early ancestor");ok(!oldV||oldV===e.s.node,"unique provider");src.set(sk,e.s.node);
       if(!old){dom.set(key,{m:m.s,V:e.s.node});slotLevelMass+=S.size;markLevelMass+=m.s.early.members.size}}
    }pend=next}
    if(e.a1){let lo=e.p,hi=5*e.p;ok(!pend.some(m=>Math.min(m.hi,hi)>Math.max(m.lo,lo)),"pending disjoint");pend.push({lo,hi,s:e.s})}
   }}
   ok(matched===stable+unstable,"transport partition");ok(slotLevelMass<=Math.exp(eps)*markLevelMass+1e-6&&markLevelMass<=4*allMarkWeight+1e-6,"provider level mass");
   ok(partnerLoss<=2*Math.exp(eps)*eps*stable+1e-6,"partner loss");
   let unique=new Map();for(let z of dom.values())unique.set(z.V.id,z.V);
   const present=(id,C,t)=>tags[id].some(e=>(e.C===C&&e.t<=t&&t<e.n)||(e.J===C&&e.n===t));
   function birth(i,j){let a=tags[i],b=tags[j],u=0,k=0,best=null;
    // All actual common occupied plateau intervals and completed poststates.
    for(let x of a)for(let y of b){if(x.C===y.C){let t=Math.max(x.t,y.t);if(t<Math.min(x.n,y.n)&&(!best||t<best.t))best={C:x.C,t}}
     if(x.J===y.J&&x.n===y.n&&(!best||x.n<best.t))best={C:x.J,t:x.n};
     if(x.J===y.C&&y.t<=x.n&&x.n<y.n&&(!best||x.n<best.t))best={C:x.J,t:x.n};
     if(y.J===x.C&&x.t<=y.n&&y.n<x.n&&(!best||y.n<best.t))best={C:y.J,t:y.n};
    }return best
   }
   for(let V of [...unique.values()].slice(0,100)){let ids=[...V.members].sort((a,b)=>a-b),b=ids.length;if(b<2)continue;let bad=0,rho=.25;
    for(let a=0;a<b;a++)for(let c=a+1;c<b;c++){let z=birth(ids[a],ids[c]);ok(z,"actual first meeting");let tail=ids.slice(a).filter(j=>present(j,z.C,z.t)).length,pre=ids.slice(0,c+1).filter(j=>present(j,z.C,z.t)).length;rankCount++;if(tail<rho*b||pre<rho*b)bad++}
    ok(2*bad<=4*rho*b*b+1e-8,"rank bound");rankCut+=2*bad
   }
   controls.push({eps,matched,unstable,stable,checks,dominant:dom.size,partnerLoss,slotLevelMass,markLevelMass,rankCount,rankCut})
  }
  // Actual bounded comparable support leaves in disjoint 24-event blocks.
  let leafChecks=0,smallLeaves=0,twoLeaves=0,smallLeafExamples=[];
  for(let path of tags)for(let start=0;start<path.length;start+=24){let block=path.slice(start,start+24);
   for(let Z=8;Z<=B;Z*=2){let all=[...new Set(block.filter(e=>e.p>=Z&&e.p<2*Z).map(e=>e.p))].sort((a,b)=>a-b),F=[];let prod=1;
    for(let p of all)if(F.length<5&&prod*p<=4*(T+B)){F.push(p);prod*=p}
    if(F.length<2)continue;let word=block.map((e,j)=>({e,j})).filter(z=>F.includes(z.e.p)),nodes=[];
    for(let i=0;i<word.length;i++){let p=word[i].e.p;for(let j=i+1;j<word.length;j++){let q=word[j].e.p;if(q>p)break;if(q===p){nodes.push([i,j]);break}}}
    for(let [i,j] of nodes)for(let [a,b] of nodes)ok(!(i<a&&a<j&&j<b),"laminar");
    let leaves=nodes.filter(([i,j])=>!nodes.some(([a,b])=>i<=a&&b<=j&&(i<a||b<j))).sort((a,b)=>a[0]-b[0]);
    for(let k=0;k<leaves.length;k++){let [i,j]=leaves[k];if(k)ok(leaves[k-1][1]<=i,"disjoint leaves");
     let w=word.slice(i,j+1),p=w[0].e.p,C=w[0].e.C,end=w.at(-1).e.C,m=j-i,E=end-C-w.slice(0,-1).reduce((s,z)=>s+z.e.p-1,0),labels=[...new Set(w.map(z=>z.e.p))],l=labels.length;
     ok(E>=0&&E%2===0&&m<=2**(l-1),"leaf size");leafChecks++;
     if(E<=2&&E<Z-1){smallLeaves++;ok(l>=2,"nonempty interior");if(l===2){twoLeaves++;let q=labels.find(q=>q!==p);ok(p-q<=E,"two label close")}
      if(smallLeafExamples.length<3)smallLeafExamples.push({Z,C,end,E,labels,w:w.map(z=>z.e.p)})
     }
    }
   }
  }
  res.push({X,focus,T,N:tags.length,events,reaches,slots:slots.size,early,mixed,mixedTags,mixedExample,waitChecks,rawPairs,neg,pos,retired,controls,leafChecks,smallLeaves,twoLeaves,smallLeafExamples})
 }
 ok(res.some(x=>x.mixed>0)&&res.some(x=>x.controls.some(c=>c.dominant>0)),"coverage");
 return res
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
