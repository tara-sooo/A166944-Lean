// Clock-block reverse decoding: truncated subtree weights and Kraft support certificates, with retirement filtering.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=1000005,spf=new Int32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let x=p*p;x<=N;x+=p)if(!spf[x])spf[x]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function clocks(a){return [...fs(a+1).filter(q=>q>2).map(p=>[p,0]),...fs(a-1).filter(q=>q>2).map(p=>[p,p+2])]}
 function next(a,n){let p=Infinity,w=Infinity;for(let [q,c] of clocks(a)){let v=mod(c-n,2*q)||2*q;if(v<w||v===w&&q<p){p=q;w=v}}return {p,w}}
 const f=x=>x?x*Math.log(x):0;
 let z={roots:0,events:0,selected:0,endpointTrees:0,clockBlocks:0,candidates:0,actualBranches:0,actualBirths:0,kraftChecks:0,exactTreeChecks:0,rows:[]};
 for(let R of [12000,48000,192000,480000]){
  let K=Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),T=4*K,J=Math.floor(T/5),H=Math.floor(3+T-J/2),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nr=(hi-lo)/6+1,endpoints=new Map(),badCount=0;
  for(let a=2*Math.ceil((lo-2*T-6)/2);a<=hi;a+=2){let p=spf[a-1]||a-1,q=spf[a+1]||a+1;if(p>K&&q>K&&(p!==a-1||q!==a+1))badCount++}
  let ns=0;
  for(let A=lo;A<=hi;A+=6){let a=A,n=3-A/2,end=n+T,path=[];
   for(;;){let e=next(a,n);if(n+e.w>end)break;n+=e.w;let b=n+a/2;path.push({a,u:b-1,p:e.p});a-=e.p-1;z.events++}
   z.roots++;if(A-a>J)continue;let v=endpoints.get(a)||[];v.push({A,path});endpoints.set(a,v);ns++;z.selected++;
  }
  let depth=4,E=Array(depth+1).fill(0),W=Array(depth+1).fill(0),maxCost=Array(depth+1).fill(0),L=0,branchRatios=Array(depth+1).fill(0),firstTerms=Array(depth+1).fill(0),maxNodes=0,meanNodes=0,exactMass=0;
  for(let [a0,paths] of endpoints){
   let Amax=Math.min(hi,a0+J),Bnext=H+next(a0,H-a0/2).w,Amin=Math.max(lo,a0+2*(3+T-Bnext)+2),nodes=new Map(),root;
   function node(a,u){
    let key=a+":"+u;if(nodes.has(key))return nodes.get(key);
    let d=0;for(let [p,c] of clocks(a))d=Math.max(d,u-mod(u-a/2-c,2*p));
    let birth=+(a>=Amin&&a<=hi&&a%6===0&&d<=3&&3<=u),children=[],g=Amax-a,hmax=Math.min(u,Math.floor(11+7*g/4));
    for(let [p,c] of [...fs(a).filter(p=>p>2).map(p=>[p,0]),...fs(a-2).filter(p=>p>2).map(p=>[p,p+2])]){
     let b=a+p-1;if(b>Amax)continue;let k=(p-1)/2,hh=Math.min(hmax,H-k,Math.floor(35*(g+10)/18)-k);
     for(let h=d+mod(c+a/2-d,2*p);h<=hh;h+=2*p){let n=h-a/2,p0=Infinity;
      for(let [q,c1] of clocks(b))if(mod(n-c1,2*q)===0)p0=Math.min(p0,q);
      if(p0!==p)continue;children.push({a:b,u:h+k-1});z.candidates++;
     }
    }
    let v={a,u,birth,children,M:[1],exact:null};nodes.set(key,v);z.clockBlocks++;return v
   }
   function M(v,d){if(v.M[d]!==undefined)return v.M[d];let m=v.birth;for(let c of v.children)m+=M(node(c.a,c.u),d-1);v.M[d]=m;return m}
   function exact(v){if(v.exact!==null)return v.exact;let m=v.birth;for(let c of v.children)m+=exact(node(c.a,c.u));return v.exact=m}
   root=node(a0,H);let S=Array(depth+1).fill(0);L+=f(paths.length);
   if(a0%97===0){let m=exact(root);ck(m===paths.length,{a0,m,paths:paths.length,Amin,Bnext});z.exactTreeChecks++;exactMass+=m}
   for(let {A,path} of paths){
    let v=root,cost=Array(depth+1).fill(0),first=Array(depth+1).fill(0);
    for(let d=0;d<=depth;d++)first[d]=Math.log(M(root,d+1));
    for(let i=path.length-1;i>=0;i--){
     let a=path[i].a,u=path[i].u;ck(v.children.some(c=>c.a===a&&c.u===u),{A,a0,a,u,from:[v.a,v.u]});z.actualBranches++;
     let w=node(a,u);
     for(let d=0;d<=depth;d++){let top=M(v,d+1),bot=M(w,d);ck(top>=bot&&bot>0,"positive weight");cost[d]+=Math.log(top/bot)}
     v=w
    }
    ck(v.a===A&&v.birth===1,"birth");z.actualBirths++;
    for(let d=0;d<=depth;d++){cost[d]+=Math.log(M(v,d+1));S[d]+=Math.exp(-cost[d]);E[d]+=cost[d];W[d]+=Math.exp(-cost[d]);maxCost[d]=Math.max(maxCost[d],cost[d]);firstTerms[d]+=first[d];branchRatios[d]+=cost[d]-first[d]}
   }
   ck(S.every(w=>w<=1+1e-8),"Kraft");z.kraftChecks++;z.endpointTrees++;maxNodes=Math.max(maxNodes,nodes.size);meanNodes+=nodes.size;
  }
  L/=ns;E=E.map(x=>x/ns);ck(E.every(x=>x>=L-1e-8)&&W.every(x=>x<=endpoints.size+1e-7),"global");
  z.rows.push({R,K,T,J,H,nr,ns,distinct:endpoints.size,badCount,L,entropySupport:ns*Math.exp(-L),depthCost:E,depthWeight:W,maxCost,meanRootTerm:firstTerms.map(x=>x/ns),meanRatioTerm:branchRatios.map(x=>x/ns),meanNodes:meanNodes/endpoints.size,maxNodes,exactMass})
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
