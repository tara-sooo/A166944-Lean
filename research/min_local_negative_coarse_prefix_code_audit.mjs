// Coarse inverse code: compress adjacent-cell exits and encode nonadjacent source-cell ranks.
// node research/min_local_negative_coarse_prefix_code_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+5),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},add=(m,k,v=1)=>m.set(k,(m.get(k)||0)+v),f=x=>x?x*Math.log(x):0;
 let rows=[];
 for(let R of Rs){
  const S=Math.sqrt(2*R+1),T=Math.ceil(S),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1,B=2*T+6,L=Math.log(S);
  const q=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1),cost=a=>{let t=Math.log(Math.min(S,q(a))),d=L-t;return 2*Math.log(L/t)+Math.log1p(d)+2*Math.log1p(Math.log1p(d))};
  let stats=[6,30,210].map(Q=>({Q,M:Q/6,candidates:new Map(),controls:[1,2,4,8,Infinity].map(K=>({K,maps:new Map(),cells:new Map(),codes:new Map(),penalty:0,codelen:0,rank:0,gap:0,depth:0,large:0,adj:0,checks:0,weighted:new Map()}))}));
  function candidates(s,j){
   let c=s.candidates.get(j);if(c)return c;
   let {Q}=s,arr=new Set();
   for(let b=Math.max(4,j*Q);b<(j+1)*Q&&b<=hi;b+=2)
    for(let p of [...fs(b),...fs(b-2)])if(p>Q&&p-1<=B){let a=b+p-1,i=Math.floor(a/Q);if(a<=hi&&i>j+1)arr.add(i);}
   c=[...arr].sort((a,b)=>a-b);s.candidates.set(j,c);return c;
  }
  let checks=0,roots=0,events=0;
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,end=n+T,path=[A];
   for(;;){let e=next(a,n),fire=n+e.w;if(fire>end)break;a-=e.p-1;n=fire;path.push(a);events++}
   roots++;
   for(let s of stats){
    let cell=x=>Math.floor(x/s.Q),seq=[cell(A)],best=A,records=[];
    // Save the best roughness in first K cells (or full prefix if fewer).
    for(let x of path){
     let j=cell(x);
     if(j!==seq.at(-1)){seq.push(j);}
     if(q(x)>q(best))best=x;
     records.push({x,best,k:seq.length-1});
    }
    for(let c of s.controls){
     let rec=records.filter(z=>z.k<c.K).at(-1),X=rec.best,j=cell(X),prefix=seq.slice(0,seq.indexOf(j)+1);
     ck(prefix.at(-1)===j&&prefix[0]===cell(A),"prefix");
     let gaps=[0],non=[];
     for(let i=prefix.length-1;i>0;i--){let b=prefix[i],a=prefix[i-1];if(a===b+1)gaps[gaps.length-1]++;else{non.push({b,a});gaps.push(0);}}
     let y=j,rank=0,ranks=[];
     for(let i=0;i<non.length;i++){y+=gaps[i];ck(y===non[i].b,"adjacent run");let cand=candidates(s,y),k=cand.indexOf(non[i].a);ck(k>=0,["source rank",s.Q,A,X,y,non[i].a]);rank+=Math.log(cand.length);ranks.push(k);y=cand[k];}
     y+=gaps.at(-1);ck(y===cell(A),"decode");
     // Probability of k nonadjacent transitions: 1/((k+1)(k+2)).
     // Each adjacent-run length g has probability 1/((g+1)(g+2)).
     // Each nonadjacent source cell has uniform probability among arithmetic candidates.
     const gc=g=>Math.log(g+1)+Math.log(g+2);
     let gapCost=gc(non.length)+gaps.reduce((v,g)=>v+gc(g),0),length=Math.log(s.M)+gapCost+rank;
     let key=gaps.join(",")+"|"+ranks.join(",")+"|"+((A%s.Q)/6);
     let p=Math.exp(-length),m=c.codes.get(j)||new Map();m.set(key,p);c.codes.set(j,m);
     add(c.maps,X);add(c.cells,j);c.penalty+=cost(X);c.codelen+=length;c.rank+=rank;c.gap+=gapCost;c.depth+=prefix.length-1;c.large+=non.length;c.adj+=gaps.reduce((a,b)=>a+b,0);c.checks++;checks++;
     c.weighted.set(X,(c.weighted.get(X)||0)+p);
    }
   }
  }
  const output=[];
  for(let s of stats){
   for(let c of s.controls){
    for(let m of c.codes.values())ck([...m.values()].reduce((a,b)=>a+b,0)<=1+1e-8,"Kraft");
    const h=[...c.maps.values()].reduce((a,b)=>a+f(b),0)/N,hc=[...c.cells.values()].reduce((a,b)=>a+f(b),0)/N,penalty=c.penalty/N,code=c.codelen/N;
    ck(h<=hc+1e-8&&hc<=code+1e-8,"entropy bound");
    let support=0,weighted=0;
    for(let [X,z] of c.weighted){ck(z<=1+1e-8,"fiber mass");support+=Math.exp(-cost(X));weighted+=z*Math.exp(-cost(X));}
    ck(weighted<=support+1e-8&&N*Math.exp(-code-penalty)<=weighted+1e-8,"weighted Jensen");
    output.push({Q:s.Q,K:Number.isFinite(c.K)?c.K:"all",h,hc,penalty,score:h+penalty,code,codeScore:code+penalty,meanRank:c.rank/N,meanGap:c.gap/N,meanDepth:c.depth/N,meanLarge:c.large/N,meanAdjacent:c.adj/N,support,weighted,checks:c.checks});
   }
  }
  rows.push({R,N,roots,events,checks,output});
 }
 return rows
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000]),null,2));
