// Reverse spatial ancestor graph, stationary-walk degree moments, and compressed low-label runs.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=2200000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let a=p*p;a<=N+2;a+=p)spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function ev(a,v){let p=Infinity,w=Infinity;for(let [d,c] of [[a+1,0],[a-1,2]])for(let q of fs(d)){let t=mod((c===0?0:q+2)-v,2*q)||2*q;if(t<w||t===w&&q<p){p=q;w=t}}return {p,w}}
 function wall(P){let Q=P.reduce((a,b)=>a*b,1),W=[];for(let x=0;x<Q;x++)if(P.every(p=>mod(-x,p)<=(p-3)/2))W.push(x);let M=1;for(let i=0;i<W.length;i++)M=Math.max(M,(W[i+1]??Q)-W[i]);return {Q,M}}
 const low=[3,5],M=wall(low).M;ck(M===9,"wall gap");
 let s={roots:0,events:0,successes:0,badSuccesses:0,graphControls:0,edges:0,degreeChecks:0,walkMomentChecks:0,restrictedMomentChecks:0,actualPathChecks:0,macroPathChecks:0,lowRunChecks:0,basinChecks:0,rows:[],graphs:[]};
 for(let R of [3000,12000,48000,192000,480000,1000000]){
  let K=Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),H=4*K,L=Math.floor(H/4),lo=2*Math.ceil((R-L)/2),hi=2*R,nn=(hi-lo)/2+1;
  const isBad=a=>{let x=fs(a-1),y=fs(a+1);return x.length>1||y.length>1||x[0]!==a-1||y[0]!==a+1};
  let bad=new Set();for(let a=lo;a<=hi;a+=2){let q=Math.min(...fs(a-1),...fs(a+1));if(q>9*H/32-7&&isBad(a))bad.add(a)}
  let rec=[],hist={},maxDepth=0,success=0,bads=0,counts=new Map();
  for(let A=6*Math.ceil(R/6);A<=2*R;A+=6){
   let a=A,v=3-A/2,h=3,g=0,d=0,high=0,run=0,path=[A],macro=[A],anchor=A;
   while(true){let e=ev(a,v);if(h+e.w>H){
    ck(g<=L&&h<H,"pass");ck(run<2*M,"terminal low run");s.lowRunChecks++;
    if(macro.at(-1)!==a)macro.push(a);
    ck(macro.length<=high+2,"compressed length");
    success++;s.successes++;let b=isBad(a);if(b){ck(bad.has(a),"bad subset");bads++;s.badSuccesses++}
    let m=counts.get(a)||{all:0,bad:b,depth:new Array(7).fill(0),macro:new Array(7).fill(0)};m.all++;for(let k=0;k<=6;k++){if(d<=k)m.depth[k]++;if(high+1<=k)m.macro[k]++}counts.set(a,m);
    maxDepth=Math.max(maxDepth,d);
    let key=d+":"+high,old=hist[key]||[0,0];old[b?1:0]++;hist[key]=old;
    if(R<=48000)rec.push({A,a,path,macro,d,high,b});break}
    if(g+e.p-1>L)break;
    if(e.p<=5){run+=e.p-1;ck(run<2*M,"low wall run");s.lowRunChecks++}
    else{high++;run=0;anchor=a-e.p+1;macro.push(anchor)}
    a-=e.p-1;v+=e.w;h+=e.w-(e.p-1)/2;g+=e.p-1;d++;path.push(a);s.events++;
   }s.roots++;
  }
  let row={R,H,L,success,bads,distinct:counts.size,badDistinct:[...counts.values()].filter(x=>x.bad).length,badCandidates:bad.size,maxDepth,maxBadMass:0,maxTwinMass:0,energyBad:0,energyTwin:0,depth:[],macro:[]};
  for(let m of counts.values()){if(m.bad){row.energyBad+=m.all*m.all;row.maxBadMass=Math.max(row.maxBadMass,m.all)}else{row.energyTwin+=m.all*m.all;row.maxTwinMass=Math.max(row.maxTwinMass,m.all)}}
  for(let k=0;k<=6;k++)for(let key of ["depth","macro"]){let mass=0,C=0,all=0;for(let m of counts.values()){let n=m[key][k];all+=n;if(m.bad){mass+=n;C+=n*n}}row[key].push({k,mass,C,all});}
  ck(row.energyBad>=bads&&row.energyBad<=bads*(Math.floor(L/6)+1),"bad energy bounds");s.basinChecks++;
  if(R<=48000)for(let kind of ["ordinary","macro"]){
   let adj=Array.from({length:nn},(_,i)=>new Set([i]));const id=a=>(a-lo)/2;
   function link(a,b){if(a===b||b<lo||a>hi||a-b>L)return;let i=id(a),j=id(b);adj[i].add(j);adj[j].add(i)}
   for(let a=lo;a<=hi;a+=2){if(kind==="ordinary"){for(let p of [...fs(a-1),...fs(a+1)])link(a,a-p+1)}
    else{for(let d=0;d<=2*(M-1)&&d<=L&&a-d>=lo;d+=2){if(d)link(a,a-d);for(let p of [...fs(a-d-1),...fs(a-d+1)])if(p>5)link(a,a-d-p+1)}}
   }
   let D=adj.map(x=>x.size);s.edges+=D.reduce((a,b)=>a+b,0);for(let a=lo;a<=hi;a+=2){let bound=1+fs(a-1).length+fs(a+1).length+fs(a).length+fs(a-2).length;
    if(kind==="macro"){bound=1+2*(M-1)+M*(fs(a).length+fs(a-2).length);for(let d=0;d<=2*(M-1);d+=2)bound+=fs(a-d-1).length+fs(a-d+1).length}
    ck(D[id(a)]<=bound,"degree envelope");s.degreeChecks++}
   for(let r of rec){let path=kind==="ordinary"?r.path:r.macro;for(let i=1;i<path.length;i++){ck(adj[id(path[i-1])].has(id(path[i])),"ancestor path cover");if(kind==="ordinary")s.actualPathChecks++;else s.macroPathChecks++}}
   let F=new Float64Array(nn).fill(1),mom=[];
   for(let d=1;d<=6;d++){let V=new Float64Array(nn);for(let i=0;i<nn;i++)for(let j of adj[i])V[i]+=F[j];F=V;
    for(let q of [1,2,3,4,8]){let lhs=0,rhs=0;for(let i=0;i<nn;i++){lhs+=F[i]**q;rhs+=D[i]**(d*q)}ck(lhs<=rhs*(1+1e-9),"walk moment");s.walkMomentChecks++;
     for(let k of [1,2])if(q>=k){let x=0;for(let a of bad)x+=F[id(a)]**k;let bound=bad.size?bad.size**(1-k/q)*rhs**(k/q):0;ck(x<=bound*(1+1e-9),"restricted moment");s.restrictedMomentChecks++;}
    }
    for(let [a,m] of counts){let n=kind==="ordinary"?m.depth[d]:m.macro[d];ck(n<=F[id(a)],"walk majorant");s.basinChecks++}
    mom.push({d,maxWalk:Math.max(...F),degreeMomentRoot:D.reduce((a,b)=>a+b**(2*d),0)**(1/(2*d)),meanWalk:F.reduce((a,b)=>a+b,0)/nn});
   }
   s.graphControls++;s.graphs.push({R,kind,nn,maxDegree:Math.max(...D),mom})
  }
  s.rows.push(row);
 }
 return s
}
console.log(JSON.stringify(audit(),null,2));
