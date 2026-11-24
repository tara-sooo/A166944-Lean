// Node.js: first physical/clock saturation classification in selected-key absorbed MIN.
function audit(X) {
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,cap=Math.max(2,Math.floor(B/4)),spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=x=>{if(!x)throw Error("assertion")},mod=(x,m)=>(x%m+m)%m,gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return a};
 function hit(t,C,K){let u=K+1,q=0;for(let s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let h=t+1+mod((s===-1?0:p+2)-t-1,2*p);if(h<u||(h===u&&p<q)){u=h;q=p}while(v%p===0)v/=p}}return [u,q]}
 const names=["never","clock_top_pair","clock_root_top","clock_short_other","clock_long","vertex_top_pair","vertex_root_top","vertex_other"];
 const modes=[[8,Math.max(11,Math.ceil(Math.sqrt(B))),31],[32,Math.max(11,Math.ceil(Math.sqrt(B))),31],[8,Math.max(11,Math.ceil(B/Math.log(B)**.25)),31]].map(([k,Q,z])=>({k,Q,z,first:new Uint8Array(N),counts:Array(8).fill(0),stopCounts:Array(8).fill(0),topStopCounts:Array(8).fill(0),topStops:0,topLight:0,topStopKeys:0,topLightClockGroups:0,clockPairs:0,rootPairs:0,vertexTop:0,vertexRoot:0,vertexTopClassBound:0,vertexRootClassBound:0,rareClockNew:0,rareVertexNew:0}));
 const head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N).fill(-1),t=new Int32Array(N),K=new Int32Array(N),last=new Int32Array(N);
 function push(i,C){next[i]=head[C/2];head[C/2]=i}
 for(let i=0;i<N;i++){let M=X+2*i+1;t[i]=M+2;K[i]=Math.floor((7*M-1)/4);push(i,2*M-2)}
 function set(m,i,c){ck(m.first[i]===0);m.first[i]=c;m.counts[c]++}
 let R=0,events=0,stopped=0,sinks=0,twin=0,bad=0,literal=0,maxPhysical=0,maxClock=0,maxPassed=0;
 for(let C=2*X;C<7*X;C+=2){
  let i=head[C/2];if(i<0)continue;const parents=new Map(),keys=new Map(),clocks=new Map(),r=Math.min(spf[C-1],spf[C+1]);
  while(i>=0){let j=next[i];if(!parents.has(t[i]))parents.set(t[i],[]);parents.get(t[i]).push(i);i=j}
  for(let [u,a] of parents){
   maxPhysical=Math.max(maxPhysical,a.length);
   for(let m of modes)if(a.length>=m.k){
    let by=new Map();for(let i of a)by.set(last[i],(by.get(last[i])||0)+1);
    let top=[...by.keys()].filter(p=>p>=m.Q),root=by.has(0);if(top.length>=2){m.vertexTop++;m.vertexTopClassBound+=(m.k-1)*top.length}if(root&&top.length){m.vertexRoot++;m.vertexRootClassBound+=(m.k-1)*top.length+1}
    for(let i of a)if(!m.first[i]){
     ck(by.get(last[i])<m.k);
     let c=last[i]>=m.Q&&top.length>=2?5:(root&&top.length&&(last[i]===0||last[i]>=m.Q))?6:7;
     set(m,i,c);if(c===5||c===6)m.rareVertexNew++;
    }
   }
   for(let i of a){let [n,p]=hit(u,C,K[i]);if(X<=1024){let nn=K[i]+1,pp=0;for(let j=u+1;j<=K[i];j++){let g=gcd(j%2?j-2:j,C+(j%2?1:-1));if(g>1&&spf[g]<=B){nn=j;pp=spf[g];break}}ck(n===nn&&p===pp);literal++}
    if(!p){if(spf[C-1]===C-1&&spf[C+1]===C+1)twin++;else bad++;continue}
    ck(n-u<=2*r);let key=p,clock=n*B+p;if(!keys.has(key))keys.set(key,[]);if(!clocks.has(clock))clocks.set(clock,{n,p,a:[]});keys.get(key).push(i);clocks.get(clock).a.push(i)
   }
  }
  for(let {n,p,a} of clocks.values()){
   maxClock=Math.max(maxClock,a.length);
   for(let m of modes)if(a.length>=m.k){
    const qual=new Map();for(let i of a)if(last[i]>=m.Q||last[i]===0){if(!qual.has(t[i]))qual.set(t[i],{top:new Set(),root:false});let q=qual.get(t[i]);if(last[i]===0)q.root=true;else q.top.add(last[i])}
    let pairsTop=new Set(),pairsRoot=new Set();
    if(r<=m.z){
     let list=[...qual.entries()];for(let j=0;j<list.length;j++)for(let l=j+1;l<list.length;l++){
      let [u,A]=list[j],[v,D]=list[l];ck(Math.abs(u-v)<2*r);
      if(A.top.size&&D.top.size){if(m.Q>m.z)for(let q of A.top)ck(!D.top.has(q));pairsTop.add(u);pairsTop.add(v);m.clockPairs++}
      if((A.root&&D.top.size)||(D.root&&A.top.size)){if(m.Q>2*m.z+6){let rt=A.root?u:v,ot=A.root?v:u;ck(ot===rt-3)}pairsRoot.add(u);pairsRoot.add(v);m.rootPairs++}
     }
    }
    for(let i of a)if(!m.first[i]){ck(parents.get(t[i]).length<m.k);let c=r>m.z?4:pairsTop.has(t[i])?1:pairsRoot.has(t[i])?2:3;set(m,i,c);if(c===1||c===2)m.rareClockNew++}
   }
  }
  for(let [p,a] of keys){
   if(p>7&&a.length>=cap){
    stopped+=a.length;sinks++;
    for(let m of modes){if(p>=m.Q)m.topStopKeys++;for(let i of a){m.stopCounts[m.first[i]]++;if(p>=m.Q){m.topStops++;m.topStopCounts[m.first[i]]++;if(!m.first[i])m.topLight++}}if(p>=m.Q)for(let v of clocks.values())if(v.p===p&&v.a.length<m.k)m.topLightClockGroups++}
   }else{
    if(p>7)maxPassed=Math.max(maxPassed,a.length);
    for(let i of a){let [n,q]=hit(t[i],C,K[i]);ck(q===p);R+=r;events++;t[i]=n;last[i]=p;ck(C+p-1<=2*n);push(i,C+p-1)}
   }
  }
 }
 ck(stopped+twin+bad===N&&maxPassed<cap);
 for(let m of modes){
  m.counts[0]=N-m.counts.slice(1).reduce((a,b)=>a+b,0);ck(m.stopCounts.reduce((a,b)=>a+b,0)===stopped);ck(m.topStopCounts.reduce((a,b)=>a+b,0)===m.topStops);
  ck(m.rareClockNew<=2*(m.k-1)*(m.clockPairs+m.rootPairs));
  ck(m.rareVertexNew<=m.vertexTopClassBound+m.vertexRootClassBound);
  ck(m.topLight<=m.topLightClockGroups*(m.k-1));
  delete m.first;
 }
 return {X,B,N,cap,R,events,stopped,sinks,twin,bad,literal,maxPhysical,maxClock,maxPassed,names,modes};
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
