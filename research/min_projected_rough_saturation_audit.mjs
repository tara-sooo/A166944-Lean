// Exact projected high-key first saturation and same-parent clock compression audit.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,L=210,cap=Math.max(2,Math.floor(B/4)),spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=b=>{if(!b)throw Error("assertion")},mod=(x,m)=>(x%m+m)%m,gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return a};
 function hit(t,C,K){let u=K+1,q=0;for(let s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let h=t+1+mod((s===-1?0:p+2)-t-1,2*p);if(h<u||(h===u&&p<q)){u=h;q=p}while(v%p===0)v/=p}}return [u,q]}
 function lastClock(n,C){let a=-Infinity;for(let s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let phase=s===-1?0:p+2;a=Math.max(a,n-1-mod(n-1-phase,2*p));while(v%p===0)v/=p}}return a}
 const modes=[[8,Math.max(37,Math.ceil(Math.sqrt(B))),31],[32,Math.max(37,Math.ceil(Math.sqrt(B))),31],[8,Math.max(37,Math.ceil(B/Math.log(B)**.25)),31],[8,Math.max(37,Math.ceil(B*Math.exp(-Math.sqrt(Math.log(B))))),Math.ceil(Math.exp(Math.sqrt(Math.log(B))))]].map(([k,Q,Z])=>({k,Q,Z,mark:new Uint8Array(N),first:Array(5).fill(0),stopFirst:Array(5).fill(0),firstTop:0,firstComparable:0,firstRoots:0,roughKeys:0,roughStopTags:0,roughStopUnmarkedBefore:0,roughStopMarkedEarlier:0,roughStopMarkedHere:0,roughWitnessStopTags:0,roughWitnessStopMarkedHere:0,firstMarkKeys:0,firstMarkMass:0,rareClassChecks:0}));
 const head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N),t=new Int32Array(N),K=new Int32Array(N),prevP=new Int32Array(N),prevD=new Int32Array(N),prevR=new Int32Array(N),prevMass=new Int32Array(N),last=new Int32Array(N),initial=i=>2*X+4*i;
 function push(i,C){next[i]=head[C/2];head[C/2]=i}
 for(let i=0;i<N;i++){let M=X+2*i+1;t[i]=M+2;K[i]=Math.floor((7*M-1)/4);push(i,initial(i))}
 let R=0,events=0,stopped=0,sinks=0,twin=0,bad=0,literal=0,maxPassed=0;
 let clock={groups:0,multi:0,parentLabelMulti:0,allParentLabelMulti:0,maxTimes:0,maxRatio:0,ratios:[0,0,0,0,0],sameQWitnessTags:0,examples:[]};
 for(let C=2*X;C<7*X;C+=2){
  let i=head[C/2];if(i<0)continue;let keys=new Map(),clocks=new Map(),r=Math.min(spf[C-1],spf[C+1]);
  while(i>=0){let j=next[i],[n,p]=hit(t[i],C,K[i]);if(X<=1024){let nn=K[i]+1,pp=0;for(let k=t[i]+1;k<=K[i];k++){let g=gcd(k%2?k-2:k,C+(k%2?1:-1));if(g>1&&spf[g]<=B){nn=k;pp=spf[g];break}}ck(n===nn&&p===pp);literal++}
   if(!p){if(spf[C-1]===C-1&&spf[C+1]===C+1)twin++;else bad++}
   else{ck(n-t[i]<=2*r);if(!keys.has(p))keys.set(p,[]);keys.get(p).push([i,n]);let k=n*B+p;if(!clocks.has(k))clocks.set(k,{n,p,a:[]});clocks.get(k).a.push(i)}
   i=j
  }
  for(let {n,p,a} of clocks.values()){
   clock.groups++;let by=new Map();for(let i of a){let q=last[i];if(q){if(!by.has(q))by.set(q,new Set());by.get(q).add(t[i])}}
   let any=false,ell=lastClock(n,C),w=n-ell;ck(w<=2*r);
   for(let [q,s] of by){let m=s.size;for(let u of s)ck(ell<=u&&u<n);ck(m<=Math.ceil(w/(2*q)));if(m>1){ck(q<r);any=true;clock.parentLabelMulti++;clock.maxTimes=Math.max(clock.maxTimes,m);clock.maxRatio=Math.max(clock.maxRatio,r/q);clock.ratios[Math.min(4,Math.floor(Math.log2(r/q)))]++;for(let i of a)if(last[i]===q)clock.sameQWitnessTags++;if(clock.examples.length<6)clock.examples.push({C,p,q,n,r,w,m,mass:a.length})}}
   if(any){clock.multi++;if(by.size===1&&a.every(i=>last[i]))clock.allParentLabelMulti++}
  }
  for(let [p,a] of keys){
   if(p<=7){for(let [i,n] of a){R+=r;events++;t[i]=n;last[i]=p;ck(C+p-1<=2*n);push(i,C+p-1)}continue}
   const classes=new Map(),rootClass=[];
   for(let [i,n] of a){let q=prevP[i],D=prevD[i];if(!q){ck(C-initial(i)<L);rootClass.push(i)}else{let g=C-D-q+1;ck(g>=0&&g<L&&g%2===0);ck((C-g)%q===0||(C-g+2)%q===0);if(q>L+3)ck(p!==q);let key=q+":"+D;if(!classes.has(key))classes.set(key,{q,D,g,r:prevR[i],mass:prevMass[i],a:[]});let v=classes.get(key);ck(v.mass===prevMass[i]&&v.r===prevR[i]);v.a.push(i)}}
   ck(rootClass.length<=Math.floor(L/4)+1);
   for(let v of classes.values())ck(v.a.length<=v.mass);
   const isStop=a.length>=cap;
   for(let m of modes){
    let rough=r>=m.Z,roughWitness=[...classes.values()].some(v=>v.r>=m.Z),top=p>=m.Q||[...classes.values()].some(v=>v.q>=m.Q);
    if(rough)m.roughKeys++;
    let fresh=a.filter(([i])=>!m.mark[i]).map(([i])=>i);
    if(isStop&&rough){m.roughStopTags+=a.length;m.roughStopUnmarkedBefore+=fresh.length;m.roughStopMarkedEarlier+=a.length-fresh.length}
    if(isStop&&roughWitness)m.roughWitnessStopTags+=a.length;
    if(a.length>=m.k&&fresh.length){
     m.firstMarkKeys++;m.firstMarkMass+=fresh.length;
     for(let v of classes.values())if(v.a.some(i=>!m.mark[i])){ck(v.mass<m.k);m.rareClassChecks++}
     if(classes.size===1&&!rootClass.length){let v=[...classes.values()][0];ck(!fresh.length||v.mass>=m.k);/* incompatible with new tags; catches errors */}
     let c=rough?(roughWitness?3:1):(roughWitness?2:4);
     for(let i of fresh){
      m.mark[i]=c;m.first[c]++;if(top)m.firstTop++;if(!prevP[i])m.firstRoots++;
      else if(prevP[i]>=m.Q&&p>=m.Q&&Math.max(prevP[i],p)<=2*Math.min(prevP[i],p))m.firstComparable++;
     }
     if(isStop&&rough)m.roughStopMarkedHere+=fresh.length;
     if(isStop&&roughWitness)m.roughWitnessStopMarkedHere+=fresh.length
    }
    if(isStop)for(let [i] of a)m.stopFirst[m.mark[i]]++
   }
   if(isStop){stopped+=a.length;sinks++;continue}
   maxPassed=Math.max(maxPassed,a.length);
   for(let [i,n] of a){R+=r;events++;prevP[i]=p;prevD[i]=C;prevR[i]=r;prevMass[i]=a.length;last[i]=p;t[i]=n;ck(C+p-1<=2*n);push(i,C+p-1)}
  }
 }
 ck(stopped+twin+bad===N&&maxPassed<cap);
 for(let m of modes){m.first[0]=N-m.firstMarkMass;ck(m.first.reduce((a,b)=>a+b,0)===N&&m.stopFirst.reduce((a,b)=>a+b,0)===stopped);ck(m.roughStopMarkedEarlier+m.roughStopUnmarkedBefore===m.roughStopTags);delete m.mark}
 return {X,B,N,L,cap,R,events,stopped,sinks,twin,bad,literal,maxPassed,clock,modes};
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
