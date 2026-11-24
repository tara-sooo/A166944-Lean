// Retained physical forest, origin-cell majority loss, transport, deep arrivals and cross-color variance audit.
function audit(X,y=7){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,Y=11,L=210,T=Math.max(53,Math.ceil(X/256)),cap=Math.max(2,Math.floor(B/4))*B,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 let W=2;for(let p=3;p<y;p++)if(spf[p]===p)W*=p;const w0=Math.floor(W/4)+1,H=Math.max(12,Math.floor(Math.sqrt(B))),Q=Math.max(11,Math.ceil(B/2)),J=7;
 const ck=(b,m)=>{if(!b)throw Error(m)},mod=(a,b)=>(a%b+b)%b,cell=(C,W)=>Math.floor((C-1)/W);
 const orig=i=>2*(X+2*i+1)-2,colour=i=>cell(orig(i),W);
 function hit(t,C,K){let n=K+1,p=0;for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(q>B)break;let u=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(u<n||(u===n&&q<p)){n=u;p=q}while(v%q===0)v/=q}}return [n,p]}
 const traces=Array.from({length:N},()=>[]),term=new Uint8Array(N),times=new Int32Array(N),cuts=new Int32Array(N),head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N),admit=new Map();
 function add(i,C,entry){next[i]=head[C/2];head[C/2]=i;if(entry){let b=cell(C,L);admit.set(b,(admit.get(b)||0)+1)}}
 for(let i=0;i<N;i++){let M=X+2*i+1;times[i]=M+2;cuts[i]=Math.floor((7*M-1)/4);add(i,orig(i),true)}
 let S=0,events=0,primeStops=0,cellStops=0;
 for(let b=cell(2*X,L);b<=cell(7*X-2,L);b++){
  if(!admit.has(b))continue;let stop=admit.get(b)>=T;
  for(let C=Math.max(2*X,b*L+2);C<=Math.min(7*X-2,(b+1)*L);C+=2){
   let i=head[C/2];head[C/2]=-1;let groups=new Map();
   while(i>=0){let j=next[i];if(stop){term[i]=1;S++;cellStops++}else{let [n,p]=hit(times[i],C,cuts[i]);if(!p){term[i]=3}else{if(!groups.has(p))groups.set(p,[]);groups.get(p).push([i,n])}}i=j}
   for(let [p,a] of groups){let stopP=p>=Y&&a.length>=Math.ceil(cap/p);for(let [i,n] of a){traces[i].push({p,n,C,r:Math.min(spf[C-1],spf[C+1])});if(stopP){term[i]=2;S++;primeStops++}else{times[i]=n;let C1=C+p-1;events++;add(i,C1,cell(C1,L)!==b)}}}
  }
 }
 // Replay exactly the retained stop prefixes. V and A vertices form a physical forest.
 head.fill(-1);const ptr=new Int32Array(N),marked=new Uint8Array(N),high=new Uint8Array(N),depart=new Uint8Array(N),wasRare=new Uint8Array(N),arrival=new Map(),termClasses=[],localMarks=new Map(),localRareMarks=new Map(),rareCells=new Set();
 let marks=0,heightFirst=0,markFirst=0,local=0,migrant=0,terminalUnmarked=0,transport=0,firstDepart=0,foreignContact=0,F=0,merge=0,near=0,maxGroup=0,vertices=0,largePremark=0,rareArrival=0,ordinaryArrival=0,rareTop=0,rareRough=0,rareNonreset=0,firstDepartBeforeMark=0,localNeverDepart=0,firstLocalMarkWithRare=0;
 const lastF=new Float64Array(N),lastGroup=new Int32Array(N).fill(-1);let groupId=0;const groupSize=[],deepMarks=new Map(),deepImm=new Map(),lastDeep=new Int32Array(N).fill(-1),entryC=new Int32Array(N),entryP=new Int32Array(N);let deepLocal=0,deepOrdinary=0,deepOrdinaryLargeJump=0,deepOrdinaryInCell=0,nearPairs=0,nearProxy=0,farProxy=0,firstOrdinaryDeparture=0,firstRareDeparture=0;
 const dist=Math.max(1,Math.floor(W/Math.log(W)**2));
 for(let i=0;i<N;i++)if(term[i]===1||term[i]===2){times[i]=X+2*i+3;add(i,orig(i),false)}
 function inspect(a,C,t,isV,terminal=false){
  vertices++;maxGroup=Math.max(maxGroup,a.length);const c=cell(C,W),counts=new Map(),old=new Map();
  for(let i of a){let k=colour(i);counts.set(k,(counts.get(k)||0)+1);if(lastGroup[i]>=0)old.set(lastGroup[i],lastF[i])}
  let val=(a.length-[...counts.values()].reduce((s,m)=>s+m*m,0)/a.length)/2,prev=[...old.values()].reduce((s,x)=>s+x,0);
  ck(val+1e-8>=prev,"variance increment");merge+=val-prev;
  let id=groupId++;groupSize[id]=a.length;const oldGroups=new Map();for(let i of a){let b=lastGroup[i];if(b>=0)oldGroups.set(b,(oldGroups.get(b)||0)+1)}for(let [b,n] of oldGroups)ck(n===groupSize[b],'whole parent group');
  for(let x=0;x<a.length;x++)for(let y=x+1;y<a.length;y++){let i=a[x],j=a[y];if(colour(i)===colour(j)||(lastGroup[i]>=0&&lastGroup[i]===lastGroup[j]))continue;if(2*Math.abs(i-j)<=dist){nearPairs++;nearProxy+=1/a.length}else farProxy+=1/a.length;}
  for(let i of a)if(colour(i)<c&&C-c*W>=2*dist&&lastDeep[i]!==c){lastDeep[i]=c;deepImm.set(c,(deepImm.get(c)||0)+1);if(!wasRare[i]){deepOrdinary++;if(entryP[i]-1>=dist)deepOrdinaryLargeJump++;else{ck(C-entryC[i]>=dist,'deep short-entry transport');deepOrdinaryInCell++;}}}
  for(let i of a){
   
   if(isV&&!marked[i]&&!high[i]&&2*t-C>=H){high[i]=1;heightFirst++}
   if(!marked[i]){
    const own=counts.get(colour(i));ck(own<=w0,"color cap");
    if(2*own<=a.length){
     marked[i]=1;marks++;if(!high[i])markFirst++;
     if(colour(i)===c){local++;localMarks.set(c,(localMarks.get(c)||0)+1);if(orig(i)-c*W>=2*dist){deepLocal++;deepMarks.set(c,(deepMarks.get(c)||0)+1);}if(a.some(j=>colour(j)!==c&&wasRare[j])){firstLocalMarkWithRare++;localRareMarks.set(c,(localRareMarks.get(c)||0)+1)}}else migrant++;
    }else ck(a.length<2*w0,"majority mass cap");
   }
   lastGroup[i]=id;lastF[i]=val;
  }
  if(terminal){F+=val;termClasses.push({ids:a.slice(),C,val});for(let i of a)if(!marked[i]&&!high[i]){terminalUnmarked++;ck(a.length<2*w0,"terminal cap")}}
 }
 for(let C=2*X;C<=7*X-2;C+=2){let i=head[C/2];head[C/2]=-1;if(i<0)continue;const V=new Map(),A=new Map();
  while(i>=0){let j=next[i];if(!V.has(times[i]))V.set(times[i],[]);V.get(times[i]).push(i);i=j}
  for(let [t,a] of V){let stopped=a.filter(i=>ptr[i]===traces[i].length);if(stopped.length){ck(stopped.length===a.length&&a.every(i=>term[i]===1),"terminal V non-split");inspect(a,C,t,true,true);continue}
   inspect(a,C,t,true,false);
   for(let i of a){let ev=traces[i][ptr[i]];ck(ev.C===C&&ev.n>t,"replay");let k=ev.n*B+ev.p;if(!A.has(k))A.set(k,{ev,a:[]});A.get(k).a.push(i)}
  }
  for(let {ev,a} of A.values()){
   const stop=a.filter(i=>term[i]===2&&ptr[i]+1===traces[i].length);
   ck(!stop.length||stop.length===a.length,"terminal A non-split");inspect(a,C,ev.n,false,stop.length>0);if(stop.length)continue;
   let C1=C+ev.p-1,from=cell(C,W),to=cell(C1,W),h1=2*ev.n-C1,reset=h1===(ev.n%2?6:0);
   for(let i of a){
    if(!marked[i]&&!high[i]&&ev.p>2*H+2){ck(ev.r>ev.p/8,"rough large");largePremark++}
    if(from!==to){ck(ev.p>=y,"barrier crossing");transport++;let rare=ev.p>=Q||(ev.p>=y&&ev.r>=ev.p/8&&ev.p>2*H+2)||(!reset&&h1<H&&ev.p>=J);
     wasRare[i]=+rare;entryC[i]=C1;entryP[i]=ev.p;arrival.set(to,(arrival.get(to)||0)+1);
     if(rare){rareCells.add(to);rareArrival++;if(ev.p>=Q)rareTop++;if(ev.p>2*H+2&&ev.r>=ev.p/8)rareRough++;if(!reset&&h1<H&&ev.p>=J)rareNonreset++}else ordinaryArrival++;
     if(!depart[i]){ck(from===colour(i),"first exit");depart[i]=1;firstDepart++;if(!marked[i]&&!high[i]){firstDepartBeforeMark++;if(rare)firstRareDeparture++;else firstOrdinaryDeparture++;}}
    }
    times[i]=ev.n;ptr[i]++;add(i,C1,false)
   }
  }
 }
 let minBound=0,maxBound=0,localMarkedTerminal=0,colourLossBound=0;
 for(let {ids,C,val} of termClasses){let c=cell(C,W),cnt=new Map();for(let i of ids){cnt.set(colour(i),(cnt.get(colour(i))||0)+1);if(marked[i]&&!depart[i])localNeverDepart++}
  let max=Math.max(...cnt.values()),minor=ids.length-max,m=ids.filter(i=>marked[i]).length;ck(val<=m+1e-8&&m<=2*minor,"terminal majority-variance");minBound+=minor;maxBound+=m;colourLossBound+=2*minor;
  let localMarked=ids.filter(i=>marked[i]&&!depart[i]).length,foreign=ids.filter(i=>depart[i]).length;ck(localMarked<=foreign,"terminal resident charging");localMarkedTerminal+=localMarked;
 }
 for(let [c,m] of localMarks)ck(m<=(arrival.get(c)||0),"cell resident charging");
 for(let [c,m] of deepMarks)ck(m<=(deepImm.get(c)||0),'deep local charging');let deepLocalOrd=0;for(let [c,m] of deepMarks)if(!rareCells.has(c))deepLocalOrd+=m;ck(deepLocalOrd<=deepOrdinary,'deep ordinary charge');ck(F<=nearProxy+farProxy+1e-7,'cross-color proxy dominates variance');
 let localOrd=0;for(let [c,m] of localMarks)if(!rareCells.has(c))localOrd+=m;ck(localOrd<=ordinaryArrival&&local<=ordinaryArrival+w0*rareCells.size,"rare cell deletion");
 ck(Math.abs(F-merge)<1e-6&&marks<=4*F+1e-6&&F<=marks+1e-6,"global variance and marks");ck(marks<=2*firstDepart,"departure charge");
 return {X,Y,y,W,w0,H,Q,J,N,S,events,primeStops,cellStops,vertices,maxGroup,marks,heightFirst,markFirst,terminalUnmarked,local,migrant,transport,firstDepart,firstDepartBeforeMark,localNeverDepart,localMarkedTerminal,rareArrival,ordinaryArrival,rareTop,rareRough,rareNonreset,rareCells:rareCells.size,firstLocalMarkWithRare,localOrd,largePremark,F,merge,minority:minBound,colourLossBound,dist,deepLocal,deepLocalOrd,deepOrdinary,deepOrdinaryLargeJump,deepOrdinaryInCell,nearPairs,nearProxy,farProxy,firstOrdinaryDeparture,firstRareDeparture};
}
for(const x of process.argv.slice(2).map(Number))for(const y of [5,7,11])console.log(JSON.stringify(audit(x,y)));
