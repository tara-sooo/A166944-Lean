// Long gain-stopped prime-root moving-light ancestry and first-good meeting expiry audit.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,Ps=[6,30,210],lim=7*X+B+20,S=new Int32Array(lim),L=6,y=3,k=2,m=Math.max(2,Math.floor(B**.5)),Q=Math.max(5,Math.ceil(B**.75)),tau=.25,bmin=3;
 const ok=(b,msg)=>{if(!b)throw Error(`${X}/${focus}: ${msg}`)},mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let j=p*p;j<lim;j+=p)S[j]=S[j]||p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const tags=[],at=new Map(),slots=new Map();let events=0,hit=0;
 for(let M=X;M<2*X;M++)if(S[M]===M){let C=2*M-2,t=M+2,stop=Math.floor((7*M-1)/4),es=[],id=tags.length,tag={M,id,es};tags.push(tag);
  for(;;){let e={C,t,end:t,p:0,w:0,tag,i:es.length};es.push(e);let ar=at.get(C)||[];ar.push(e);at.set(C,ar);if(C-(2*M-2)>=T){hit++;break}
   let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>stop)break;Object.assign(e,{p,w:v-t,v,r,J:C+p-1,end:v-1});let key=C+"|"+p+"|"+v,a=slots.get(key)||[];a.push(e);slots.set(key,a);events++;C=e.J;t=v;
  }
 }
 let maxd=1;for(let C of at.keys())maxd=Math.max(maxd,new Set([...fac(C),...fac(C+2)].filter(p=>p>y)).size);
 const g=L*(maxd+1),bound=(m+1)*L*Array.from({length:k+2},(_,i)=>g**i).reduce((a,b)=>a+b,0);
 let moving=0,good=0,top=0,topMoving=0,topGood=0,topThinProj=0,topThinPhys=0,topBoth=0,firstHeavy=0,maxMoving=0,maxGood=0,reverseChecks=0,rootStarts=0,depthChecks=0;
 for(let tag of tags){let es=tag.es,depth=0,last=0,heavy=-1,heavyD=0,expiry=null;
  for(let i=0;i<es.length;i++){let e=es[i];e.depth=depth;if(at.get(e.C).length<=m)last=i;if(heavy<0&&at.get(e.C).length>m){heavy=i;heavyD=depth;firstHeavy++}
   e.good=heavy<0||depth-heavyD<=k;e.moving=depth-es[last].depth<=k+1;e.start=last;
   ok(!e.good||e.moving,"good prefix included moving");if(e.good){expiry=e;good++}
   if(e.moving){moving++;if(last===0)rootStarts++;let low=0,non=0,rev=[];for(let j=i-1;j>=last;j--){let x=es[j];if(x.p<=y){low+=x.p-1;ok(low<L,"LOW barrier")}else{ok(x.p>y&&(x.J%x.p===0||(x.J+2)%x.p===0),"reverse candidate");rev.push(low+":"+x.p);low=0;non++;reverseChecks++}}ok(non===depth-es[last].depth&&non<=k+1,"moving depth");depthChecks++;e.word=rev.join(",")+"|"+low}
   if(e.p>=Q&&e.w>=tau*(e.p-1)){top+=e.w;if(e.moving)topMoving+=e.w;if(e.good)topGood+=e.w;let a=slots.get(e.C+"|"+e.p+"|"+e.v),n=at.get(e.C).filter(x=>x.p===e.p).length,thinP=n<=Math.floor(B**.65),thinS=a.length<=m;if(thinP)topThinProj+=e.w;if(thinS)topThinPhys+=e.w;if(thinP||thinS||e.moving)topBoth+=e.w}
   if(e.p>y)depth++;
  }
  tag.expiry=expiry;ok(expiry&&es.slice(expiry.i+1).every(e=>!e.good),"monotone good prefix");
 }
 let first=new Set(),expiryCount=0,expiryChecks=0,wordChecks=0,goodPairInc=0;
 const key=(a,b)=>Math.min(a,b)+"|"+Math.max(a,b);
 for(let [C,ar] of at){let mv=ar.filter(e=>e.moving),gs=ar.filter(e=>e.good);maxMoving=Math.max(maxMoving,mv.length);maxGood=Math.max(maxGood,gs.length);ok(mv.length<=bound,"uniform moving mass");
  let leaves=new Map();for(let e of mv){let s=e.tag.es[e.start],q=leaves.get(e.word)||{C:s.C,n:0};ok(q.C===s.C,"reverse word unique start");q.n++;leaves.set(e.word,q)}
  for(let q of leaves.values()){ok(q.n<=m+1,"eligible start mass");wordChecks++}
  for(let i=0;i<gs.length;i++)for(let j=i+1;j<gs.length;j++){let a=gs[i],b=gs[j];if(Math.max(a.t,b.t)<=Math.min(a.end,b.end)){first.add(key(a.tag.id,b.tag.id));goodPairInc++}}
  const expiries=new Map();for(let e of gs)if(e.tag.expiry===e){let a=expiries.get(e.end)||[];a.push(e);expiries.set(e.end,a)}
  for(let [t,a] of expiries){let g0=gs.filter(e=>e.t<=t&&t<=e.end).length;ok(g0>=a.length,"expiry occupancy");expiryCount+=a.length*(g0-a.length)+a.length*(a.length-1)/2;expiryChecks++}
 }
 ok(first.size===expiryCount&&first.size<=tags.length*Math.max(0,maxGood-1),"expiry identity");
 let rows=Ps.map(P=>({P,charge:0,pairCap:0,inc:0}));for(let [_,a] of slots){if(a.length<bmin)continue;let e=a[0];for(let z of rows){let P=z.P,nk=Math.ceil(e.J/P)-Math.ceil(e.C/P);if(!nk)continue;for(let i=0;i<a.length;i++)for(let j=i+1;j<a.length;j++)if(first.has(key(a[i].tag.id,a[j].tag.id))){z.charge+=2*P*nk/a.length;z.inc++}}}
 for(let z of rows){z.pairCap=2*(H+z.P)*first.size/bmin;ok(z.charge<=z.pairCap+1e-7,"whole suffix compatible-clock payment");z.charge=+z.charge.toFixed(6)}
 return {X,focus,B,T,H,N:tags.length,events,hit,m,k,maxd,bound,moving,good,top,topMoving,topGood,topThinProj,topThinPhys,topBoth,firstHeavy,maxMoving,maxGood,reverseChecks,rootStarts,depthChecks,wordChecks,firstGoodPairs:first.size,expiryCount,expiryChecks,goodPairInc,rows}
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
