// Height-adaptive physical cap, local high passage and dense universal barrier audit.
function audit(X,mode=0){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,H0=24,T0=Math.max(8,Math.floor(B/4)),a=mode?8:4,Q=Math.max(48,Math.floor(B*(mode?1.5:.5))),J=12,D=4;
 const spf=new Int32Array(7*X+10);for(let p=2;p<spf.length;p++)if(!spf[p]){spf[p]=p;if(p*p<spf.length)for(let k=p*p;k<spf.length;k+=p)spf[k]=p}
 const mod=(v,p)=>(v%p+p)%p,ck=(b,m)=>{if(!b)throw Error(m)};
 const cap=h=>h<=H0?T0:Math.min(T0,Math.ceil(a*Math.sqrt(8*X/(h+1))));
 const head=new Int32Array(Math.floor(spf.length/2)).fill(-1),link=new Int32Array(N),time=new Int32Array(N),cut=new Int32Array(N),incomingR=new Int32Array(N),incomingP=new Int32Array(N),incomingC=new Int32Array(N),incomingLow=new Uint8Array(N),hit=new Uint8Array(N),cost=new Int32Array(N),entryH=new Int32Array(N).fill(-1),entryF=new Float64Array(N),pos=new Float64Array(N);
 const Y=7,L=30,K=8,S=16,pr=[3,5],nphase=L*L/2,wait=new Int32Array(nphase),delta=new Int32Array(nphase),succ=new Int32Array(nphase);
 const idx=(C,t)=>mod(C,L)/2*L+mod(t,L);
 for(let C=0;C<L;C+=2)for(let t=0;t<L;t++){
  let w=Infinity,p=0;
  for(let q of pr){let cc=C%q;if(cc!==1&&cc!==q-1)continue;let z=2*q-mod(t-(cc===1?0:q+2),2*q);if(z<w||(z===w&&q<p)){p=q;w=z}}
  if(p){let i=idx(C,t);wait[i]=w;delta[i]=2*w-(p-1);succ[i]=idx(C+p-1,t+w)}
 }
 const values=Array.from({length:2*S+1},()=>new Int32Array(nphase)),sum=new Int32Array(nphase);
 for(let j=1;j<=2*S;j++)for(let i=0;i<nphase;i++){let w=wait[i];if(w&&w<=j)values[j][i]=Math.max(0,delta[i]+values[j-w][succ[i]]);if(j>=S)sum[i]+=Math.min(K,values[j][i])}
 const F=(C,t)=>sum[idx(C,t)]/(S+1);
 const out={X,mode,B,N,H0,T0,a,Q,stops:0,lowStops:0,highStops:0,stopVertices:0,minStop:null,maxStop:0,terminal:0,twin:0,nontwin:0,events:0,cost:0,stopEdgeCost:0,lowArrivalCost:0,midArrivalCost:0,highArrivalCost:0,hitTags:0,hitViaStop:0,highTagCost:0,bandPassageChecks:0,nontrivialPassageChecks:0,bandPositive:0,passagePositive:0,bandEntryOvershootMax:0,maxHeight:0,clockChecks:0,largeHeightSmallGroup:0,stopsAtAnchor:0,anchorArrivals:0,bands:{}};
 const keys=new Map();
 function next(C,t){let p=0,n=Infinity,r=Infinity;for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(!q)throw Error("factor");if(q>B)break;r=Math.min(r,q);let u=t+2*q-mod(t-(s===-1?0:q+2),2*q);if(u<n||(u===n&&q<p)){n=u;p=q}while(v%q===0)v/=q}}return {p,n,r}}
 function add(i,C){link[i]=head[C/2];head[C/2]=i}
 for(let i=0;i<N;i++){let M=X+2*i+1;time[i]=M+2;cut[i]=Math.floor((7*M-1)/4);add(i,2*M-2)}
 for(let C=2*X;C<=7*X-2;C+=2){
  let i=head[C/2];if(i<0)continue;let groups=new Map();
  while(i>=0){let j=link[i];if(!groups.has(time[i]))groups.set(time[i],[]);groups.get(time[i]).push(i);i=j}
  for(let [t,ids] of groups){let h=2*t-C,limit=cap(h),stopped=ids.length>=limit;
   ck(h>=0&&h<=8*X&&limit>=Math.min(a,T0),"height and cap");out.maxHeight=Math.max(out.maxHeight,h);
   if(stopped){out.stops+=ids.length;out.stopVertices++;out.minStop=out.minStop===null?ids.length:Math.min(out.minStop,ids.length);out.maxStop=Math.max(out.maxStop,ids.length);if(h<=H0)out.lowStops+=ids.length;else out.highStops+=ids.length;if(ids.some(i=>incomingLow[i]))out.stopsAtAnchor+=ids.length;}
   let b=h<=H0?"low":Math.floor(Math.log2(h+1)),brec=out.bands[b]||(out.bands[b]={cost:0,clocks:0,maxMass:0,capMax:0});
   let donors=new Map();
   for(let i of ids){let r=incomingR[i],p=incomingP[i],from=incomingC[i];if(r){
     if(stopped){out.stopEdgeCost+=r;if(!hit[i]&&h>=Q)out.hitViaStop++}
     else {
      if(h<=H0)out.lowArrivalCost+=r;else if(h<Q)out.midArrivalCost+=r;else out.highArrivalCost+=r;
      brec.cost+=r;let key=p+"/"+from;donors.set(key,(donors.get(key)||0)+1);
     }
    }
    if(stopped)continue;
    if(!hit[i]&&h>=Q){
     hit[i]=1;out.hitTags++;if(entryH[i]>=0){let gain=h+F(C,t)-entryF[i];ck(pos[i]+1e-7>=gain,"band passage corrected gain");ck(pos[i]+1e-7>=Q-entryH[i]-K,"band passage lower");out.bandPassageChecks++;out.nontrivialPassageChecks+=Q-entryH[i]-K>0;out.passagePositive+=pos[i];}
    }
    if(!hit[i]&&h<Q/2){entryH[i]=-1;pos[i]=0}
    else if(!hit[i]&&entryH[i]<0){entryH[i]=h;entryF[i]=h+F(C,t);pos[i]=0;out.bandEntryOvershootMax=Math.max(out.bandEntryOvershootMax,h-Q/2)}
   }
   if(stopped)continue;
   ck(ids.length<limit,"continuing group cap");
   for(let [key,m] of donors){ck(m<limit,"event mass");let k=key+"/"+b;if(!keys.has(k))keys.set(k,new Set());keys.get(k).add(t);brec.clocks++;brec.maxMass=Math.max(brec.maxMass,m);brec.capMax=Math.max(brec.capMax,limit);}
   let z=next(C,t);
   for(let i of ids){
    if(!z.p||z.n>cut[i]){out.terminal++;if(z.p)out.nontwin++;else out.twin++;continue}
    let C1=C+z.p-1,h1=2*z.n-C1,df=h1+F(C1,z.n)-h-F(C,t);
    ck(h1>=0&&z.n-t<=2*z.r&&z.r<=z.p,"clock");
    if(!hit[i]&&entryH[i]>=0){pos[i]+=Math.max(0,df);out.bandPositive+=Math.max(0,df);}
    out.events++;out.cost+=z.r;cost[i]+=z.r;incomingR[i]=z.r;incomingP[i]=z.p;incomingC[i]=C;incomingLow[i]=+(z.p>=11&&h<=D*z.p&&(J+4)*z.r>=z.p);
    if(incomingLow[i])out.anchorArrivals++;
    time[i]=z.n;add(i,C1);
   }
  }
 }
 for(let [key,clocks] of keys){let [p,C,b]=key.split("/");p=+p;let width=b==="low"?H0+1:2**(+b);ck(clocks.size<=1+Math.floor(width/(4*p)),"band clock count");out.clockChecks++}
 for(let i=0;i<N;i++){ck(cost[i]<=11*X,"per-source cost");if(hit[i])out.highTagCost+=cost[i]}
 ck(out.stops+out.terminal===N&&out.lowStops+out.highStops===out.stops,"conservation");
 ck(out.cost===out.stopEdgeCost+out.lowArrivalCost+out.midArrivalCost+out.highArrivalCost,"cost partition");
 ck(out.stopEdgeCost<=B*out.stops&&out.highArrivalCost<=out.highTagCost&&out.highTagCost<=11*X*out.hitTags,"charged high tags");
 return out
}
function barrier(Y){
 const ps=[];for(let p=3;p<Y;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const L=2*ps.reduce((a,b)=>a*b,1),mod=(a,b)=>(a%b+b)%b,ck=(x,m)=>{if(!x)throw Error(m)};
 let positions=[],localChecks=0,maxGap=0,minGap=Infinity,expected=ps.reduce((a,p)=>a*(p-1)/2,1);
 for(let J=0;J<L;J+=2){
  let safe=true;
  for(let p of ps){let n=0;for(let C=J-p+3;C<=J;C+=2)if(mod(C,p)===1||mod(C,p)===p-1)n++;
   let r=J%(2*p),want=r<=p-3?0:(r===p-1||r===2*p-2?1:2);ck(n===want,"exact barrier gateway count");localChecks++;if(n)safe=false;
  }
  if(safe)positions.push(J);
 }
 ck(positions.length===expected&&positions[0]===0,"CRT count");
 for(let i=0;i<positions.length;i++){let g=(positions[i+1]??L)-positions[i];maxGap=Math.max(maxGap,g);minGap=Math.min(minGap,g)}
 return {Y,L,count:positions.length,meanGap:L/positions.length,minGap,maxGap,localChecks}
}
for(const X of process.argv.slice(2).map(Number))for(const mode of [0,1])console.log(JSON.stringify(audit(X,mode)));
for(const Y of [5,7,11,13,17])console.log(JSON.stringify(barrier(Y)));
