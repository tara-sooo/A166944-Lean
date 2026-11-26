// Deficit excursion and restricted-relay audit, standard integer MIN.
function excursionAudit(limit=500000){
 const ps=[3,5,7,11,13,17],mod=(x,m)=>(x%m+m)%m,ck=(c,m)=>{if(!c)throw Error(m)};
 const gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return Math.abs(a)};
 let tables=[],tableControls=0;
 for(let T of ps){
  const A=ps.filter(p=>p<=T),Q=2*A.reduce((a,b)=>a*b,1),F=new Uint32Array(Q/2+1),N=new Uint32Array(Q/2+1);
  for(let u=Q-2;u>=0;u-=2)for(let p of A)if(u%p===1||u%p===p-1){let U=u+p-1;ck(U<=Q,"wall");F[u/2]=Math.max(F[u/2],p-1+F[U/2]);N[u/2]=Math.max(N[u/2],1+N[U/2])}
  let relaxedMax=0,maxCount=0;for(let i=0;i<F.length;i++){relaxedMax=Math.max(relaxedMax,F[i]);maxCount=Math.max(maxCount,N[i])}
  let exact=null;
  if(T<=11){
   const size=(Q/2+1)*Q,G=new Uint16Array(size),W=new Uint16Array(size),C=new Uint16Array(size);let maxG=0,maxW=0,maxC=0,maxState=null;
   for(let u=Q-2;u>=0;u-=2){
    let cand=[];for(let p of A){if(u%p===1)cand.push([p,0]);if(u%p===p-1)cand.push([p,p+2])}
    if(!cand.length)continue;
    for(let v=0;v<Q;v++){
     let p=0,w=Infinity;for(let [r,s] of cand){let t=mod(s-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}}
     let j=(u+p-1)/2*Q+(v+w)%Q,i=u/2*Q+v;G[i]=p-1+G[j];W[i]=w+W[j];C[i]=1+C[j];
     ck(G[i]<=F[u/2],"projected");if(G[i]>maxG){maxG=G[i];maxState={u,v}}maxW=Math.max(maxW,W[i]);maxC=Math.max(maxC,C[i]);
     if(T<=7||((u/2*Q+v)%97===0)){
      let literal=null;for(let t=1;t<=2*T;t++){let n=v+t,side=n%2?u+1:u-1,d=gcd(n%2?n-2:n,side),sel=A.find(q=>d%q===0);if(sel){literal=[sel,t];break}}
      ck(literal&&literal[0]===p&&literal[1]===w,"restricted literal");tableControls++;
     }
    }
   }
   exact={size,maxG,maxW,maxC,maxState};
  }
  tables.push({T,Q,relaxedMax,maxCount,exact});
 }
 const spf=new Uint32Array(2*limit+3);
 for(let p=3;p*p<spf.length;p+=2)if(!spf[p])for(let n=p*p;n<spf.length;n+=2*p)if(!spf[n])spf[n]=p;
 function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function ev(u,v){let a=fac(u-1),b=fac(u+1),p=Infinity,w=Infinity,e=0;for(let [f,s] of [[a,1],[b,-1]])for(let q of f){let z=mod((s===1?0:q+2)-v,2*q)||2*q;if(z<w||z===w&&q<p){w=z;p=q;e=s}}return {p,w,e,twin:a[0]===u-1&&b[0]===u+1}}
 const core=d=>d===0||d===6;
 let s={roots:0,events:0,departures:0,nonTwinLargeDepartures:0,completed:0,censored:0,largeCompleted:0,largeCensored:0,firstHighReturn:0,firstHighNotReturn:0,noHighBeforeReturn:0,returnBoundChecks:0,tableChecks:0,bandChecks:0,bandBlocks:0,literalTicks:0,maxDepartureRatio:{ratio:0},maxExcursion:{gain:0},minReturnRatio:{ratio:Infinity},examples:{},cutoffs:{}};
 for(let t of [3,5,7,11,13,17])s.cutoffs[t]={eligible:0,lowReturn:0,highReturn:0,highNotReturn:0,censored:0,maxLowGain:0};
 for(let X=12;X<=limit;X+=6){
  s.roots++;let u=X,v=X/2+3,ex=null;
  while(u<2*X){
   let d=2*v-u,{p,w,e,twin}=ev(u,v);if(twin)break;
   let U=u+p-1,V=v+w,D=2*V-U,s0=e===1?0:6;
   ck(D>=0&&V<=U+1,"envelope");ck((D-s0)%p===0,"deficit congruence");s.events++;
   if(X<600&&w<500){for(let t=1;t<=w;t++){let n=v+t,z=gcd(n%2?n-2:n,n%2?u+1:u-1);ck(t===w?(spf[z]||z)===p:z===1,"literal");s.literalTicks++}}
   if(core(d)&&!core(D)){
    ck(!ex,"excursion overlap");s.departures++;
    ex={u,p,d,D,e,large:p>=13,afterGain:0,afterWait:0,n:0,cut:tables.map(t=>({T:t.T,M:t.exact?.maxG??t.relaxedMax,g:0,n:0,done:false,eligible:p>=13&&p>t.T&&2*p-6>(t.exact?.maxG??t.relaxedMax)})),bandAlive:p>=37,bandT:p,bandMax:1.5*p,bandLow:0,bandLastP:p,bandLastD:D};
    if(ex.large){
     s.nonTwinLargeDepartures++;ck(D===2*p+s0&&2*w===3*p-1+s0-d,"large launch");ck(u%6===0,"large launch source");ck(p*p<=u+1,"departure cap");
     let ratio=p/Math.sqrt(u+1);if(ratio>s.maxDepartureRatio.ratio)s.maxDepartureRatio={u,p,d,D,w,ratio};
     if(!s.examples.launch)s.examples.launch={X,u,d,p,w,e,D};
     for(let c of ex.cut)if(c.eligible)s.cutoffs[c.T].eligible++;
    }
   }else if(ex){
    ex.afterGain+=p-1;ex.afterWait+=w;ex.n++;
    for(let c of ex.cut)if(c.eligible&&!c.done){
     let st=s.cutoffs[c.T];
     if(p<=c.T){c.g+=p-1;c.n++;ck(c.g<=c.M,"actual restricted relay");st.maxLowGain=Math.max(st.maxLowGain,c.g);s.tableChecks++;if(core(D)){st.lowReturn++;throw Error("forbidden low return")}}
     else{c.done=true;if(core(D)){st.highReturn++;ck(p>=2*ex.p+(ex.e===1?0:6)-c.g+2*c.n-3,"first high return lower");s.returnBoundChecks++;}else st.highNotReturn++}
    }
    if(ex.bandAlive){
      if(p<=11){ex.bandLow+=p-1;ck(ex.bandLow<=104,"band low relay");if(core(D)&&2*ex.bandT-6>104)throw Error("band low return");}
      else if(p>=ex.bandT&&p<=ex.bandMax&&ex.bandT>214){
       ck(D>=2*ex.bandT,"band corridor");s.bandChecks++;ex.bandLow=0;ex.bandLastP=p;ex.bandLastD=D;
      }else{ex.bandAlive=false;s.bandBlocks++}
    }
    if(core(D)){
      s.completed++;if(ex.large){s.largeCompleted++;ck(ex.afterGain===2*ex.afterWait+ex.D-D,"excursion identity");ck(ex.afterGain>=2*ex.p+(ex.e===1?0:6)-6+2*ex.n,"return gain lower");s.returnBoundChecks++;
       let ratio=ex.afterGain/ex.p;if(ratio<s.minReturnRatio.ratio)s.minReturnRatio={X,u:ex.u,p:ex.p,returnU:U,returnD:D,afterGain:ex.afterGain,n:ex.n,ratio};
       if(ex.afterGain>s.maxExcursion.gain)s.maxExcursion={X,u:ex.u,p:ex.p,returnU:U,n:ex.n,gain:ex.afterGain};
       if(!s.examples.completed)s.examples.completed={X,u:ex.u,p:ex.p,returnU:U,gain:ex.afterGain,n:ex.n};
      }
      for(let c of ex.cut)if(c.eligible&&!c.done)throw Error("unresolved eligible completed");
      ex=null;
    }
   }
   u=U;v=V;
  }
  if(ex){s.censored++;if(ex.large)s.largeCensored++;for(let c of ex.cut)if(c.eligible&&!c.done)s.cutoffs[c.T].censored++}
 }
 // A separate band check on arbitrary exact source states, independent of the
 // canonical-root scan: construct each eligible non-twin launch and follow
 // small relays and labels in [p,1.5p] until the first outside event.
 let band={launches:0,acceptedHigh:0,lowEvents:0,exits:0,twinStops:0,limitStops:0,maxHighCount:0,example:null};
 for(let u=12;u<=limit;u+=6)for(let d of [0,6]){
   let v=(u+d)/2,z=ev(u,v),D=d+2*z.w-z.p+1;
   if(z.twin||z.p<=214||core(D))continue;
   ck(D===2*z.p+(z.e===1?0:6),"band launch");let P=z.p,U=u+P-1,V=v+z.w,E=0,n=1;band.launches++;
   while(U<2*limit){
     let a=ev(U,V);if(a.twin){band.twinStops++;break}
     if(a.p<=11){E+=a.p-1;ck(E<=104,"band relay");band.lowEvents++;ck(!core(2*(V+a.w)-(U+a.p-1)),"no low return")}
     else if(a.p>=P&&2*a.p<=3*P){let dd=2*(V+a.w)-(U+a.p-1);ck(dd>=2*P,"band persistence");band.acceptedHigh++;E=0;n++}
     else{band.exits++;break}
     U+=a.p-1;V+=a.w;
   }
   if(U>=2*limit)band.limitStops++;
   if(n>band.maxHighCount){band.maxHighCount=n;band.example={u,d,P,n}}
 }
 return {limit,tables,tableControls,stats:s,band};
}
console.log(JSON.stringify(excursionAudit(Number(process.argv[2]||500000)),null,2));
