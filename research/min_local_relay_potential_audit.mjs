// Exact signed restricted-relay potentials and band-persistence controls.
function downwardAudit(limit=500000){
 const mod=(x,m)=>(x%m+m)%m,ck=(c,m)=>{if(!c)throw Error(m)},gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return Math.abs(a)};
 let tables=[],checks=0;
 for(let T of [3,5,7,11]){
  let A=[3,5,7,11].filter(p=>p<=T),Q=2*A.reduce((a,b)=>a*b,1),size=(Q/2+1)*Q,down=new Uint16Array(size),up=new Uint16Array(size),nextP=new Uint8Array(size),nextW=new Uint8Array(size),maxDown=0,maxUp=0,downAt=null,upAt=null;
  for(let u=Q-2;u>=0;u-=2){
   let cand=[];for(let p of A){if(u%p===1)cand.push([p,0]);if(u%p===p-1)cand.push([p,p+2])}
   if(!cand.length)continue;
   for(let v=0;v<Q;v++){
    let w=Infinity,p=Infinity;for(let [r,s] of cand){let z=mod(s-v,2*r)||2*r;if(z<w||z===w&&r<p){w=z;p=r}}
    let j=(u+p-1)/2*Q+(v+w)%Q,i=u/2*Q+v;
    down[i]=Math.max(0,p-1-2*w+down[j]);up[i]=Math.max(0,2*w-p+1+up[j]);nextP[i]=p;nextW[i]=w;
    if(down[i]>maxDown){maxDown=down[i];downAt={u,v}}if(up[i]>maxUp){maxUp=up[i];upAt={u,v}}
   }
  }
  // Independent literal restricted ticks, then check every Bellman cell.
  for(let u=0;u<=Q;u+=2)for(let v=0;v<Q;v++){
   let p=0,w=0;for(let t=1;t<=2*T;t++){let n=v+t,z=gcd(n%2?n-2:n,n%2?u+1:u-1);let r=A.find(q=>z%q===0);if(r){p=r;w=t;break}}
   let i=u/2*Q+v;ck(p===nextP[i]&&w===nextW[i],"literal");
   if(p){let j=(u+p-1)/2*Q+(v+w)%Q;ck(down[i]===Math.max(0,p-1-2*w+down[j])&&up[i]===Math.max(0,2*w-p+1+up[j]),"bellman")}
   else ck(down[i]===0&&up[i]===0,"terminal");
   checks++;
  }
  function witness(s,mode){if(!s)return [];let {u,v}=s,out=[],A=mode==="down"?down:up;while(A[u/2*Q+v]>0){let i=u/2*Q+v,p=nextP[i],w=nextW[i];out.push({u,v,p,w});u+=p-1;v=(v+w)%Q}return out}
  tables.push({T,Q,size,maxDown,maxUp,downAt,upAt,downWord:witness(downAt,"down"),upWord:witness(upAt,"up")});
 }
 const a=new Uint32Array(2*limit+3);
 for(let p=3;p*p<a.length;p+=2)if(!a[p])for(let n=p*p;n<a.length;n+=2*p)if(!a[n])a[n]=p;
 function fs(n){let f=[];while(n>1){let p=a[n]||n;f.push(p);while(n%p===0)n/=p}return f}
 function ev(u,v){let f=fs(u-1),g=fs(u+1),w=Infinity,p=Infinity,e=0;for(let [A,s] of [[f,1],[g,-1]])for(let r of A){let z=mod((s===1?0:r+2)-v,2*r)||2*r;if(z<w||z===w&&r<p){w=z;p=r;e=s}}return {p,w,e,twin:f[0]===u-1&&g[0]===u+1}}
 let s={sources:0,launches:0,firstHighReturn:0,firstHighNotReturn:0,twinStops:0,lowIncidences:0,largestDrop:0,bandStarts:0,bandAccepted:0,bandLow:0,bandOutside:0,bandTwin:0,bandMaxHigh:0,bandExample:null,returnExample:null,minReturnSlack:null};
 for(let u=12;u<=limit;u+=6)for(let d of [0,6]){
  s.sources++;let v=(u+d)/2,z=ev(u,v),D=d+2*z.w-z.p+1,p=z.p;
  if(z.twin||p<13||D===0||D===6)continue;
  let ss=z.e===1?0:6;ck(D===2*p+ss,"launch");s.launches++;
  let U=u+p-1,V=v+z.w;
  while(U<2*limit){
   let y=ev(U,V);if(y.twin){s.twinStops++;break}
   let dd=2*(V+y.w)-(U+y.p-1);
   if(y.p<=11){ck(dd>=D-16&&dd<=D+192&&dd!==0&&dd!==6,"low potential");s.lowIncidences++;s.largestDrop=Math.max(s.largestDrop,D-dd);U+=y.p-1;V+=y.w;continue}
   if(dd===0||dd===6){
    s.firstHighReturn++;let slack=y.p-(2*p+ss-19);ck(slack>=0,"return threshold");
    if(s.minReturnSlack===null||slack<s.minReturnSlack){s.minReturnSlack=slack;s.returnExample={u,d,p,launchD:D,returnU:U,preD:2*V-U,r:y.p,w:y.w,postD:dd,slack}}
   }else s.firstHighNotReturn++;
   break;
  }
  if(p<=38)continue;
  s.bandStarts++;U=u+p-1;V=v+z.w;let lastD=D,n=1;
  while(U<2*limit){
   let y=ev(U,V);if(y.twin){s.bandTwin++;break}
   let dd=2*(V+y.w)-(U+y.p-1);
   if(y.p<=11){ck(dd>=lastD-16&&dd<=lastD+192&&dd!==0&&dd!==6,"band low");s.bandLow++}
   else if(y.p>=p&&2*y.p<=3*p){ck(dd>=2*p,"band high");s.bandAccepted++;lastD=dd;n++}
   else{s.bandOutside++;break}
   U+=y.p-1;V+=y.w;
  }
  if(n>s.bandMaxHigh){s.bandMaxHigh=n;s.bandExample={u,d,p,n}}
 }
 return {limit,tables,checks,stats:s};
}
console.log(JSON.stringify(downwardAudit(Number(process.argv[2]||500000)),null,2));
