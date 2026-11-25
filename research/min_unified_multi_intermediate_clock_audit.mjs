// Extended radical and multi-intermediary cumulative-clock CRT audit. Finite parameters intentionally differ from asymptotic scales.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),H=T+B,Q=Math.max(5,Math.ceil(B/10)),R=Math.max(3,Math.min(Math.ceil(Math.sqrt(B)),Math.ceil(Q/2))),P=6,kmax=2,Dmax=Math.floor(B**.8),theta=.4,m=8,lo=2*X-2,hi=7*X,lim=hi+B+P+10;
 const spf=new Int32Array(lim),r=new Int32Array(lim),fail=(b,s)=>{if(!b)throw Error(X+" "+s)},mod=(a,m)=>((a%m)+m)%m;
 for(let p=2;p<lim;p++)if(!spf[p]){spf[p]=p;if(p*p<lim)for(let j=p*p;j<lim;j+=p)if(!spf[j])spf[j]=p}
 function factors(n){let a=[];while(n>1){let p=spf[n];if(p!==2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const labels=new Map();for(let C=lo;C<=hi;C+=2){let a=factors(C-1),b=factors(C+1);r[C]=Math.min(a[0]||B+1,b[0]||B+1);labels.set(C,[...a.map(p=>[p,-1]),...b.map(p=>[p,1])]);}
 const rough=C=>C<=hi&&C>=lo&&r[C]>=R,high=(C,p)=>p>=Q&&2*r[C]>p,good=p=>p>Dmax&&p>kmax*(P+Math.sqrt(Dmax))+3,phase=(p,s)=>s===-1?0:p+2,key=(C,p)=>C+"|"+p;
 let wordSupport=new Set(),timeSupport=new Map(),oldWordSupport=new Set(),words=0,extendedWords=0,spatialCRT=0,prefixCRT=0,timeCandidates=0,bruteTimeChecks=0;
 function spatial(C,p,s,J,qs,D,cs){
   for(let e=0;e<P;e+=2){const A=J+e;if(A>hi)continue;
     if(rough(A)){words++;wordSupport.add(key(C,p));if(D<=Math.floor(Math.sqrt(B)))oldWordSupport.add(key(C,p));else extendedWords++;
       fail((C+s)%p===0,"initial congruence");for(let [q,t,off] of cs){fail(q!==p&&(C+off+t)%q===0,"spatial CRT");spatialCRT++}
     }
     if(qs.length===kmax)continue;
     for(let [q,t] of labels.get(A)){if(q<=3||q===p)continue;const DD=qs.includes(q)?D:D*q;if(DD<=Dmax)spatial(C,p,s,A+q-1,[...qs,q],DD,[...cs,[q,t,A-C]])}
   }
 }
 function timed(C,p,s,J,h,q0,qs,cs,cand){
   for(let e=0;e<P;e+=2){const A=J+e;if(A>hi)continue;
     for(let [q,t] of labels.get(A)){
       if(q>q0&&q>3){fail(q!==p,"different big successor");for(let [a,b,off] of cs){fail((C+off+b)%a===0&&a<=q0,"prefix CRT");prefixCRT++}
         cand.set(q+"|"+t,[q,t]);timeCandidates++;
       }else if(q>3&&q!==p&&qs.length<h-1)timed(C,p,s,A+q-1,h,q0,[...qs,q],[...cs,[q,t,A-C]],cand);
     }
   }
 }
 for(let C=lo;C<=hi;C+=2)for(let [p,s] of labels.get(C))if(high(C,p)&&good(p)){
   spatial(C,p,s,C+p-1,[],1,[]);
   let cand=new Map();for(let h=1;h<=kmax;h++)timed(C,p,s,C+p-1,h,Dmax**(1/h),[],[],cand);
   if(cand.size)timeSupport.set(key(C,p),[...cand.values()]);
 }
 function cheap(v,C,p){const opts=timeSupport.get(key(C,p))||[];return opts.some(([q,s])=>1+mod(phase(q,s)-v-1,2*q)<=Math.floor(theta*q))}
 let N=0,events=0,raw=0,rawHigh=0,paths=[],states=new Map(),witnesses=0,extendedWitnesses=0,largeRadWitnesses=0,cheapWitnesses=0,nonfirstWitnesses=0,multiWitnesses=0,actualPhaseChecks=0;
 for(let M=X;M<2*X;M++)if(spf[M]===M){
   N++;let t=M+2,C=2*M-2,C0=C,K=Math.floor((7*M-1)/4),es=[];
   while(C-C0<T){
     let v=Infinity,p=0,sg=0;for(let [q,s] of labels.get(C)){let j=t+1+mod(phase(q,s)-t-1,2*q);if(j<v||(j===v&&q<p)){v=j;p=q;sg=s}}
     if(!p||v>K)break;
     let J=C+p-1,w=v-t;fail(w<=2*r[C]&&w<=3*(p-1)&&2*t>=C,"clock");
     let hh=high(C,p);es.push({C,t,v,p,J,w,sg,high:hh});events++;raw+=w;if(hh)rawHigh+=w;
     for(let j=t;j<v;j++){let z=j*lim+C,a=states.get(z);if(!a){a={n:0,C,p,v,high:hh};states.set(z,a)}fail(a.p===p&&a.v===v,"deterministic exit");a.n++}
     C=J;t=v;
   }
   for(let i=0;i<es.length;i++)if(es[i].high&&good(es[i].p)){
     let a=es[i],j=i+1;while(j<es.length&&!es[j].high)j++;
     if(j===es.length)continue;
     let inter=es.slice(i+1,j),non=inter.filter(e=>e.p>3),h=non.length;
     if(h>kmax)continue;
     let D=[...new Set(non.map(e=>e.p))].reduce((a,b)=>a*b,1);let G=es[j].C-a.J;
     fail(inter.reduce((n,e)=>n+e.p-1,0)===G,"exact gap gain");
     fail(inter.reduce((n,e)=>n+e.w,0)===es[j].t-a.v,"exact gap wait");
     if(D<=Dmax){fail(wordSupport.has(key(a.C,a.p)),"actual word witness");witnesses++;if(D>Math.floor(Math.sqrt(B)))extendedWitnesses++;}
     else{
       largeRadWitnesses++;if(h>1)multiWitnesses++;
       const q0=Dmax**(1/h),b=non.find(e=>e.p>q0);fail(!!b,"large intermediate");if(b!==non[0])nonfirstWitnesses++;
       fail(b.p!==a.p&&mod(a.v-phase(a.p,a.sg),2*a.p)===0&&mod(b.v-phase(b.p,b.sg),2*b.p)===0,"actual time CRT");actualPhaseChecks++;
       const dt=b.v-a.v;if(dt<=Math.floor(theta*b.p)){cheapWitnesses++;fail(cheap(a.v,a.C,a.p),"actual cumulative cheap witness");}
       a.gap={wait:es[j].t-a.v,dt,q:b.p,q0};
     }
   }
   paths.push(es);
 }
 let oldPaid=0,wordPaid=0,timePaid=0,remaining=0,thinRemaining=0,conditionalChecks=0,minRatio=Infinity;
 for(let a of states.values())if(a.high){
   let z=key(a.C,a.p),c=cheap(a.v,a.C,a.p);
   if(bruteTimeChecks<5000&&timeSupport.has(z)){
     let brute=false;for(let [q,s] of timeSupport.get(z))for(let h=1;h<=Math.floor(theta*q);h++)if(mod(a.v+h-phase(q,s),2*q)===0)brute=true;
     fail(brute===c,"literal time existence");bruteTimeChecks++;
   }
   if(a.n<=m&&wordSupport.has(z)){wordPaid+=a.n;if(oldWordSupport.has(z))oldPaid+=a.n;}
   else if(a.n<=m&&c)timePaid+=a.n;
   else{remaining+=a.n;if(a.n<=m)thinRemaining+=a.n;}
 }
 for(let es of paths)for(let a of es)if(a.gap){
   let z=key(a.C,a.p);if(wordSupport.has(z)||cheap(a.v,a.C,a.p))continue;
   let thin=false;for(let j=a.t;j<a.v;j++)if(states.get(j*lim+a.C).n<=m){thin=true;break}
   if(thin){fail(a.gap.wait>=a.gap.dt&&a.gap.dt>theta*a.gap.q&&a.gap.q>a.gap.q0,"retained cumulative clock lower bound");conditionalChecks++;minRatio=Math.min(minRatio,a.gap.wait/a.gap.q);}
 }
 fail(wordPaid+timePaid+remaining===rawHigh,"partition");
 return {X,B,T,Q,R,P,kmax,Dmax,theta,m,N,events,raw,rawHigh,states:states.size,wordSupport:wordSupport.size,oldWordSupport:oldWordSupport.size,words,extendedWords,spatialCRT,prefixCRT,timeCandidates,timeKeys:timeSupport.size,bruteTimeChecks,witnesses,extendedWitnesses,largeRadWitnesses,multiWitnesses,nonfirstWitnesses,cheapWitnesses,actualPhaseChecks,oldPaid,wordPaid,timePaid,remaining,thinRemaining,conditionalChecks,minRatio:Number.isFinite(minRatio)?+minRatio.toFixed(6):null};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536])) console.log(JSON.stringify(audit(X)));
