// Intermediate-word and clock CRT audit. Finite parameters intentionally differ from asymptotic scales.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),H=T+B,Q=Math.max(5,Math.ceil(B/10)),R=Math.max(3,Math.min(Math.ceil(Math.sqrt(B)),Math.ceil(Q/2))),P=6,kmax=2,cap=Math.floor(Math.sqrt(B)),large=Math.ceil(Math.sqrt(B)),theta=.2,m=8,lo=2*X-2,hi=7*X,lim=hi+B+P+10;
 const spf=new Int32Array(lim),r=new Int32Array(lim),fail=(b,s)=>{if(!b)throw Error(X+" "+s)},mod=(a,m)=>((a%m)+m)%m;
 for(let p=2;p<lim;p++)if(!spf[p]){spf[p]=p;if(p*p<lim)for(let j=p*p;j<lim;j+=p)if(!spf[j])spf[j]=p}
 function factors(n){let a=[];while(n>1){let p=spf[n];if(p!==2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const labels=new Map();for(let C=lo;C<=hi;C+=2){let a=factors(C-1),b=factors(C+1);r[C]=Math.min(a[0]||B+1,b[0]||B+1);labels.set(C,[...a.map(p=>[p,-1]),...b.map(p=>[p,1])]);}
 const rough=C=>C<=hi&&C>=lo&&r[C]>=R,high=(C,p)=>p>=Q&&2*r[C]>p;
 let support=new Set(),timeKeys=new Map(),words=0,nonzeroWords=0,crtChecks=0,timeCandidates=0,walks=0;
 function enumerate(C,p,s,J,qs,prod,offsets){
  for(let e=0;e<P;e+=2){let A=J+e;if(A>hi)continue;
   if(rough(A)){support.add(C);words++;if(qs.length)nonzeroWords++;fail((C+s)%p===0,"initial congruence");for(let [q,sg,off] of offsets){fail((C+off+sg)%q===0,"word CRT");crtChecks++;}}
   if(qs.length===kmax)continue;
   for(let [q,sg] of labels.get(A)){if(q<=3||q===p)continue;let nextProd=qs.includes(q)?prod:prod*q;if(nextProd>cap)continue;walks++;enumerate(C,p,s,A+q-1,[...qs,q],nextProd,[...offsets,[q,sg,A-C]]);}
  }
 }
 for(let C=lo;C<=hi;C+=2)for(let [p,s] of labels.get(C))if(high(C,p)){
   if(p>cap)enumerate(C,p,s,C+p-1,[],1,[]);
   if(p<=P+2)continue;
   let opts=[];for(let e=0;e<P;e+=2){let A=C+p-1+e;if(A>hi)continue;for(let [q,sg] of labels.get(A))if(q>=large&&q>3&&q!==p){opts.push([q,sg,e]);timeCandidates++;}}
   if(opts.length)timeKeys.set(C+"|"+p,opts);
 }
 function eligible(v,C,p){let opts=timeKeys.get(C+"|"+p)||[];for(let [q,s,e] of opts){let phase=s===-1?0:q+2,h=1+mod(phase-v-1,2*q);if(h<=3*(P-1)+theta*q)return true;}return false}
 let N=0,events=0,raw=0,rawHigh=0,wordWitness=0,nonzeroWitness=0,largeRad=0,many=0,cheapWitness=0,expensiveWitness=0,paths=[],states=new Map();
 for(let M=X;M<2*X;M++)if(spf[M]===M){
   N++;let t=M+2,C=2*M-2,C0=C,K=Math.floor((7*M-1)/4),es=[];
   while(C-C0<T){
     let v=Infinity,p=0;for(let [q,s] of labels.get(C)){let phase=s===-1?0:q+2,j=t+1+mod(phase-t-1,2*q);if(j<v||(j===v&&q<p)){v=j;p=q}}
     if(!p||v>K)break;
     let J=C+p-1,w=v-t;fail(w<=2*r[C]&&w<=3*(p-1),"clock");let hiEvent=high(C,p);es.push({C,t,v,p,J,w,high:hiEvent});events++;raw+=w;if(hiEvent)rawHigh+=w;
     for(let j=t;j<v;j++){let key=j*lim+C,a=states.get(key);if(!a){a={n:0,C,p,v,high:hiEvent};states.set(key,a)}fail(a.p===p&&a.v===v,"deterministic exit");a.n++}
     C=J;t=v;
   }
   for(let i=0;i<es.length;i++)if(es[i].high){
     let a=es[i],last=a.J,qs=[],prod=1,first=-1,checked=false;
     for(let j=i+1;j<=es.length;j++){
       let A=j<es.length?es[j].C:C;
       if(rough(A)){
         if(a.p>cap&&qs.length<=kmax&&prod<=cap){fail(support.has(a.C),"actual short word support");wordWitness++;if(qs.length)nonzeroWitness++;}
         else if(qs.length>kmax)many++;else if(prod>cap)largeRad++;
         checked=true;break;
       }
       if(j===es.length)break;
       let b=es[j];if(b.p>3){fail(b.C-last<P,"LOW primorial gap");if(first<0)first=j;if(!qs.includes(b.p))prod*=b.p;qs.push(b.p);last=b.J;if(qs.length>kmax||prod>cap)break;}
     }
     // independent scan to actual first nonLOW event (may follow an earlier rough vertex)
     let j=i+1;while(j<es.length&&es[j].p<=3)j++;
     if(j<es.length&&a.p>P+2&&es[j].p>=large&&es[j].p>3){let b=es[j],e=b.C-a.J;fail(e>=0&&e<P&&a.p!==b.p,"first nonLOW geometry");if(b.w<=theta*b.p){fail(b.v-a.v<=3*(P-1)+theta*b.p&&eligible(a.v,a.C,a.p),"actual cheap time CRT");cheapWitness++;}else expensiveWitness++;}
   }
   paths.push(es);
 }
 let wordPaid=0,timePaid=0,remaining=0,wordStates=0,timeStates=0,retainedThin=0;
 for(let a of states.values())if(a.high){
   if(a.n<=m&&a.p>cap&&support.has(a.C)){wordPaid+=a.n;wordStates++;}
   else if(a.n<=m&&eligible(a.v,a.C,a.p)){timePaid+=a.n;timeStates++;}
   else {remaining+=a.n;if(a.n<=m)retainedThin+=a.n;}
 }
 fail(rawHigh===wordPaid+timePaid+remaining,"partition");
 return {X,B,T,Q,R,P,kmax,cap,large,theta,m,N,events,raw,rawHigh,states:states.size,support:support.size,words,nonzeroWords,crtChecks,walks,timeCandidates,wordWitness,nonzeroWitness,cheapWitness,expensiveWitness,wordPaid,timePaid,remaining,wordStates,timeStates,retainedThin};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));
