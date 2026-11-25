// Short boundary close-label projected support and weak-r temporal-pair audit.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,P=focus?210:30,y=focus?7:5,J=4,L=8,R0=Math.max(3,Math.floor(Math.sqrt(B))),lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(x,s)=>{if(!x)throw Error(X+" "+s)},mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const close=new Map(),phase=new Map(),keys=new Map(),census=new Map(),cpKeys=new Set(),phaseKeys=new Set();
 let N=0,hit=0,events=0,short=0,weight=0,nonrough=0,closePaid=0,closeNonrough=0,closeInc=0,inside=0,outside=0,forward=0,backward=0,phaseWeight=0,phaseInc=0,phaseChecks=0,sourceChecks=0,tailChecks=0,modChecks=0,rootChecks=0,capPaid=0,capThin=0,capHeavy=0,maxMass=0,tailMax=0;
 function add(m,k,w){m.set(k,(m.get(k)||0)+w)}
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[];
  while(C-C0<T){
   let p=0,v=Infinity,r=Infinity,sg=0;
   for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j;sg=s}}
   if(!p||v>cut)break;
   let g=p-1,A=C+g,n=Math.ceil(A/P)-Math.ceil(C/P),w=v-t,fp=Math.max(0,P*n-Math.max(0,g-4*r));
   ok(w<=2*r&&r<=p&&2*t-C>=0&&2*v-A>=0&&(!n||P%p!==0),"geometry");
   es.push({C,A,p,r,v,t,sg,g,n,weight:n?(fp+P/4)/n:0});events++;C=A;t=v;
  }
  if(C-C0>=T)hit++;
  for(let i=0;i<es.length;i++){let a=es[i];if(!a.n||a.p>=2*P)continue;let p=a.p;short++;weight+=a.weight*a.n;
   if(a.r<a.g/Math.log(2+p))nonrough+=a.weight*a.n;
   let near=null,prior=null;
   for(let j=i-1;j>=0;j--){let b=es[j],e=a.C-b.A;if(e>Math.max(J,L))break;let q=b.p;
    if(e<=J&&p>J+3&&Math.abs(p-q)<=J&&!near)near={b,e,dir:-1};
    if(e<=L&&p>L+3&&p>=Math.sqrt(P)&&q>y&&q>=p/2&&q<=2*p&&a.r<=R0&&!prior)prior={b,e};
   }
   for(let j=i+1;j<es.length&&!near;j++){let b=es[j],e=b.C-a.A;if(e>J)break;if(p>J+3&&Math.abs(p-b.p)<=J)near={b,e,dir:1}}
   for(let K=P*Math.ceil(a.C/P);K<a.A;K+=P){
    let key=[K,a.C,p].join("|");add(keys,key,a.weight);rootChecks++;ok(a.C>=C0&&a.C<C0+H,"root interval");
    if(near){let {b,e,dir}=near,q=b.p,off=K-a.C,shift=dir===1?p-1+e:-(q-1+e);
     ok(q!==p&&off>=0&&off<p-1&&b.C===a.C+shift&&mod(a.C+a.sg,p)===0&&mod(b.C+b.sg,q)===0,"close distinct CRT");
     let k=[p,q,e,dir,a.sg,b.sg].join("|"),o=close.get(k)||{p,q,e,dir,s:a.sg,t:b.sg,set:new Set()};
     o.set.add(key);close.set(k,o);cpKeys.add(key);closePaid+=a.weight;closeInc++;if(a.r<a.g/Math.log(2+p))closeNonrough+=a.weight;
     if(P%q===0){ok(mod(-off+shift+b.sg,q)===0,"q divides grid");inside++}else outside++;
     if(dir===1)forward++;else backward++;continue;
    }
    if(prior){let {b,e}=prior,q=b.p,h=a.v-b.v;
     ok(p!==q&&h>0&&h<=3*e+2*a.r&&mod(a.v-(a.sg===-1?0:p+2),2*p)===0&&mod(b.v-(b.sg===-1?0:q+2),2*q)===0,"prior time CRT");
     let pk=[K,a.C,p,b.C,q,a.v,b.v].join("|");add(phase,pk,a.weight);phaseKeys.add(key);phaseWeight+=a.weight;phaseInc++;phaseChecks++;
    }
   }
  }
 }
 for(let o of close.values()){let {p,q,e,dir,t,set}=o,shift=dir===1?p-1+e:-(q-1+e),aCount=0;
  for(let a=0;a<p-1;a+=2)if(P%q!==0||mod(-a+shift+t,q)===0)aCount++;
  let period=P*p*(P%q===0?1:q),cap=aCount*(Math.floor(lim/period)+1);
  ok(set.size<=cap,"relaxed close support");modChecks++;
 }
 for(let [key,w] of phase){let [K,C,p,A,q,v,V]=key.split("|").map(Number),m=w/(1.25*P),cap=(focus ? .02 : 1)*p/(R0+L+1);
  maxMass=Math.max(maxMass,m);if(m<=cap){capThin++;capPaid+=w}else capHeavy++;
 }
 for(let C=2*X-2;C<7*X;C+=2){let f=[...fac(C-1),...fac(C+1)],r=Math.min(...f);for(let p of f){if(p<=y||p>=2*P)continue;
  let n=Math.ceil((C+p-1)/P)-Math.ceil(C/P);if(!n)continue;
  let o=census.get(p)||{n:0,tail:[0,0,0,0],moment:0};o.n+=n;
  let rs=[3,5,11,23];for(let j=0;j<rs.length;j++)if(r>=rs[j])o.tail[j]+=n;
  o.moment+=n*Math.log(2+r)**2/(1+Math.log(Math.log(2+r)))**2;census.set(p,o);
 }}
 for(let [p,o] of census){ok(o.n<=2*(Math.floor(lim/P)+1)&&o.tail.every((v,i)=>i===0?v===o.n:v<=o.tail[i-1]),"relaxed tail census");tailChecks++;tailMax=Math.max(tailMax,o.moment/(X/P))}
 for(let [key,w] of keys){let [K,C,p]=key.split("|").map(Number);ok(w<=1.25*P*N+1e-7&&p>y,"projected weight");sourceChecks++}
 ok(closePaid+phaseWeight<=weight+1e-7&&capPaid<=phaseWeight+1e-7&&inside+outside===closeInc&&forward+backward===closeInc,"partition");
 const rd=x=>+x.toFixed(6);return {X,focus,B,T,P,y,J,L,R0,N,hit,events,short,weight:rd(weight),nonrough:rd(nonrough),closePaid:rd(closePaid),closeNonrough:rd(closeNonrough),closeInc,inside,outside,forward,backward,closeGroups:close.size,closeKeys:cpKeys.size,phaseWeight:rd(phaseWeight),phaseInc,phaseChecks,phaseKeys:phase.size,phaseProjectedKeys:phaseKeys.size,capThin,capHeavy,capPaid:rd(capPaid),maxMass:rd(maxMass),rootChecks,modChecks,sourceChecks,tailChecks,tailMax:rd(tailMax)};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
