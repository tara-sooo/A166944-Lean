// Rotation-based time CRT and all-mass same-high return audit. Finite diagnostic parameters.
function rotationAudit(X,J=16,theta=.4){
 const B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),H=T+B,Q=Math.max(5,Math.ceil(B/10)),R=Math.max(5,Math.ceil(Math.sqrt(B))),P=6,K=16,A0=3,m=8,lim=7*X+B+J+20;
 const spf=new Int32Array(lim),r=new Int32Array(lim),fail=(b,s)=>{if(!b)throw Error(`${X} ${s}`)},mod=(a,m)=>((a%m)+m)%m;
 for(let p=2;p<lim;p++)if(!spf[p]){spf[p]=p;if(p*p<lim)for(let j=p*p;j<lim;j+=p)if(!spf[j])spf[j]=p}
 function factors(n){let a=[];while(n>1){let p=spf[n];if(p!==2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const labels=new Map();for(let C=2*X-2;C<=7*X;C+=2){let a=factors(C-1),b=factors(C+1);r[C]=Math.min(a[0]||B+1,b[0]||B+1);labels.set(C,[...a.map(p=>[p,-1]),...b.map(p=>[p,1])]);}
 const phase=(p,s)=>s===-1?0:p+2,high=(C,p)=>p>=Q&&r[C]>3&&2*r[C]>p,key=(C,p)=>`${C}|${p}`;
 const paths=[],states=new Map(),centres=new Map();let N=0,events=0,raw=0,rawHigh=0,literal=0;
 function gcd(a,b){while(b){let c=a%b;a=b;b=c}return a}
 for(let M=X;M<2*X;M++)if(spf[M]===M){
   N++;let t=M+2,C=2*M-2,C0=C,cut=Math.floor((7*M-1)/4),es=[];
   while(C-C0<T){let v=Infinity,p=0,s=0;for(let [q,sg] of labels.get(C)){let j=t+1+mod(phase(q,sg)-t-1,2*q);if(j<v||(j===v&&q<p)){v=j;p=q;s=sg}}
     if(X<=1024){let vv=Infinity,pp=0;for(let j=t+1;j<=Math.min(cut,t+2*B);j++){let g=j%2?gcd(j-2,C+1):gcd(j,C-1),q=factors(g)[0];if(q){vv=j;pp=q;break}}fail((!p||v>cut)?vv===Infinity:vv===v&&pp===p,"literal MIN");literal++}
     if(!p||v>cut)break;
     let w=v-t,hh=high(C,p),e={C,t,v,p,s,w,J:C+p-1,high:hh,mark:false};
     fail(w<=2*r[C]&&w<=3*(p-1),"wait");es.push(e);events++;raw+=w;if(hh){rawHigh+=w;centres.set(key(C,p),{C,p,s});}
     for(let j=t;j<v;j++){let z=j*lim+C,a=states.get(z);if(!a){a={C,p,v,n:0,high:hh};states.set(z,a)}fail(a.p===p&&a.v===v,"deterministic state");a.n++;}
     C=e.J;t=v;
   }
   paths.push(es);
 }
 let support=new Map(),good=0,bad=0,small=0,rotationBlocks=0,rotationChecks=0,dirichletChecks=0,returnSupport=new Set(),returnPatterns=0;
 for(let c of centres.values()){
   let {C,p,s}=c,opts=[];
   if(p>P+2)for(let e=0;e<P;e+=2){let A=C+p-1+e;if(!labels.has(A))continue;
     for(let [q,t] of labels.get(A))if(q>=R&&q!==p){
       let kind="small",a=0,b=0;
       if(q>=Q){
         for(let d=1;d<=K;d++){let n=Math.round(d*p/q);if(Math.abs(d*p-n*q)*K<=q){a=d;b=n;break}}
         fail(a>0&&gcd(a,Math.abs(b))===1&&Math.abs(a*p-b*q)*K<=q,"Dirichlet");dirichletChecks++;
         kind=a<A0?"bad":"good";
       }
       if(kind==="bad")bad++;else if(kind==="small")small++;else good++;
       opts.push({q,t,e,kind,a,b});
       if(kind==="good"){
         const start=Math.ceil((C/2-phase(p,s))/(2*p)),last=Math.floor((C/2+3*H+2*B-phase(p,s))/(2*p)),n=last-start+1;
         let total=0;
         for(let j=start;j<=last;j+=a){
           let k=0;for(let l=j;l<=Math.min(last,j+a-1);l++){let v=phase(p,s)+2*p*l;if(1+mod(phase(q,t)-v-1,2*q)<=theta*q)k++;rotationChecks++}
           fail(k<=a*(theta/2+2/K)+2+1e-9,"rotation block");rotationBlocks++;total+=k;
         }
         fail(total<=Math.ceil(n/a)*(a*(theta/2+2/K)+2)+1e-9,"rotation total");
       }
     }
   }
   support.set(key(C,p),opts);
   if(p>2*J+8)for(let e0=0;e0<=J;e0+=2){let U=C+p-1+e0;if(!labels.has(U))continue;
     for(let [q,t] of labels.get(U))if(q!==p)for(let e1=0;e0+e1<=J;e1+=2){
       let V=U+q-1+e1;if(!labels.has(V)||!high(V,p)||!labels.get(V).some(([a])=>a===p))continue;
       let s1=labels.get(V).find(([a])=>a===p)[1];
       let M=(q-2+e0+e1+s1-s)/p;
       fail(Number.isInteger(M)&&M>=1&&q>=p/2&&(C+s)%p===0&&(U+t)%q===0,"return congruence");
       returnPatterns++;returnSupport.add(`${C}|${p}|${q}|${e0}|${e1}`);
     }
   }
 }
 function timeMask(a){return (support.get(key(a.C,a.p))||[]).some(o=>o.kind==="bad"||1+mod(phase(o.q,o.t)-a.v-1,2*o.q)<=theta*o.q)}
 let actualCheap=0,actualGood=0,actualBad=0,actualSmall=0,retainedChecks=0,actualReturns=0,returnPaid=0,returnHigh=0,returnIntermediate=0,returnMinRatio=Infinity;
 for(let es of paths)for(let i=0;i<es.length;i++)if(es[i].high){
   let a=es[i],k=i+1;while(k<es.length&&es[k].p<=3)k++;
   if(k<es.length&&a.p>P+2&&es[k].p>=R&&es[k].p>3){
     let b=es[k],e=b.C-a.J,opts=support.get(key(a.C,a.p))||[],o=opts.find(o=>o.q===b.p&&o.e===e&&o.t===b.s);
     fail(o&&e<P&&b.p!==a.p,"actual first nonLOW support");
     const cheap=b.v-a.v<=theta*b.p,am={C:a.C,p:a.p,v:a.v};
     if(cheap){actualCheap++;fail(timeMask(am),"actual cheap mask");if(o.kind==="good")actualGood++;else if(o.kind==="bad")actualBad++;else actualSmall++;}
     let thin=false;for(let j=a.t;j<a.v;j++)if(states.get(j*lim+a.C).n<=m)thin=true;
     if(thin&&!timeMask(am)){fail(!cheap,"retained total time");retainedChecks++;}
   }
   let j=i+1;while(j<es.length&&!es[j].high)j++;
   if(j===es.length||es[j].p!==a.p||a.p<=2*J+8)continue;
   let G=es[j].C-a.J;
   fail(G>=a.p-1,"same high spacing");
   for(let l=i+1;l<j;l++){
     let q=es[l].p,e0=es[l].C-a.J,e1=es[j].C-es[l].J;
     if(e0+e1>J)continue;
     fail(returnSupport.has(`${a.C}|${a.p}|${q}|${e0}|${e1}`),"actual return support");
     actualReturns++;returnMinRatio=Math.min(returnMinRatio,q/a.p);
     for(let z=i;z<=j;z++)es[z].mark=true;
   }
 }
 let paid=0,paidBad=0,paidTime=0;for(let a of states.values())if(a.high&&a.n<=m&&timeMask(a)){paid+=a.n;if((support.get(key(a.C,a.p))||[]).some(o=>o.kind==="bad"))paidBad+=a.n;else paidTime+=a.n;}
 for(let es of paths)for(let e of es)if(e.mark){returnPaid+=e.w;if(e.high)returnHigh+=e.w;else returnIntermediate+=e.w}
 fail(returnPaid===returnHigh+returnIntermediate&&paid===paidBad+paidTime,"partitions");
 return {X,B,T,Q,R,J,theta,K,A0,m,N,events,raw,rawHigh,literal,centres:centres.size,good,bad,small,dirichletChecks,rotationBlocks,rotationChecks,actualCheap,actualGood,actualBad,actualSmall,retainedChecks,paid,paidBad,paidTime,returnPatterns,returnKeys:returnSupport.size,actualReturns,returnPaid,returnHigh,returnIntermediate,returnMinRatio:Number.isFinite(returnMinRatio)?returnMinRatio:null};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(rotationAudit(X,16,.4)));console.log(JSON.stringify(rotationAudit(65536,32,.8)));
