// All-mass rational-band transition and adjusted phase audit. Finite diagnostic parameters.
function rationalAudit(X,K,L,J){
 const B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),Q=Math.max(5,Math.ceil(B/10)),lo=2*X-2,hi=7*X,lim=hi+B+L+20;
 const spf=new Int32Array(lim),r=new Int32Array(lim),fail=(b,s)=>{if(!b)throw Error(X+" "+s)},mod=(a,m)=>((a%m)+m)%m;
 function gcd(a,b){while(b){let t=a%b;a=b;b=t}return a}
 for(let p=2;p<lim;p++)if(!spf[p]){spf[p]=p;if(p*p<lim)for(let j=p*p;j<lim;j+=p)if(!spf[j])spf[j]=p}
 function factors(n){let a=[];while(n>1){let p=spf[n];if(p!==2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const labels=new Map();for(let C=lo;C<=hi;C+=2){let a=factors(C-1),b=factors(C+1);r[C]=Math.min(a[0]||B+1,b[0]||B+1);labels.set(C,[...a.map(p=>[p,-1]),...b.map(p=>[p,1])]);}
 const phase=(p,s)=>s===-1?0:p+2,high=(C,p)=>p>=Q&&r[C]>3&&2*r[C]>p,good=p=>p>L+3&&p>2*J&&p>K,ck=(C,p)=>`${C}|${p}`,key=(C,p,e,q)=>`${C}|${p}|${e}|${q}`;
 function relation(p,q){for(let a=1;a<=K;a++)for(let b=1;b<=K;b++){if(gcd(a,b)!==1)continue;let c=a*p-b*q;if(c&&Math.abs(c)<=J)return [a,b,c]}return null}
 const paths=[],centres=new Map();let N=0,events=0,raw=0,rawHigh=0,literal=0,phaseChecks=0;
 for(let M=X;M<2*X;M++)if(spf[M]===M){
   N++;let t=M+2,C=2*M-2,C0=C,cut=Math.floor((7*M-1)/4),es=[];
   while(C-C0<T){let v=Infinity,p=0,s=0;for(let [q,sg] of labels.get(C)){let j=t+1+mod(phase(q,sg)-t-1,2*q);if(j<v||(j===v&&q<p)){v=j;p=q;s=sg}}
     if(X<=1024){let vv=Infinity,pp=0;for(let j=t+1;j<=Math.min(cut,t+2*B);j++){let g=j%2?gcd(j-2,C+1):gcd(j,C-1),q=factors(g)[0];if(q){vv=j;pp=q;break}}fail((!p||v>cut)?vv===Infinity:vv===v&&pp===p,"literal MIN");literal++}
     if(!p||v>cut)break;
     let w=v-t,hh=high(C,p),D=C+p-1,kap=(2*v-D-6*(v%2))/(2*p),e={C,t,v,p,s,w,J:D,high:hh,kap,mark:false,markHigh:false};
     fail(w<=2*r[C]&&w<=3*(p-1)&&2*t>=C,"clock");fail(Number.isInteger(kap)&&(p===3||kap>=0),"adjusted phase");phaseChecks++;
     es.push(e);events++;raw+=w;if(hh){rawHigh+=w;if(good(p)){let z=ck(C,p),a=centres.get(z)||{C,p,s,n:0};a.n++;centres.set(z,a);}}
     C=D;t=v;
   }
   paths.push(es);
 }
 let support=new Map(),pairSet=new Set(),crtChecks=0,relationChecks=0,weightedKeys=0,closeSupport=0,qBelowQ=0,relaxCost=0;
 for(let a of centres.values())for(let e=0;e<=L;e+=2){
   let A=a.C+a.p-1+e;if(!labels.has(A))continue;
   for(let [q,t] of labels.get(A)){
     fail(q!==a.p,"distinct labels");
     let rel=relation(a.p,q);if(!rel)continue;
     let [k,l,c]=rel;fail(q>=a.p/(2*K)&&gcd(k,l)===1&&k*a.p-l*q===c&&c!==0,"reduced relation");
     fail((a.C+a.s)%a.p===0&&(A+t)%q===0,"spatial congruences");
     let n0=mod(a.C,a.p*q);fail((n0+a.s)%a.p===0&&(n0+a.p-1+e+t)%q===0,"CRT residue");crtChecks++;
     let z=key(a.C,a.p,e,q);fail(!support.has(z),"unique support");
     support.set(z,{p:a.p,q,e,rel});pairSet.add(`${a.p}|${q}`);weightedKeys+=a.p+q;
     if(Math.abs(a.p-q)<=J)closeSupport++;
     if(q<Q)qBelowQ++;
     relaxCost+=a.n*(2*a.p+3*e+2*q);
   }
 }
 let matches=0,highMatches=0,otherMatches=0,nonCloseMatches=0,lowPhaseChecks=0,resetChecks=0,oneZeroChecks=0,largeDriftChecks=0,phasePaid=0,actualCostSum=0;
 for(let es of paths)for(let i=0;i<es.length;i++)if(es[i].high&&good(es[i].p)){
   let a=es[i],nextHigh=-1;
   for(let j=i+1;j<es.length&&es[j].C-a.J<=L;j++){
     let b=es[j],e=b.C-a.J;fail(e>=0&&e%2===0,"background gain");
     if(b.high&&nextHigh<0)nextHigh=j;
     let rel=relation(a.p,b.p);
     if(rel){
       fail(support.has(key(a.C,a.p,e,b.p)),"actual support");matches++;if(b.high)highMatches++;else otherMatches++;if(Math.abs(a.p-b.p)>J)nonCloseMatches++;
       let w=0,g=0;for(let k=i;k<=j;k++){es[k].mark=true;if(b.high)es[k].markHigh=true;w+=es[k].w;if(k>i&&k<j)g+=es[k].p-1}
       fail(g===e&&w<=2*a.p+3*e+2*b.p,"actual interval bound");actualCostSum+=w;
     }
   }
   if(nextHigh>=0){let b=es[nextHigh],k=a.kap,l=b.kap;
     if(k>=0&&l>=0&&k<=K&&l<=K){
       const delta=Math.abs(k*a.p-l*b.p);
       if(k===0&&l===0){resetChecks++;continue}
       if(k===0||l===0){oneZeroChecks++;if(b.p>J)fail(delta>J,"one zero phase");}
       if(k>0&&l>0&&delta<=J){
         fail(a.p!==b.p&&delta>0&&relation(a.p,b.p)&&a.mark&&b.mark,"small phase transfer");lowPhaseChecks++;phasePaid+=a.w;
       }else if(delta>J)largeDriftChecks++;
     }
   }
 }
 let paid=0,paidHigh=0,paidOther=0,bothHighUnion=0,remaining=0,markedEvents=0;
 for(let es of paths)for(let a of es){if(a.mark){paid+=a.w;markedEvents++;if(a.high)paidHigh+=a.w;else paidOther+=a.w;}else if(a.high)remaining+=a.w;if(a.markHigh)bothHighUnion+=a.w;}
 fail(paid<=actualCostSum&&actualCostSum<=relaxCost&&paid===paidHigh+paidOther&&paidHigh+remaining===rawHigh,"union and support budgets");
 // Independently enumerate the reduced rational pair relation by (k,l,c,p), solving q exactly.
 let pairs=new Set();for(let k=1;k<=K;k++)for(let l=1;l<=K;l++)if(gcd(k,l)===1)for(let c=-J;c<=J;c++)if(c)for(let p=Q;p<=B;p++)if(spf[p]===p&&good(p)){let q=(k*p-c)/l;if(Number.isInteger(q)&&q>=3&&q<=B&&q!==p&&spf[q]===q)pairs.add(`${p}|${q}`);}
 for(let s of pairSet){fail(pairs.has(s),"independent pair enumeration");relationChecks++}
 return {X,B,T,Q,K,L,J,N,events,raw,rawHigh,literal,phaseChecks,centres:centres.size,support:support.size,pairSupport:pairSet.size,independentPairs:pairs.size,weightedKeys,crtChecks,relationChecks,closeSupport,qBelowQ,matches,highMatches,otherMatches,nonCloseMatches,lowPhaseChecks,resetChecks,oneZeroChecks,largeDriftChecks,phasePaid,actualCostSum,relaxCost,paid,paidHigh,paidOther,bothHighUnion,remaining,markedEvents};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(rationalAudit(X,4,16,8)));console.log(JSON.stringify(rationalAudit(65536,8,32,16)));
