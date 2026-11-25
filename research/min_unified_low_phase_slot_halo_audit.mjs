// Low-index high-exit slot and reset halo audit. Finite parameters, not analytic scales.
function slotAudit(X,mode="normal"){
 const B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),H=T+B,Q=Math.max(5,Math.ceil(B/10)),lo=2*X-2,hi=7*X,lim=hi+B+20,K=mode==="stress"?8:4,kappa=mode==="stress"?3:2,M=mode==="stress"?24:12;
 const spf=new Int32Array(lim),r=new Int32Array(lim),fail=(b,s)=>{if(!b)throw Error(X+" "+s)},mod=(a,m)=>((a%m)+m)%m;
 function gcd(a,b){while(b){let t=a%b;a=b;b=t}return a}
 for(let p=2;p<lim;p++)if(!spf[p]){spf[p]=p;if(p*p<lim)for(let j=p*p;j<lim;j+=p)if(!spf[j])spf[j]=p}
 function factors(n){let a=[];while(n>1){let p=spf[n];if(p!==2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const labels=new Map();for(let C=lo;C<=hi;C+=2){let a=factors(C-1),b=factors(C+1);r[C]=Math.min(a[0]||B+1,b[0]||B+1);labels.set(C,[...a.map(p=>[p,-1]),...b.map(p=>[p,1])]);}
 const phase=(p,s)=>s===-1?0:p+2,high=(C,p)=>p>=Q&&r[C]>3&&2*r[C]>p,key=(C,p,v)=>`${C}|${p}|${v}`,massCap=(p,k)=>M*B/(p*(k+1));
 const paths=[],slots=new Map(),ticks=new Map();let N=0,events=0,raw=0,rawHigh=0,literal=0,phaseChecks=0,resetRaw=0,phaseRaw=0;
 for(let M0=X;M0<2*X;M0++)if(spf[M0]===M0){
   N++;let t=M0+2,C=2*M0-2,C0=C,cut=Math.floor((7*M0-1)/4),es=[];
   while(C-C0<T){let v=Infinity,p=0,s=0;for(let [q,sg] of labels.get(C)){let j=t+1+mod(phase(q,sg)-t-1,2*q);if(j<v||(j===v&&q<p)){v=j;p=q;s=sg}}
     if(X<=1024){let vv=Infinity,pp=0;for(let j=t+1;j<=Math.min(cut,t+2*B);j++){let g=j%2?gcd(j-2,C+1):gcd(j,C-1),q=factors(g)[0];if(q){vv=j;pp=q;break}}fail((!p||v>cut)?vv===Infinity:vv===v&&pp===p,"literal MIN");literal++}
     if(!p||v>cut)break;
     let w=v-t,hh=high(C,p),J=C+p-1,d=2*v-J,k=(d-6*(v%2))/(2*p),e={C,t,v,p,s,w,J,high:hh,k,mark:false,resetMark:false};
     fail(w<=2*r[C]&&w<=3*(p-1)&&2*t>=C,"clock");
     fail(Number.isInteger(k)&&(p===3||k>=0),"phase");phaseChecks++;
     es.push(e);events++;raw+=w;
     if(hh){rawHigh+=w;if(k<=K){phaseRaw+=w;if(k===0)resetRaw+=w;let z=key(C,p,v),a=slots.get(z)||{C,p,v,k,s,n:0,wait:0,minT:v};a.n++;a.wait+=w;a.minT=Math.min(a.minT,t);slots.set(z,a);}}
     for(let j=t;j<v;j++){let z=j*lim+C,a=ticks.get(z)||{C,j,v,p,n:0};fail(a.v===v&&a.p===p,"deterministic tick");a.n++;ticks.set(z,a)}
     C=J;t=v;
   }
   paths.push(es);
 }
 let distinctCK=new Set(),slotChecks=0,lastTickChecks=0,thinSlots=0,thinResetSlots=0,slotBudget=0,slotActual=0,eligible=new Set(),resetEligible=new Set(),weightedSlotCount=0,phaseUniqueChecks=0,maxSlot=0;
 for(let [z,a] of slots){
   let ck=`${a.C}|${a.p}|${a.k}`;
   fail(!distinctCK.has(ck),"unique low-phase exit");distinctCK.add(ck);phaseUniqueChecks++;
   let v=(a.C+a.p-1+6*(a.s===1?1:0)+2*a.p*a.k)/2;
   fail(v===a.v&&mod(v-phase(a.p,a.s),2*a.p)===0,"exit formula");slotChecks++;
   fail(ticks.get((a.v-1)*lim+a.C).n===a.n,"last tick full mass");lastTickChecks++;
   weightedSlotCount+=a.p;
   maxSlot=Math.max(maxSlot,a.n);
   if(a.n<=massCap(a.p,a.k)){eligible.add(z);thinSlots++;if(a.k===0){resetEligible.add(z);thinResetSlots++}slotBudget+=massCap(a.p,a.k)*a.p;slotActual+=a.wait;}
 }
 let haloBudget=0,perPathGainBudget=0,perPathGain=0,paid=0,paidHigh=0,paidReset=0,paidOther=0,resetHalo=0,marked=0,centres=0,neighbourChecks=0;
 for(let es of paths){
   let halos=[],rh=[],budget=0;
   for(let a of es){let z=key(a.C,a.p,a.v);if(a.high&&eligible.has(z)){
     centres++;let h=[a.C-kappa*a.p,a.J+kappa*a.p];halos.push(h);if(resetEligible.has(z))rh.push(h);
     budget+=h[1]-h[0];
   }}
   haloBudget+=3*budget;perPathGainBudget+=budget;let gain=0;
   for(let a of es){if(halos.some(h=>h[0]<=a.C&&a.J<=h[1])){a.mark=true;gain+=a.p-1;paid+=a.w;marked++;if(a.high){paidHigh+=a.w;if(a.k===0)paidReset+=a.w;}else paidOther+=a.w;}
     if(rh.some(h=>h[0]<=a.C&&a.J<=h[1])){fail(a.mark,"reset halo subset");resetHalo+=a.w;}
     if(a.high&&eligible.has(key(a.C,a.p,a.v)))fail(a.mark,"centre covered");
   }
   fail(gain<=budget,"union gain bound");perPathGain+=gain;
   for(let i=0;i<es.length;i++)if(es[i].high&&eligible.has(key(es[i].C,es[i].p,es[i].v))){
     let a=es[i];if(a.k!==0)continue;
     for(let j=i+1;j<es.length&&es[j].J<=a.J+kappa*a.p;j++){fail(es[j].mark,"forward reset halo");neighbourChecks++;}
   }
 }
 fail(paid===paidHigh+paidOther&&paid<=haloBudget&&slotActual<=2*slotBudget,"linear budget");
 return {X,B,T,Q,K,kappa,M,N,events,raw,rawHigh,literal,phaseChecks,resetRaw,phaseRaw,slots:slots.size,phaseUniqueChecks,slotChecks,lastTickChecks,maxSlot,weightedSlotCount,thinSlots,thinResetSlots,slotActual,slotBudget,centres,haloBudget,perPathGainBudget,perPathGain,paid,paidHigh,paidOther,paidReset,resetHalo,marked,neighbourChecks,remainingHigh:rawHigh-paidHigh};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(slotAudit(X)));console.log(JSON.stringify(slotAudit(65536,'stress')));
