// Reproduce: node research/min_prime_root_high_history_audit.mjs
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),analytic=mode==="analytic",T=analytic?Math.floor(X/u**.25):mode==="short"?B:4*B,Q=analytic?Math.ceil(B/u):mode==="high"?Math.max(5,Math.ceil(B/8)):7,k=analytic?Math.max(1,Math.floor(u**.125)):mode==="one"?1:2,G=analytic?Math.floor(B*Math.sqrt(u)):B,tau=analytic?Math.floor(u**3):mode==="high"?1:2,mass=analytic?Math.floor(B*u**1.5):mode==="high"?2:4;
 const lim=7*X+5,spf=new Int32Array(lim+1),pr=[];for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n<=B&&n%2)pr.push(n);if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)spf[j]=spf[j]||n;}
 const fs=n=>{const a=[];while(n>1){const p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;},mod=(a,m)=>((a%m)+m)%m,gcd=(a,b)=>{while(b){const c=a%b;a=b;b=c;}return a;},ok=(v,m)=>{if(!v)throw Error(m);};
 const rmin=analytic?Q/Math.sqrt(u):Q/2,z=Math.max(1,Math.min(17,Math.ceil(rmin)-1)),qs=pr.filter(p=>p<=z);
 const rc=new Uint16Array(lim),rough=new Uint32Array(lim);let S=0,H=0,SH=0;
 for(let C=2*X-2;C<=7*X;C+=2){const a=[...fs(C-1),...fs(C+1)],r=a.length?Math.min(...a):0;rc[C]=r;S+=r;if(r>=rmin){H++;SH+=r;}}
 for(let C=1;C<lim;C++)rough[C]=rough[C-1]+Number(C>=2*X-2&&C<=7*X&&C%2===0&&qs.every(q=>(C-1)%q&&(C+1)%q));
 const byC=new Map(),roots=new Map(),add=(m,c,e)=>{if(!m.has(c))m.set(c,[]);m.get(c).push(e);};
 let N=0,R=0,events=0,literal=0,cross=0,twins=0,other=0,inputR=0,inputHits=0,spanSum=0,spanCost=0;
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){N++;let C=2*M-2,t=M+2,cut=Math.floor((7*M-1)/4),ar=[],cost=0;
   while(C-(2*M-2)<T){let tt=Infinity,p=Infinity;for(const sig of [-1,1])for(const q of fs(C+sig)){const tick=t+1+mod((sig===-1?0:q+2)-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;}}
     if(X<=1024){let lt=Infinity,lp=Infinity;for(let s=t+1;s<=cut;s++){const f=fs(gcd(s%2?s-2:s,C+(s%2?1:-1)));if(f.length){lt=s;lp=f[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal");literal++;}
     if(tt>cut)break;const r=rc[C];ok(r>0&&r<=p&&tt-t<=2*r,"clock");R+=r;cost+=r;events++;
     if(p>=Q&&r>p/(analytic?Math.sqrt(Math.log(p)):2)){ok(r>=rmin&&qs.every(q=>(C-1)%q&&(C+1)%q),"rough input");const e={M,C,p,r,i:ar.length,keep:false};ar.push(e);add(byC,C,e);inputR+=r;inputHits++;}
     t=tt;C+=p-1;ok(C<=2*t,"invariant");
   }
   const gain=C-(2*M-2);ok(gain<T+B&&2*cost<=3*gain,"gain");
   if(gain>=T){cross++;ok(4*cost>=T-6,"cross");}else if(spf[C-1]===C-1&&spf[C+1]===C+1)twins++;else{other++;ok(cut-M-2<=3*T+2*B,"tail");}
   let ss=0;for(let i=k;i<ar.length-k;i++){ss+=ar[i+k].C-ar[i-k].C;}
   ok(ss<=2*k*gain,"two-sided telescoping");spanSum+=ss;roots.set(M,ar);
 }
 let lowHorizons=0,lowInc=0,E0=0,diag=0;for(const [C,es] of byC){E0+=rc[C]*es.length**2;diag+=rc[C]*es.length;if(es.length<=mass){lowHorizons++;lowInc+=es.length;}}
 ok(diag===inputR&&lowInc<=mass*H,"input energy");
 const lags=[];for(let j=1;j<=k;j++)lags.push(-j,j);
 let endCost=0,endHits=0,spanHits=0,globalCost=0,globalHits=0,groupCost=0,groupHits=0,groupRemoved=0,passes=0,cascadeHits=0,cascadeCost=0,postGate=0,peelCandidate=0,roughBound=0,localChecks=0,finalR=0,finalHits=0,Efinal=0,finalHorizons=0,maxGroup=0,minGroup=Infinity,finalLagMass=Array(2*k).fill(0),transfer=Array(2*k).fill(0),currentInternal=Array(2*k).fill(0),transferChecks=0,candidateGroupCount=0,initialSmall=0;
 const w=(C)=>byC.get(C)?.length||0;
 for(const [C,es] of byC){
   let current=[];for(const e of es){const ar=roots.get(e.M),i=e.i;
     if(i<k||i+k>=ar.length){endCost+=e.r;endHits++;continue;}
     if(ar[i+k].C-ar[i-k].C>G){spanCost+=e.r;spanHits++;continue;}
     e.ds=lags.map(j=>ar[i+j].C);ok(e.ds.every(D=>Math.abs(D-C)<=G&&D!==C),"lag span");
     if(w(C)<=mass||e.ds.some(D=>w(D)<=mass)){globalCost+=e.r;globalHits++;continue;}
     current.push(e);
   }
   if(!current.length)continue;
   postGate+=current.length;const lo=Math.max(0,C-G-1),hi=Math.min(lim-1,C+G),cap=rough[hi]-rough[lo];roughBound+=rc[C]*2*k*cap*tau;
   const maps=ar=>lags.map((j,h)=>{const m=new Map();for(const e of ar){const D=e.ds[h];if(!m.has(D))m.set(D,[]);m.get(D).push(e);}return m;});
   let groups=maps(current);const nkeys=groups.reduce((s,m)=>s+m.size,0);candidateGroupCount+=nkeys;ok(groups.every(m=>m.size<=cap),"local rough support");localChecks+=groups.length;peelCandidate+=rc[C]*tau*nkeys;
   const ever=new Set();let round=0;
   while(current.length){const bad=new Set();for(let h=0;h<groups.length;h++)for(const [D,ar] of groups[h])if(ar.length<=tau){const id=h+":"+D;ok(!ever.has(id),"group removed once");ever.add(id);groupRemoved++;if(round===0)initialSmall++;for(const e of ar)bad.add(e);}
     if(!bad.size)break;round++;passes++;
     for(const e of bad){groupCost+=e.r;groupHits++;if(round>1){cascadeHits++;cascadeCost+=e.r;}}
     current=current.filter(e=>!bad.has(e));groups=maps(current);
   }
   ok(ever.size<=nkeys,"peeling ledger");
   if(!current.length)continue;finalHorizons++;finalR+=rc[C]*current.length;finalHits+=current.length;Efinal+=rc[C]*current.length**2;
   for(const e of current)e.keep=true;
   for(let h=0;h<groups.length;h++)for(const [D,ar] of groups[h]){ok(ar.length>tau,"simultaneous thickness");minGroup=Math.min(minGroup,ar.length);maxGroup=Math.max(maxGroup,ar.length);finalLagMass[h]+=ar.length;transfer[h]+=rc[D]*ar.length**2;currentInternal[h]+=rc[C]*ar.length**2;for(const e of ar){const a=roots.get(e.M);ok(a[e.i+lags[h]].C===D,"lag identity");transferChecks++;}}
 }
 ok(endHits<=2*k*N&&endCost<=B*endHits&&spanHits*G<=spanSum&&spanCost<=B*spanHits,"end and span budgets");ok(globalHits<= (2*k+1)*lowInc&&globalCost<=B*globalHits,"global neighbor mass budget");
 ok(groupCost<=peelCandidate&&peelCandidate<=roughBound&&inputHits===endHits+spanHits+globalHits+groupHits+finalHits&&inputR===endCost+spanCost+globalCost+groupCost+finalR,"peeling partition");
 ok(finalLagMass.every(n=>n===finalHits)&&transfer.every(n=>n<=E0),"transfer energy upper");
 // Independent lag transfer oracle: at each original D partition its tags by signed successor C and surviving flag.
 for(let h=0;h<lags.length;h++){let val=0;for(const [D,es] of byC){let mm=new Map();for(const e of es){const ar=roots.get(e.M),v=ar[e.i-lags[h]];if(v?.keep)mm.set(v.C,(mm.get(v.C)||0)+1);}const sum=[...mm.values()].reduce((s,n)=>s+n*n,0);ok(sum<=es.length**2,"injective reverse partition");val+=rc[D]*sum;}ok(val===transfer[h],"independent reverse oracle");}
 // Shared-high chain births/young/old on the ORIGINAL input, independent of peeling.
 let birthE=0,youngE=0,oldE=0,pairE=0,births=0,maxChain=0,longPairs=0;const seen=new Map();
 for(const C of [...byC.keys()].sort((a,b)=>a-b)){const es=byC.get(C);for(let i=0;i<es.length;i++)for(let j=i+1;j<es.length;j++){const a=es[i],b=es[j],id=(Math.min(a.M,b.M)-X)*X+Math.max(a.M,b.M)-X,prev=seen.get(id);let age=1;if(prev&&prev.ai===a.i-1&&prev.bi===b.i-1){age=prev.age+1;ok(roots.get(a.M)[a.i-1].C===roots.get(b.M)[b.i-1].C,"chain predecessor");}
 // byC constructed in ascending root order, so pair ordering stable.
 if(age===1){birthE+=2*rc[C];births++;}if(age<=k)youngE+=2*rc[C];else{oldE+=2*rc[C];longPairs++;}pairE+=2*rc[C];maxChain=Math.max(maxChain,age);seen.set(id,{ai:a.i,bi:b.i,age});}}
 ok(E0===diag+pairE&&pairE===youngE+oldE&&youngE*rmin<=k*B*birthE+1e-5,"chain energy ledger");
 return {mode,X,B,T,Q,k,G,tau,mass,N,R,events,literal,cross,twins,other,inputR,inputHits,H,SH,S,z,E0,lowHorizons,lowInc,endCost,endHits,spanCost,spanHits,globalCost,globalHits,postGate,groupCost,groupHits,groupRemoved,passes,cascadeHits,cascadeCost,initialSmall,localChecks,candidateGroupCount,peelCandidate,roughBound,finalR,finalHits,Efinal,finalHorizons,minGroup:Number.isFinite(minGroup)?minGroup:null,maxGroup,transfer,transferChecks,currentInternal,birthE,births,youngE,oldE,maxChain,longPairs};
}
const xs=process.argv.slice(2).map(Number);for(const mode of ['analytic','short','wide','high','one'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
