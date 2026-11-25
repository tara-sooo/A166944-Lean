// Reproduce: node research/min_prime_root_band_birth_audit.mjs
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),analytic=mode==="analytic",T=analytic?Math.floor(X/u**.25):mode==="short"?B:4*B,Q=analytic?Math.ceil(B/u):mode==="wide"?7:Math.max(5,Math.ceil(B/8)),k=analytic?Math.max(1,Math.floor(u**.125)):2,L=analytic?Math.floor(u**2.25):1,A=analytic?Math.floor(B*Math.sqrt(u)):Math.max(2,Math.floor(B/8)),cap2=analytic?X*u**4:32,cap4=analytic?X*u**5/A:16,rmin=Q/(analytic?Math.sqrt(u):2);
 const lo=2*X-2,hi=7*X,lim=hi+5,ok=(v,m)=>{if(!v)throw Error(m);},mod=(a,m)=>((a%m)+m)%m,gcd=(a,b)=>{while(b){const c=a%b;a=b;b=c;}return a;};
 const spf=new Int32Array(lim+1);for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)spf[j]=spf[j]||n;}
 const fs=n=>{let a=[];while(n>1){const p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const rc=new Uint16Array(lim),hs=[];for(let C=lo;C<=hi;C+=2){const f=[...fs(C-1),...fs(C+1)];if(f.length)rc[C]=Math.min(...f);if(rc[C]>=rmin)hs.push(C);}
 let support2=0,support4=0;for(let i=0;i<hs.length;i++)for(let j=i+1;j<hs.length&&hs[j]-hs[i]<=A;j++){if(hs[j]-hs[i]===2)support2++;else support4++;}
 // Verify the residue count of three/four forms independently, with the quotient substitution.
 let residueChecks=0;for(let h=2;h<=A;h+=2)for(const q of [5,7,11,13,17,19,23,29,31]){if(q>=B||h%q===0||(h-2)%q===0&&h!==2||(h+2)%q===0)continue;for(const s of [-1,1]){const p=B%q===0?B+1:B;let count=0;for(let n=0;n<q;n++){let D=p*(2*n+1)-s;if([D-1,D+1,D+h-1,D+h+1].some(v=>mod(v,q)===0))count++;}ok(count===(h===2?3:4),"quotient residue rank");residueChecks++;}}
 const byC=new Map(),roots=new Map(),add=e=>{if(!byC.has(e.C))byC.set(e.C,[]);byC.get(e.C).push(e);};
 let N=0,R=0,G=0,events=0,visits=0,literal=0,cross=0,twins=0,other=0,Ihits=0,IR=0,Jhits=0,JR=0,maxBandCount=0;
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){N++;let C=2*M-2,t=M+2,cut=Math.floor((7*M-1)/4),a=[],bands=new Map(),cost=0;
   while(true){let e={M,C,t,p:0,r:0,band:-1,prev:0,bi:-1,keep:false};a.push(e);add(e);visits++;
     if(C-(2*M-2)>=T){cross++;break;}
     let tt=Infinity,p=Infinity;for(const sig of [-1,1])for(const q of fs(C+sig)){const tick=t+1+mod((sig===-1?0:q+2)-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;}}
     if(X<=1024){let lt=Infinity,lp=Infinity;for(let s=t+1;s<=cut;s++){const f=fs(gcd(s%2?s-2:s,C+(s%2?1:-1)));if(f.length){lt=s;lp=f[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal");literal++;}
     if(tt>cut){if(spf[C-1]===C-1&&spf[C+1]===C+1)twins++;else other++;break;}
     const r=rc[C];ok(r>0&&r<=p&&tt-t<=2*r,"clock");e.p=p;e.r=r;R+=r;cost+=r;events++;
     if(p>=Q&&r>p/(analytic?Math.sqrt(Math.log(p)):2)){ok(r>=rmin,"clock lower");e.band=Math.floor(Math.log2(r));if(!bands.has(e.band))bands.set(e.band,[]);const list=bands.get(e.band);e.bi=list.length;e.prev=list.length?list[list.length-1].C:0;list.push(e);Ihits++;IR+=r;}
     t=tt;C+=p-1;ok(C<=2*t,"horizon");
   }
   const gain=C-(2*M-2);G+=gain;ok(gain<T+B&&2*cost<=3*gain,"gain");if(gain>=T)ok(4*cost>=T-6,"cross");else if(!(spf[C-1]===C-1&&spf[C+1]===C+1))ok(cut-M-2<=3*T+2*B,"tail");
   maxBandCount=Math.max(maxBandCount,bands.size);
   // Diagnostic arbitrary submask, not an asymptotically cheap deletion.
   for(const list of bands.values())for(const e of list)if((e.bi+Math.floor(M/2))%3!==0){e.keep=true;Jhits++;JR+=e.r;}
   roots.set(M,{a,bands});
 }
 const names=["missing","postPhysical","firstL","closeSmall","closeLarge","far"],birthCounts=Array(6).fill(0),birthEnergy=Array(6).fill(0),youngI=Array(6).fill(0),youngJ=Array(6).fill(0),oldI={v:0},oldJ={v:0};
 const pairs=new Map(),groups=new Map(),flow=new Map();let EI=0,EJ=0,di=0,dj=0,bandPairs=0,allPairs=0,syncPairs=0,births=0,lateBirths=0,postBirths=0,maxBirths=0,maxAge=0,unmatched=0,postChecks=0,closeChecks=0,missingCount=0,submaskHoles=0,postSyncBirthPerBand=0;
 const gkey=(D,E)=>Math.min(D,E)+":"+Math.max(D,E);
 function grp(D,E){const id=gkey(D,E);if(!groups.has(id))groups.set(id,{D:Math.min(D,E),E:Math.max(D,E),n:0,allBirth:0,lateBirth:0,lateN:0,yi:0,yj:0});return groups.get(id);}
 for(const C of [...byC.keys()].sort((a,b)=>a-b)){
   const es=byC.get(C),ii=es.filter(e=>e.band>=0),jj=ii.filter(e=>e.keep);EI+=rc[C]*ii.length**2;EJ+=rc[C]*jj.length**2;di+=rc[C]*ii.length;dj+=rc[C]*jj.length;
   const pred=new Map();for(const e of ii)if(e.prev)pred.set(e.prev,(pred.get(e.prev)||0)+1);const pp=[...pred];for(let a=0;a<pp.length;a++)for(let b=a+1;b<pp.length;b++){const [D,n]=pp[a],[E,m]=pp[b];if(Math.abs(D-E)<=A){const id=gkey(D,E);flow.set(id,(flow.get(id)||0)+n*m);}}
   for(let i=0;i<es.length;i++)for(let j=i+1;j<es.length;j++){const a=es[i],b=es[j],id=(a.M-X)*X+b.M-X;ok(a.M<b.M,"source order");let q=pairs.get(id);if(!q){q={sync:false,n:0,bands:new Map(),extra:0,firstC:C};pairs.set(id,q);allPairs++;ok(2*(b.M-a.M)<T+B,"root locality");}
     if(q.sync){ok(a.t===b.t,"common physical suffix");postChecks++;}else if(a.t===b.t){q.sync=true;syncPairs++;}
     if(a.band<0||b.band<0)continue;ok(a.band===b.band&&a.r===b.r,"clock band");let v=q.bands.get(a.band);if(!v){v={ai:-1,bi:-1,age:0,cl:0,g:null,post:0,nb:0,seenBoth:false};q.bands.set(a.band,v);bandPairs++;}
     const extend=!!a.prev&&a.prev===b.prev;ok(extend===(v.age>0&&v.ai===a.bi-1&&v.bi===b.bi-1),"chain predecessor oracle");
     if(extend){v.age++;if(!v.prevKeep&&a.keep&&b.keep)submaskHoles++;}
     else{
       births++;q.n++;v.nb++;v.age=1;maxBirths=Math.max(maxBirths,q.n);
       if(v.nb>1){let gap=(a.bi-v.ai-1)+(b.bi-v.bi-1);ok(gap>=1,"new chain needs unmatched hit");q.extra+=gap;unmatched+=gap;}
       if(q.sync){postBirths++;v.post++;ok(v.post===1,"one birth per band after synchronization");postSyncBirthPerBand=Math.max(postSyncBirthPerBand,v.post);}
       const missing=!a.prev||!b.prev;if(missing)missingCount++;
       let gr=null;if(!missing&&Math.abs(a.prev-b.prev)<=A){ok(a.prev!==b.prev&&rc[a.prev]>=rmin&&rc[b.prev]>=rmin,"close predecessors");gr=grp(a.prev,b.prev);gr.n++;gr.allBirth+=2*a.r;closeChecks++;}
       let cl=missing?0:q.sync?1:q.n<=L?2:gr?3:5;
       if(q.n>L&&!missing&&!q.sync)lateBirths++;
       v.cl=cl;v.g=cl===3?gr:null;
       if(cl===3){gr.lateN++;gr.lateBirth+=2*a.r;}else{birthCounts[cl]++;birthEnergy[cl]+=2*a.r;}
     }
     v.ai=a.bi;v.bi=b.bi;v.prevKeep=a.keep&&b.keep;maxAge=Math.max(maxAge,v.age);
     if(v.age<=k){if(v.cl===3){v.g.yi+=2*a.r;if(v.prevKeep)v.g.yj+=2*a.r;}else{youngI[v.cl]+=2*a.r;if(v.prevKeep)youngJ[v.cl]+=2*a.r;}}
     else{oldI.v+=2*a.r;if(v.prevKeep)oldJ.v+=2*a.r;}
   }
 }
 let n2=0,n4=0,capPassed=0,capFailed=0,rawProduct=0,flowProduct=0,strictFlow=0;
 // Exact overlap product equals the count of all close births, regardless of their priority.
 for(const [id,g] of groups){ok(g.n===flow.get(id),"flow product oracle");const shift=g.E-g.D,cap=shift===2?cap2:cap4;ok(g.D>=lo&&g.E<=hi&&shift<=A,"arithmetic support membership");if(shift===2)n2++;else n4++;
   let r1=byC.get(g.D).filter(e=>e.band>=0).length,r2=byC.get(g.E).filter(e=>e.band>=0).length;rawProduct+=r1*r2;flowProduct+=g.n;if(g.n<r1*r2)strictFlow++;
   ok(g.n<=r1*r2&&g.yi<=2*k*B*g.lateN&&g.yj<=g.yi,"group young budget");
   const cl=g.n<=cap?3:4;if(g.lateN){if(cl===3)capPassed++;else capFailed++;}
   birthCounts[cl]+=g.lateN;birthEnergy[cl]+=g.lateBirth;youngI[cl]+=g.yi;youngJ[cl]+=g.yj;
 }
 ok(n2<=support2&&n4<=support4&&flow.size===groups.size,"support envelope");
 let highPairs=0;for(const q of pairs.values())if(q.n){highPairs++;ok(q.extra>=q.n-q.bands.size,"unmatched high hits");}
 ok(di===IR&&dj===JR&&EI===di+youngI.reduce((a,b)=>a+b,0)+oldI.v&&EJ===dj+youngJ.reduce((a,b)=>a+b,0)+oldJ.v,"energy ledger");
 ok(birthCounts.reduce((a,b)=>a+b,0)===births&&birthCounts[0]<=2*maxBandCount*highPairs&&postBirths<=maxBandCount*highPairs&&birthCounts[2]<=L*highPairs,"birth caps");
 ok(youngI.every((v,i)=>v<=2*k*birthEnergy[i])&&youngJ.every((v,i)=>v<=youngI[i]),"band young charge");
 return {mode,X,B,T,Q,k,L,A,cap2,cap4,N,R,G,events,visits,literal,cross,twins,other,Ihits,IR,Jhits,JR,EI,EJ,di,dj,support2,support4,residueChecks,allPairs,highPairs,syncPairs,bandPairs,births,lateBirths,postBirths,maxBirths,maxAge,unmatched,postChecks,closeChecks,missingCount,submaskHoles,postSyncBirthPerBand,n2,n4,capPassed,capFailed,rawProduct,flowProduct,strictFlow,birthCounts:Object.fromEntries(names.map((n,i)=>[n,birthCounts[i]])),birthEnergy:Object.fromEntries(names.map((n,i)=>[n,birthEnergy[i]])),youngI:Object.fromEntries(names.map((n,i)=>[n,youngI[i]])),youngJ:Object.fromEntries(names.map((n,i)=>[n,youngJ[i]])),oldI:oldI.v,oldJ:oldJ.v};
}
const xs=process.argv.slice(2).map(Number);for(const mode of ['short','wide','analytic'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
