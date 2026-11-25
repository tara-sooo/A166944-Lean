// Compressed word low-phase slot and all-event halo audit. Finite diagnostic parameters.
function audit(X,stress=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),Q=Math.max(5,Math.ceil(B/10)),P=6,kmax=stress?3:2,D1=Math.floor(Math.sqrt(B)),D2=Math.floor(B**.8),kap=stress?3:2,M=stress?32:12,lo=2*X-2,hi=7*X,lim=hi+B+P+20;
 const spf=new Int32Array(lim),r=new Int32Array(lim),fail=(v,s)=>{if(!v)throw Error(X+" "+s)},mod=(a,m)=>((a%m)+m)%m;
 function gcd(a,b){while(b){let c=a%b;a=b;b=c}return a}
 for(let p=2;p<lim;p++)if(!spf[p]){spf[p]=p;if(p*p<lim)for(let j=p*p;j<lim;j+=p)if(!spf[j])spf[j]=p}
 function factors(n){let a=[];while(n>1){let p=spf[n];if(p!==2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const labels=new Map();for(let C=lo;C<=hi;C+=2){let a=factors(C-1),b=factors(C+1);r[C]=Math.min(a[0]||B+1,b[0]||B+1);labels.set(C,[...a.map(p=>[p,-1]),...b.map(p=>[p,1])]);}
 const high=(C,p)=>p>=Q&&r[C]>3&&2*r[C]>p,phase=(p,s)=>s===-1?0:p+2,good=p=>p>D2&&p>kmax*(D2+P)+P,sk=a=>`${a.C}|${a.p}|${a.v}`;
 const paths=[],groups=new Map(),starts=new Map(),slots=new Map();let N=0,events=0,raw=0,rawHigh=0,literal=0,phaseChecks=0,wordChecks=0,nonresetNext=0,nonzeroStart=0,extended=0,nonempty=0,slotChecks=0,roughChecks=0,compressedChecks=0;
 for(let root=X;root<2*X;root++)if(spf[root]===root){
  N++;let t=root+2,C=2*root-2,C0=C,cut=Math.floor((7*root-1)/4),es=[];
  while(C-C0<T){
   let v=Infinity,p=0,s=0;for(let [q,sg] of labels.get(C)){let j=t+1+mod(phase(q,sg)-t-1,2*q);if(j<v||(j===v&&q<p)){v=j;p=q;s=sg}}
   if(X<=1024){let vv=Infinity,pp=0;for(let j=t+1;j<=Math.min(cut,t+2*B);j++){let g=j%2?gcd(j-2,C+1):gcd(j,C-1),q=factors(g)[0];if(q){vv=j;pp=q;break}}fail((!p||v>cut)?vv===Infinity:vv===v&&pp===p,"literal MIN");literal++}
   if(!p||v>cut)break;
   let w=v-t,J=C+p-1,j=(2*v-J-6*(v%2))/(2*p),hh=high(C,p),a={C,t,v,p,s,w,J,j,high:hh,mark:false};
   fail(w<=2*r[C]&&w<=3*(p-1)&&Number.isInteger(j)&&(p===3||j>=0),"clock and phase");phaseChecks++;
   if(hh){rawHigh+=w;slots.set(sk(a),(slots.get(sk(a))||0)+1);}
   es.push(a);events++;raw+=w;C=J;t=v;
  }
  let prev=-1;
  for(let i=0;i<es.length;i++)if(es[i].high){
   if(prev>=0){let a=es[prev],b=es[i],gap=es.slice(prev+1,i),non=gap.filter(x=>x.p>3),h=non.length,D=[...new Set(non.map(x=>x.p))].reduce((x,y)=>x*y,1);
    if(good(a.p)&&h<=kmax&&D<=D2){
      let off=[],word=[],z=a.J;for(let x of non){off.push(x.C-z);word.push([x.p,x.s]);z=x.J;}off.push(b.C-z);
      fail(off.every(e=>e>=0&&e<P&&e%2===0),"LOW compression");compressedChecks+=off.length;
      fail(gap.reduce((n,x)=>n+x.p-1,0)===b.C-a.J,"gap gain");
      fail(a.p!==b.p,"distinct endpoint primes");
      let m=1;for(let x of non){fail(x.p!==a.p&&(x.C+x.s)%x.p===0,"word congruence");wordChecks++;if(m%x.p!==0)m*=x.p;}fail(m===D,"radical");
      let form=[(a.C+a.s)/a.p,a.C-a.s,b.C-1,b.C+1];
      for(let q=3;q<Math.min(a.p/2,b.p/2);q+=2)if(spf[q]===q){fail(form.every(f=>f%q!==0),"rough four forms");roughChecks++}
      let key=sk(a),sig=JSON.stringify([word,off,b.C,b.p,b.v]),g=groups.get(key)||{a,b,D,h,n:0,sig};
      fail(g.sig===sig&&g.D===D,"deterministic actual suffix");g.n++;groups.set(key,g);
      let spatial=JSON.stringify([a.C,a.p,word,off,b.p]);let set=starts.get(spatial)||new Set();set.add(a.j);starts.set(spatial,set);
      if(h)nonempty++;if(D>D1)extended++;if(a.j)nonzeroStart++;if(b.j)nonresetNext++;
      a.pairKey=key;a.pairEnd=i;
    }
   }prev=i;
  }
  paths.push(es);
 }
 const eligible=new Set();let eligibleReset=0,eligiblePositive=0,eligibleExtended=0,heavy=0,maxMass=0,phaseSlotChecks=0,eligibleNonresetNext=0,eligibleNonempty=0,capCost=0;
 for(let [key,g] of groups){
   fail(g.n<=slots.get(key)&&g.n<=slots.get(sk(g.b)),"cohort endpoint subset");slotChecks++;
   let a=g.a;fail(a.v===(a.C+a.p-1+6*(a.s===1?1:0)+2*a.p*a.j)/2,"unique phase");phaseSlotChecks++;
   let cap=M*B/(a.p+g.b.p)/(a.j+1)*(g.D<=D1?2:1);
   maxMass=Math.max(maxMass,g.n);if(g.n<=cap){eligible.add(key);capCost+=cap*(a.p+g.b.p);if(a.j===0)eligibleReset++;else eligiblePositive++;if(g.D>D1)eligibleExtended++;if(g.b.j)eligibleNonresetNext++;if(g.h)eligibleNonempty++;}else heavy++;
 }
 let haloBudget=0,paid=0,paidHigh=0,paidOther=0,paidReset=0,marked=0,covered=0,eligibleTagPairs=0,extendedPaid=0,nonresetNextPaid=0,heavyTagPairs=0;
 for(let es of paths){let halos=[],chosen=[];for(let i=0;i<es.length;i++){let a=es[i];if(a.pairKey){if(eligible.has(a.pairKey)){let b=es[a.pairEnd],h=[a.C-kap*a.p,b.J+kap*b.p];halos.push(h);haloBudget+=3*(h[1]-h[0]);chosen.push([i,a.pairEnd]);eligibleTagPairs++;if(groups.get(a.pairKey).D>D1)extendedPaid++;if(b.j)nonresetNextPaid++;}else heavyTagPairs++;}}
   for(let a of es)if(halos.some(h=>h[0]<=a.C&&a.J<=h[1])){a.mark=true;marked++;paid+=a.w;if(a.high){paidHigh+=a.w;if(a.j===0)paidReset+=a.w;}else paidOther+=a.w;}
   for(let [i,j] of chosen){for(let l=i;l<=j;l++)fail(es[l].mark,"whole sequence coverage");covered++;}
 }
 fail(paid===paidHigh+paidOther&&paid<=haloBudget,"union budget");
 let phaseVariants=0,maxVariants=0;for(let s of starts.values()){phaseVariants+=s.size;maxVariants=Math.max(maxVariants,s.size)}
 return {X,B,T,Q,P,kmax,D1,D2,kap,M,N,events,raw,rawHigh,literal,phaseChecks,wordChecks,roughChecks,compressedChecks,groups:groups.size,spatialKeys:starts.size,phaseVariants,maxVariants,nonempty,extended,nonresetNext,nonzeroStart,slotChecks,phaseSlotChecks,eligible:eligible.size,eligibleReset,eligiblePositive,eligibleExtended,eligibleNonempty,eligibleNonresetNext,heavy,maxMass,capCost,eligibleTagPairs,heavyTagPairs,extendedPaid,nonresetNextPaid,haloBudget,paid,paidHigh,paidOther,paidReset,remainingHigh:rawHigh-paidHigh,marked,covered};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));console.log(JSON.stringify(audit(65536,true)));
