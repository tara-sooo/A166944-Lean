// Congruence-specific absorption recharge and paired rough-source capacity diagnostics.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b,N=420000,spf=new Uint32Array(N+2);
 for(let p=2;p*p<=N+1;p++)if(!spf[p])for(let n=p*p;n<=N+1;n+=p)if(!spf[n])spf[n]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
 function q(a){return Math.min(...fs(a-1),...fs(a+1))}
 function isrough(a,z){return q(a)>z}
 let profiles=[],tables=[];
 for(let z of [3,5,7]){
  let A=[];for(let p=3;p<=z;p+=2)if(!spf[p])A.push(p);
  let Q=2*A.reduce((a,p)=>a*p,1),R=new Uint16Array(Q*Q/2),rough=new Uint8Array(Q/2);
  let idx=(a,k)=>mod(a,Q)/2*Q+mod(k,Q),get=(a,k)=>R[idx(a,k)],rr=a=>rough[mod(a,Q)/2]===1;
  function low(a,k){return A.find(p=>mod(k%2?k+2:k,p)===0&&mod(a-(k%2?1:-1),p)===0)||0}
  for(let a=0;a<Q;a+=2){let E=[];for(let p of A){if(mod(a+1,p)===0)E.push([p,0]);else if(mod(a-1,p)===0)E.push([p,p+2])}
   if(!E.length){rough[a/2]=1;continue}
   for(let k=0;k<Q;k++){let p=Infinity,w=Infinity;for(let [r,t] of E){let h=mod(t+k,2*r)||2*r;if(h<w||h===w&&r<p){p=r;w=h}}R[idx(a,k)]=w+get(a-p+1,k-w)}
  }
  let classes={},checks=0,maxR=Math.max(...(z<7?R:[0]));if(z===7)for(let r of R)maxR=Math.max(maxR,r);
  for(let r=1;r<Q;r+=2)if(A.every(p=>r%p)){
   let s={r,max:0,min:0,maxActive:0,maxRough:0,maxEven:0,maxOdd:0,roughBoth:0,valid:0};
   for(let a=0;a<Q;a+=2)for(let k=0;k<Q;k++){if(low(a,k))continue;let b=a-r+1,d=get(b,k)-get(a,k);s.valid++;checks++;
    s.max=Math.max(s.max,d);s.min=Math.min(s.min,d);if(rr(a)){s.maxRough=Math.max(s.maxRough,d);if(rr(b)){ck(d===0,"rough zero");s.roughBoth++}}else s.maxActive=Math.max(s.maxActive,d);
    if(k%2)s.maxOdd=Math.max(s.maxOdd,d);else s.maxEven=Math.max(s.maxEven,d);
   }
   let prod=1;for(let l of A){let nu=new Set([mod(-1,l),1,mod(r-2,l),mod(r,l)]).size;prod*=l-nu}
   ck(s.roughBoth===prod*Q,"rough pair CRT");classes[r]=s;
  }
  profiles.push({z,Q,maxR,checks,classes:Object.values(classes)});tables.push({z,Q,get,rr,low,classes})
 }
 let crt=[];
 for(let z of [3,5,7,11,13]){
  let A=[];for(let p=3;p<=z;p+=2)if(!spf[p])A.push(p);let Q=2*A.reduce((x,p)=>x*p,1),row={z,Q,primeClasses:0,states:0,pairChecks:0,zeroClasses:0};
  for(let p of [17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]){
   if(p<=z)continue;
   let prod=1;for(let l of A){let nu=new Set([mod(-1,l),1,mod(p-2,l),mod(p,l)]).size;let v=p%l===1?2:p%l===3%l||p%l===l-1?3:4;ck(nu===v,"local dimension");prod*=l-nu}
   // For a=pm+e, even a requires odd m. Each of the Q/2 odd m residues
   // ranges once over every allowed small-prime residue, since p coprime Q.
   for(let e of [-1,1]){let n=0;for(let m=1;m<Q;m+=2){let a=p*m+e,b=a-p+1;let both=A.every(l=>mod(a-1,l)&&mod(a+1,l)&&mod(b-1,l)&&mod(b+1,l));
    if(both)n++;row.states++}
    ck(n===prod,"progression CRT");row.pairChecks++}
   row.primeClasses++;if(prod===0)row.zeroClasses++;
  }
  crt.push(row)
 }
 let slabs=[];
 for(let [R,z] of [[10000,5],[10000,17],[100000,7],[100000,31],[200000,53]]){
  let byP=new Map(),s={R,z,sources:0,roughSources:0,eligible:0,pairEligible:0,formsChecks:0,neutralMod6:0,capacity:0,maxLabelCapacity:0,distinct:0,excludedNonrough:0,primeTargets:0};
  for(let a=R+(R%2);a<2*R;a+=2){
   s.sources++;let qa=q(a);if(qa<=z)continue;s.roughSources++;
   for(let e of [-1,1])for(let p of fs(a-e)){
    s.eligible++;let b=a-p+1;if(b<2){s.primeTargets++;continue}
    let qb=q(b),m=(a-e)/p,forms=[m,p*m+2*e,p*(m-1)+e,p*(m-1)+e+2],ok=forms.every(n=>fs(n).every(l=>l>z));
    ck(ok===(qb>z),"four forms");s.formsChecks++;
    if(!ok){s.excludedNonrough++;continue}
    ck(p%6===1,"rough pair label mod 6");s.neutralMod6++;s.pairEligible++;
    let w=2*Math.min(p,qa);byP.set(p,(byP.get(p)||0)+w);s.capacity+=w;
   }
  }
  s.distinct=byP.size;for(let c of byP.values())s.maxLabelCapacity=Math.max(s.maxLabelCapacity,c);slabs.push(s)
 }
 let paths={roots:0,events:0,profileChecks:0,telescopes:0,roughPairChecks:0,roughPairTicks:0,roughSourceTicks:0,roughEntryTicks:0,elapsed:0,slabCapacityChecks:0,highByClass:{}};
 for(let X=12;X<=200000;X+=198){let a=X,v=-X/2+3,sums=tables.map(t=>({start:t.get(a,-v),active:0,delta:0,upper:0}));
  while(v< -1&&a){let p=Infinity,w=Infinity,e=0;for(let [d,sg] of [[a+1,-1],[a-1,1]])for(let r of fs(d)){let j=mod((sg===-1?0:r+2)-v,2*r)||2*r;if(j<w||j===w&&r<p){p=r;w=j;e=sg}}
   let W=Math.min(w,-1-v),b=W===w?a-p+1:a,k=-v-W,qa=q(a);
   for(let i=0;i<tables.length;i++){let t=tables[i],s=sums[i],high=W===w&&p>t.z,d=high?t.get(b,k)-t.get(a,k):0;
    s.active+=W*(t.rr(a)?0:1);s.delta+=d;
    if(high){ck(t.low(a,k)===0,"no low preemption");let c=t.classes[p%t.Q];ck(d<=c.max&&d>=c.min&&d<=(t.rr(a)?c.maxRough:c.maxActive)&&d<=(k%2?c.maxOdd:c.maxEven),"class profile");s.upper+=t.rr(a)?c.maxRough:c.maxActive;paths.profileChecks++;}
   }
   if(qa>7){paths.roughSourceTicks+=W;if(W===w&&b>=2&&q(b)>7){ck(p%6===1,"actual pair residue");paths.roughPairTicks+=W;paths.roughPairChecks++}else if(W===w)paths.roughEntryTicks+=W;}
   paths.elapsed+=W;paths.events++;a=b;v+=W;
  }
  for(let i=0;i<tables.length;i++){let t=tables[i],s=sums[i];ck(s.active===s.start-t.get(a,-v)+s.delta&&s.delta<=s.upper,"profile telescope");paths.telescopes++}
  paths.roots++;
 }
 return {profiles,crt,slabs,paths};
}
console.log(JSON.stringify(audit(),null,2));
