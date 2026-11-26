// Deferred CRT query rank identity on actual restricted trajectories.
function audit(){
 const ck=(a,m)=>{if(!a)throw Error(m)},mod=(a,b)=>(a%b+b)%b,lim=4000000,spf=new Uint32Array(lim+1);
 for(let p=2;p*p<=lim;p++)if(!spf[p])for(let n=p*p;n<=lim;n+=p)if(!spf[n])spf[n]=p;
 function fs(n){n=Math.abs(n);ck(n>=1&&n<=lim,"factor "+n);let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function ev(u,v,z){let p=Infinity,w=Infinity,e=0;for(let [n,s] of [[u-1,1],[u+1,-1]])for(let r of fs(n)){if(r>z)continue;let k=mod((s===1?0:r+2)-v,2*r)||2*r;if(k<w||k===w&&r<p){p=r;w=k;e=s}}return {p,w,e}}
 const rows=[];
 for(let [kind,y,z,R,end,D] of [["period",5,7,420,840,20],["period",6,11,4620,9240,24],["period",7,13,60060,120120,28],["period",9,17,1021020,2042040,36],["local",127,254,100000,112000,508],["local",503,1006,1000000,1012000,2012],["local",997,1994,1000000,1012000,3988]]){
  let H=[];for(let p=y;p<=z;p++)if(p>=5&&!spf[p])H.push(p);
  const N=(end-R)/6,period=kind==="period",groups=new Map();
  if(period)for(let p of H){ck(N%p===0,"group size");groups.set(p,{q:new Uint32Array(N/p),hit:new Uint32Array(N/p),n:new Uint32Array(N/p)})}
  let h0=Math.ceil((y-1)/2),maxh=3+3*(D+z)+4,phi=new Float64Array(maxh+1),a=new Float64Array(maxh+1);
  for(let h=1;h<=maxh;h++){for(let p of H){if((2*h+1)%p===0)a[h]+=1/p;if((2*h-5)%p===0)a[h]+=1/p;}phi[h]=phi[h-1]+a[h]}
  let s={kind,y,z,D,roots:0,events:0,highEvents:0,distinctHigh:0,repeatEvents:0,queryAttempts:0,distinctQueries:0,terminalQueries:0,terminalStops:0,gainStops:0,actualTicks:0,terminalTicks:0,pointwiseChecks:0,spacingChecks:0,groupChecks:0,groupHitSum:0,groupQuerySum:0,queryWeighted:0,coareaWeighted:0,distinctGain:0,highGain:0,totalGain:0,highOccupationEnergy:0,maxQueries:0,maxRepeat:0,perPrime:{}};
  for(let p of H)s.perPrime[p]={hits:0,queries:0,repeat:0};
  for(let X=Math.ceil(R/6)*6;X<end;X+=6){
   let u=X,v=X/2+3,G=0,seen=new Map(),used=new Set(),last=new Map(),counts=new Map(),up=0,down=0,intervals=[];
   function query(t,j,lastp,terminal){
    const e=t%2?-1:1,h=t-u/2,f=2*h+(e===1?1:-5);
    for(let p of fs(f)){if(p<y||p>z||used.has(p)||p>lastp)continue;
     let r=mod(e-(u-X),p);if(!seen.has(p))seen.set(p,new Set());let S=seen.get(p);s.queryAttempts++;
     ck(mod(u-e,p)===0?mod(t-(e===1?0:p+2),2*p)===0:true,"clock congruence");
     if(S.has(r)){ck(mod(X,p)!==r,"repeat positive");continue}
     S.add(r);s.distinctQueries++;if(terminal)s.terminalQueries++;
     if(mod(X,p)===r){ck(!terminal&&p===lastp&&j,"positive query winner");used.add(p);s.distinctHigh++;s.distinctGain+=p-1;s.perPrime[p].hits++}
    }
   }
   while(G<D){
    let r=ev(u,v,z);
    if(!isFinite(r.p)){s.terminalStops++;for(let j=1;j<=2*z;j++){query(v+j,false,Infinity,true);s.terminalTicks++}break}
    let g=r.p-1,h=v-u/2,k=h+r.w,hp=k-g/2;ck(hp>=0&&k<=maxh,"height");
    for(let j=1;j<=r.w;j++){query(v+j,j===r.w,j===r.w?r.p:Infinity,false);s.actualTicks++}
    if(r.p>=y){ck(used.has(r.p),"winner hit");s.highEvents++;s.highGain+=g;let n=(counts.get(r.p)||0)+1;counts.set(r.p,n);s.maxRepeat=Math.max(s.maxRepeat,n);
     if(last.has(r.p)){ck(u-last.get(r.p)>=2*(r.p-1),"same label source spacing");s.spacingChecks++;s.repeatEvents++;s.perPrime[r.p].repeat++}last.set(r.p,u)}
    up+=phi[k]-phi[h];down+=phi[k]-phi[hp];intervals.push([hp+1,k]);u+=g;v+=r.w;G+=g;s.events++;
   }
   if(G>=D)s.gainStops++;
   let qsum=0;for(let p of H){let n=seen.get(p)?.size||0;ck(n<=p,"residue count");s.perPrime[p].queries+=n;qsum+=n/p;s.maxQueries=Math.max(s.maxQueries,n);
    if(period){let a=groups.get(p),i=((X-R)/6)%a.q.length;a.q[i]+=n;a.hit[i]+=used.has(p)?1:0;a.n[i]++}
   }
   let h=v-u/2;ck(Math.abs(up-down-(phi[h]-phi[3]))<1e-8,"coarea");let b=H.reduce((t,p)=>t+2/p,0);
   ck(qsum<=up+b+1e-8,"query cost");s.pointwiseChecks++;
   let hi=new Uint32Array(maxh+1);for(let [l,r] of intervals)for(let j=Math.max(l,h0);j<=r;j++)hi[j]++;
   let E=0;for(let j=h0;j<=maxh;j++)E+=hi[j]*hi[j];s.highOccupationEnergy+=E;s.queryWeighted+=qsum;s.coareaWeighted+=up+b;s.totalGain+=G;s.roots++;
  }
  if(period){
   for(let [p,g] of groups){for(let i=0;i<g.q.length;i++){let q=g.hit[i];ck(g.n[i]===p,"complete conditional lift");ck(g.q[i]===p*q-q*(q-1)/2,"exact query rank law "+JSON.stringify({y,p,i,q,sum:g.q[i]}));s.groupChecks++;s.groupHitSum+=q;s.groupQuerySum+=g.q[i]}}
   ck(s.distinctHigh<=2*s.queryWeighted+1e-7&&s.queryWeighted<=s.distinctHigh+1e-7,"two sided");}
  ck(s.terminalStops+s.gainStops===s.roots,"stops");rows.push(s);
 }
 return rows
}
console.log(JSON.stringify(audit(),null,2));
