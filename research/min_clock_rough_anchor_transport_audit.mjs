// All-odd rough target, last-nonLOW anchor and weighted support audit.
function audit(X, stress=false){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,u=Math.log(B),D=Math.max(1,Math.floor(stress?B/4:B/u**2)),rough=Math.max(3,Math.ceil(D/4)),ratio=stress?2:u**(1/16),cap=stress?12:u**(11/4);
 const assert=(x,m)=>{if(!x)throw Error(m)},close=(a,b)=>Math.abs(a-b)<1e-7*Math.max(1,Math.abs(a),Math.abs(b));
 const spf=new Int32Array(8*X+100);
 for(let i=2;i<spf.length;i++)if(!spf[i])for(let j=i;j<spf.length;j+=i)if(!spf[j])spf[j]=i;
 let L=2,y=2;const lmax=stress?30:u**(1/16);
 for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>lmax)break;L*=p;y=p}
 function factors(n){const out=[];while(n>1){let p=spf[n];out.push(p);while(n%p===0)n/=p}return out}
 function r(C){let p=Math.min(spf[C-1]||Infinity,spf[C+1]||Infinity);return p<=B?p:0}
 function gcd(a,b){while(b){let t=a%b;a=b;b=t}return a}
 const anchors=new Map(),g=[new Map(),new Map()],roughTargets=new Map();
 let roots=0,anchorVisits=0,oracle=0,rootOnlyVisits=0,roughVisits=0,maxTail=0,maxLowRootCount=0;
 for(let M=X+1;M<2*X;M+=2){
   roots++;const s=M+2,K=Math.floor((7*M-1)/4);assert(s+H+2*B<=K,"original cutoff");
   let t=s,C=2*M-2,anc=null;
   while(t<s+H){
     const q0=r(C);if(!q0)break;
     const lo=t;let p=0;
     while(!p){t++;const side=t%2,gg=gcd(t-2*side,C+2*side-1);p=spf[gg]||0;if(p>B)p=0}
     assert(t-lo<=2*q0&&t<=s+H+2*B,"completed wait");
     if(q0>=rough&&q0>y){
       roughVisits++;const J=anc?anc.J:2*M-2,b=anc?anc.t:s;
       assert(C>=J&&C-J<L&&lo-b<=3*(C-J),"low tail barrier and clock");
       maxTail=Math.max(maxTail,C-J);
       if(anc){
         const prior=roughTargets.get(anc.key);
         assert(!prior||(prior.C===C&&prior.v===t),"unique deterministic rough target");
         roughTargets.set(anc.key,{C,v:t,r:q0});
         if(oracle<128){
           let z=anc.J,h=anc.t,p2=0;
           while(r(z)&&r(z)<=y){do{h++;let k=h%2;let d=gcd(h-2*k,z+2*k-1);p2=spf[d]||0;if(p2>B)p2=0}while(!p2);if(p2>y)break;z+=p2-1;}
           assert(z===C&&h===lo,"independent deterministic low suffix");oracle++;
         }
       }else rootOnlyVisits++;
       for(let mode=0;mode<2;mode++){
         if(mode===0&&p<=Math.ceil(B**.25))continue;
         if(mode===1&&2*(t-lo)<=p-1)continue;
         const len=mode===0?Math.max(0,Math.min(t,s+H)-Math.max(lo,s+a)):t-lo;
         if(!len)continue;
         let group=g[mode].get(C);if(!group){group={r:q0,entries:new Map(),root:0};g[mode].set(C,group)}
         let key=anc?anc.key:"root";
         group.entries.set(key,(group.entries.get(key)||0)+len/(2*q0));
         if(!anc)group.root++;
       }
     }
     C+=p-1;assert(C<=2*t,"deficit");
     if(p>y&&t<s+H){
       const side=t%2,d=2*t-C,k=(d-6*side)/(2*p);
       assert(Number.isInteger(k)&&k>=Math.ceil(-6*side/(2*p))&&((C+2*side)%p===0),"anchor phase");
       const key=`${C},${t},${p}`;
       let v=anchors.get(key);
       if(!v){v={J:C,t,q:p,n:0,key};anchors.set(key,v)}
       v.n++;anchorVisits++;anc=v;
     }
   }
 }
 let supportWeight=0,actualComparableWeight=0,allGain=0,comparableGain=0,actualComparable=0,supportKeys=0,actualKeys=0,roughCount=0,supportByQ=new Map();
 for(let C=2*X-2;C<=4*X+2*H+6;C+=2){
   const rr=r(C);if(rr<rough||rr<=y)continue;
   roughCount++;
   for(let e=0;e<L;e+=2){
     const J=C-e;if(J<2*X-2)continue;
     for(let side=0;side<2;side++)for(const p of factors(J+2*side)){
       if(p<=y||p>B||p*ratio<rr)continue;
       const k=Math.max(0,Math.floor((2*H+6-6*side)/(2*p))-Math.ceil(-6*side/(2*p))+1);
       supportKeys+=k;supportWeight+=rr*k;
       supportByQ.set(p,(supportByQ.get(p)||0)+rr*k);
     }
   }
 }
 for(const [key,v] of roughTargets){
   const b=anchors.get(key);assert(b&&b.n>=1,"actual anchor counts");allGain+=b.q*b.n;actualKeys++;
   if(b.q*ratio>=v.r){
     actualComparable++;actualComparableWeight+=v.r;comparableGain+=b.q*b.n*b.n;
     assert((supportByQ.get(b.q)||0)>0,"comparable supported label");
   }
 }
 assert(actualComparable<=supportKeys&&actualComparableWeight<=supportWeight,"weighted arithmetic support");
 const results=[];
 for(let mode=0;mode<2;mode++){
   let R=0,E=0,Rroot=0,Rthin=0,keepR=0,keepE=0,sameComparable=0,sameSmall=0,cross=0,sameGain=0,removedKeys=0,heavyKeys=0,smallKeys=0,maxMass=0,rootEnergy=0,thinEnergy=0,maxGroups=0;
   for(const [C,h] of g[mode]){
     const rr=h.r;let U=0,ret=0,sc=0,ss=0,rootW=h.entries.get("root")||0,thinW=0;
     assert(h.root<=Math.ceil(L/2),"root-only source distance count");maxLowRootCount=Math.max(maxLowRootCount,h.root);
     maxGroups=Math.max(maxGroups,h.entries.size);
     for(const [key,w] of h.entries){
       U+=w;
       if(key==="root")continue;
       const b=anchors.get(key),target=roughTargets.get(key);
       assert(target.C===C&&w<=b.n+1e-7,"actual anchor group occupation");
       maxMass=Math.max(maxMass,b.n);
       if(b.q*ratio>=rr&&b.n<=cap){thinW+=w;removedKeys++;continue}
       ret+=w;
       if(b.q*ratio>=rr){sc+=rr*w*w;sameGain+=b.q*b.n*b.n;heavyKeys++}
       else{ss+=rr*w*w;smallKeys++}
     }
     R+=rr*U;E+=rr*U*U;Rroot+=rr*rootW;Rthin+=rr*thinW;keepR+=rr*ret;keepE+=rr*ret*ret;
     rootEnergy+=rr*(U*U-(U-rootW)**2);thinEnergy+=rr*((U-rootW)**2-ret**2);
     sameComparable+=sc;sameSmall+=ss;cross+=rr*ret*ret-sc-ss;
   }
   assert(close(R,Rroot+Rthin+keepR)&&close(E,rootEnergy+thinEnergy+keepE),"linear and quadratic ledgers");
   assert(Rroot<=B*Math.ceil(L/2)*roughCount+1e-6,"root-only bound");
   assert(Rthin<=cap*actualComparableWeight+1e-6&&Rthin<=cap*supportWeight+1e-6,"thin comparable bound");
   assert(sameComparable<=ratio*sameGain+1e-6,"gain transport");
   assert(close(keepE,sameComparable+sameSmall+cross),"remaining partition");
   results.push({mode:mode?"full-positive":"late-high",R,E,Rroot,Rthin,keepR,keepE,rootEnergy,thinEnergy,sameComparable,sameSmall,cross,sameGain,removedKeys,heavyKeys,smallKeys,maxMass,maxGroups});
 }
 return {X,B,D,rough,ratio,cap,L,y,stress,roots,anchors:anchors.size,anchorVisits,roughVisits,rootOnlyVisits,maxTail,maxLowRootCount,oracle,roughCount,actualKeys,actualComparable,actualComparableWeight,supportKeys,supportWeight,allGain,comparableGain,results};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))for(const stress of [false,true])console.log(JSON.stringify(audit(X,stress)));
