// Exact reverse-tick reachability and generalized modular barrier diagnostics.
function audit(N=100000,steps=180){
 const cap=4*N+20000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b;
 function gcd(a,b){a=Math.abs(a);while(b)[a,b]=[b,a%b];return a}
 function fac(z){let a=[];while(z>1){let p=spf[z];if(!p)throw Error("range");a.push(p);while(z%p===0)z/=p}return a}
 function tick(n,H){let e=n%2?-1:1,g=gcd(n%2?n-2:n,H-e);if(g===1)return 0;let p=spf[g];return p*p<=H+1?p:0}
 function next(t,H){let best=null;for(let e of [1,-1])for(let p of fac(H-e)){if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}return best}
 const s={N,steps,reverseTargets:0,reverseStates:0,reverseCandidateChecks:0,forwardRootChecks:0,reverseMemberships:0,localTargets:0,localRoots:0,localReverseChecks:0,events:0,paths:0,barrierIntervals:0,lowBarrierChecks:0,farGainChecks:0,barrierCounts:[],localExample:null,largestFarExample:null};
 // Full inverse tick recursion vs direct forward event trajectories.
 for(let Z=8;Z<=600;Z+=2){
  let layer=new Set(),roots=new Set(),actual=new Set();
  for(let n=3*Z+3;n>=7;n--){
   if(Z<=2*n)layer.add(Z);
   let prev=new Set();
   for(let h of layer){s.reverseStates++;
    if(h%4===0&&n===h/2+3)roots.add(h/2+1);
    if(h<=2*(n-1)&&tick(n,h)===0)prev.add(h);
    let e=n%2?-1:1;
    for(let p of fac(gcd(n%2?n-2:n,h+1-e))){
     if(p===2)continue;
     let H=h-p+1;if(H<8||H>2*(n-1)||p*p>H+1)continue;
     s.reverseCandidateChecks++;
     if(tick(n,H)===p)prev.add(H);
    }
   }
   layer=prev;
  }
  for(let H=8;H<=Z;H+=4){let M=H/2+1,t=M+2,h=H;
   while(h<Z){let a=next(t,h);if(!a)break;h+=a.p-1;t+=a.w}
   if(h===Z)actual.add(M);
   s.forwardRootChecks++;
  }
  if(roots.size!==actual.size||[...roots].some(v=>!actual.has(v)))throw Error("reverse exact "+Z);
  s.reverseMemberships+=roots.size;s.reverseTargets++;
 }
 const ps=R=>{let a=[];for(let p=3;p<=R;p+=2)if(spf[p]===p)a.push(p);return a};
 // Twin-admissible locally isolated targets, actual reachability, not assuming terminality.
 for(let R of [7,11,13,17,19,23])for(let Z=48;Z<=Math.min(cap-100,200000);Z+=2){
  if(Z%3||Z%5!==3||ps(R).some(p=>p>=7&&[0,-2,2,4,1,-1].some(d=>mod(Z-d,p)===0)))continue;
  s.localTargets++;
  for(let d of [0,2,4])for(let p of ps(R)){
   if((Z-d)%p===0||(Z-d+2)%p===0){if(![0,2,4].includes(d+p-1))throw Error("local closure");}
   s.localReverseChecks++;
  }
  let hits=[];
  for(let H=Math.max(8,Z-R+1);H<=Z;H++){if(H%4)continue;let t=H/2+3,h=H;while(h<Z){let a=next(t,h);if(!a)break;h+=a.p-1;t+=a.w}if(h===Z)hits.push(H)}
  let target=Z%4===0?[Z-4,Z]:[Z-2];
  if(hits.join()!==target.join())throw Error("local actual "+JSON.stringify({R,Z,hits,target}));
  s.localRoots+=hits.length;
  if(!s.localExample&&R>=13)s.localExample={R,Z,hits,terminal:!next(Z/2+3,Z)};
 }
 // Exact modular barrier counts. Prefix index counts even horizons 2j.
 let tables=[];
 for(let R of [3,5,7,11,13,17]){
  let P=ps(R).reduce((a,p)=>a*p,1),pref=new Uint32Array(P+1);
  for(let j=0;j<P;j++)pref[j+1]=pref[j]+(ps(R).every(p=>mod(2*j,p)%2===0&&mod(2*j,p)<=p-3)?1:0);
  let A=ps(R).reduce((a,p)=>a*(p-1)/2,1);if(pref[P]!==A)throw Error("barrier density");
  function C(j){return Math.floor(j/P)*A+pref[j%P]}
  tables.push({R,P,A,count:(h,z)=>C(z/2)-C(h/2)});
  s.barrierCounts.push({R,P,A,density:A/P});
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,start=H,ev=[];
  for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+20>=cap)throw Error("cap");let a=next(t,H);if(!a)break;let q=(H-a.e)/a.p,x=(a.p+q)/2,k=(q-a.p)/2;let near=x>=64&&2*k*k<=x;
   ev.push({H,p:a.p,near});H+=a.p-1;t+=a.w;s.events++}
  if(!ev.length)continue;s.paths++;
  for(let {R,P,A,count} of tables){let total=count(start,H),nearCount=0,nearGain=0,nearN=0,F=0,farCount=0;
   for(let v of ev){let b=count(v.H,v.H+v.p-1);
    if(v.p<=R){if(b)throw Error("low crossed");s.lowBarrierChecks++;}
    else if(v.near){nearCount+=b;nearGain+=v.p-1;nearN++}
    else {F+=v.p-1;farCount+=b;}
   }
   if(total!==nearCount+farCount||2*P*nearCount>A*nearGain+2*P*A*nearN||F<2*farCount||P*F<2*P*total-A*nearGain-2*P*A*nearN)throw Error("far bound");
   s.barrierIntervals++;s.farGainChecks++;
   if(!s.largestFarExample||farCount>s.largestFarExample.farCount)s.largestFarExample={M,R,start,H,total,nearCount,farCount,F};
  }
 }
 return s;
}
console.log(JSON.stringify(audit(Number(process.argv[2]||100000),Number(process.argv[3]||180)),null,2));
