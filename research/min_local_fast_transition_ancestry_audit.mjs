// Odd-shift fast high-transition supply, with unrestricted bounded-gain relays.
function audit(){
 const lim=4000400,spf=new Uint32Array(lim+1);
 for(let p=2;p*p<=lim;p++)if(!spf[p])for(let n=p*p;n<=lim;n+=p)if(!spf[n])spf[n]=p;
 const ck=(a,m)=>{if(!a)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function fs(n){ck(n>0&&n<=lim,"factor domain");let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function gcd(a,b){while(b){let z=a%b;a=b;b=z}return a}
 function ev(x,v){let f=fs(x-1),g=fs(x+1),p=Infinity,w=Infinity,e=0;for(let [A,s] of [[f,1],[g,-1]])for(let r of A){let z=mod((s===1?0:r+2)-v,2*r)||2*r;if(z<w||z===w&&r<p){p=r;w=z;e=s}}return {p,w,e,q:Math.min(f[0],g[0]),twin:f[0]===x-1&&g[0]===x+1}}
 const side=e=>e===1?0:6;
 let out=[];
 for(let [R,T,D,B,S,K] of [[10000,53,106,4,5,8],[100000,157,314,12,12,8],[1000000,503,1006,20,24,8],[1000000,997,1994,32,40,8]]){
  let Q=5*B+2*S+7;ck(Q<T&&B<T-1,"cutoffs");
  const st={R,T,D,B,S,K,Q,roots:0,events:0,highEvents:0,highPairs:0,shortPairs:0,shortFastPairs:0,cappedFastPairs:0,allFastEvents:0,firstFastEvents:0,budgetFastEvents:0,budgetHighEvents:0,budgetRoots:0,firstFastMinLowGain:null,actualOffsets:0,actualCappedOffsets:0,ambientCandidateOffsets:0,ambientCandidateTuples:0,relaxedArrivals:0,relaxedRelayEvents:0,relaxedFastPairs:0,relaxedFastOffsets:0,relaxedSameLabel:0,oddChecks:0,literalTicks:0,ancestorChecks:0,maxFastMass:0,maxBudgetMass:0,example:null,relaxedExample:null,largeBudgetWitness:null,relaxedFirstFastCheck:0};
  const primes=[];for(let r=T;r<=K*T;r++)if(r>=3&&!spf[r])primes.push(r);
  // Exact upper graph: enumerate the necessary odd linear equation and CRT.
  // For each r,a,c, factor 2ar+c instead of iterating b. The chosen sign
  // convention below is (2b+1)p-2ar=c.
  const offsets=new Set();
  for(let r of primes)for(let a=1;a<=K;a++){
   if(2*a*r>2*K*T)break;
   for(let c=-Q;c<=Q;c++)if(c%2!==0){
    const N=2*a*r+c;
    for(let p of fs(N)){
     if(p<T||p===r)continue;
     const z=N/p;if(z%2!==1)continue;const b=(z-1)/2;if(b<0||b>K||2*b*p>2*K*T)continue;
     // At current source x: x=e mod p, x=E+arrivalSide mod r.
     for(let E=0;E<=B;E+=2)for(let e of [1,-1])for(let f of [0,-2]){
      let start=Math.ceil((R-e)/p)*p+e;
      let inv=0; // modular inverse of p mod r via Euclid
      let v=p%r,w=r,u=1,t=0;while(w){let k=Math.floor(v/w);[v,w]=[w,v-k*w];[u,t]=[t,u-k*t]}ck(v===1,"coprime");inv=mod(u,r);
      let x=start+p*mod((E+f-start)*inv,r),step=p*r;
      if(x%2){x+=step;step*=2}else step*=2;
      for(;x<3*R;x+=step){ck(mod(x-e,p)===0&&mod(x-E-f,r)===0,"CRT");offsets.add(x);st.ambientCandidateTuples++}
     }
    }
   }
  }
  st.ambientCandidateOffsets=offsets.size;
  const actual=new Set(),capped=new Set(),fastMass=new Map(),budgetMass=new Map(),relaxed=new Set();
  function checkPair(last,x,v,z){
   let E=x-last.u,V=v-last.v,d0=2*last.v-last.u,d1=2*(v+z.w)-(x+z.p-1);
   let a=(d0-side(last.e))/(2*last.p),b=(d1-side(z.e))/(2*z.p);
   ck(Number.isInteger(a)&&Number.isInteger(b)&&a>=0&&b>=0,"multipliers");
   ck(E>=0&&V>=0&&V<=3*E,"relay");
   let c=(2*b+1)*z.p-2*a*last.p;
   ck(c===side(last.e)-side(z.e)+2*(V+z.w)-E+1&&c%2!==0,"odd shift");st.oddChecks++;
   if(E<=B&&z.w<=S){ck(Math.abs(c)<=Q&&a>=1&&z.p!==last.p,"short fast");if(d0<=2*K*T&&d1<=2*K*T){ck(offsets.has(x),"ambient covers "+JSON.stringify({last,x,v,z,a,b,c}));st.ancestorChecks++;return true}}
   return false;
  }
  for(let X=Math.ceil(R/6)*6;X<2*R;X+=6){
   st.roots++;let x=X,v=X/2+3,last=null,low=0,fast=false;
   while(x<X+D){
    let z=ev(x,v);if(z.twin)break;
    const U=x+z.p-1,V=v+z.w,d=2*v-x,dd=2*V-U;
    ck(d>=0&&dd>=0&&V<=U+1,"envelope");
    if(X<R+36&&z.w<1000)for(let i=1;i<=z.w;i++){let n=v+i,g=gcd(n%2?n-2:n,n%2?x+1:x-1);ck(i===z.w?(spf[g]||g)===z.p:g===1,"literal");st.literalTicks++}
    if(z.p>=T){
     st.highEvents++;if(low<=B)st.budgetHighEvents++;
     if(z.w<=S){st.allFastEvents++;actual.add(x);fastMass.set(x,(fastMass.get(x)||0)+1);
      if(!last){st.firstFastEvents++;ck(5*low+6>=z.p-1-2*z.w,"first fast fuel");st.firstFastMinLowGain=st.firstFastMinLowGain===null?low:Math.min(st.firstFastMinLowGain,low);}
      if(low<=B){st.budgetFastEvents++;fast=true;budgetMass.set(x,(budgetMass.get(x)||0)+1);ck(last!==null,"first fast below budget");}
     }
     if(last){st.highPairs++;let E=x-last.u;if(E<=B)st.shortPairs++;if(E<=B&&z.w<=S)st.shortFastPairs++;if(checkPair(last,x,v,z)){st.cappedFastPairs++;capped.add(x);if(!st.example)st.example={X,last,x,v,z,low};}
      if(low<=B&&z.w<=S)ck(2*last.v-last.u<=2*K*T&&dd<=2*K*T&&offsets.has(x),"budget fast cover");
     }
     last={u:U,v:V,p:z.p,e:z.e};
    }else low+=z.p-1;
    x=U;v=V;st.events++;
   }
   if(fast)st.budgetRoots++;
  }
  // Follow a deterministic sample of relaxed high arrival states, with
  // arbitrary intervening labels, including phases inaccessible to resets.
  for(let u=R;u<Math.min(2*R,R+20000);u+=2)for(let e of [1,-1]){
   for(let r of fs(u+(e===1?0:2)))if(r>=T&&r<=K*T){
    for(let a=0;a<=K;a++){
     let d=2*a*r+side(e),v=(u+d)/2;if(d>2*K*T||v>u+1||mod(v,2*r)!==(e===1?0:r+2))continue;
     st.relaxedArrivals++;let x=u,t=v,last={u,v,p:r,e};
     while(x-u<=B){
      let z=ev(x,t),U=x+z.p-1,V=t+z.w,dd=2*V-U;
      if(z.p>=T){if(z.w<=S&&dd<=2*K*T){ck(checkPair(last,x,t,z),"relaxed fast coverage");st.relaxedFastPairs++;relaxed.add(x);if(!st.relaxedExample)st.relaxedExample={last,x,t,z};}break}
      if(U-u>B)break;x=U;t=V;st.relaxedRelayEvents++;
     }
    }
   }
  }
  st.actualOffsets=actual.size;st.actualCappedOffsets=capped.size;st.relaxedFastOffsets=relaxed.size;
  for(let n of fastMass.values())st.maxFastMass=Math.max(st.maxFastMass,n);
  for(let n of budgetMass.values())st.maxBudgetMass=Math.max(st.maxBudgetMass,n);
  out.push(st);
 }
 return out;
}
console.log(JSON.stringify(audit(),null,2));
