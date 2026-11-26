// First support-product crossing certificates, with tilted query costs.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 const primes=[];for(let p=3;p<=127;p+=2){let b=true;for(let q=3;q*q<=p;q+=2)if(p%q===0){b=false;break}if(b)primes.push(p)}
 const controls=[
 {base:[3],z:7,D:18,B:1.1,s:.5,R:420,len:420},
 {base:[3,5],z:13,D:65,B:1.35,s:.5,R:60060,len:60060},
 {base:[3,5,7],z:17,D:300,B:1.2,s:.5,R:1021020,len:1021020},
 {base:[3],z:31,D:45,B:1.0,s:.5,R:10000,len:10000},
 {base:[3,5],z:61,D:120,B:1.0,s:.4,R:100000,len:30000},
 {base:[3,5,7],z:127,D:300,B:1.25,s:.3,R:100000,len:30000},
 {base:[3],z:17,D:300,B:2.0,s:.3,R:1021020,len:1021020},
 {base:[3,5],z:31,D:1000,B:1.8,s:.3,R:100000,len:30000},
 {base:[3],z:127,D:1000,B:1.5,s:.25,R:100000,len:30000}
 ];
 let out=[];
 for(let c of controls){
  let {base,z,D,B,s,R,len}=c,A=primes.filter(p=>p<=z),H=A.filter(p=>!base.includes(p)),P=4*base.reduce((t,p)=>t*p,1),M0=2*D/P;
  ck(M0>1&&H.length>0,"threshold");
  let st={...c,P,M0,roots:0,classes:0,states:0,queries:0,leaves:0,certCount:0,weight:0,tiltedWeight:0,maxClassTilt:0,realHits:0,covered:0,exits:0,exitBudgetHits:0,budgetStops:0,terminalBeforeThreshold:0,wallChecks:0,clockChecks:0,maxMod:0,duplicateCovers:0,multiLeaves:0,multiHits:0};
  let certs=new Map(),a=p=>p**(s-1);
  function certificate(r,K,prod){
   let x=r,m=P;for(let [p,v] of K){let t=0;while(mod(x+m*t,p)!==v)t++;x+=m*t;m*=p}ck(m===P*prod&&m>=2*D&&m<2*D*z+1,"modulus");
   return {x,m,n:Math.max(0,Math.ceil((R+len-x)/m)-Math.ceil((R-x)/m))};
  }
  for(let r=0;r<P;r+=6){
   st.classes++;let leaves=[],weight=0,tilt=0,stack=[{G:0,W:0,j:1,i:0,neg:new Map(),known:new Map(),prod:1,cost:0}];
   while(stack.length){
    let {G,W,j,i,neg,known,prod,cost}=stack.pop();st.states++;
    if(prod>=M0){let l=certificate(r,known,prod);leaves.push(l);st.leaves++;if(known.size>=2)st.multiLeaves++;st.certCount+=l.n;weight+=1/prod;tilt+=prod**(s-1);st.maxMod=Math.max(st.maxMod,l.m);continue}
    ck(G<D,"wall before product threshold");
    while(G<D&&j<=2*z){
     let t=r/2+3+W+j,h=3+W+j-G/2,e=t%2?-1:1,f=2*h+(e===1?1:-5);
     if(i===A.length){i=0;j++;continue}
     let p=A[i++];if(f%p!==0)continue;let b=mod(e-G,p);
     if(base.includes(p)||known.has(p)){let hit=base.includes(p)?mod(r,p)===b:known.get(p)===b;
      if(hit){G+=p-1;W+=j;j=1;i=0;
       // In impossible negative branches, all selected labels still satisfy
       // the positive CRT constraints. The wall applies to any representative.
       ck(G<P*prod/2&&G<D,"wall on relaxed positive branch");st.wallChecks++}
      continue}
     let S=neg.get(p)||new Set();if(S.has(b))continue;
     let C=cost+a(p);if(C>B+1e-12)break;st.queries++;
     let kn=new Map(known);kn.set(p,b);
     stack.push({G:G+p-1,W:W+j,j:1,i:0,neg,known:kn,prod:prod*p,cost:C});
     let ng=new Map(neg),T=new Set(S);T.add(b);ng.set(p,T);neg=ng;cost=C;
    }
   }
   ck(tilt<=Math.expm1(B)+1e-10&&weight<=Math.expm1(B)/M0**s+1e-10,"tilted bound");
   st.weight+=weight;st.tiltedWeight+=tilt;st.maxClassTilt=Math.max(st.maxClassTilt,tilt);certs.set(r,leaves)
  }
  function trueEvent(X,G,W){let u=X+G,v=X/2+3+W,p=Infinity,w=Infinity;for(let q of A){let e=mod(u,q)===1?1:mod(u,q)===q-1?-1:0;if(!e)continue;let j=mod((e===1?0:q+2)-v,2*q)||2*q;if(j<w||j===w&&q<p){p=q;w=j}}return {p,w}}
  for(let X=Math.ceil(R/6)*6;X<R+len;X+=6){
   st.roots++;let G=0,W=0,prod=1,cost=0,hit=false,budgetExceeded=false,known=new Map(),neg=new Map();
   // Simulate ordinary trajectory until physical cutoff, track first support-product crossing.
   while(G<D){
    let {p,w}=trueEvent(X,G,W),v=X/2+3+W;
    if(!hit){
     for(let j=1;j<=Math.min(w,2*z)&&!hit;j++){
      let t=v+j,h=3+W+j-G/2,e=t%2?-1:1,f=2*h+(e===1?1:-5);
      for(let q of A){if(f%q!==0)continue;let b=mod(e-G,q),yes=mod(X,q)===b;
       if(!base.includes(q)&&!known.has(q)){let S=neg.get(q)||new Set();if(!S.has(b)){cost+=a(q);if(cost>B+1e-12)budgetExceeded=true;if(yes){known.set(q,b);prod*=q;if(prod>=M0){hit=true;st.realHits++;if(known.size>=2)st.multiHits++;if(!budgetExceeded){st.covered++;let leaves=certs.get(mod(X,P)),n=leaves.filter(l=>mod(X-l.x,l.m)===0).length;ck(n>0,"coverage");st.duplicateCovers+=n-1}}}else{S.add(b);neg.set(q,S)}}}
       if(yes){ck(p===q&&w===j,"clock");st.clockChecks++;break}
      }
     }
    }
    if(!isFinite(p))break;G+=p-1;W+=w;
    if(!hit){ck(G<P*prod/2&&G<D,"actual wall");st.wallChecks++}
   }
   if(G>=D){st.exits++;ck(hit,"exit must reach support threshold");if(!budgetExceeded)st.exitBudgetHits++}
   if(budgetExceeded)st.budgetStops++;
   if(!hit)st.terminalBeforeThreshold++;
  }
  st.fractionBound=(1+2*D*z/len)*Math.expm1(B)/M0**s;
  ck(st.covered<=st.certCount&&st.certCount<=len/6*st.fractionBound+1e-8,"local tilted bound");ck(st.exitBudgetHits<=st.covered,"exit budget cover");out.push(st)
 }
 return out;
}
console.log(JSON.stringify(audit(),null,2));
