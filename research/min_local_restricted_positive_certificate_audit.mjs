// Positive CRT certificates for budget-stopped adaptive discovery paths.
function audit(){
 const ck=(c,m)=>{if(!c)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 const primes=[];for(let p=3;p<=257;p+=2){let yes=true;for(let q=3;q*q<=p;q+=2)if(p%q===0){yes=false;break}if(yes)primes.push(p)}
 const rows=[];
 for(const [A0,H,B,k,D,R,len] of [
 [[3],[5,7],.55,2,20,420,420],
 [[3,5],[7,11,13],.48,2,40,60060,60060],
 [[3,5,7],[11,13,17],.38,3,60,1021020,1021020],
 [[3],primes.filter(p=>p>=31&&p<=62),.13,2,124,10000,10000],
 [[3,5],primes.filter(p=>p>=103&&p<=206),.12,2,412,100000,30000],
 [[3,5,7],primes.filter(p=>p>=127&&p<=254),.15,2,508,100000,30000]
 ]){
  const P=4*A0.reduce((a,b)=>a*b,1),A=A0.concat(H).sort((a,b)=>a-b),z=Math.max(...H);
  let s={A0,H,B,k,D,R,len,P,baseClasses:0,states:0,queries:0,leaves:0,weighted:0,maxClassWeight:0,upperCount:0,exactCount:0,smallModCount:0,smallModWeight:0,smallModHits:0,actualHits:0,roots:0,coverChecks:0,duplicateCovers:0,negativeBranches:0,positiveBranches:0,oracleChecks:0};
  const leaves=new Map();
  function cert(r,known){
   let a=r,m=P,prod=1;for(let [p,c] of known){let t=0;while(mod(a+m*t,p)!==c)t++;a+=m*t;m*=p;prod*=p;ck(Number.isSafeInteger(m),"modulus");}
   let count=Math.max(0,Math.ceil((R+len-a)/m)-Math.ceil((R-a)/m));return {a,m,prod,count};
  }
  const b=B**k/(k===3?6:k===2?2:1);
  function enumerate(r){
   let arr=[],weight=0,stack=[{G:0,W:0,j:1,i:0,neg:new Map(),known:new Map(),cost:0}];
   while(stack.length){
    let {G,W,j,i,neg,known,cost}=stack.pop();s.states++;
    if(known.size===k){let a=cert(r,known);arr.push(a);weight+=1/a.prod;s.leaves++;s.weighted+=1/a.prod;s.exactCount+=a.count;s.upperCount+=len/a.m+1;if(a.m<=len){s.smallModCount+=a.count;s.smallModWeight+=1/a.prod}continue}
    if(G>=D)continue;
    // Advance deterministically until an unknown residue is queried or the path stops.
    while(G<D&&j<=2*z){
     let n=r/2+3+W+j,h=3+W+j-G/2,e=n%2?-1:1,f=2*h+(e===1?1:-5);
     if(i===A.length){j++;i=0;continue}
     let p=A[i];i++;if(f%p!==0)continue;
     let c=mod(e-G,p);
     if(A0.includes(p)||known.has(p)){let yes=A0.includes(p)?mod(r,p)===c:known.get(p)===c;if(yes){G+=p-1;W+=j;j=1;i=0}continue}
     let S=neg.get(p)||new Set();if(S.has(c))continue;
     let C=cost+1/p;if(C>B+1e-12)break;
     s.queries++;let kn=new Map(known);kn.set(p,c);s.positiveBranches++;
     stack.push({G:G+p-1,W:W+j,j:1,i:0,neg,known:kn,cost:C});
     let ng=new Map(neg),T=new Set(S);T.add(c);ng.set(p,T);s.negativeBranches++;
     neg=ng;cost=C;
    }
   }
   ck(weight<=b+1e-10,"certificate weight");
   s.maxClassWeight=Math.max(s.maxClassWeight,weight);leaves.set(r,arr);s.baseClasses++;
  }
  for(let r=0;r<P;r+=6)enumerate(r);
  function actual(X){
   let G=0,W=0,seen=new Map(),known=new Map(),cost=0;
   while(G<D){
    let u=X+G,v=X/2+3+W,pwin=Infinity,w=Infinity;
    for(let p of A){let e=mod(u,p)===1?1:mod(u,p)===p-1?-1:0;if(!e)continue;let t=mod((e===1?0:p+2)-v,2*p)||2*p;if(t<w||t===w&&p<pwin){pwin=p;w=t}}
    for(let j=1;j<=Math.min(w,2*z);j++){let n=v+j,h=3+W+j-G/2,e=n%2?-1:1,f=2*h+(e===1?1:-5);
     for(let p of A){if(f%p!==0)continue;let c=mod(e-G,p),yes=mod(X,p)===c;
      if(H.includes(p)&&!known.has(p)){
       let S=seen.get(p)||new Set();if(!S.has(c)){cost+=1/p;if(cost>B+1e-12)return null;if(yes){known.set(p,c);if(known.size===k)return known}else{S.add(c);seen.set(p,S)}}
      }
      if(yes){ck(j===w&&p===pwin,"oracle");s.oracleChecks++;break}
     }
    }
    if(!isFinite(pwin))return null;G+=pwin-1;W+=w;
   }
   return null;
  }
  for(let X=Math.ceil(R/6)*6;X<R+len;X+=6){
   s.roots++;let kn=actual(X);if(!kn)continue;s.actualHits++;let cs=leaves.get(mod(X,P)),n=0,small=false,exact=false,prod=1;
   for(let p of kn.keys())prod*=p;
   for(let a of cs)if(mod(X-a.a,a.m)===0){n++;if(a.m<=len)small=true;if(a.prod===prod)exact=true}
   ck(n>=1&&exact,"coverage");s.coverChecks++;s.duplicateCovers+=n-1;if(P*prod<=len){ck(small,"small-mod coverage");s.smallModHits++}
  }
  ck(s.actualHits<=s.exactCount&&s.smallModHits<=s.smallModCount,"local count");
  ck(s.exactCount<=(len+P*z**k)*b/6+1e-7,"local bound");ck(s.smallModCount<=2*len*b/6+1e-7,"small modulus bound");
  s.bound=b;rows.push(s)
 }
 return rows
}
console.log(JSON.stringify(audit(),null,2));
