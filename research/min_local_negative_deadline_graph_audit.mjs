// Compressed inverse jump graph, forced clock deadlines, and canonical-line tests.
function audit(){
 const ck=(c,m)=>{if(!c)throw Error(m)},mod=(x,p)=>(x%p+p)%p,N=300000,Kmax=8192,limit=1000000,spf=new Uint32Array(limit+1);
 for(let p=2;p*p<=limit;p++)if(!spf[p])for(let k=p*p;k<=limit;k+=p)if(!spf[k])spf[k]=p;
 function factors(n){ck(n>=1,"factor domain");let a=[];if(n>limit){for(let p=2;p*p<=n;p++)if(n%p===0){if(p>2)a.push(p);while(n%p===0)n/=p;}if(n>2)a.push(n);return a}while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
 let C=Array.from({length:Kmax+1},(_,k)=>k?factors(k%2?k+2:k):[]);
 function step(b,k){let e=k%2?1:-1,p=C[k].find(p=>mod(b-e,p)===0);return p===undefined?b:b-p+1}
 function first(j,r,p){return j+mod(r-j,2*p)}
 function deadline(b,j){let d=Infinity,q=Infinity;for(let p of factors(b+1)){q=Math.min(q,p);d=Math.min(d,first(j,0,p))}for(let p of factors(b-1)){q=Math.min(q,p);d=Math.min(d,first(j,p-2,p))}ck(d>=j&&d<j+2*q,"deadline");return {d,q}}
 const s={targets:0,extinct:0,maxDeath:0,tickSteps:0,tickEdges:0,jumpNodes:0,duplicateNodes:0,jumpCandidates:0,jumpEdges:0,deadlineChecks:0,branchBoundChecks:0,depthMatches:0,finalFiberMatches:0,canonicalOrigins:0,canonicalTargets:0,canonicalMatches:0,canonicalNonzero:0,canonicalForwardEvents:0,canonicalPruned:0,canonicalJumpNodes:0,weightedTimeChecks:0,maxChildren:0,maxCandidateRatio:0,examples:[]};
 function literal(b,K,prune=false){
  let S=new Set([b]),orig=new Set(),death=0;
  for(let k=1;k<=K;k++){
   if(prune){for(let a of S){if(a===2*k+6&&a%6===0)orig.add(a);if(a<2*k)S.delete(a)}}
   let V=new Set();for(let a of S){if(step(a,k)===a&&(!prune||a>=2*(k+1)))V.add(a);for(let p of C[k]){let x=a+p-1;if(step(x,k)===a&&(!prune||x>=2*(k+1)))V.add(x)}}
   s.tickSteps++;s.tickEdges+=V.size;S=V;if(!S.size){death=k;break}
  }
  if(prune)for(let a of S)if(a===2*(K+1)+6&&a%6===0)orig.add(a);
  return {S,death,orig}
 }
 function compressed(b,K,prune=false){
  let stack=[[b,1,0,0]],seen=new Set(),max=0,ends=new Set(),orig=new Set(),nodes=0;
  let q0=deadline(b,1).q;
  while(stack.length){
   let [a,j,G,Q]=stack.pop();
   // G is reverse gain and Q=sum of q at successive jumped-to states
   // It is enough to keep one witness per identical state, since future is identical.
   let key=a+":"+j;if(seen.has(key)){s.duplicateNodes++;continue}seen.add(key);nodes++;s.jumpNodes++;
   if(prune&&a<2*j){s.canonicalPruned++;continue}
   let {d,q}=deadline(a,j);s.deadlineChecks++;
   ck(j-1<=2*q0+2*Q-1,"weighted time at node");s.weightedTimeChecks++;
   let upper=Math.min(d,K+1,prune?a/2:Infinity),jb=a/2-3;
   if(prune&&jb>=j&&jb<=upper&&a%6===0)orig.add(a);
   let last=upper-1;max=Math.max(max,last);
   ck(last<=2*q0+2*Q-1,"weighted idle bound");s.weightedTimeChecks++;
   if(upper===K+1){ends.add(a);continueIfNoJump();}
   function continueIfNoJump(){} // still enumerate other branches before horizon
   let L=Math.min(d,K,prune?a/2:Infinity),children=0,bound=0;
   if(L<j)continue;
   let options=[];for(let p of factors(a))options.push([p,0]);
   if(a>2){for(let p of factors(a-2))options.push([p,p-2]);}
   else{for(let k=j;k<=L;k++)if(k%2)for(let p of C[k])options.push([p,p-2]);options=[...new Map(options.map(x=>[x.join(":"),x])).values()]}
   for(let [p,r] of options){bound+=Math.ceil(q/p);for(let k=first(j,r,p);k<=L;k+=2*p){s.jumpCandidates++;let x=a+p-1;if(step(x,k)!==a)continue;
     children++;s.jumpEdges++;let q1=deadline(x,k+1).q;ck(q1<=p&&x-b===G+p-1,"jump witness");stack.push([x,k+1,G+p-1,Q+q1]);
   }}
   ck(children<=bound,"branch cap");s.branchBoundChecks++;s.maxChildren=Math.max(s.maxChildren,children);if(bound)s.maxCandidateRatio=Math.max(s.maxCandidateRatio,children/bound);
  }
  return {S:ends,death:ends.size?0:max+1,orig,nodes}
 }
 // At a node j=K+1, the stationary endpoint must be registered even if
 // no further tick is allowed; upper is K+1 and all loop intervals empty.
 for(let p=1009;p<=N;p+=2)if(!spf[p]&&spf[p-2]){
  let b=p-1,K=Math.min(Kmax,b/2-4),x=literal(b,K),y=compressed(b,K);
  ck(x.death===y.death&&x.S.size===y.S.size&&[...x.S].every(a=>y.S.has(a)),"exact compressed comparison "+p);
  s.targets++;s.depthMatches++;s.finalFiberMatches++;if(y.death){s.extinct++;s.maxDeath=Math.max(s.maxDeath,y.death)}
 }
 // Exact canonical-line test: all A=12..600 by 6 (A=6 starts at time 0).
 const cap=600/2-4,expected=new Map();
 for(let A=12;A<=600;A+=6){let a=A,v=-A/2+3,last=0;while(a){let p=Infinity,w=Infinity;for(let r of factors(a+1)){let t=mod(-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}}for(let r of factors(a-1)){let t=mod(r+2-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}}ck(isFinite(p),"forward");a-=p-1;v+=w;last=p;s.canonicalForwardEvents++}if(v===0){if(!expected.has(last-1))expected.set(last-1,new Set());expected.get(last-1).add(A);s.canonicalOrigins++}else s.canonicalNonzero++;}
 for(let b=2;b<=600;b+=2)if(!spf[b+1]){
  let x=literal(b,cap,true),y=compressed(b,cap,true),ref=expected.get(b)||new Set();
  ck(x.orig.size===y.orig.size&&[...x.orig].every(a=>y.orig.has(a)),"pruned comparison "+b);
  ck(ref.size===y.orig.size&&[...ref].every(a=>y.orig.has(a)),"canonical origins "+b);
  s.canonicalTargets++;s.canonicalMatches+=ref.size;s.canonicalJumpNodes+=y.nodes;
 }
 return s;
}
console.log(JSON.stringify(audit(),null,2));
