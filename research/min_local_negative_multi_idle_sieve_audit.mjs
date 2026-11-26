// Compressed multi-idle transcript certificate and separated-mark construction.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=2400000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)spf[n]=p;
 function fs(n){n=Math.abs(n);let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function inv(a,p){a=mod(a,p);let t=0,u=1,b=p;while(a){let q=Math.floor(b/a);[b,a]=[a,b-q*a];[t,u]=[u,t-q*u]}ck(b===1,"inverse");return mod(t,p)}
 function c(p,e){return e===-1?0:p+2}
 function delay(t,par,p,e,r){let j=r+p*mod(par-r,2);return mod(c(p,e)-3+3*j-t,2*p)||2*p}
 function exact(j,G,t){let a=6*j-G,v=3-3*j+t,p=Infinity,w=Infinity,e=0;for(let [d,f] of [[a+1,-1],[a-1,1]])for(let q of fs(d)){let d0=mod(c(q,f)-v,2*q)||2*q;if(d0<w||d0===w&&q<p){p=q;w=d0;e=f}}return {p,w,e}}
 let ps=[];for(let p=5;p<=N;p+=2)if(!spf[p])ps.push(p);
 let s={words:0,roots:0,exactChecks:0,positiveConflicts:0,compatibleWords:0,forbiddenChecks:0,remainderChecks:0,constructedWords:0,constructedMarks:0,constructedClockChecks:0,constructedTickChecks:0,constructedCrossChecks:0,constructedFreeChecks:0,rows:[]};
 // Exact compressed certificate for a prescribed signed word and idle tail.
 function cert(word,par,K){
  let pos=new Map(),st=[],G=0,t=0,gate=true;
  for(let [p,e] of word){
   let r=p===3?par:mod((G+e)*inv(6,p),p);
   if(p===3){if(mod(-G-e,3)!==0)gate=false}
   else if(pos.has(p)&&pos.get(p)!==r)gate=false;else pos.set(p,r);
   let w=delay(t,par,p,e,r);
   st.push({G,t,p,e,w});G+=p-1;t+=w;
  }
  st.push({G,t,p:Infinity,e:0,w:K});let z=2*(t+K)+7,B=new Map();
  for(let a of st){
   for(let e of [-1,1])if(mod(-a.G-e,3)===0){
    let w=delay(a.t,par,3,e,par);
    if(w<a.w||w===a.w&&3<a.p)gate=false
   }
   for(let q of ps){if(q>z)break;let r0=inv(6,q);
    for(let e of [-1,1]){
     let r=mod((a.G+e)*r0,q),w=delay(a.t,par,q,e,r);
     if(w<a.w||w===a.w&&q<a.p){let x=B.get(q)||new Set();x.add(r);B.set(q,x)}
    }
   }
  }
  for(let [p,r] of pos)if(B.get(p)?.has(r))gate=false;
  return {pos,st,G,t,z,B,gate}
 }
 // Independent direct event enumeration on genuine roots.
 for(let par of [0,1]){
  let controls=new Map();
  for(let j=1200+par;j<1500;j+=2){let G=0,t=0,word=[];
   for(let i=0;i<3;i++){let x=exact(j,G,t);if(t+x.w>80)break;word.push([x.p,x.e]);G+=x.p-1;t+=x.w;controls.set(JSON.stringify(word),word)}
  }
  for(let word of controls.values())for(let K of [0,7,25]){
   let q=cert(word,par,K);s.words++;if(!q.gate)s.positiveConflicts++;else s.compatibleWords++;
   for(let j=1200+par;j<1600;j+=2){let G=0,t=0,ok=true;
    for(let [p,e] of word){let x=exact(j,G,t);if(x.p!==p||x.e!==e){ok=false;break}G+=p-1;t+=x.w}
    if(ok)ok=exact(j,G,t).w>K;
    let pred=q.gate&&[...q.pos].every(([p,r])=>j%p===r)&&[...q.B].every(([p,B])=>!B.has(j%p));
    ck(pred===ok,{word,K,j,pred,ok});s.roots++;s.exactChecks++;
   }
   for(let B of q.B.values()){ck(B.size<=2*(word.length+1),"dimension");s.forbiddenChecks++}
   if(q.gate){let free=[...q.B].filter(([p])=>!q.pos.has(p)).slice(0,5);
    for(let i=0;i<free.length;i++)for(let j=i+1;j<free.length;j++){let [p,B]=free[i],[r,C]=free[j],d=p*r,nu=B.size*C.size,n=137,count=0;
     for(let a=11;a<11+n;a++)if(B.has(a%p)&&C.has(a%r))count++;
     ck(Math.abs(count-n*nu/d)<=nu+1e-8,"CRT remainder");s.remainderChecks++
    }
   }
  }
 }
 // Construct separated marks after the p=7 prefix. For finite controls
 // use small Y and a ratio >=32; choose primes in fixed AP and test
 // all selected-prime noneligibility conditions across every state.
 for(let m of [1,2])for(let Y of m===1?[450,900,1800]:[2000,3000,5000]){
  let M=m===1?462:2310,small=m===1?[]:[5],picks=[],Gs=[6],t=3,par=1,rows=[];
  for(let i=0;i<m;i++){
   let low=32**i*Y,high=2*low,p=ps.find(q=>q>=low&&q<=high&&q%M===1&&picks.every((r,k)=>![0,r-2].includes(mod(Gs[i]+q-1-Gs[k],r))));
   if(!p)break;
   ck(Gs[i]-Gs[0]+2<p,"separation");
   let r=mod((Gs[i]-1)*inv(6,p),p),w=delay(t,par,p,-1,r);
   ck(w>=p/5&&w<=2*p,"long gap");picks.push(p);rows.push({p,r,w,t,G:Gs[i]});t+=w;Gs.push(Gs[i]+p-1)
  }
  if(picks.length!==m)continue;
  let K=2*t+17,z=2*(t+K)+7;ck(z<N,"factor table size");
  let pinned=new Map([[7,6],[11,0],...small.map(p=>[p,1]),...rows.map(x=>[x.p,x.r])]);
  for(let [q,r] of pinned)for(let i=0;i<Gs.length;i++){
   let a=mod(6*r-Gs[i],q),eligible=a===1||a===q-1;
   ck(eligible===(i<m&&q===picks[i]),{q,r,i,G:Gs[i],a});s.constructedCrossChecks++
  }
  // Complete finite residue environment: each remaining prime avoids all
  // 2(m+1) stationary-state residues. A true integer representative exists
  // by CRT, but we do not materialize its enormous integer value.
  for(let q of ps){if(q>z)break;if(pinned.has(q))continue;
   let r0=inv(6,q),B=new Set(Gs.flatMap(G=>[mod((G-1)*r0,q),mod((G+1)*r0,q)]));
   let r=0;while(B.has(r))r++;ck(r<q,"admissible");pinned.set(q,r);s.constructedFreeChecks++
  }
  let h=3,actual=[],G=0;
  for(let tick=1;tick<=t+K;tick++){
   let b=h+1,e=mod(3-3*par+tick,2)===0?-1:1,p=0;
   for(let q of fs(e===-1?2*b+1:2*b-5)){
    if(q===3?mod(3+tick-c(q,e),3)===0:mod(3+tick-c(q,e)-3*pinned.get(q),q)===0){p=q;break}
   }
   h=b-(p?(p-1)/2:0);if(p){G+=p-1;actual.push([p,e,tick]);}
   ck(h>=0&&h===3+tick-G/2,"height");s.constructedTickChecks++
  }
  let expected=[[7,1,3],...rows.map(x=>[x.p,-1,x.t+x.w])];
  ck(JSON.stringify(actual)===JSON.stringify(expected),{m,Y,actual,expected});s.constructedClockChecks++;s.constructedWords++;s.constructedMarks+=m;s.rows.push({m,Y,picks,t,K,z,G,h})
 }
 return s
}
console.log(JSON.stringify(audit(),null,2));
