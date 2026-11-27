// Exact net-value optimizer on merging forests; independent of Lean.
// v.reward-v.price*charge is a signed integer net reward per live pre-tick.
// Every node points to at most one strictly later node.
function audit(Rs=[12000,48000]){
 const ck=(h,m)=>{if(!h)throw Error(JSON.stringify(m))};
 let checks=0;
 function solve(nodes,M){
   const dp=[], full=[], out=new Int32Array(nodes.length), k=new Int32Array(nodes.length);
   let objective=0, independent=0, maxDebt=0;
   for(let i=0;i<nodes.length;i++){
     const v=nodes[i], inSlots=[], all=[];
     for(let b=0;b<v.birth;b++){inSlots.push({d:0,p:-1,j:b});all.push(0)}
     for(let p of v.pred){
       ck(p<i&&nodes[p].next===i,"forest order");
       for(let j=0;j<dp[p].slopes.length;j++)inSlots.push({d:Math.max(0,-dp[p].slopes[j]),p,j});
       all.push(...full[p]);
     }
     inSlots.sort((a,b)=>a.d-b.d||a.p-b.p||a.j-b.j);
     all.sort((a,b)=>a-b);
     let slots=inSlots.slice(0,M), slopes=slots.map(x=>v.w-x.d);
     let best=slopes.filter(x=>x>0).length, profit=slopes.slice(0,best).reduce((a,x)=>a+x,0);
     let orig=all.slice(0,M);
     ck(slots.length===orig.length&&slots.every((s,j)=>s.d===orig[j]),["clipped reflected debt",i,v,M]);
     independent+=orig.reduce((a,x)=>a+Math.max(0,v.w-x),0);
     objective+=profit; maxDebt=Math.max(maxDebt,all.at(-1)||0);
     full.push(all.map(d=>Math.max(0,d-v.w)));
     dp.push({slots,slopes,best,profit}); checks++;
   }
   for(let i=nodes.length-1;i>=0;i--){
     let v=nodes[i],r=dp[i];
     if(v.next<0)k[i]=r.best;
     ck(k[i]<=r.slopes.length,"reachable requested count");
     let want=new Map();
     for(let j=0;j<k[i];j++){let p=r.slots[j].p;if(p>=0)want.set(p,(want.get(p)||0)+1)}
     for(let p of v.pred)k[p]=Math.max(dp[p].best,want.get(p)||0);
   }
   let value=0,life=0,cost=0;
   for(let i=0;i<nodes.length;i++){
     let v=nodes[i],avail=v.birth+v.pred.reduce((a,p)=>a+k[p],0);
     ck(k[i]<=M&&k[i]<=avail,"feasible reconstructed flow");
     value+=v.w*k[i];life+=(v.reward||0)*k[i];cost+=(v.charge||0)*k[i];checks++;
   }
   ck(value===objective&&objective===independent,["net objective",value,objective,independent]);
   checks++;
   return {value,life,cost,k,maxDebt};
 }
 function brute(nodes,M){
   let best=-Infinity,ks=new Int32Array(nodes.length);
   function go(i,v){if(i===nodes.length){best=Math.max(best,v);return}let n=nodes[i],cap=Math.min(M,n.birth+n.pred.reduce((s,p)=>s+ks[p],0));for(let k=0;k<=cap;k++){ks[i]=k;go(i+1,v+k*n.w)}}
   go(0,0);return best
 }
 let seed=1729;const rng=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n};
 for(let t=0;t<1200;t++){
   let n=1+rng(9),M=1+rng(3),nodes=Array.from({length:n},(_,i)=>({pred:[],next:-1,birth:rng(3),w:rng(15)-8}));
   for(let i=0;i<n-1;i++)if(rng(4)){let j=i+1+rng(n-i-1);nodes[i].next=j;nodes[j].pred.push(i)}
   ck(solve(nodes,M).value===brute(nodes,M),["brute",t,nodes,M]);checks++;
 }
 const spf=new Int32Array(2*Math.max(...Rs)+10);
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 const lpf=n=>spf[n]||n,q=x=>Math.min(lpf(x-1),lpf(x+1));
 const gcd=(a,b)=>{a=Math.abs(a);while(b){let t=a%b;a=b;b=t}return a};
 const result=[];
 for(let R of Rs){
   let T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
   const controls=[1,4,16,64].flatMap(M=>[0,1,4,16].map(price=>({M,price,value:0,life:0,cost:0,maxDebt:0})));
   let nodeCount=0,rootTicks=0,events=0,windows=0;
   for(let l=lo;l<=hi;l+=W){
     const maxA=Math.min(hi,l+W-6),start=3-maxA/2,n0=3-l/2,end=n0+T,births=new Map();
     for(let A=l;A<=maxA;A+=6)births.set(3-A/2,A);
     let active=new Map(),nodes=[],rootMass=[];
     for(let n=start;n<end;n++){
       if(births.has(n)&&!active.has(births.get(n)))active.set(births.get(n),[]);
       let next=new Map();
       for(let [x,pred] of active){
         let g=(n+1)%2===0?gcd(n+1,x+1):gcd(n-1,x-1),p=g>1?lpf(g):0;
         let y=x-(p?p-1:0),birth=births.get(n)===x?1:0;
         let charge=p>5&&p<47?8:p>=47&&p<T/2&&4*q(x)**2>=p?2*q(x):0;
         let id=nodes.length, reward=n>=n0?1:0;
         let mass=birth+pred.reduce((s,j)=>s+rootMass[j],0);
         nodes.push({pred,next:-1,birth,reward,charge,w:0,x,n});
         rootMass.push(mass);rootTicks+=mass;events+=p?mass:0;
         for(let j of pred){ck(nodes[j].next===-1,"no splits");nodes[j].next=id}
         let incoming=next.get(y)||[];incoming.push(id);next.set(y,incoming);
       }
       active=next;
     }
     nodeCount+=nodes.length;windows++;
     for(let c of controls){
       for(let v of nodes)v.w=v.reward-c.price*v.charge;
       let s=solve(nodes,c.M);
       ck(s.value===s.life-c.price*s.cost,"actual net identity");
       c.value+=s.value;c.life+=s.life;c.cost+=s.cost;c.maxDebt=Math.max(c.maxDebt,s.maxDebt);
       // Reconstruct actual token identities, not merely counts. Every token
       // appears only at birth and then through one predecessor until discarded.
       let carried=[],born=new Set(),dead=new Set(),life=0,cost=0;
       for(let i=0;i<nodes.length;i++){
         let v=nodes[i],a=[];
         for(let p of v.pred)a.push(...carried[p]);
         if(v.birth){ck(!born.has(v.x),"unique birth");born.add(v.x);a.push(v.x)}
         ck(new Set(a).size===a.length&&a.every(A=>!dead.has(A)),"identity flow");
         let selected=a.slice(0,s.k[i]);for(let A of a.slice(s.k[i]))dead.add(A);
         carried.push(selected);life+=v.reward*selected.length;cost+=v.charge*selected.length;
       }
       ck(life===s.life&&cost===s.cost,"actual token reconstruction");checks++;
     }
   }
   const den=N*T;
   result.push({R,N,T,windows,nodeCount,rootTicks,events,controls:controls.map(c=>({...c,value:c.value/den,life:c.life/den,cost:c.cost/den}))});
 }
 return {synthetic:1200,checks,slabs:result};
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000]),null,2));
