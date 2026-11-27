// Independent finite audit of subset-reset trees. Run: node research/lean/negative_min_subset_reset_tree_audit.mjs
// The third case checks CRT residue certificates and first-event calendars; only the first two materialize a center and replay literal ticks.
function audit(){
 const mod=(a,q)=>((a%q)+q)%q;
 const assert=(h,msg)=>{if(!h)throw Error(msg)};
 function primes(n){let a=new Uint8Array(n+1);for(let p=2;p*p<=n;p++)if(!a[p])for(let k=p*p;k<=n;k+=p)a[k]=1;let ps=[];for(let p=2;p<=n;p++)if(!a[p])ps.push(p);return ps}
 function inverse(a,q){let u=1,v=0,b=q;while(b){let t=Math.floor(a/b);[a,b]=[b,a-t*b];[u,v]=[v,u-t*v]}assert(a===1,"inverse");return mod(u,q)}
 let results=[];
 for(const labels of [[13],[13,313],[13,1873,1460941]]){
  let span=labels.reduce((s,p)=>s+p-1,0),Z=4*span+100,T=Math.floor((Z-8)/3);
  const ps=primes(Z),primeSet=new Set(ps),r=labels.length;
  const subs=Array.from({length:2**r},(_,i)=>{let word=labels.filter((_,j)=>i&(1<<j));return {word,shift:word.reduce((s,p)=>s+p-1,0),min:word[0]??Infinity}});
  assert(new Set(subs.map(s=>s.shift)).size===2**r,"distinct subset roots");
  for(let i=0;i<r;i++){let p=labels[i];assert(primeSet.has(p)&&p%12===1,"prime / 12");assert(p-1>labels.slice(0,i).reduce((s,q)=>s+q-1,0),"superincreasing");for(let j=0;j<i;j++)assert(p%labels[j]===1,"nested congruences")}
  let residues=new Map(),checks=0;
  for(const q of ps){if(q===2)continue;let bad=new Set();for(const s of subs)if(q<s.min){bad.add(mod(1-s.shift,q));bad.add(mod(-1-s.shift,q))}
   let a=0;if(q!==3&&!labels.includes(q)){while(bad.has(a)&&a<q)a++}
   assert(a<q&&!bad.has(a),"admissibility "+q);residues.set(q,a);
   for(const s of subs)if(q<s.min){assert(mod(a+s.shift-1,q)!==0&&mod(a+s.shift+1,q)!==0,"rough source/target");checks++}
  }
  let calendar=0;
  for(const s of subs)if(s.word.length){
   let p=s.word[0],dest=s.shift-p+1,w=(p-7)/2;
   assert(dest%4===0&&mod(residues.get(p)+dest,p)===0,"target 4p");
   let minWait=Infinity,winner=0;
   for(const q of ps){if(q===2)continue;if(q>p)break;
    const a=residues.get(q),half=2*mod(a*inverse(4,q),q),n0=3-half-s.shift/2;
    let target=null;if(mod(a+s.shift+1,q)===0)target=0;else if(mod(a+s.shift-1,q)===0)target=q+2;
    if(target!==null){let t=mod(target-n0,2*q)||2*q;if(t<minWait){minWait=t;winner=q}}
    calendar++;
   }
   assert(minWait===w&&winner===p,"actual first calendar event");
   assert(s.shift/2-w===dest/2+3,"reset clock");
  }
  let ticks=0,events=0,digits=null;
  if(r<=2){
   let x=0n,B=12n;
   for(const q of ps){if(q<=3)continue;let qb=BigInt(q),u=mod((residues.get(q)-Number(x%qb))*inverse(Number(B%qb),q),q);x+=B*BigInt(u);B*=qb}
   x+=B;digits=x.toString().length;assert(x%12n===0n,"CRT");
   for(const s of subs){
    let a=x+BigInt(s.shift),n=3n-a/2n,actual=[];
    const end=3n-x/2n+BigInt(T-1);
    while(n<end){n++;let win=0,hh=Number(2n*n+a),bound=Math.max(hh+1,Math.abs(hh-5),3);
     for(const p of ps){if(p===2)continue;if(p>bound)break;let P=BigInt(p),even=n%2n===0n;
      if(even?(a+1n)%P===0n&&n%(2n*P)===0n:(a-1n)%P===0n&&((n%(2n*P)+2n*P)%(2n*P))===P+2n){win=p;break}}
     if(win){a-=BigInt(win-1);actual.push(win);events++}
     if(n>=3n-x/2n)assert(a===x,"actual stationary after final birth");ticks++;
    }
    assert(JSON.stringify(actual)===JSON.stringify(s.word),"actual label word")
   }
  }
  results.push({labels,roots:subs.length,span,Z,T,localChecks:checks,calendarChecks:calendar,literalTicks:ticks,literalEvents:events,centerDigits:digits});
 }
 return results
}
console.log(JSON.stringify(audit(),null,2));
