function audit(maxJ=1000000){
  const abs=x=>x<0n?-x:x;
  const gcd=(a,b)=>{a=abs(a);b=abs(b);while(b){[a,b]=[b,a%b]}return a};
  function factors(a){a=abs(a);let out=[];for(let p=3n;p*p<=a;p+=2n){if(a%p===0n){out.push(p);while(a%p===0n)a/=p}}if(a>1n)out.push(a);return out}
  function trace(M,T){if(M%2n!==1n||M<5n)throw Error("odd M>=5");let E=0n,rows=[];for(let j=1n;j<=BigInt(T);j++){let n=M+2n+j,C=2n*M-2n+E;let even=n%2n===0n;let h=2n*j+(even?7n:1n)-E;let g=even?gcd(n,C-1n):gcd(n-2n,C+1n);let p=factors(g)[0]??1n; if(h===0n||h%2n===0n||h%g!==0n||abs(h)>2n*BigInt(T)+7n)throw Error("defect");rows.push({j,E,h,p});E+=p-1n;if(2n*M-2n+E>2n*n)throw Error("envelope")}return {rows,E}}
  const mod=(a,b)=>(a%b+b)%b;
  function inv(a,p){let x=1n;while(mod(a*x,p)!==1n)x++;return x}
  function cylinder(rows){let sets=new Map;for(let {j,h,p} of rows){for(let q of factors(h)){if(p!==1n&&q>p)continue;let r=mod(-j-(j%2n===1n?2n:0n),q);if(!sets.has(q))sets.set(q,new Set(Array.from({length:Number(q)},(_,i)=>BigInt(i))));let a=sets.get(q);if(q===p){for(let u of a)if(u!==r)a.delete(u)}else a.delete(r)}}return sets}
  function same(a,b){return a.E===b.E&&a.rows.every((r,i)=>r.p===b.rows[i].p&&r.E===b.rows[i].E&&r.h===b.rows[i].h)}
  function prime(n){return n>1n&& (n===2n||n%2n!==0n&&factors(n).length===1&&factors(n)[0]===n)}
  let comparisons=0;for(let M=5n;M<200n;M+=2n){let a=trace(M,40),c=cylinder(a.rows);for(let K=5n;K<250n;K+=2n){let allowed=[...c].every(([q,s])=>s.has(K%q));if(allowed!==same(a,trace(K,40)))throw Error("cylinder mismatch");comparisons++}}
  let M=1663n,T=120,a=trace(M,T);let Q=2n;for(let p of new Set(a.rows.flatMap(r=>factors(r.h))))Q*=p;let offsets=[...new Set([...a.rows.map(r=>r.E),a.E])];let Cfinal=2n*M-2n+a.E;let lastHit=a.rows.filter(r=>r.p>1n).at(-1).j;if(!prime(Cfinal-1n)||!prime(Cfinal+1n)||!a.rows.every(r=>r.p===1n||r.p*r.p<=2n*M-1n+r.E)||BigInt(T)-lastHit<2n*BigInt(Math.floor(Math.sqrt(Number(Cfinal+1n)))))throw Error("original adaptive twin certificate");let cert=[],delta=0n,modulus=Q;let q=2n*BigInt(T)+100n;
  for(let E of offsets)for(let s of [-1n,1n]){do{q++}while(!prime(q));let rhs=mod(-(2n*M-2n+E+s)*inv(2n,q),q);let k=mod((rhs-delta)*inv(mod(modulus,q),q),q);delta+=modulus*k;modulus*=q;cert.push({E,s,q})}
  delta+=modulus;let lifted=M+delta;let b=trace(lifted,T);if(!same(a,b)||!b.rows.every(r=>r.p===1n||r.p*r.p<=2n*lifted-1n+r.E))throw Error("lift mismatch");for(let {E,s,q} of cert){let z=2n*lifted-2n+E+s;if(z<=q||z%q!==0n)throw Error("composite certificate")}
  let ps=[];for(let p=3;p*p<=maxJ+1;p+=2)if(prime(BigInt(p)))ps.push(p);
  let barriers=[],adaptiveBarriers=[],noBypass=[],pairTests=0;for(let J=6;J<=maxJ;J+=2){let barrier=true,ad=true,nb=true;for(let p of ps){if(p*p>J+1)break;let r=J%p;let pred=r%2===1?J-r+1:r===p-1?J:-1;let crossing=pred>=0;let adaptive=crossing&&p*p<=pred+1;let bypass=p>=5&&r%2===1;if(J<=1000){let brute=false,ba=false,bb=false;for(let d=0;d<=p-3;d+=2){let C=J-d;if((C-1)%p===0||(C+1)%p===0){brute=true;if(p*p<=C+1)ba=true;if(d>0)bb=true}}if(brute!==crossing||ba!==adaptive||bb!==bypass)throw Error("barrier mismatch");pairTests++}if(crossing)barrier=false;if(adaptive)ad=false;if(bypass)nb=false;if(!barrier&&!ad&&!nb&&J>1000)break}if(barrier)barriers.push(J);if(ad)adaptiveBarriers.push(J);if(nb)noBypass.push(J)}
  return {comparisons,pairTests,translation:{M:String(M),T,Q:String(Q),word:a.rows.filter(r=>r.p>1n).map(r=>[String(r.j),String(r.p)]),Cfinal:String(Cfinal),quiet:String(BigInt(T)-lastHit),offsets:offsets.map(String),lifted:String(lifted),cert:cert.map(c=>[String(c.E),String(c.s),String(c.q)])},maxJ,barriers,adaptiveBarriers,noBypassCount:noBypass.length,noBypassLast:noBypass.slice(-15)};
}

const maxJ = Number(process.argv[2] || 1000000);
console.log(JSON.stringify(audit(maxJ), null, 2));
