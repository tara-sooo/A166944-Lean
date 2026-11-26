// Standalone finite audit; Node.js: node research/infinite-orbit/audit.mjs
function audit(){
  function ok(b,m){if(!b)throw Error(m)}
  function prime(n){if(n<2)return false;if(n%2===0)return n===2;for(let d=3;d*d<=n;d+=2)if(n%d===0)return false;return true}
  function factors(n){n=Math.abs(n);let a=[];for(let d=3;d*d<=n;d+=2)if(n%d===0){a.push(d);while(n%d===0)n/=d}if(n>1)a.push(n);return a}
  function mod(a,p){return ((a%p)+p)%p}
  function modB(a,p){return ((a%p)+p)%p}
  function gcd(a,b){while(b){[a,b]=[b,a%b]}return a<0n?-a:a}
  function inv(a,p){let x=0n,y=1n,b=p;while(a){let q=b/a;[b,a]=[a,b-q*a];[x,y]=[y,x-q*y]}ok(b===1n,"invert");return modB(x,p)}
  let qs=new Map(), bs=new Map(), last=2, index=0;
  function extend(){const b=(index%2===0?1:-1)*(2*Math.floor(index/2)+1);let p=Math.max(last+1,b*b+4,5);while(!prime(p))p++;last=p;index++;qs.set(b,p);bs.set(p,b)}
  function qFor(b){ok(b%2!==0,"odd b");while(!qs.has(b))extend();return qs.get(b)}
  function rho(p){if(p===2)return 1;while(last<p)extend();let b=bs.get(p);return b===undefined?1:mod(-b*((p+1)/2),p)}
  function crt(conds){let a=0n,m=1n;for(const [p,r] of [...conds].sort((x,y)=>x[0]-y[0])){let P=BigInt(p);a+=m*modB((BigInt(r)-a)*inv(m%P,P),P);m*=P}return [a,m]}
  const runs=[];
  for(const T of [128,512,2048]){
    const offsets=[0,2,8,30], conds=new Map([[2,1]]);let traces=[],events=0,quiet=0,factorChecks=0,waitChecks=0,maxP=0,visited=new Set(),escape=0;
    for(let p=3;p<=2*T+7;p+=2)if(prime(p))conds.set(p,rho(p));
    for(const k of offsets){
      let E=0,prev=0,trace=[];
      for(let j=1;j<=T;j++){
        let h=(j%2?2*j+7:2*j+1)-E;
        ok(h%2!==0&&h!==0&&Math.abs(h)<=2*T+7,"h bound");
        let p=1;
        for(const f of factors(h)){factorChecks++;if(mod(rho(f)+k+j+(j%2?2:0),f)===0){p=f;break}}
        if(p>1){events++;maxP=Math.max(maxP,p);ok(j-prev<=2*p,"period wait");waitChecks++;prev=j}else quiet++;
        trace.push([j,E,p]);E+=p-1;ok(6+2*j-E>=0,"deficit");
      }
      for(const e of new Set([0,E,...trace.map(z=>z[1])]))for(const s of [-1,1]){
        const b=2*k-2+e+s,q=qFor(b),r=rho(q);ok(q>b*b&&r!==0&&mod(2*r+b,q)===0,"composite residue");conds.set(q,r);visited.add(b);escape=Math.max(escape,(q-b)/2);
      }
      traces.push({k,E,trace});
    }
    let [M,L]=crt(conds);M+=L*(1n+BigInt((2*T+7)**2));
    let checks=0,compChecks=0;
    for(const {k,E:final,trace} of traces){
      let E=0,R=M+BigInt(k);
      for(const [j,e,p] of trace){
        ok(E===e,"gain");
        let n=R+2n+BigInt(j),C=2n*R-2n+BigInt(E);
        let g=j%2?gcd(n,C-1n):gcd(n-2n,C+1n);
        let actual=g===1n?1:factors(Number(g))[0];
        ok(actual===p,"literal gcd mismatch");ok(p===1||BigInt(p)*BigInt(p)<=C+1n,"adaptive eligibility");
        E+=p-1;checks++;
      }
      ok(E===final,"terminal gain");
      for(const e of new Set([0,E,...trace.map(z=>z[1])]))for(const s of [-1,1]){
        const b=2*k-2+e+s,q=BigInt(qFor(b)),v=2n*M+BigInt(b);ok(v%q===0n&&v>q,"proper divisor");compChecks++;
      }
    }
    for(const [p,r] of conds){ok(modB(M,BigInt(p))===BigInt(r),"CRT");ok(r!==0,"unit")}
    runs.push({T,roots:offsets.length,checks,events,quiet,factorChecks,waitChecks,maxP,distinctCompositeOffsets:visited.size,properDivisorChecks:compChecks,moduli:conds.size,liftDigits:String(M).length,finalGains:traces.map(t=>t.E),escapeLowerBound:escape});
  }
  return runs
}
console.log(JSON.stringify(audit(), null, 2));
