// General fresh-plateau clock score and exact finite residue law.
function audit(){
 const prime=n=>{if(n<2)return false;for(let d=2;d*d<=n;d++)if(n%d===0)return false;return true};
 const primes=n=>Array.from({length:n-2},(_,i)=>i+3).filter(prime);
 const mod=(a,b)=>(a%b+b)%b;
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function crt(x,m,p,r){while(x%p!==r)x+=m;return x}
 const s={configs:0,phaseAssignments:0,scoreCandidateChecks:0,finiteCountChecks:0,actualTickChecks:0,actualPaths:0,resetChecks:0,nonresetChecks:0,quietChecks:0,examples:[],rows:[]};
 for(let [L,U] of [[7,19],[11,23],[13,29],[17,31],[19,37]]){
  const small=primes(L),fresh=primes(U).filter(p=>p>L),P=fresh.reduce((a,p)=>a*p,1);
  // Total product for literal integer witnesses can be too large: use BigInt.
  let Q=small.concat(fresh).reduce((a,p)=>a*BigInt(p),4n);
  for(let h4 of [0,2]){
   for(let d=0;d<=L-3;d+=2){
    const tpar=mod((h4+d)/2,2),c=mod(1-h4,4);
    const tests=fresh.flatMap(p=>{let k=p%4===c?1:3;return [{p,k,e:1,S:k*p,w:(k*p-d-1)/2},{p,k,e:-1,S:k*p+6,w:(k*p-d+5)/2}]}).sort((a,b)=>a.S-b.S);
    for(let x of tests){if(x.w<=0||mod(tpar+x.w,2)!==(x.e===1?0:1)||!Number.isInteger(x.w))throw Error("clock candidate");s.scoreCandidateChecks++}
    const key=x=>x?`${x.p},${x.e},${x.w}`:"none";
    let remain=new Map(fresh.map(p=>[p,p])),expected=new Map(),tot=0;
    for(let a of tests){let n=1;for(let p of fresh)if(p!==a.p)n*=remain.get(p);expected.set(key(a),n);tot+=n;remain.set(a.p,remain.get(a.p)-1)}
    let none=[...remain.values()].reduce((a,b)=>a*b,1);expected.set("none",none);if(tot+none!==P)throw Error("product");
    const obs=new Map(),sample=new Set();
    for(let z=0;z<P;z++){
     let H=crt(z,P,4,h4),t=(H+d)/2,win=null;
     for(let p of fresh){
      let e=H%p===1?1:H%p===p-1?-1:0;if(!e)continue;
      let w=mod((e===1?0:p+2)-t,2*p)||2*p;
      if(!win||w<win.w||w===win.w&&p<win.p)win={p,e,w};
     }
     let pred=tests.find(a=>mod(H-a.e,a.p)===0);
     if(key(win)!==key(pred))throw Error("first clock");
     let k=key(win);obs.set(k,(obs.get(k)||0)+1);s.phaseAssignments++;
     // If score <=U, no untested prime can occur by that tick.
     if((pred&&pred.S<=U||!pred)&&!sample.has(k)&&sample.size<8){
      sample.add(k);
      let h=BigInt(h4),m=4n;
      for(let p of small.concat(fresh)){
       let f=BigInt(p),r=BigInt(p<=L?0:H%p);
       while(h%f!==r)h+=m;m*=f;
      }
      if(m!==Q)throw Error("CRT product");
      let target=BigInt(U*U+100);if(h<target)h+=m*((target-h+m-1n)/m);
      let t=(h+BigInt(d))/2n;
      let bound=pred?pred.w:Math.max(0,Math.floor((U-d-1)/2)),hit=null;
      for(let j=1;j<=bound;j++){
       let n=t+BigInt(j),e=n%2n?-1:1,A=e===1?n:n-2n,B=h-BigInt(e);
       while(B)[A,B]=[B,A%B];s.actualTickChecks++;
       if(A!==1n){let p=primes(Number(A)).find(p=>A%BigInt(p)===0n);if(!p||BigInt(p*p)>h+1n)throw Error("literal eligible");hit={p,e,w:j};break}
      }
      if(key(hit)!==key(pred))throw Error("literal first");
      if(pred){let D=2n*(t+BigInt(pred.w))-(h+BigInt(pred.p-1))-BigInt(3*(1-pred.e));if(D!==BigInt((pred.k-1)*pred.p))throw Error("D");if(pred.k===1)s.resetChecks++;else s.nonresetChecks++;if(s.examples.length<8)s.examples.push({L,U,h4,d,p:pred.p,e:pred.e,w:pred.w,D:Number(D)})}
      else s.quietChecks++;
      s.actualPaths++;
     }
    }
    for(let [k,v] of expected){if((obs.get(k)||0)!==v)throw Error("exact counts "+k);s.finiteCountChecks++}
    s.configs++;
    if(d===0){let v={L,U,h4,P,reset:0,nonreset:0,none};for(let a of tests)v[a.k===1?"reset":"nonreset"]+=expected.get(key(a));s.rows.push(v)}
   }
  }
 }
 return s;
}
console.log(JSON.stringify(audit(),null,2));
