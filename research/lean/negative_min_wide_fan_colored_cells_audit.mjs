// Finite audit for wide direct reset fans and two-color compressed ancestry. Run with node.
function audit(){
 const mod=(a,q)=>((a%q)+q)%q;
 const check=(b,msg)=>{if(!b)throw Error(msg)};
 function primeTable(n){let sp=new Int32Array(n+1),ps=[];for(let i=2;i<=n;i++){if(!sp[i]){sp[i]=i;ps.push(i);if(i*i<=n)for(let j=i*i;j<=n;j+=i)if(!sp[j])sp[j]=i}}return {ps,sp}}
 function inv(a,q){let u=1,v=0,b=q;while(b){let k=Math.floor(a/b);[a,b]=[b,a-k*b];[u,v]=[v,u-k*v]}check(a===1,"inverse");return mod(u,q)}
 const fans=[];
 for(const [P,r] of [[100,3],[1000,8],[3000,12],[10000,20]]){
  const {ps}=primeTable(8*P+100);
  const labels=ps.filter(p=>P<=p&&p<2*P&&p%12===1&&ps.filter(q=>q>=5&&q<=2*r+2).every(q=>(p-2)%q!==0)).slice(0,r);
  check(labels.length===r,"enough finite labels");
  const Z=8*P+100,T=Math.floor((Z-8)/3);let local=0,cal=0;
  let residues=new Map();
  for(const q of ps){if(q===2)continue;let bad=new Set([1,q-1]);for(const p of labels)if(q<p){bad.add(mod(-p,q));bad.add(mod(2-p,q))}
   let a=0;if(q>2*r+2&&!labels.includes(q)&&q!==3)while(bad.has(a)&&a<q)a++;
   check(a<q&&!bad.has(a),"compatible direct fan");residues.set(q,a);
   for(const p of labels)if(q<p){check(mod(a+p,q)!==0&&mod(a+p-2,q)!==0,"source roughness");local++}
  }
  for(const p of labels){check(residues.get(p)===0,"p divides target");let best=Infinity,winner=0;
   for(const q of ps){if(q===2)continue;if(q>p)break;let a=residues.get(q),half=2*mod(a*inv(4,q),q),n0=3-half-(p-1)/2;
    let event=mod(a+p,q)===0?0:mod(a+p-2,q)===0?q+2:null;
    if(event!==null){let wait=mod(event-n0,2*q)||2*q;if(wait<best){best=wait;winner=q}}cal++;
   }check(best===(p-7)/2&&winner===p,"first actual event");
  }
  let literal=0;
  if(P===100){let x=0n,B=12n;for(const q of ps)if(q>3){let qb=BigInt(q),u=mod((residues.get(q)-Number(x%qb))*inv(Number(B%qb),q),q);x+=B*BigInt(u);B*=qb}x+=B;
   for(const p0 of [1,...labels]){let a=x+BigInt(p0-1),n=3n-a/2n,events=[];
    while(n<3n-x/2n+BigInt(T-1)){n++;let hh=Number(2n*n+a),bound=Math.max(hh+1,Math.abs(hh-5),3),win=0;
     for(const p of ps){if(p===2)continue;if(p>bound)break;let b=BigInt(p);
      if(n%2n===0n?(a+1n)%b===0n&&n%(2n*b)===0n:(a-1n)%b===0n&&((n%(2n*b)+2n*b)%(2n*b))===b+2n){win=p;break}}
     if(win){a-=BigInt(win-1);events.push(win)}if(n>=3n-x/2n)check(a===x,"full physical stationary");literal++;
    }
    check(JSON.stringify(events)===JSON.stringify(p0===1?[]:[p0]),"literal direct word")
   }
  }
  fans.push({P,r,labels,local,calendar:cal,literal});
 }
 const graphs=[];
 for(const [R,T,Q,Y] of [[12000,96,6,30],[12000,96,30,30],[48000,192,210,60]]){
  const {sp}=primeTable(2*R+1);
  function factors(x){let a=[];while(x>=2){let p=sp[x];a.push(p);while(x%p===0)x/=p}return a}
  const lo=R-3*T-6,hi=2*R,first=Math.floor(lo/Q),last=Math.floor(hi/Q),n=last-first+1;
  let med=Array.from({length:n},()=>new Set()),high=Array.from({length:n},()=>new Set()),mi=new Int32Array(n),hiD=new Int32Array(n);
  const cell=x=>Math.floor(x/Q)-first;
  for(let x=lo+(lo%2);x<=hi;x+=2){
   for(const p of [...new Set([...factors(x-1),...factors(x+1)])])if(p>2){let y=x-p+1;if(y<lo)continue;let a=cell(x),b=cell(y);
    if(Q%p===0)check(a===b,"base wall");if(a===b)continue;let set=p>=Y?high:med,deg=p>=Y?hiD:mi;if(!set[a].has(b)){set[a].add(b);deg[b]++}
   }
  }
  const D=med.map((s,i)=>Math.max(1,s.size,mi[i])),B=Math.max(1,...high.map((s,i)=>Math.max(s.size,hiD[i])));
  let roots=0,ticks=0,crossings=0;
  const H=10,terminal=new Set();
  for(let x=lo+(lo%2);x<=hi;x+=2)if([...factors(x-1),...factors(x+1)].every(p=>p>H))terminal.add(cell(x));
  for(let A=Math.ceil(R/6)*6;A<=hi;A+=6){roots++;let x=A,n0=3-A/2,cs=0,mc=0,hc=0,ph=1;
   for(let a=1;a<=Math.floor(T/2);a++){let t=n0+a,even=mod(t,2)===0,p=0;
    for(const q of factors(even?x+1:x-1))if(q>2&&mod(t,2*q)===(even?0:q+2)){p=q;break}
    if(p){let y=x-p+1,s=cell(x),d=cell(y);ph++;if(s!==d){cs++;crossings++;check((p>=Y?high:med)[s].has(d),"actual colored edge");check(Q%p!==0,"actual nonbase crossing");if(p>=Y)hc++;else mc++}x=y}
    ticks++;
   }
   check(cs===mc+hc&&ph<=(cs+1)*(Q/2+1),"compressed phase count");
  }
  let bounds=0;
  for(let d=0;d<=3;d++)for(let h=0;h<=2;h++){
   const dp=Array.from({length:d+1},()=>Array.from({length:h+1},()=>Array(n).fill(0n)));
   for(let i=0;i<=d;i++)for(let j=0;j<=h;j++)for(let v=0;v<n;v++){
    if(i===0&&j===0)dp[i][j][v]=terminal.has(v)?1n:0n;
    if(i)for(const w of med[v])dp[i][j][v]+=dp[i-1][j][w];
    if(j)for(const w of high[v])dp[i][j][v]+=dp[i][j-1][w];
   }
   let total=0n;for(const row of dp)for(const a of row)for(const x of a)total+=x;
   for(const K of [1,2,4,8]){let tail=D.reduce((a,v)=>a+(v>K?BigInt(v)**BigInt(d):0n),0n);
    let b=(2n**BigInt(d+h+1))*(BigInt(B)**BigInt(h))*(BigInt(terminal.size)*BigInt(K)**BigInt(d)+BigInt(d+h+1)*tail);
    check(total<=b,"colored max-degree path bound");bounds++;
   }
  }
  graphs.push({R,T,Q,Y,roots,ticks,crossings,vertices:n,roughCells:terminal.size,maxHighDegree:B,bounds});
 }
 return {fans,graphs}
}
console.log(JSON.stringify(audit(),null,2));
