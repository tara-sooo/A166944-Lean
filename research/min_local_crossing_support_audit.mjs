// Exact finite audit; no asymptotic or Lean claim.
function audit(limit=1000000) {
  const a=new Uint32Array(2*limit+3);
  for(let p=3;p*p<a.length;p+=2)if(!a[p])for(let n=p*p;n<a.length;n+=2*p)if(!a[n])a[n]=p;
  const factors=n=>{const out=[];while(n>1){let p=a[n]||n;out.push(p);while(n%p===0)n/=p;}return out};
  const mod=(x,m)=>(x%m+m)%m;
  const gcd=(x,y)=>{while(y){let z=x%y;x=y;y=z}return Math.abs(x)};
  const require=(ok,msg)=>{if(!ok)throw Error(msg)};
  function event(u,v){let w=Infinity,p=Infinity;
    for(const [n,plus] of [[u-1,false],[u+1,true]])for(const q of factors(n)){
      let h=mod((plus?q+2:0)-v,2*q)||2*q;
      if(h<w||h===w&&q<p){w=h;p=q}
    }return [w,p];
  }
  function literal(u,v){for(let w=1;;w++){let n=v+w;let z=gcd(n%2?n-2:n,n%2?u+1:u-1);if(z>1)return [w,a[z]||z]}}
  function cylinder(X,T) {
    const allowed=new Map(), forced=new Map(), forbidden=new Map();
    let g=0,events=[],a4=X%4;
    for(let t=1;t<=T;t++){
      let n=X/2+3+t, e=n%2?-1:1;
      let h=2*t-g+(e===1?7:1);
      require(h!==0&&Math.abs(h)<=2*T+7,"relative factor bound");
      let candidates=factors(Math.abs(h));
      let chosen=candidates.find(p=>mod(X+g-e,p)===0);
      for(let p of candidates){
        if(chosen!==undefined&&p>chosen)break;
        let r=mod(e-g,p);
        if(p===chosen){
          require(!forced.has(p)||forced.get(p)===r,"forced clash");
          forced.set(p,r);
        }else{
          if(!forbidden.has(p))forbidden.set(p,new Set());
          forbidden.get(p).add(r);
        }
      }
      if(chosen!==undefined){events.push([t,chosen]);g+=chosen-1}
    }
    for(let p of new Set([...forced.keys(),...forbidden.keys(),3])){
      let f=forbidden.get(p)||new Set(),r=forced.get(p);
      if(p===3){require(r===undefined||r===0,"3 reset");r=0}
      require(r===undefined||!f.has(r),"excluded forced");
      allowed.set(p,{r,f});
    }
    let numerator=1n,denominator=1n;
    for(let [p,{r,f}] of allowed){numerator*=BigInt(r===undefined?p-f.size:1);denominator*=BigInt(p)}
    function accepts(Y){
      if(Y%4!==a4||Y%6!==0)return false;
      for(let [p,{r,f}] of allowed){let y=Y%p;if(r!==undefined?y!==r:f.has(y))return false}
      return true
    }
    return {events,accepts,numerator,denominator,allowed};
  }
  function word(X,T){let u=X,v=X/2+3,base=v,events=[];while(true){let [w,p]=event(u,v);v+=w;if(v-base>T)break;events.push([v-base,p]);u+=p-1}return JSON.stringify(events)}
  let stats=[],controls=0,cylinderChecks=0;
  for(let X=6;X<=Math.min(300,limit);X+=6){let u=X,v=X/2+3;for(let i=0;i<12&&u<limit;i++){let m=event(u,v),l=literal(u,v);require(m[0]===l[0]&&m[1]===l[1],"literal mismatch");controls++;u+=m[1]-1;v+=m[0]}}
  for(let T of [4,8,16,32,64])for(let X=6;X<=Math.min(300,limit);X+=6){
    const c=cylinder(X,T),w=JSON.stringify(c.events);require(w===word(X,T),"relative word");
    for(let Y=6;Y<=Math.min(1200,limit);Y+=6)if(Y%4===X%4){require(c.accepts(Y)===(word(Y,T)===w),"cylinder mismatch");cylinderChecks++}
  }
  for(const [lo,hi] of [[10000,20000],[100000,200000],[500000,1000000]]){
    if(hi>limit)continue;
    let s={lo,hi,seeds:0,twinStart:0,twinLater:0,noTwin:0,old:0,relaxed:0,oldNoTwin:0,relaxedNoTwin:0,events:0,minNoTwin:null,example:null};
    for(let X=Math.ceil(lo/6)*6;X<=hi;X+=6){
      let D=Math.ceil(X**.75);require(BigInt(D-1)**4n<BigInt(X)**3n&&BigInt(D)**4n>=BigInt(X)**3n,"D rounding");
      let u=X,v=X/2+3,first=-1,i=0,frequencies=new Map(),high=new Set(),steps=[];
      while(u<X+D){
        let fs=factors(u-1),gs=factors(u+1),twin=fs.length===1&&fs[0]===u-1&&gs.length===1&&gs[0]===u+1;
        if(twin&&first<0)first=i;
        let [w,p]=event(u,v);
        require(w<=2*p,"wait bound");
        if(!twin)require(w*w<=4*(u+1),"non-twin wait");
        frequencies.set(p,(frequencies.get(p)||0)+1);
        if(p**4>=X&&4*w>=p-1)high.add(p);
        steps.push([u,v,w,p]);u+=p-1;v+=w;i++;
        require(2*v>=u&&v<=u+1,"envelope");
      }
      let K=Math.floor(.9*Math.log2(Math.log(X))),L=0;
      for(let [p,n] of frequencies)if(p**4<X&&n**8>X)L++;
      let old=frequencies.size<=K,relaxed=L<=K&&high.size<=3;
      s.seeds++;s.events+=i;
      if(first===0)s.twinStart++;else if(first>0)s.twinLater++;else{s.noTwin++;require(2*(v-X/2-3)>=D-6,"wait lower");if(!s.minNoTwin||frequencies.size<s.minNoTwin.K)s.minNoTwin={X,K:frequencies.size,L,H:high.size,W:v-X/2-3,D}}
      if(first!==0){if(old)s.old++;if(relaxed)s.relaxed++}
      if(first<0){if(old)s.oldNoTwin++;if(relaxed)s.relaxedNoTwin++}
      if(X===500172)s.example={X,steps,first,L,H:high.size,K:frequencies.size};
    }stats.push(s)
  }
  return {limit,controls,cylinderChecks,stats};
}
console.log(JSON.stringify(audit(Number(process.argv[2]||1000000)),null,2));
