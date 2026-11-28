// Finite structural proxies, not asymptotic evidence. Run with Node or a compatible ECMAScript runtime.
function audit() {
  const assert=(v,m)=>{if(!v)throw Error(m)};
  const mod=(x,m)=>((x%m)+m)%m;
  function spf(N){const f=new Int32Array(N+1);for(let p=2;p<=N;p++)if(!f[p]){f[p]=p;if(p*p<=N)for(let n=p*p;n<=N;n+=p)if(!f[n])f[n]=p;}return f;}
  const f=spf(400100), fac=n=>{n=Math.abs(n);let a=[];while(n>1){const p=f[n];assert(p>0,"factor range");a.push(p);while(n%p===0)n/=p;}return a;};
  const next=(x,n)=>{
    let best=Infinity,lab=0,sg=0;
    for(const s of [1,-1])for(const p of fac(x+s)){
      if(p===2)continue;
      const target=s===1?0:p+2;
      let w=mod(target-n,2*p);if(w===0)w=2*p;
      if(w<best||(w===best&&p<lab)){best=w;lab=p;sg=s;}
    }
    return [best,lab,sg];
  };
  let rootCount=0, eventCount=0,topCount=0,slowCount=0,pairCount=0,shortPairCount=0,repeatPairCount=0,terminalChecks=0,distinctSinks=0,badSinkChecks=0;
  const data=[];
  for(const R of [12000,48000,192000]){
    const H=Math.floor(R**.4),Y=Math.max(7,Math.floor(H/3)),K=Math.max(3,Math.floor(Math.sqrt(H))),D=K;
    let roots=0,events=0,tops=0,slows=0,pairs=0,shorts=0,repeats=0,successes=0;
    const sinks=new Map(), bad=new Set(), actualTopKeys=new Set(),slowKeys=new Set(),relayKeys=new Set();
    for(let A=6*Math.ceil(R/6);A<=2*R;A+=6){
      roots++;
      let x=A,n=3-A/2,h=3,G=0,last=null,slow=false,short=false,topGain=0,topWait=0,lowGain=0,lowWait=0,finalIdle=0,hit=false;
      while(G<=4*H){
        const [w,p,s]=next(x,n);
        assert(w<=3*(p-1),"wait bound");
        if(h+w-1>=H){finalIdle=H-h;n+=finalIdle;h=H;hit=true;break;}
        const before=x,ng=G+p-1;n+=w;x-=p-1;h+=w-(p-1)/2;
        assert(h===x/2+n&&h>=0&&h<H,"height ledger");
        assert(mod(x-(1-s),p)===0&&mod(h-(s===1?0:3),p)===0,"arrival pins");
        if(ng>4*H)break;
        events++;
        if(p>=Y){
          tops++;topGain+=p-1;topWait+=w;
          const key=[before,n,p].join(",");actualTopKeys.add(key);
          if(w>=K){
            slows++;slow=true;slowKeys.add(key);
            const qmin=Math.min(f[before-1],f[before+1]);
            assert(qmin>=w/2,"slow rough source");
          }
          if(last){
            pairs++;const g=G-last.G,dt=n-last.n;
            const F=2*last.h+2*dt-g+1-2*(s===1?0:3);
            assert(F%p===0&&mod(last.x-g+s,p)===0,"two-arrival pins");
            assert(dt>=1&&g>=0&&dt<=3*g+w,"relay wait");
            if(p===last.p){repeats++;assert(g>=p-3,"repeat relay minimum");}
            if(g<=D&&w<K){
              short=true;shorts++;
              assert(dt<=3*D+K,"short relay time");
              if(p>D+3)assert(p!==last.p,"no repeat for short relay");
              relayKeys.add([last.x,last.h,last.p,g,dt,p,s].join(","));
            }
          }
          last={x,h,n,p,G:ng};
        }else{lowGain+=p-1;lowWait+=w;}
        G=ng;
      }
      if(hit){
        successes++;terminalChecks++;
        assert(G===A-x&&h===H&&G<=4*H,"first hit");
        assert(H-3===topWait+lowWait+finalIdle-(topGain+lowGain)/2,"split ledger");
        const key=x.toString();
        if(slow||short)bad.add(key);
        if(!sinks.has(key))sinks.set(key,{good:false,bad:false});
        const z=sinks.get(key);if(slow||short)z.bad=true;else z.good=true;
        if(!slow){assert(topWait<K*(topGain/(Y-1)+1),"fast top wait bound");}
      }
    }
    assert(bad.size<=slowKeys.size+relayKeys.size,"bad sink charge to deterministic keys");
    for(const [k,v] of sinks){assert(bad.has(k)===v.bad,"bad sink union");badSinkChecks++;}
    rootCount+=roots;eventCount+=events;topCount+=tops;slowCount+=slows;pairCount+=pairs;shortPairCount+=shorts;repeatPairCount+=repeats;distinctSinks+=sinks.size;
    data.push({R,H,Y,K,D,roots,events,tops,slows,pairs,shorts,repeats,successes,sinks:sinks.size,badSinks:bad.size,distinctSlowKeys:slowKeys.size,distinctShortRelayKeys:relayKeys.size});
  }
  const ps=[11,13,17,19,23,29,31,37,41,43];
  let crtCases=0,degenerate=0,nondegenerate=0,localDensityCases=0,nearClockCases=0;
  for(const [c,b,shift] of [[0,0,-2],[2,3,2]])for(const p of ps)for(const q of ps)if(p!==q)for(let d=-40;d<=40;d+=2){
    const m=p*q;
    let x0=-1,count=0;
    for(let x=0;x<m;x++)if(mod(x-c,p)===0&&mod(x+d-c,q)===0){x0=x;count++;}
    assert(count===1,"unique CRT");
    if(x0%2)x0+=m;
    const shifts=[p-c,p-c+shift,d+q-c,d+q-c+shift];
    const degen=new Set(shifts).size<4;
    assert(degen===[0,2,-2].includes(d+q-p),"degeneracy exact");
    if(degen)degenerate++;else nondegenerate++;
    const n=p+b-x0/2,np=q+b-(x0+d)/2;
    assert(np-n===q-p-d/2,"clock relation");
    if(Math.abs(np-n)<=7){nearClockCases++;if(degen)assert(Math.abs(d)<=2*(7+2)/3+1,"degenerate near clock");}
    for(const ell of [47,53,59]){
      if(shifts.some((a,i)=>shifts.slice(i+1).some(z=>mod(a-z,ell)===0)))continue;
      let nbad=0;
      for(let j=0;j<ell;j++){
        const x=x0+2*m*j,u=(x-c)/p+1,v=(x+d-c)/q+1;
        const forms=[u,p*u+shift,v,q*v+shift];
        if(forms.some(z=>mod(z,ell)===0))nbad++;
      }
      assert(nbad===4,"four distinct local roots");localDensityCases++;
    }
    crtCases++;
  }
  assert(pairCount>0&&shortPairCount>0&&slowCount>0&&localDensityCases>0&&degenerate>0&&nondegenerate>0,"nonvacuity");
  const a=3000,c=3128,t=900,delta=1200;
  assert(delta+2*t===a,"boundary polynomial example");
  assert(delta+t<a&&2*c<10000,"power margin");
  const beta=2700,rho=2200;
  assert(c+rho<2*beta&&beta<2800&&2800<a,"stretched time relay margin");
  assert(3<4,"collision logarithmic margin");
  return {rootCount,eventCount,topCount,slowCount,pairCount,shortPairCount,repeatPairCount,terminalChecks,distinctSinks,badSinkChecks,crtCases,degenerate,nondegenerate,localDensityCases,nearClockCases,data};
}
console.log(JSON.stringify(audit(),null,2));
