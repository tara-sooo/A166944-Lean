// Time-clock guard and terminal-only low suffix offset audit.
function audit(Y,N=512){
 const V=8*Y,T=Math.floor(Y*Math.sqrt(Math.log(Y))),z=Math.ceil(T**.8),v=Math.max(1,Math.floor(T**.3)),ps=[];
 for(let p=3;p<V;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const k=ps.findIndex(p=>p>=z);if(k<0)throw Error("no high");
 let rng=(0x4c179d25^Y)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let l=4294967296-4294967296%p,x;do{x=u32()}while(x>=l);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)};
 const caps=[v,Math.max(v,Math.floor(Math.sqrt(z))),Math.max(v,Math.floor(z/4))].filter((x,i,a)=>a.indexOf(x)===i).map(v=>({v,fresh:0,short:0,shortGainLarge:0,clockBad:0,ownClockBad:0,actualKnownDuring:0,actualOwnDuring:0,knownTerminal:0,ownTerminal:0,guardGood:0,terminalGood:0,ownDivisorChecks:0,knownCongruenceChecks:0,spreadTests:0,spreadSum:0,spreadMax:0,spreadGainMax:0,spreadGoodCandidates:0,spreadBadKnown:0,spreadBadOwn:0,spreadClockChecks:0}));
 let nFresh=0,repeatHigh=0,repeatThree=0,initials=caps.map(()=>0);
 for(let j=0;j<N;j++){
  let parity=uni(2);for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let a=uni(p);t[i]=a%2===parity?a:a+p}
  function next(e,g,limit){let w=Infinity,b=-1;for(let i=0;i<limit;i++){let p=ps[i],cc=mod(c[i]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[i]+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[b])){w=f;b=i}}return {w,b}}
  function low(e,g,v){let u=e,h=g,states=[{e,g}];for(;;){let a=next(u,h,k);if(a.b<0)return {done:true,d:h-g,dt:u-e,states};if(u+a.w-e>v)return {done:false,d:h-g,dt:u-e,states};u+=a.w;h+=ps[a.b]-1;states.push({e:u,g:h})}}
  function clockIn(i,e,v){let p=ps[i];return Math.min(2*p-mod(t[i]+e,2*p),2*p-mod(t[i]+e-(p+2),2*p))<=v}
  function elig(i,g){let cc=mod(c[i]+g,ps[i]);return cc===1||cc===ps[i]-1}
  function ownBad(q,d){return (d-1)%q===0||(d+1)%q===0||(d-3)%q===0}
  for(let a=0;a<caps.length;a++)initials[a]+=low(0,0,caps[a].v).done;
  let e=0,g=0,seen=new Set();
  for(;;){
   let a=next(e,g,ps.length);if(a.b<0||e+a.w>T)break;
   let i=a.b,p=ps[i],oldg=g;e+=a.w;g+=p-1;
   if(i>=k){
    if(seen.has(i)){repeatHigh++}else{
     nFresh++;
     let known=[...seen].filter(x=>x>=k);
     for(let b of caps){
      b.fresh++;let v=b.v,cb=known.some(x=>clockIn(x,e,v)),ob=clockIn(i,e,v);
      b.clockBad+=cb;b.ownClockBad+=ob;
      if(v<p-2)ck(!ob,"own clock guard");
      let l=low(e,g,v);
      // Test matching clocks at all actual frozen low horizons through the cap (ties included).
      let ak=false,ao=false;
      for(let s=e+1,hidx=0;s<=e+v;s++){
       while(hidx+1<l.states.length&&l.states[hidx+1].e<s)hidx++;
       let h=l.states[hidx].g;
       function hit(x){let q=ps[x],cc=mod(c[x]+h,q);return (cc===1||cc===q-1)&&mod(t[x]+s-(cc===1?0:q+2),2*q)===0}
       if(known.some(hit))ak=true;if(hit(i))ao=true;
      }
      ck(!ak||cb,"clock inclusion");ck(!ao||ob,"own clock inclusion");b.actualKnownDuring+=ak;b.actualOwnDuring+=ao;
      if(l.done){
       b.short++;b.shortGainLarge+=l.d>v;
       let kb=known.some(x=>elig(x,g+l.d)),own=elig(i,g+l.d);
       b.knownTerminal+=kb;b.ownTerminal+=own;
       ck(!own||ownBad(p,l.d),"own divisibility");b.ownDivisorChecks++;
       for(let x of known){let q=ps[x],u=mod(p,q),a=mod(2-c[x]-oldg-l.d,q),d=mod(-c[x]-oldg-l.d,q);ck(elig(x,g+l.d)===(u===a||u===d),"known terminal congruence");b.knownCongruenceChecks++}
       if(!cb&&!ob){b.guardGood++;if(!kb&&!own)b.terminalGood++}
      }
      // Conditional set of terminal gains across candidate high labels, finite V.
      if(b.spreadTests<64){
       b.spreadTests++;let D=new Set(),dmax=0;
       for(let qidx=k;qidx<ps.length;qidx++){if(seen.has(qidx))continue;let q=ps[qidx],a=low(e,oldg+q-1,v);
        if(!a.done)continue;D.add(a.d);dmax=Math.max(dmax,a.d);b.spreadGoodCandidates++;
        if(known.some(x=>elig(x,oldg+q-1+a.d)))b.spreadBadKnown++;
        if(ownBad(q,a.d))b.spreadBadOwn++;
        // Even when hypothetical q was not actually selected, its own post residue would be 0 or -2.
        ck(a.d%2===0&&a.d<=v*(z-1),"finite gain");
       }
       b.spreadSum+=D.size;b.spreadMax=Math.max(b.spreadMax,D.size);b.spreadGainMax=Math.max(b.spreadGainMax,dmax);
      }
     }
    }
   }
   seen.add(i);
  }
 }
 return {Y,V,T,z,N,nFresh,repeatHigh,initials,caps};
}
for(const y of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(y)));
