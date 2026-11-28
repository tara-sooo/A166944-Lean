// Finite adaptive transcript, mixed-source residue and true-orbit checks. Not an asymptotic proof.
function audit() {
  const assert=(v,m)=>{if(!v)throw Error(m)};
  const mod=(x,m)=>((x%m)+m)%m;
  const inv=(x,p)=>{for(let a=1;a<p;a++)if(mod(x*a,p)===1)return a;throw Error("no inverse")};
  const winner=(x,n,ps)=>{const s=n%2===0?1:-1;for(const p of ps)if(mod(x+s,p)===0&&mod(n,2*p)===(s===1?0:p+2))return p;return 0};
  const x0=(r,u,c)=>r*(u-1)+c;
  const pin=(g,w,s,b,c,q)=>{
    const bs=s===1?0:3;
    const rr=mod((g-2*b-2*w-1+2*bs)*inv(2,q),q);
    if(!rr)return null;
    const uu=mod(1+(g-c-s)*inv(rr,q),q);
    return [rr,uu];
  };
  const goodSource=(r,u,p,shift)=>mod(r,p)!==0&&mod(u,p)!==0&&mod(r*u+shift,p)!==0;
  let modelRoots=0, modelLeaves=0, modelTicks=0, pinChecks=0, outsideChecks=0, forbiddenChecks=0, emptyLeaves=0;
  const modelDetails=[];
  for(const [c,b,shift] of [[0,0,-2],[2,3,2]]){
    const B=12,M=B*5*7,T=18,ps=[3,5,7],base=[3],fresh=[5,7];
    const groups=new Map();
    for(let rr=1;rr<M;rr+=2)for(let uu=1;uu<M;uu+=2){
      if(!ps.every(q=>goodSource(rr,uu,q,shift)))continue;
      const r=rr+100*M,u=uu+100*M,start=x0(r,u,c),n0=r+b-start/2;
      let x=start,known=new Set(base),events=[],word=[];
      for(let w=1;w<=T;w++){
        const n=n0+w,s=n%2===0?1:-1,g=start-x,p=winner(x,n,ps),trial=winner(x,n,[...known].sort((a,b)=>a-b));
        if(p&&!known.has(p)){
          const z=pin(g,w,s,b,c,p);
          assert(z&&z[0]===mod(r,p)&&z[1]===mod(u,p),"fresh pin");
          assert(!trial||trial>p,"fresh priority");
          pinChecks++;known.add(p);events.push([w,p]);
        }else assert(trial===p,"known winner exact");
        word.push([g,w,s,p]);
        if(p)x-=p-1;
        modelTicks++;
      }
      const key=JSON.stringify([rr%B,uu%B,events]);
      const str=JSON.stringify(word);
      if(groups.has(key)){const a=groups.get(key);assert(a.str===str,"history must determine all ticks");a.count++;}
      else groups.set(key,{str,word,events,count:1,rr,uu});
      modelRoots++;
    }
    let sum=0;
    for(const a of groups.values()){
      let product=1;
      for(const q of fresh){
        const fired=a.events.find(e=>e[1]===q);
        if(fired){
          const t=a.word[fired[0]-1],z=pin(t[0],t[1],t[2],b,c,q);
          assert(z&&goodSource(z[0],z[1],q,shift),"pinned source");
          for(const [g,w,s,p] of a.word){
            if(w>=fired[0])break;
            if(!p||q<p){const v=pin(g,w,s,b,c,q);assert(!v||v[0]!==z[0]||v[1]!==z[1],"earlier denial");}
          }
        }else{
          const denied=new Set();
          for(const [g,w,s,p] of a.word)if(!p||q<p){const z=pin(g,w,s,b,c,q);if(z)denied.add(z.join(","));}
          let count=0;
          for(let rr=0;rr<q;rr++)for(let uu=0;uu<q;uu++)if(goodSource(rr,uu,q,shift)&&!denied.has(rr+","+uu))count++;
          assert(denied.size<=T,"denied density");
          product*=count;
        }
      }
      assert(product===a.count,"exact leaf CRT mass");
      sum+=product;modelLeaves++;
      // An outside prime is independent of the restricted history:
      // check the two pin equations against all nonzero r residues.
      for(const [g,w,s] of a.word.filter((_,i)=>i%6===0)){
        const q=11,z=pin(g,w,s,b,c,q);let count=0;
        for(let rr=1;rr<q;rr++)for(let uu=0;uu<q;uu++){
          const bs=s===1?0:3;
          const ok=mod(2*(rr+b)+2*w-g+1-2*bs,q)===0&&mod(rr*(uu-1)+c-g+s,q)===0;
          if(ok){count++;assert(z&&rr===z[0]&&uu===z[1],"external pin uniqueness");}
        }
        assert(count===(z?1:0),"external count");
        outsideChecks++;
      }
    }
    assert(sum===[...groups.values()].reduce((a,b)=>a+b.count,0),"mass sum");
    modelDetails.push({c,b,roots:sum,leaves:groups.size});
  }
  for(const [c,shift] of [[0,-2],[2,2]])for(const p of [11,13,17,19,23,29,31,37,41,43,47,53])for(let g=0;g<=120;g+=2){
    let three=0,five=0;
    for(let r=0;r<p;r++)for(let u=0;u<p;u++){
      const bad=!goodSource(r,u,p,shift),y=r*(u-1)+c-g;
      if(bad)three++;
      if(bad||mod(y-1,p)===0||mod(y+1,p)===0)five++;
    }
    assert(three===3*p-2,"source local count");
    assert(five<=5*p&&five>=5*p-14,"five-form density uniform");
    forbiddenChecks++;
  }
  function spf(N){const f=new Int32Array(N+1);for(let p=2;p<=N;p++)if(!f[p]){f[p]=p;if(p*p<=N)for(let n=p*p;n<=N;n+=p)if(!f[n])f[n]=p}return f;}
  let anchors=0,actualTicks=0,actualFresh=0,matchTicks=0,absorptions=0,actualDetails=[];
  for(const R of [100000,400000,1000000]){
    const f=spf(2*R+5),fac=n=>{const a=[];while(n>1){const p=f[n];a.push(p);while(n%p===0)n/=p;}return a;};
    let local=0,lt=0,lf=0,lm=0,la=0;
    for(let A=6*Math.ceil(R/6);A<=2*R;A+=6){
      const n=A+1,p=f[n],v=n/p;
      if(v<=p||f[v]!==v||p<R**.28||p>R**.46)continue;
      const r=f[A-1],u=(A-1)/r;
      if(r<R**.16||u<=r||u%4!==1)continue;
      const allOther=[...fac(A-1).filter(q=>q!==r),...fac(A+1)];
      if(allOther.some(q=>q<=3*r+7))continue;
      const w0=(3*r-1)/2,nBirth=3-A/2;
      let w=1,actual=0;
      for(;w<=w0;w++){const n=nBirth+w;actual=winner(A,n,fac(A+(n%2===0?1:-1)));if(actual)break;}
      assert(w===w0&&actual===r,"actual high minus anchor");
      const start=A-r+1,n0=nBirth+w0;
      assert(start===x0(r,u,2)&&start/2+n0===r+3,"actual anchor geometry");
      const T=96,Z=31,small=[3,5,7],known=new Set(small);
      let x=start,y=start,matching=true,absorbed=false;
      for(let t=1;t<=T;t++){
        const n=n0+t,s=n%2===0?1:-1,g=start-x,all=fac(x+s),q=winner(x,n,all),trial=winner(x,n,[...known].sort((a,b)=>a-b));
        if(q&&!known.has(q)){
          if(q!==r&&g<r-3){const z=pin(g,t,s,3,2,q);assert(z&&z[0]===mod(r,q)&&z[1]===mod(u,q),"actual new pin");}
          assert(!trial||trial>q,"actual new priority");known.add(q);lf++;
        }else assert(trial===q,"actual adaptive replay");
        const smallFactors=[...new Set([...fac(y-1),...fac(y+1)])].filter(q=>q<=Z&&q%2===1);
        const qz=winner(y,n,smallFactors);
        if(!smallFactors.length){if(!absorbed)la++;absorbed=true;}
        if(absorbed)assert(qz===0,"rough restricted absorption");
        if(matching){assert(x===y,"prefix state");if(q===qz)lm++;else{assert(q>Z&&qz===0,"first discrepancy");matching=false;}}
        if(q)x-=q-1;if(qz)y-=qz-1;
        lt++;
        if(x<=2||y<=2)break;
      }
      local++;
    }
    anchors+=local;actualTicks+=lt;actualFresh+=lf;matchTicks+=lm;absorptions+=la;
    actualDetails.push({R,anchors:local,ticks:lt,fresh:lf,matchedPrefixTicks:lm,absorptions:la});
  }
  assert(anchors>0&&actualFresh>0&&absorptions>0,"nonvacuous actual checks");
  // Fixed power-budget checks (units 1/10000).
  const a=2855,c=3130,b=100,delta=100,u=100,beta=500;
  assert(b+delta+2*u+beta<a,"CRT parameter margin");
  assert(b+delta+c<10000-c,"large prime tail progression");
  assert(b+delta+2*u+beta+u<a,"CRT summed-error margin");
  return {modelDetails,modelRoots,modelLeaves,modelTicks,pinChecks,outsideChecks,forbiddenChecks,actualDetails,anchors,actualTicks,actualFresh,matchTicks,absorptions};
}
console.log(JSON.stringify(audit(),null,2));
