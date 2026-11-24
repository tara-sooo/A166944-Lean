// MIN wheel: source-preserving SAME/ROOT demotions with recent large labels.
// Run: node research/min_recent_large_merge_audit.mjs 256 1024 4096 16384 65536
function audit(X,y,qOverride,zOverride) {
  const B=Math.ceil(Math.sqrt(7*X)), L=y===3?6:210;
  const Q=qOverride??Math.ceil(B/Math.cbrt(Math.log(B))), z=zOverride??Math.max(1,Math.floor(Math.sqrt(Math.log(B))));
  const gate=Q>2*z+3*L+2;
  const spf=new Int32Array(7*X+4);
  for(let p=2;p<spf.length;p++) if(!spf[p]) {
    spf[p]=p;
    if(p*p<spf.length) for(let i=p*p;i<spf.length;i+=p) if(!spf[i])spf[i]=p;
  }
  function hit(t,C,K) {
    let T=K+1,P=0;
    for(const s of [-1,1]){
      let v=C+s;
      while(v>1){let p=spf[v];if(p>B)break;
        let m=2*p,r=s===-1?0:p+2,u=t+1+((r-(t+1)%m+m)%m);
        if(p>2&&(u<T||(u===T&&u<=K&&p<P))){T=u;P=p;}
        while(v%p===0)v/=p;
      }
    }return [T,P];
  }
  const check=(x,msg)=>{if(!x)throw Error(msg)};
  const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a};
  const key=(t,C)=>t*(7*X+4)+C;
  const V=new Map(), costs=new Float64Array(X/2);
  let events=0, literal=0;
  for(let M=X+1;M<2*X;M+=2){
    let t=M+2,C=2*M-2,K=Math.floor((7*M-1)/4),h=null;
    let k=key(t,C),v=V.get(k);
    if(!v)V.set(k,v={t,C,root:0,edges:new Map()});
    v.root=M;
    for(;;){
      let [T,p]=hit(t,C,K);
      if(X<=1024){
        let a=K+1,b=0;
        for(let j=t+1;j<=K;j++){
          let g=gcd(j%2?j-2:j,j%2?C+1:C-1);
          if(g>1&&spf[g]<=B){a=j;b=spf[g];break}
        }check(a===T&&b===p,'literal clock');literal++;
      }
      if(!p)break;
      let r=Math.min(spf[C-1],spf[C+1]);check(T-t<=2*r,'clock bound');
      costs[(M-X-1)/2]+=r;events++;
      let D=C+p-1, nh=p>y?{p,t:T,C:D}:h;
      if(h){check(C-h.C<L&&t-h.t<=3*(C-h.C),'LOW block');}
      let nk=key(T,D), w=V.get(nk);
      if(!w)V.set(nk,w={t:T,C:D,root:0,edges:new Map()});
      // M increasing: last writer is the maximal original cutoff.
      w.edges.set(k,{M,p,t,C,h,nh});
      t=T;C=D;h=nh;k=nk;
    }
  }
  let same=0,root=0,rareSame=0,rareRoot=0,near=0,rareSameCost=0,rareRootCost=0;
  const demoted=new Set(), candidates=new Set();
  function demote(M){check(!demoted.has(M),'double demotion');demoted.add(M);}
  for(const v of V.values()){
    const groups=new Map();
    for(const e of v.edges.values()){
      if(!groups.has(e.p))groups.set(e.p,[]);
      groups.get(e.p).push(e);
    }
    let winners=[];
    for(const list of groups.values()){
      list.sort((a,b)=>b.M-a.M);
      const a=list[0];winners.push(a);
      for(const b of list.slice(1)){
        same++;demote(b.M);
        check(a.C===b.C&&a.t!==b.t,'same predecessor horizon');
        if(Math.abs(a.t-b.t)<2*z){near++;
          if(a.h&&b.h&&a.h.p>=Q&&b.h.p>=Q){
            rareSame++;rareSameCost+=costs[(b.M-X-1)/2];
            const e1=a.C-a.h.C,e2=b.C-b.h.C;
            check(e1>=0&&e1<L&&e2>=0&&e2<L,'gain offsets');
            check(Math.abs(a.h.t-b.h.t)<2*z+3*L,'time offset');
            if(gate)check(a.h.p!==b.h.p,'same recent label under gate');
            let ck=[a.C,a.h.p,b.h.p,e1,e2,a.h.t,b.h.t].join(',');
            check(!candidates.has(ck),'candidate injection');candidates.add(ck);
          }
        }
      }
    }
    winners.sort((a,b)=>b.M-a.M);
    for(const e of winners.slice(1))demote(e.M);
    if(v.root&&winners.length){
      let a=winners[0];root++;check(a.M<v.root,'root cutoff order');demote(a.M);
      if(a.nh&&a.nh.p>=Q){rareRoot++;rareRootCost+=costs[(a.M-X-1)/2];
        const e=v.C-a.nh.C;
        check(e>=0&&e<L,'root low offset');
        check((v.C-e)%a.nh.p===0||(v.C-e+2)%a.nh.p===0,'root residue');
      }
    }
  }
  return {X,y,B,L,Q,z,gate,events,literal,same,root,near,rareSame,rareRoot,rareSameCost,rareRootCost};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[256,1024,4096,16384,65536]) {
  for(const y of [3,7])console.log(JSON.stringify(audit(X,y)));
  if(X>=4096)console.log(JSON.stringify(audit(X,3,29,3)));
}
