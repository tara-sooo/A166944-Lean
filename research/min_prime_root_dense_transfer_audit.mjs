// Reproduce: node research/min_prime_root_dense_transfer_audit.mjs
function audit(X, mode="analytic") {
  const B=Math.ceil(Math.sqrt(7*X)), Q=Math.ceil(B/Math.log(B)), K=mode==="analytic"?Math.max(2,Math.floor(Math.pow(Math.max(1,Math.log(Math.log(B))),.25))):6;
  const J=mode==="analytic"?Math.max(0,Math.floor(Math.pow(Math.max(1,Math.log(Math.log(B))),.25))):mode==="wide"?12:2;
  const Z=mode==="analytic"?Math.max(J+5,Math.ceil(Math.sqrt(B))):mode==="wide"?17:7;
  const y=3,L=6,k=Math.max(1,Math.floor(Math.sqrt(Math.log(B))));
  const lim=7*X+5,spf=new Int32Array(lim+1),ps=[];
  for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n<=B&&n%2)ps.push(n);if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)if(!spf[j])spf[j]=n;}
  const factors=n=>{let a=[];while(n>1){let p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
  const mod=(a,m)=>((a%m)+m)%m;
  const gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c;}return a;};
  const ok=(b,msg)=>{if(!b)throw Error(msg);};
  const det=mat=>{let a=mat.map(row=>row.map(BigInt)), n=a.length;if(!n)return 1n;let sign=1n,prev=1n;for(let k=0;k<n-1;k++){let j=k;while(j<n&&a[j][k]===0n)j++;if(j===n)return 0n;if(j!==k){[a[j],a[k]]=[a[k],a[j]];sign=-sign;}const piv=a[k][k];for(let i=k+1;i<n;i++)for(let l=k+1;l<n;l++){const z=a[i][l]*piv-a[i][k]*a[k][l];ok(z%prev===0n,"Bareiss exact");a[i][l]=z/prev;}for(let i=k+1;i<n;i++)a[i][k]=0n;prev=piv;}return sign*a[n-1][n-1];};
  const rcache=new Int32Array(lim+1);
  function least(C){if(rcache[C])return rcache[C]-1;let v=0;for(const n of [C-1,C+1])for(const p of factors(n))if(!v||p<v)v=p;rcache[C]=v+1;return v;}
  let N=0,R=0,H=0,events=0,literal=0,nontwin=0,words=0,dense=0,coupled=0,rootChecks=0,rootSingular=0,scaleChecks=0,affineChecks=0,anchors=0,anchorWeight=0,denseWeight=0,denseClock=0,low=0,base=0,medium=0,high=0,Zmid=0,mediumCount=0,lowBlocks=0,lowGainMax=0;
  const support=new Map(), Wh=new Map();
  for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){
    N++;let t=M+2,C=2*M-2,cut=Math.floor((7*M-1)/4);H+=cut-t;const a=[];
    while(true){
      let tt=Infinity,p=Infinity,sg=0;
      for(const sigma of [-1,1])for(const q of factors(C+sigma)){const residue=sigma===-1?0:q+2,tick=t+1+mod(residue-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;sg=sigma;}}
      if(X<=1024){let lt=Infinity,lp=Infinity;for(let n=t+1;n<=cut;n++){let fs=factors(gcd(n%2?n-2:n,C+(n%2?1:-1)));if(fs.length){lt=n;lp=fs[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal parity gcd");literal++;}
      if(tt>cut)break;const r=least(C);ok(r>0&&r<=p&&tt-t<=2*r,"clock");a.push({C,p,sg,r});R+=r;events++;t=tt;C+=p-1;ok(C<=2*t,"post");
    }
    if(spf[C-1]!==C-1||spf[C+1]!==C+1)nontwin++;
    const ids=[];for(let i=0;i<a.length;i++)if(a[i].p>=Z)ids.push(i);
    const marks=new Uint8Array(a.length), anchorSet=new Set(), blockSet=new Set();
    let pathDense=0,pathAnchor=0;
    for(let u=0;u<ids.length;u++){
      const cnt=new Map();let P=Infinity;
      for(let v=u;v<ids.length&&v-u<=2*K;v++){
        const e=a[ids[v]];P=Math.min(P,e.p);
        if(v>u){let g=e.C-a[ids[v-1]].C-(a[ids[v-1]].p-1);if(g>J)break;ok(g>=0&&g%2===0,"background");}
        if(e.C-a[ids[u]].C>K*P)break;
        cnt.set(e.p,(cnt.get(e.p)||0)+1);words++;
        if(v-u<3||[...cnt.values()].some(n=>n<2))continue;
        dense++;
        const labels=[...cnt.keys()].sort((x,y)=>x-y), h=labels.length, word=ids.slice(u,v+1).map(i=>a[i].p), first=labels.map(p=>word.indexOf(p)),last=labels.map(p=>word.lastIndexOf(p));
        const reach=labels.map((p,i)=>labels.map((q,j)=>i===j||word.slice(first[i]+1,last[i]).includes(q)));
        for(let k=0;k<h;k++)for(let i=0;i<h;i++)for(let j=0;j<h;j++)reach[i][j] ||= reach[i][k]&&reach[k][j];
        const sink=labels.map((p,i)=>i).find(i=>labels.every((q,j)=>!reach[i][j]||reach[j][i]));
        ok(sink!==undefined,"sink exists");const members=labels.map((p,i)=>i).filter(i=>reach[sink][i]&&reach[i][sink]);
        ok(members.length>=2,"single sink");const lo=Math.min(...members.map(i=>first[i])),hi=Math.max(...members.map(i=>last[i]));
        const cword=word.slice(lo,hi+1);ok(cword.every(p=>members.some(i=>labels[i]===p)),"sink contiguous");
        const ci=ids.slice(u+lo,u+hi+1), anchor=ci[0], end=ids[v], start=ids[u];anchorSet.add(anchor);
        for(let j=start;j<=end;j++){ok(a[j].C>=a[anchor].C-K*a[anchor].p&&a[j].C+a[j].p-1<=a[anchor].C+2*K*a[anchor].p,"cover gain interval");marks[j]=1;}
        const key=anchor+":"+ci[ci.length-1];if(blockSet.has(key))continue;blockSet.add(key);coupled++;
        const pp=[...new Set(cword)].sort((x,y)=>x-y), hh=pp.length, mat=[],rhs=[];
        for(const p of pp){
          const f=cword.indexOf(p),l=cword.lastIndexOf(p), f0=a[ci[f]],l0=a[ci[l]], gap=l0.C-f0.C, off=f0.sg-l0.sg, m=(gap-off)/p;
          ok(Number.isInteger(m)&&m>=2&&m%2===0&&m<=K+2,"return multiple");
          const ns=pp.map(q=>cword.slice(f,l).filter(x=>x===q).length), total=l-f, donor=ns.reduce((s,n,j)=>s+n*(pp[j]-1),0), d=gap-donor;
          ok(d>=0&&d<=total*J,"background gain");
          mat.push(ns.map((n,j)=>(pp[j]===p?m:0)-n));rhs.push(d-total-off);
        }
        const E0=2*K*(J+1)+2;
        for(let i=0;i<hh;i++)ok(mat[i].reduce((s,x,j)=>s+x*pp[j],0)===rhs[i],"matrix equation");
        for(let root=0;root<hh;root++){
          const rest=pp.map((p,i)=>i).filter(i=>i!==root), sub=rest.map(i=>rest.map(j=>mat[i][j])), D=det(sub);
          rootChecks++;const gate=BigInt(pp[0])>BigInt(E0)*BigInt(2*K+1)**BigInt(hh);if(gate){scaleChecks++;ok(D!==0n,"rooted scale gate");}
          if(!D){rootSingular++;continue;}
          for(let j=0;j<rest.length;j++){
            const A=det(sub.map((row,i)=>row.map((z,l)=>l===j?-mat[rest[i]][root]:z))), b=det(sub.map((row,i)=>row.map((z,l)=>l===j?rhs[rest[i]]:z)));
            ok(D*BigInt(pp[rest[j]])===A*BigInt(pp[root])+b,"affine reconstruction");affineChecks++;
          }
        }
        const p=a[ci[0]].p,q=a[ci[1]].p,C0=a[ci[0]].C,e1=a[ci[1]].C-C0-(p-1);
        ok(p!==q&&mod(C0+a[ci[0]].sg,p)===0&&mod(C0+p-1+e1+a[ci[1]].sg,q)===0,"anchor CRT");
        support.set(C0+":"+p,p);
      }
    }
    for(const i of anchorSet){anchors++;pathAnchor+=a[i].p;}
    let lowRun=0,lowClock=0,above=0,baseAbove=0,midAbove=0,highAbove=0,markedAbove=0;
    const counts=new Map(),mc=new Map();
    for(let i=0;i<a.length;i++){
      const e=a[i],n=(counts.get(e.p)||0)+1;counts.set(e.p,n);
      if(marks[i]){pathDense+=e.p;denseClock+=e.r;}
      if(e.p<=y){low+=e.r;lowClock+=e.r;lowRun+=e.p-1;continue;}
      ok(lowRun<L,"LOW barrier");lowGainMax=Math.max(lowGainMax,lowRun);lowBlocks++;lowRun=0;above++;
      if(n<=k){base+=e.r;baseAbove++;}
      else if(marks[i]){markedAbove++;}
      else if(e.p<Q){medium+=e.r;midAbove++;mc.set(e.p,(mc.get(e.p)||0)+1);}
      else{high+=e.r;highAbove++;Wh.set(e.C,(Wh.get(e.C)||0)+1);}
    }
    ok(lowRun<L,"terminal LOW barrier");lowGainMax=Math.max(lowGainMax,lowRun);lowBlocks++;
    ok(above===baseAbove+midAbove+highAbove+markedAbove,"above partition");
    ok(2*lowClock<=3*L*(above+1),"low attachment");
    ok(pathDense<=6*K*pathAnchor,"dense cover bound");
    anchorWeight+=pathAnchor;denseWeight+=pathDense;mediumCount+=midAbove;for(const n of mc.values())Zmid+=n*n;
  }
  const supportWeight=[...support.values()].reduce((s,p)=>s+p,0);
  ok(anchorWeight<=N*supportWeight,"all-source anchor lift");
  const coef2=ps.filter(p=>p>y&&p<Q).reduce((s,p)=>s+(2*p+3*L)**2,0);
  ok(BigInt(2*medium+3*L*mediumCount)**2n<=BigInt(N)*BigInt(coef2)*BigInt(Zmid),"medium attachment Cauchy");
  let E=0n;for(const [C,w] of Wh)E+=BigInt(least(C))*BigInt(w)**2n;
  return {X,B,Q,Z,J,K,N,events,literal,nontwin,R,H,words,dense,coupled,rootChecks,rootSingular,scaleChecks,affineChecks,anchors,anchorWeight,supportSize:support.size,supportWeight,denseWeight,denseClock,low,base,medium,high,Zmid,mediumCount,lowBlocks,lowGainMax,E:E.toString()};
}
const xs=process.argv.slice(2).map(Number);const windows=xs.length?xs:[256,1024,4096,16384,65536,262144];for(const mode of ['analytic','diagnostic','wide'])for(const X of windows)console.log(JSON.stringify({mode,...audit(X,mode)}));
