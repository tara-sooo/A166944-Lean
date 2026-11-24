// Disjoint far witnesses: asynchronous triple-label relation audit.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,L=210,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=(x,m="assertion")=>{if(!x)throw Error(m)},mod=(x,m)=>(x%m+m)%m,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c}return a};
 function hit(t,C,K){let n=K+1,p=0;for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(q>B)break;let u=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(u<n||(u===n&&q<p)){n=u;p=q}while(v%q===0)v/=q}}return [n,p]}
 const out=[];
 for(let mode of ["uniform","hybrid"]){
  const T=Math.max(2,Math.floor(B/4)),floor=Math.ceil(Math.sqrt(B)),W=4,cap=p=>mode==="uniform"?T:W*Math.max(floor,p);
  const head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N),t=new Int32Array(N),K=new Int32Array(N),masses=new Map(),stops=new Map(),cohorts=[];
  const put=(i,C)=>{next[i]=head[C/2];head[C/2]=i};
  for(let i=0;i<N;i++){let M=X+2*i+1;t[i]=M+2;K[i]=Math.floor((7*M-1)/4);put(i,2*M-2)}
  let R=0,S=0,twin=0,bad=0,events=0,literal=0;
  for(let C=2*X;C<7*X;C+=2){let i=head[C/2];if(i<0)continue;let groups=new Map(),r=Math.min(spf[C-1],spf[C+1]);
   while(i>=0){let j=next[i],[n,p]=hit(t[i],C,K[i]);if(X<=1024){let nn=K[i]+1,pp=0;for(let k=t[i]+1;k<=K[i];k++){let g=gcd(k%2?k-2:k,C+(k%2?1:-1));if(g>1&&spf[g]<=B){nn=k;pp=spf[g];break}}ck(nn===n&&pp===p,"literal");literal++}
    if(!p){if(spf[C-1]===C-1&&spf[C+1]===C+1)twin++;else bad++}
    else if(p<=7){R+=r;events++;t[i]=n;put(i,C+p-1)}
    else{if(!groups.has(p))groups.set(p,[]);groups.get(p).push([i,n])}i=j}
   for(let [p,a] of groups){let key=C*B+p;ck(!masses.has(key));masses.set(key,a.length);
    if(a.length>=cap(p)){S+=a.length;stops.set(key,a.length);cohorts.push({C,p,ids:a.map(x=>x[0]).sort((a,b)=>a-b)})}
    else for(let [i,n] of a){R+=r;events++;t[i]=n;put(i,C+p-1)}
   }
  }
  ck(S+twin+bad===N);
  let Q=Math.max(11,Math.ceil(B**.4)),H=4,z=31,seen=new Uint8Array(N),stat={mode,T,floor,W,Q,H,z,R,S,twin,bad,events,literal,stopKeys:stops.size,pairs:0,unmatched:0,firstProj:0,projSameClock:0,projDifferentClock:0,projRoot:0,projBothReset:0,projMixedReset:0,projNonreset:0,projEligible:0,projEligibleSame:0,projEligibleZero:0,projEligibleDistinct:0,physical:0,physicalBeforeOrAtProj:0,physicalAfterProj:0,physRoot:0,physBothReset:0,physMixedReset:0,physNonreset:0,physImmediateSame:0,physEligible:0,physEligibleSame:0,physEligibleZero:0,physEligibleDistinct:0,physSameParentDifferentClock:0,lowBlockChecks:0,examples:[]};
  stat.async={total:0,root:0,relations:0,maxJ:0,shortJ:0,bothReset:0,mixedReset:0,nonreset:0,sameQ:0,sameP:0,distinct:0,smallProduct:0,largeProduct:0,eligible:0,eligibleReset:0,eligibleSame:0,eligibleDegenerate:0,eligibleMixed:0,eligibleSmall:0,eligibleLarge:0,eligibleLargeComparable:0,examples:[]};
  function replay(i,Cstop,pstop){
   let M=X+2*i+1,C=2*M-2,t=M+2,prior=null,physical=new Map(),projected=new Map(),cost=0,guard=0;
   for(;;){
    let key=C*(7*X+4)+t;ck(!physical.has(key));physical.set(key,{C,t,prior});if(prior){ck(C-prior.postC>=0&&C-prior.postC<L&&t-prior.n>=0&&t-prior.n<3*L,"low suffix");stat.lowBlockChecks++}
    let [n,p]=hit(t,C,K[i]);ck(p>0,"ended early");let r=Math.min(spf[C-1],spf[C+1]);ck(n-t<=2*r);
    if(p>7){let k=C*B+p;projected.set(k,{C,t,n,p,r,prior});if(stops.has(k)){ck(C===Cstop&&p===pstop);break}
     let m=masses.get(k);ck(m>0&&m<cap(p));let b=n%2?6:0,h=2*n-(C+p-1);ck(h>=b&&(h-b)%(2*p)===0);prior={q:p,D:C,n,postC:C+p-1,h,k:(h-b)/(2*p),b,m,key:k};
    }
    cost+=r;t=n;C+=p-1;ck(++guard<7*X);
   }
   return {physical,projected,cost}
  }
  function asyncClass(a,b){
   let s=stat.async,j=(a.n-b.n)/(2*a.p);ck(Number.isInteger(j)&&j!==0&&a.p===b.p&&a.C===b.C,"lag");s.total++;s.maxJ=Math.max(s.maxJ,Math.abs(j));if(Math.abs(j)<=4)s.shortJ++;
   let x=a.prior,y=b.prior;if(!x||!y){s.root++;return}
   ck(x.key!==y.key,"first projection");let g=a.C-x.postC,g2=a.C-y.postC,dt=a.n-x.n,dt2=b.n-y.n;
   ck(g>=0&&g<L&&g2>=0&&g2<L&&dt>0&&dt<=3*L+2*a.r&&dt2>0&&dt2<=3*L+2*a.r);
   let e=2*x.k*x.q-2*y.k*y.q-4*j*a.p;
   ck(e===-2*(dt-dt2)+g-g2-x.b+y.b,"three label relation");ck(Math.abs(e)<=7*L+4*a.r+6);s.relations++;
   if(!x.k&&!y.k)s.bothReset++;else if(!x.k||!y.k)s.mixedReset++;else s.nonreset++;
   if(x.q===y.q)s.sameQ++;else if(x.q===a.p||y.q===a.p)s.sameP++;else{s.distinct++;if(a.p*x.q*y.q<=X)s.smallProduct++;else s.largeProduct++}
   if(a.r<=31&&a.p>=Q&&x.q>=Q&&y.q>=Q&&x.k<=4&&y.k<=4&&Math.abs(j)<=4&&x.m<=4*x.q&&y.m<=4*y.q){
    s.eligible++;
    if(!x.k&&!y.k)s.eligibleReset++;
    else if(x.q===y.q){if(x.k!==y.k&&e!==0&&x.q!==a.p)s.eligibleSame++;else s.eligibleDegenerate++}
    else if(x.q===a.p||y.q===a.p)s.eligibleDegenerate++;
    else if(!x.k||!y.k){if(e!==0)s.eligibleMixed++;else s.eligibleDegenerate++}
    else if(a.p*x.q*y.q<=X)s.eligibleSmall++;else{s.eligibleLarge++;if(Math.min(x.q,y.q)<=a.p*2)s.eligibleLargeComparable++;}
   }
   if(a.p>=Q&&a.r<=31&&x.k<=4&&y.k<=4&&Math.abs(j)<=4&&x.q!==y.q&&x.q!==a.p&&y.q!==a.p&&a.p*x.q*y.q>X&&s.examples.length<3)s.examples.push({p:a.p,C:a.C,j,e,r:a.r,x,y});
  }
  function classify(a,b,kind){
   let x=a.prior,y=b.prior;if(!x||!y){stat[kind+"Root"]++;return}
   let dg=x.postC-y.postC,dt=x.n-y.n,limit=kind==="proj"?3*L+2*a.r:3*L;
   ck(Math.abs(dg)<L&&Math.abs(dt)<=limit,"offset");
   let e=2*x.k*x.q-2*y.k*y.q;ck(e===2*dt-dg-x.b+y.b,"height difference");ck(Math.abs(e)<=2*limit+L+6);
   if(kind==="proj")ck(x.key!==y.key,"prior projected contact");
   else if(x.key===y.key){if(x.n===y.n){ck(a.C===x.postC&&a.t===x.n,"immediate high merge");stat.physImmediateSame++;return}else stat.physSameParentDifferentClock++}
   if(!x.k&&!y.k)stat[kind+"BothReset"]++;else if(!x.k||!y.k)stat[kind+"MixedReset"]++;else stat[kind+"Nonreset"]++;
   if(x.q===y.q&&x.q>limit+L+6)ck(false,"large same label");
   if(x.q>=Q&&y.q>=Q&&x.k>0&&y.k>0&&x.h<=H*x.q&&y.h<=H*y.q&&x.m<=W*x.q&&y.m<=W*y.q&&(kind==="phys"||a.r<=z)){
    stat[kind+"Eligible"]++;if(x.q===y.q)stat[kind+"EligibleSame"]++;else if(e===0){stat[kind+"EligibleZero"]++;ck(x.q<=y.k&&y.q<=x.k,"zero determinant");}else{stat[kind+"EligibleDistinct"]++;if(stat.examples.length<5)stat.examples.push({kind,C:a.C,x,y,e})}
   }
  }
  for(let {C,p,ids} of cohorts){let m=ids.length,k=Math.floor(m/2);stat.unmatched+=m-2*k;
   for(let j=0;j<k;j++){let i=ids[j],v=ids[m-k+j];ck(!seen[i]&&!seen[v]&&2*(v-i)>=m,"matching");seen[i]=seen[v]=1;stat.pairs++;
    let a=replay(i,C,p),b=replay(v,C,p),pa=null,pb=null,va=null,vb=null;
    for(let [key,x] of a.projected){let y=b.projected.get(key);if(y){pa=x;pb=y;break}}
    ck(pa&&pb);stat.firstProj++;if(pa.n===pb.n){stat.projSameClock++;classify(pa,pb,"proj")}else {stat.projDifferentClock++;asyncClass(pa,pb);}
    for(let [key,x] of a.physical){let y=b.physical.get(key);if(y){va=x;vb=y;break}}
    if(va){stat.physical++;if(va.C<=pa.C)stat.physicalBeforeOrAtProj++;else stat.physicalAfterProj++;classify(va,vb,"phys")}
   }
  }
  ck(2*stat.pairs+stat.unmatched===S&&stat.unmatched<=stat.stopKeys&&stat.firstProj===stat.pairs&&stat.projSameClock+stat.projDifferentClock===stat.pairs);
  ck(stat.projRoot+stat.projBothReset+stat.projMixedReset+stat.projNonreset===stat.projSameClock&&stat.physRoot+stat.physBothReset+stat.physMixedReset+stat.physNonreset+stat.physImmediateSame===stat.physical);
  let s=stat.async;ck(s.total===stat.projDifferentClock&&s.root+s.relations===s.total&&s.bothReset+s.mixedReset+s.nonreset===s.relations&&s.sameQ+s.sameP+s.distinct===s.relations&&s.smallProduct+s.largeProduct===s.distinct&&s.eligible===s.eligibleReset+s.eligibleSame+s.eligibleDegenerate+s.eligibleMixed+s.eligibleSmall+s.eligibleLarge);out.push(stat)
 }
 return {X,B,N,runs:out}
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
