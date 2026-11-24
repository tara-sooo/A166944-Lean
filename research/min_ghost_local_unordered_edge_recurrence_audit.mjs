// Local recurrence of unordered high transition edges, exact difference certificates and residual windows.
function audit(U,N=96,A=5,K=12){
 const V=4*U,ps=[],sv=new Uint8Array(V+1);
 for(let p=2;p<=V;p++)if(!sv[p]){if(p>2)ps.push(p);if(p*p<=V)for(let j=p*p;j<=V;j+=p)sv[j]=1;}
 const L=2*ps.filter(p=>p<A).reduce((a,b)=>a*b,1),root=Math.ceil(Math.sqrt(2*U)),base=Math.max(7,Math.floor(root/16));
 const mod=(x,p)=>(x%p+p)%p,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x7a91de35^U)>>>0;function rand(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0;}function uni(p){let a=4294967296-4294967296%p,x;do{x=rand()}while(x>=a);return x%p;}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),ft=new Int32Array(ps.length),fg=new Int32Array(ps.length),rank=new Int32Array(ps.length);
 const out={U,N,V,A,L,K,root,base,events:0,edges:0,rootEdges:0,unorderedPairs:0,repeatEdges:0,localEdges:0,sameDirection:0,reverseDirection:0,sharedEvent:0,lateLarge:0,lateSmall:0,bothLongFirstSpan:0,farRanks:0,rootLocal:0,localWeight:0,rootWeight:0,positiveLocal:0,certificateChecks:0,multiplicityMax:0,windowChecks:0,maxSupport:0,maxWindowEdges:0};
 for(let h=0;h<N;h++){
  let parity=uni(2);ft.fill(-1);fg.fill(-1);rank.fill(0);let rk=0;
  for(let j=0;j<ps.length;j++){let p=ps[j];c[j]=uni(p);let a=uni(p);t[j]=a%2===parity?a:a+p;}
  let s=0,g=0,prev=null,edges=[],groups=new Map(),local=new Set();
  function stride(x,y,p){let D=y-x;if(D===0)return {m:0,a:0};for(let a of [-2,0,2])if(mod(D-a,p)===0){let m=(D-a)/p;ck(m>=2&&m%2===0,"positive even stride");return {m,a};}throw Error("stride");}
  for(;;){
   let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let a=2*p-mod(t[j]+s-(cc===1?0:p+2),2*p);if(a<w||(a===w&&p<ps[i])){w=a;i=j}}
   if(s+w>U)break;let p=ps[i],now=s+w,cap=g+p-1<=2*U,J=2*now-g-p+1-6*((parity+now)%2);
   if(ft[i]<0){ft[i]=now;fg[i]=g;if(p>=base)rank[i]=++rk;}
   if(cap&&p>=A){
    if(prev&&prev.p>=base&&p>=base){
     let q=prev.p;ck(p!==q||p<=L+3,"equal high exclusion");
     if(p!==q&&Math.min(p,q)>L+3){
      let lo=Math.min(p,q),hi=Math.max(p,q),li=p===lo?i:prev.i,ri=p===hi?i:prev.i;
      let d=g-prev.g-q+1;ck(d>=0&&d<L&&d%2===0,"low gain");
      let x={start:prev.g,end:g,lo,hi,li,ri,lg:p===lo?g:prev.g,rg:p===hi?g:prev.g,dir:q===lo?1:-1,d,p,q,idx:edges.length};
      let key=lo+","+hi,list=groups.get(key)||[];out.edges++;out.rootEdges+=+(lo>=root);out.repeatEdges+=+(list.length>0);
      let tuple=[x.dir,d,mod(c[li]+x.lg,lo),mod(c[ri]+x.rg,hi)].join(",");
      if(lo>=root)ck(!list.some(y=>y.tuple===tuple),"CRT unique directed signature above root");
      x.tuple=tuple;
      let y=list[list.length-1];
      if(y&&x.end-y.start<=K*lo){
       let span=x.end-y.start,aa=stride(y.rg,x.rg,hi),bb=stride(y.lg,x.lg,lo);
       let m=aa.m,n=bb.m,e=0,jr=m,jl=n;
       if(y.dir===x.dir){e=x.dir*(x.d-y.d)+bb.a-aa.a;out.sameDirection++;}
       else if(y.dir===1){jr=m+1;jl=n-1;e=2-y.d-x.d+bb.a-aa.a;out.reverseDirection++;}
       else{jr=m-1;jl=n+1;e=-2+y.d+x.d+bb.a-aa.a;out.reverseDirection++;}
       ck(jr>=1&&jl>=1&&jr*hi-jl*lo===e&&Math.abs(e)<=2*L+6,"edge difference certificate");
       ck(jr<=span/hi+2&&jl<=span/lo+2&&hi<=span+1,"coefficient and ratio");
       if(ft[ri]>ft[li]){ck(jl*lo+e===jr*hi&&jl*lo+e>0,"latest large positive divisor");out.lateLarge++;}
       else{ck(jr*hi-e===jl*lo&&jr*hi-e>0,"latest small positive divisor");out.lateSmall++;}
       ck(ft[i]<now,"later endpoint is repeated");
       out.localEdges++;out.sharedEvent+=+(y.end===x.start);out.bothLongFirstSpan+=+(x.rg-fg[ri]>K*hi&&x.lg-fg[li]>K*lo);out.farRanks+=+(Math.abs(rank[ri]-rank[li])>3);
       out.rootLocal+=+(lo>=root);out.localWeight+=p;if(lo>=root)out.rootWeight+=p;
       out.positiveLocal+=Math.max(0,J-prev.J);out.certificateChecks++;local.add(x.idx);
      }
      list.push(x);groups.set(key,list);edges.push(x);
     }
    }
    prev={p,i,g,J};
   }
   s=now;g+=p-1;out.events++;if(!cap)break;
  }
  out.unorderedPairs+=groups.size;
  for(let list of groups.values()){out.multiplicityMax=Math.max(out.multiplicityMax,list.length);if(list[0].lo>=root)ck(list.length<=4*L,"edge multiplicity cap");}
  // For every start edge, inspect all edges contained in a gain window of width K*base.
  for(let j=0;j<edges.length;j++){
   let seen=new Set(),support=new Set(),good=0;
   for(let i=j;i<edges.length&&edges[i].end-edges[j].start<=K*base;i++){
    let x=edges[i],key=x.lo+","+x.hi;support.add(x.lo);support.add(x.hi);
    if(seen.has(key))ck(local.has(x.idx),"local repeated unordered edge marked");
    seen.add(key);if(!local.has(x.idx))good++;
   }
   ck(good<=support.size*(support.size-1)/2,"simple residual window");
   out.windowChecks++;out.maxSupport=Math.max(out.maxSupport,support.size);out.maxWindowEdges=Math.max(out.maxWindowEdges,good);
  }
 }
 return out;
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?64:128)));
