// Endpoint clock integration and overlapping bounded-radical interval cover audit.
function audit(Xs=[4096,16384,65536]){
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(x,m)=>(x%m+m)%m;
 const lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1);for(let p=2;p<=lim;p++)if(!spf[p])for(let j=p;j<=lim;j+=p)spf[j]=p;
 // Inclusion-minimal interval cover: integer event-index intervals, two disjoint colors.
 function cover(input){
  let a=input.slice().sort((x,y)=>x.l-y.l||y.r-x.r),b=[];
  for(let z of a)if(!b.length||z.r>b.at(-1).r)b.push(z);
  let c=[];for(let z of b){while(c.length>=2&&c[c.length-2].r>=z.l)c.pop();c.push(z)}
  let ends=[-1,-1],color=[];for(let z of c){let k=ends[0]<=z.l?0:ends[1]<=z.l?1:-1;ok(k>=0,"two colors");ends[k]=z.r;color.push(k)}
  for(let z of a)for(let i=z.l;i<z.r;i++)ok(c.some(w=>w.l<=i&&i<w.r),"cover");
  return {c,color}
 }
 const results=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,D=Math.max(12,Math.floor(T/4)),K0=Math.max(12,Math.floor(B/2)),tags=[],slots=new Map(),events=0,reaches=0;
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let id=tags.length,C=2*M-2,C0=C,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity,I=0;for(let j=0;j<2;j++){let z=C-1+2*j;while(z>1){let q=spf[z];while(z%q===0)z/=q;if(q*q>C+1)continue;let v=mod((j?q+2:0)-t,2*q)||2*q;if(v<w||v===w&&q<p){p=q;w=v;I=j}}}if(!p)break;
    let n=t+w,J=C+p-1,d=2*t-C,dp=2*n-J,key=C+"/"+p+"/"+n;
    if(!slots.has(key))slots.set(key,{key,C,J,p,n,ids:[]});let s=slots.get(key);s.ids.push(id);
    ok(d>=0&&dp>=0&&w<=3*(p-1),"model");path.push({s,C,J,p,w,d,dp,g:p-1,a1:p>=47&&p>=5*d+15&&dp-6*I===2*p});C=J;t=n;events++;
   }if(C-C0>=T)reaches++;tags.push({id,C0,F:C,path})
  }
  function integr(tag,a,b,cut=K0){
   let w=0,sh=0,a1=0;for(let e of tag.path){let z=Math.max(0,Math.min(e.J,b)-Math.max(e.C,a));if(!z)continue;let x=z*e.w/e.g;w+=x;if(e.dp<=cut)sh+=x;if(e.a1)a1+=x}
   return {w,sh,a1,deep:w-sh}
  }
  function deficit(tag,x){let e=tag.path.find(e=>e.C<=x&&x<=e.J);ok(e,"deficit domain");return e.d+(x-e.C)*(e.dp-e.d)/e.g}
  const grids=[6,30,210],cells=new Map();
  function getCells(tag,P){let key=tag.id+"/"+P;if(cells.has(key))return cells.get(key);let out=[],w=0,sh=0,a1=0,gain=0;
   for(let e of tag.path){w+=e.w;if(e.dp<=K0)sh+=e.w;if(e.a1)a1+=e.w;gain+=e.g;let a=Math.ceil(e.C/P)*P,n=Math.max(0,Math.ceil((e.J-a)/P));if(!n)continue;
    ok(gain<=e.g+P+1,"cell fringe");let f=Math.min(1,3*P*n/w);for(let K=a;K<e.J;K+=P)out.push({K,w:w*f/n,sh:sh*f/n,a1:a1*f/n});w=sh=a1=gain=0
   }cells.set(key,out);return out
  }
  let snapshots=0,pairs=0,gridChecks=0,signedChecks=0,shallowChecks=0,cutoffChecks=0,weightedLen=0,weightedClock=0,weightedShallow=0,weightedA1=0,weightedSigned=0,weightedDeepSigned=0,weightedShallowUpper=0,weightedA1Upper=0,weightedGrid=0,weightError=0,deepPositive=0;
  // Actual endpoint snapshots. For audit cost, take deterministic sample of up to 16 tags per Q,
  // then ALL pairs in that sample; denominator remains FULL endpoint size. First shared exit is
  // a conservative proxy for true birth; lower bound is post of that exit, not used analytically.
  for(let l=Math.floor((2*X-2)/D)*D;l<4*X+H;l+=D){let e=l+D;
   for(let s of slots.values())if(s.C<e&&e<=s.J&&s.ids.length>=2){snapshots++;let ids=s.ids.slice(0,16),den=s.ids.length;
    for(let k=0;k<ids.length;k++)for(let j=k+1;j<ids.length;j++){let A=tags[ids[k]],F=tags[ids[j]],set=new Set(F.path.map(z=>z.s.key)),birth=A.path.find(z=>set.has(z.s.key));ok(birth,"same exit ancestry");
     let a=Math.max(l,birth.J+.5,A.C0+.5,F.C0+.5),b=Math.min(e,A.F-.5,F.F-.5);if(b<=a)continue;
     let len=b-a,ia=integr(A,a,b),ib=integr(F,a,b),da=deficit(A,a),db=deficit(A,b),delta=db-da,high=Math.max(0,db-K0)-Math.max(0,da-K0);
     ok(Math.abs(ia.w-ib.w)<1e-7&&Math.abs(ia.sh-ib.sh)<1e-7,"common suffix");ok(Math.abs(ia.w-(len+delta)/2)<1e-7,"signed clock");signedChecks++;
     ok(ia.sh<=len/2+K0/2+B+1e-7&&ia.a1<=len/2+B*2+3+1e-7,"local shallow and A1");shallowChecks++;
     ok(ia.w<=len/2+high/2+K0/2+1e-7,"clipped signed drift");cutoffChecks++;
     pairs++;weightedLen+=2*len/den;weightedClock+=2*ia.w/den;weightedShallow+=2*ia.sh/den;weightedA1+=2*ia.a1/den;weightedSigned+=delta/den;weightedDeepSigned+=high/den;weightedShallowUpper+=2*(len/2+K0/2+B)/den;weightedA1Upper+=2*(len/2+2*B+3)/den;if(high>0)deepPositive++;
     for(let P of grids){let ww=0,ss=0,aa=0;for(let z of getCells(A,P))if(a<=z.K&&z.K<b){ww+=z.w;ss+=z.sh;aa+=z.a1}
      let err=3*(2*B+P+2);ok(ww<=ia.w+err+1e-7&&ss<=ia.sh+err+1e-7&&aa<=ia.a1+err+1e-7,"assigned cell interval");
      ok(ss<=len/2+K0/2+2*B+P+2+1e-7,"shallow marked last event");gridChecks++;weightedGrid+=2*ww/(den*grids.length);weightError+=2*err/(den*grids.length)
     }
    }
   }
  }
  ok(Math.abs(weightedClock-weightedLen/2-weightedSigned)<1e-5,"weighted signed sum");ok(weightedClock<=weightedLen/2+weightedDeepSigned+weightedShallowUpper-weightedLen/2+1e-5,"weighted clipped");
  // Finite substitute for rare-band dominated prefix covers. Relax finite outside thresholds to
  // exercise overlapping families; product cutoff and same-band support are actual.
  let families=0,candidates=0,selected=0,overlap=0,coveredGain=0,selectedGain=0,small=0,large=0,outside=0,distinguished=0,leafChecks=0,coveredEvents=0;
  for(let tag of tags){let path=tag.path;for(let Z=8;Z<=B;Z*=2){let a=[];
    for(let i=0;i<path.length;i++){let prod=1,ps=new Set(),G=0,E=0;
     for(let j=i;j<Math.min(path.length,i+32);j++){let p=path[j].p;if(!ps.has(p)){prod*=p;ps.add(p)}if(prod>4*H)break;G+=path[j].g;if(p<Z||p>=2*Z)E+=path[j].g;if(G>=2*Z&&E<=G/4)a.push({l:i,r:j+1,G,E})}
    }
    if(!a.length)continue;families++;candidates+=a.length;let {c,color}=cover(a);selected+=c.length;let covered=new Set(),gg=0,ee=0,K=0,L=0,smallStarts=[new Set(),new Set()];
    for(let h=0;h<c.length;h++){let z=c[h];gg+=z.G;ee+=z.E;let block=path.slice(z.l,z.r),w=block.map((e,i)=>({e,i})).filter(x=>x.e.p>=Z&&x.e.p<2*Z),F=[...new Set(w.map(x=>x.e.p))],forest=[];
     for(let i=0;i<w.length;i++){let p=w[i].e.p;for(let j=i+1;j<w.length;j++){let q=w[j].e.p;if(q>p)break;if(q===p){forest.push([i,j]);break}}}
     let leaves=forest.filter(([i,j])=>!forest.some(([a,b])=>i<=a&&b<=j&&(i<a||b<j))).sort((a,b)=>a[0]-b[0]),sm=0,lg=0,eo=0;
     for(let k=0;k<leaves.length;k++){let [i,j]=leaves[k];if(k)ok(leaves[k-1][1]<=i,"disjoint leaf");let x=w[i].e.C,y=w[j].e.C,E=y-x-w.slice(i,j).reduce((s,z)=>s+z.e.g,0);ok(E>=0&&E%2===0,"outside");eo+=E;leafChecks++;
      if(E<=2){sm++;ok(!smallStarts[color[h]].has(x),"distinct small starts per color");smallStarts[color[h]].add(x)}else lg++;
     }
     ok(eo<=z.E&&lg*4<=z.E&&w.length<=(2**F.length-1)*(1+sm+lg),"laminar bound");small+=sm;large+=lg;K+=w.length;L+=sm+lg;
     for(let j=z.l;j<z.r;j++)covered.add(j)
    }
    let gain=[...covered].reduce((s,j)=>s+path[j].g,0);ok(gg<=2*(tag.F-tag.C0)&&gain<=gg,"cover capacity");if(gg>gain)overlap++;
    coveredGain+=gain;selectedGain+=gg;outside+=ee;distinguished+=K;coveredEvents+=covered.size;
  }}
  results.push({X,focus,B,T,D,K0,N:tags.length,events,reaches,snapshots,pairs,gridChecks,signedChecks,shallowChecks,cutoffChecks,weightedLen,weightedClock,weightedShallow,weightedA1,weightedSigned,weightedDeepSigned,weightedShallowUpper,weightedA1Upper,weightedGrid,weightError,deepPositive,families,candidates,selected,overlap,coveredGain,selectedGain,outside,distinguished,leafChecks,small,large,coveredEvents})
 }
 // All interval subsets over a five-cell path, plus a dense chain with no containment.
 let intervals=[];for(let i=0;i<5;i++)for(let j=i+1;j<=5;j++)intervals.push({l:i,r:j});let exhaustive=0;
 for(let mask=0;mask<2**intervals.length;mask++){cover(intervals.filter((z,i)=>mask>>i&1));exhaustive++}
 let dense=cover([{l:0,r:4},{l:2,r:6},{l:3,r:7},{l:5,r:9},{l:8,r:10}]);ok(dense.c.length<5&&new Set(dense.color).size===2,"overlap control");
 return {results,exhaustive,dense}
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
