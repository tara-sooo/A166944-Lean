// Resonant cycle lines: exact line lengths, local sieve densities, proportional cofactor exclusion.
function approx(p,q,R){
 for(let h=1;h<=Math.min(R,q);h++){let a=Math.round(h*p/q);if(Math.abs(h*p-a*q)*R<=q)return {h,a,err:h*p-a*q}}
 throw Error("Dirichlet approximation");
}
function strip(p,q,e,f,lo,hi,tol,R,mods){
 const mod=(a,b)=>(a%b+b)%b,ok=(x,m)=>{if(!x)throw Error(m)};
 let v=approx(p,q,R),{h,a,err}=v,al=Math.ceil((lo-e)/p),ah=Math.floor((hi-1-e)/p),U=Math.max(0,ah-al+1),points=[],mn=Infinity,mx=-Infinity;
 for(let x=al;x<=ah;x++){let l=Math.ceil((p*x+4*p-tol+e-f)/q),u=Math.floor((p*x+4*p+tol+e-f)/q);for(let y=l;y<=u;y++){
  let d=q*y+f-p*x-e,c=h*y-a*x;ok(Math.abs(d-4*p)<=tol&&q*c===err*x+h*(d+e-f),"exact resonance line identity");points.push({x,y});mn=Math.min(mn,c);mx=Math.max(mx,c)
 }}
 if(points.length)ok(mx-mn<=(Math.abs(err)*Math.max(0,U-1)+2*h*tol)/q+1e-7,"line spread");
 let checks=0,maxRatio=0;
 for(let k of mods){let counts=new Int32Array(k*k);for(let z of points)counts[mod(z.x,k)*k+mod(z.y,k)]++;
  let main=U*2*tol/(q*k*k),errBound=12*(U/(k*h)+h+1);
  for(let n of counts){ok(Math.abs(n-main)<=errBound+1e-7,"uniform residue rectangle discrepancy");maxRatio=Math.max(maxRatio,Math.abs(n-main)/errBound);checks++}
 }
 return {...v,U,points,checks,maxRatio,lineSpread:points.length?mx-mn:0}
}
function lineAudit(p,q,e,f,tol,z){
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(x,m)=>(x%m+m)%m;
 let {h,a:A,err:ell,U,points}=z;if(!ell||h<=0||A<=0||Math.max(h,A)>=Math.min(p,q))return null;
 let gcd=(a,b)=>b?gcd(b,a%b):a;ok(gcd(h,A)===1,"primitive certificate");
 let V=Math.min(Math.max(0,U-1)/h,2*tol/Math.abs(ell)),D=Math.abs(ell)*Math.max(0,U-1)/q+2*h*tol/q,lines=new Map();
 for(let {x,y} of points){let c=h*y-A*x;if(!lines.has(c))lines.set(c,[]);lines.get(c).push({x,y})}
 ok(lines.size<=Math.floor(D)+1+1e-7&&V*D<=4*tol*U/q+1e-7,"line count and area envelope");
 let checks=0,localMeans=0,constantFibers=0,collisions=0,zeroLines=0,zeroPoints=0,nonzeroLines=0;
 for(let [c,ps] of lines){let {x,y}=ps[0];ok(ps.length<=1+V+1e-7,"line length envelope");
  for(let v of ps){let t=(v.x-x)/h;ok(Number.isInteger(t)&&v.y-y===A*t,"primitive line direction");checks++}
  let determinants=[c,q*c+2*f*h,p*c-2*e*A,p*q*c+2*f*h*p-2*e*A*q];
  ok(determinants.slice(1).every(v=>v!==0),"nonzero remaining cross determinants");
  if(c===0){zeroLines++;zeroPoints+=ps.length;for(let v of ps)ok(v.x%h===0&&v.y%A===0,"proportional cofactors")}else nonzeroLines++;
  for(let l of [5,7,11,13,17,19])if(p%l&&q%l){
   let roots=0;for(let t=0;t<l;t++)if([x+h*t,p*(x+h*t)+2*e,y+A*t,q*(y+A*t)+2*f].some(v=>mod(v,l)===0))roots++;
   if(h%l&&A%l){ok((roots<4)===determinants.some(v=>mod(v,l)===0),"four-root collision determinants");collisions++}
   else{let bad=h%l===0?[x,p*x+2*e].some(v=>mod(v,l)===0):[y,q*y+2*f].some(v=>mod(v,l)===0);ok(roots===(bad?l:2),"constant-coordinate forbidden fiber");constantFibers++}
  }
 }
 for(let l of [5,7,11,13,17,19])if(p%l&&q%l){
  let count=new Int32Array(l),good=new Int32Array(l);
  for(let x=0;x<l;x++)for(let y=0;y<l;y++){let c=mod(h*y-A*x,l);count[c]++;if([x,p*x+2*e,y,q*y+2*f].every(v=>mod(v,l)!==0))good[c]++}
  ok(count.every(v=>v===l)&&good.reduce((s,v)=>s+v,0)===(l-2)**2,"exact average line density");
  if(h%l===0||A%l===0)ok([...good].filter(v=>v===0).length===2&&[...good].every(v=>v===0||v===l-2),"two excluded c residues");localMeans++
 }
 return {lines:lines.size,checks,localMeans,constantFibers,collisions,zeroLines,zeroPoints,nonzeroLines,V,D}
}
function audit(Xs=[4096,16384,65536]){
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 let lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1);
 for(let p=2;p<=lim;p++)if(!spf[p])for(let j=p;j<=lim;j+=p)spf[j]=p;
 let out=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,tags=[],events=0;
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let C0=2*M-2,C=C0,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity;for(let I=0;I<2;I++){let v=C-1+2*I;while(v>1){let f=spf[v];while(v%f===0)v/=f;if(f*f>C+1)continue;let r=mod((I?f+2:0)-t,2*f)||2*f;if(r<w||r===w&&f<p){p=f;w=r}}}if(!p)break;
    let J=C+p-1,n=t+w,I=n%2,d=2*t-C,dp=2*n-J;path.push({C,t,J,n,I,e:1-2*I,p,w,g:p-1,d,dp,j:path.length});events++;C=J;t=n;
   }tags.push({M,C0,F:C,path})
  }
  for(let Y of [11,17,31,61])for(let mode of [0,1]){
   let L=mode?Math.max(1,Math.floor(H/2)):H,K=6,tol=Math.max(1,Math.floor(Y/4));
   let st={X,focus,N:tags.length,events,Y,L,K,tol,bins:0,nonempty:0,pairs:0,M:0,G:0,Gu:0,Gd:0,Go:0,slack3:0,ratioAbs:0,gapAbs:0,gapOutside:0,gapChecks:0,firstPairLow:0,lastMass:0,transitionMass:0,nearMass:0,farMass:0,sameMass:0,distinctMass:0,sameChecks:0,distinctChecks:0,rootChecks:0,tupleChecks:0,finiteCandidates:0,finiteCapacity:0,sourceLabels:0,largeRelayPairs:0,allMatches:0,sameTuple:0,distinctTuple:0,rotationGroups:0,rotationChecks:0,rotationPoints:0,rotationActual:0,resonantGroups:0,nonresonantGroups:0,resonantMass:0,nonresonantMass:0,cofactorRelations:0,rotationRough:0,rotationMaxRatio:0,rotationLineSpread:0,lineControls:0,lineCount:0,lineChecks:0,lineMeans:0,lineConstants:0,lineCollisions:0,lineZero:0,lineZeroPoints:0,lineNonzero:0,actualZero:0,actualZeroMass:0,actualZeroPrimitive:0};
   for(let tag of tags){
    let bins=new Map();for(let e of tag.path){let id=Math.floor((e.C-tag.C0)/L);if(!bins.has(id))bins.set(id,[]);bins.get(id).push(e)}
    for(let [bi,es] of bins){st.bins++;let lo=tag.C0+bi*L,hi=lo+L,G=es.reduce((s,e)=>s+e.g,0),high=es.filter(e=>e.p>=Y),pairs=[],used=new Set();
     st.G+=G;
     for(let j=1;j<high.length;j++){let s=high[j-1],t=high[j],p=s.p,r=t.p;if(p>K*Y||r>K*Y||s.dp<=s.d||t.dp>=t.d)continue;
      let relay=tag.path.slice(s.j+1,t.j),E=relay.reduce((a,e)=>a+e.g,0);
      let upper=Math.min(s.dp,t.d,...relay.map(e=>e.dp)),lower=Math.max(6,s.d,t.dp),m=Math.max(0,upper-lower);
      if(!m)continue;let u=s.dp-s.d,v=t.d-t.dp;
      ok(!used.has(s)&&!used.has(t)&&m<=Math.min(u,v)&&E===t.C-s.J,"actual disjoint direct pairs");
      used.add(s);used.add(t);pairs.push({s,t,E,m,u,v});st.allMatches+=m;st.firstPairLow+=E;if(E>=Y)st.largeRelayPairs++;
     }
     if(!pairs.length){st.Go+=G;st.slack3+=3*G;continue}
     st.nonempty++;let M=pairs.reduce((a,z)=>a+z.m,0),Gu=pairs.reduce((a,z)=>a+z.s.g,0),Gd=pairs.reduce((a,z)=>a+z.t.g,0),Go=G-Gu-Gd,n=pairs.length;
     let A=3*Gu+4*n-M,D=Gd-M,slack3=A+3*D+3*Go,ratio=0,gapAbs=0,out=0,near=0,far=0,same=0,distinct=0,tuples=new Map(),rot=new Map();
     ok(A>=0&&D>=0&&Go>=0&&slack3===3*G-4*M+4*n,"adjusted saturation");
     let S=new Set(pairs.map(z=>z.s.p));st.sourceLabels+=S.size;
     for(let z of pairs){let {s,t,m,u,v}=z,a=2*s.p-s.w;ok(a>=0&&t.p-3*s.p===v-u+2-2*a+2*t.w,"ratio identity");ratio+=Math.abs(t.p-3*s.p)}
     ok(ratio<=2*(A+D)+2*n,"ratio budget");
     for(let j=1;j<n;j++){let a=pairs[j-1],b=pairs[j],p=a.s.p,r=b.s.p,shift=b.s.C-a.s.C;
      let complementary=tag.path.slice(a.s.j+1,b.s.j).filter(e=>e!==a.t).reduce((s,e)=>s+e.g,0);
      ok(a.t.j<b.s.j&&shift===a.s.g+a.t.g+complementary&&shift-4*p===a.t.p-3*p-2+complementary,"actual cycle gap identity");
      gapAbs+=Math.abs(shift-4*p);out+=complementary;st.gapChecks++;st.transitionMass+=a.m;
      if(Math.abs(shift-4*p)>tol){far+=a.m;continue}
      near+=a.m;let mod0=p*r;
      if(p===r){let q1=(a.s.C-a.s.e)/p,q2=(b.s.C-b.s.e)/p;
       ok(q2-q1===4&&shift===4*p+b.s.e-a.s.e,"near cycle same-label return");mod0=p;same+=a.m;st.sameChecks++}
      else{ok(mod(a.s.C-a.s.e,p)===0&&mod(a.s.C+shift-b.s.e,r)===0,"distinct source CRT");distinct+=a.m;st.distinctChecks++;
       let key=[p,r,a.s.e,b.s.e].join("/"),o=rot.get(key)||{p,r,e:a.s.e,f:b.s.e,actual:[],mass:0};
       o.actual.push({C:a.s.C,shift,m:a.m});o.mass+=a.m;rot.set(key,o)
      }
      let primes=[];for(let f=5;f<Y&&4*f<Math.min(p,r)-1;f+=2)if(spf[f]===f){ok([a.s.C-1,a.s.C+1,b.s.C-1,b.s.C+1].every(v=>v%f!==0),"two upward endpoints rough");let roots=new Set([1,f-1,mod(1-shift,f),mod(-1-shift,f)]);ok((roots.size<4)===[shift,shift-2,shift+2].some(v=>mod(v,f)===0),"generic four roots");st.rootChecks++;primes.push(f)}
      let id=[p,r,shift,a.s.I,b.s.I].join("/"),z=tuples.get(id)||{C:a.s.C,shift,mod0,p,r,primes,mass:0,starts:new Set()};
      ok(!z.starts.has(a.s.C)&&mod(a.s.C-z.C,mod0)===0,"actual cycle tuple progression");z.starts.add(a.s.C);z.mass+=a.m;tuples.set(id,z)
     }
     ok(out<=Go&&gapAbs<=ratio+2*n+Go&&gapAbs<=2*slack3+4*n,"cycle gap slack");
     ok(far*tol<=(3*K*Y+1)*gapAbs&&near+far+pairs.at(-1).m===M&&near===same+distinct,"weighted cycle tail partition");
     for(let z of tuples.values()){let cnt=0;for(let j=Math.ceil((lo-z.C)/z.mod0);z.C+j*z.mod0+z.shift<hi;j++){let C=z.C+j*z.mod0;if(z.primes.every(f=>[C-1,C+1,C+z.shift-1,C+z.shift+1].every(v=>v%f!==0)))cnt++}
      ok(z.starts.size<=cnt&&z.mass<=cnt*(3*z.p+1),"finite four-form candidate capacity");st.tupleChecks++;st.finiteCandidates+=cnt;st.finiteCapacity+=cnt*(3*z.p+1);if(z.p===z.r)st.sameTuple++;else st.distinctTuple++}
     let rs=0,ns=0,h0=Math.max(2,Math.ceil(Y**.15)),R=Math.max(1,Math.floor((L/Y+2)/h0));
     for(let o of rot.values()){let {p,r,e,f}=o,z=strip(p,r,e,f,lo,hi,tol,R,[1,5,7,35]);ok(z.h<=R&&Math.abs(z.err)*R<=r,"actual Dirichlet certificate");
      let actualSet=new Set(z.points.map(v=>v.x+"/"+v.y));
      for(let v of o.actual){let a=(v.C-e)/p,b=(v.C+v.shift-f)/r,c=z.h*b-z.a*a;
       ok(actualSet.has(a+"/"+b)&&r*c===z.err*a+z.h*(v.shift+e-f),"actual pair in rotation strip and cofactor line");st.cofactorRelations++;
       for(let l=5;l<Y&&4*l<Math.min(p,r)-1;l+=2)if(spf[l]===l){ok(a%l!==0&&(p*a+2*e)%l!==0&&b%l!==0&&(r*b+2*f)%l!==0,"four independent coordinate exclusions");st.rotationRough++}
      }
      st.rotationGroups++;st.rotationChecks+=z.checks;st.rotationPoints+=z.points.length;st.rotationActual+=o.actual.length;st.rotationMaxRatio=Math.max(st.rotationMaxRatio,z.maxRatio);st.rotationLineSpread=Math.max(st.rotationLineSpread,z.lineSpread);
      if(z.h<h0){rs+=o.mass;st.resonantGroups++;
       let la=lineAudit(p,r,e,f,tol,z);if(la){st.lineControls++;for(let [k,v] of Object.entries({lineCount:la.lines,lineChecks:la.checks,lineMeans:la.localMeans,lineConstants:la.constantFibers,lineCollisions:la.collisions,lineZero:la.zeroLines,lineZeroPoints:la.zeroPoints,lineNonzero:la.nonzeroLines}))st[k]+=v;
        for(let v of o.actual){let a=(v.C-e)/p,b=(v.C+v.shift-f)/r,c=z.h*b-z.a*a;if(c===0){st.actualZero++;st.actualZeroMass+=v.m;let eligible=[z.h,z.a].every(n=>{if(n%2===0)return true;for(let l=3;l<=n;l+=2)if(n%l===0&&spf[l]===l&&4*l>=Math.min(p,r)-1)return false;return true});
         if(eligible){ok(z.h===1&&z.a===1&&a===b&&r>p&&(r-p)*a===v.shift+e-f,"actual proportional collapse");st.actualZeroPrimitive++}
        }}
       }
      }else{ns+=o.mass;st.nonresonantGroups++}
     }
     ok(rs+ns===distinct,"finite rotation split");st.resonantMass+=rs;st.nonresonantMass+=ns;
     st.pairs+=n;st.M+=M;st.Gu+=Gu;st.Gd+=Gd;st.Go+=Go;st.slack3+=slack3;st.ratioAbs+=ratio;st.gapAbs+=gapAbs;st.gapOutside+=out;st.lastMass+=pairs.at(-1).m;st.nearMass+=near;st.farMass+=far;st.sameMass+=same;st.distinctMass+=distinct;
    }
   }
   ok(st.G===st.Gu+st.Gd+st.Go&&st.slack3===3*st.G-4*st.M+4*st.pairs&&st.gapAbs<=2*st.slack3+4*st.pairs&&st.gapOutside<=st.Go&&st.M===st.lastMass+st.nearMass+st.farMass&&st.nearMass===st.sameMass+st.distinctMass&&st.nearMass<=st.finiteCapacity&&st.distinctMass===st.resonantMass+st.nonresonantMass,"aggregate cycle slack and capacity");
   out.push(st)
  }
 }
 return out
}
function independent(){
 let density=0,controls=0,checks=0,points=0,resonant=0,nonresonant=0,maxRatio=0;
 for(let l of [5,7,11,13,17,19])for(let p=1;p<l;p++)for(let q=1;q<l;q++)for(let e of [-1,1])for(let f of [-1,1]){
  let c=0;for(let a=0;a<l;a++)for(let b=0;b<l;b++)if(a===0||(p*a+2*e)%l===0||b===0||(q*b+2*f)%l===0)c++;
  if(c!==4*l-4)throw Error("exact product density");density++
 }
 for(let p of [101,127,257,509])for(let q of [103,149,251,521])for(let U of [32,64,256,1024])for(let off of [0,7,113])for(let side of [-1,1]){
  let h0=4,R=Math.max(1,Math.floor(U/h0)),lo=p*(300+off),hi=lo+p*U,tol=Math.floor(Math.min(p,q)/5),z=strip(p,q,side,-side,lo,hi,tol,R,[1,5,7,35]);
  controls++;checks+=z.checks;points+=z.points.length;maxRatio=Math.max(maxRatio,z.maxRatio);if(z.h<h0)resonant++;else nonresonant++;
 }
 return {density,controls,checks,points,resonant,nonresonant,maxRatio}
}
function independentLines(){
 let out={controls:0,lines:0,checks:0,localMeans:0,constantFibers:0,collisions:0,zeroLines:0,zeroPoints:0,nonzeroLines:0};
 for(let p of [101,127,257,509])for(let q of [103,149,251,521])for(let U of [32,128,512,2048])for(let off of [0,7,113])for(let e of [-1,1]){
  let lo=p*(300+off),hi=lo+p*U,tol=Math.floor(Math.min(p,q)/5),R=Math.max(1,Math.floor(U/4)),z=strip(p,q,e,-e,lo,hi,tol,R,[]),v=lineAudit(p,q,e,-e,tol,z);
  if(v){out.controls++;for(let k of ["lines","checks","localMeans","constantFibers","collisions","zeroLines","zeroPoints","nonzeroLines"])out[k]+=v[k]}
 }
 // Force proportional and constant-coordinate examples independently of MIN.
 for(let [p,q,h,A] of [[101,103,1,1],[101,127,5,4],[127,101,4,5],[257,101,2,5],[101,257,5,2]]){
  let ell=h*p-A*q,tol=20,lo=1,hi=1200,points=[];
  for(let x=lo;x<=hi;x++)for(let y=Math.ceil((p*x+4*p-tol+2)/q);y<=Math.floor((p*x+4*p+tol+2)/q);y++)points.push({x,y});
  let v=lineAudit(p,q,1,-1,tol,{h,a:A,err:ell,U:hi-lo+1,points});if(v){out.controls++;for(let k of ["lines","checks","localMeans","constantFibers","collisions","zeroLines","zeroPoints","nonzeroLines"])out[k]+=v[k]}
 }
 return out
}
console.log(JSON.stringify({lines:independentLines(),actual:audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),independent:independent()},null,2));
