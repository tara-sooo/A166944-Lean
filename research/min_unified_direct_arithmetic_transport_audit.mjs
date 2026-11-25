// Standalone finite arithmetic + transport audit; node min_unified_direct_arithmetic_transport_audit.mjs [X ...]
function audit(X, focus=false) {
 const B=Math.ceil(Math.sqrt(7*X)), T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)), limit=7*X+100;
 const spf=new Int32Array(limit+1); for(let p=2;p<=limit;p++) if(!spf[p]) for(let j=p;j<=limit;j+=p) if(!spf[j])spf[j]=p;
 const A=(x,m)=>((x%m)+m)%m, gcd=(x,y)=>{while(y){let z=x%y;x=y;y=z}return x}, check=(q,msg)=>{if(!q)throw Error(msg)};
 const fs=x=>{let r=[];while(x>1){let p=spf[x];r.push(p);while(x%p===0)x/=p}return r};
 const next=(C,t)=>{let w=Infinity,p=0; for(let I=0;I<=1;I++)for(const q of fs(C-1+2*I))if(q*q<=C+1){let z=A((I?q+2:0)-t,2*q)||2*q;if(z<w||z===w&&q<p){w=z;p=q}}return p?{C,t,p,w,v:t+w,J:C+p-1}:null};
 const tags=[];let evCount=0,reaches=0,literal=0;
 for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let C=2*M-2,t=M+2,es=[];while(C-(2*M-2)<T){let e=next(C,t);if(!e)break;check(e.w<=3*(e.p-1)&&2*e.v>=e.J,"wait or deficit");if(X===1024){for(let z=t+1;z<=e.v;z++){let I=z%2,d=gcd(z-2*I,C-1+2*I),p=d>1?spf[d]:0;if(p&&p*p>C+1)p=0;check(p===(z===e.v?e.p:0),"literal gcd");literal++}}es.push(e);C=e.J;t=e.v}if(C-(2*M-2)>=T)reaches++;evCount+=es.length;tags.push({M,es,C,t})}
 const N=tags.length, D=10,L=8,S=3,jNeed=2, small=[3], Psmall=3, A0=2*X-2, G=4*X+T+B-A0, maxDef=D+2*L+3;
 check(maxDef*maxDef<=A0+1,"cutoff");
 const rare=new Set(), codes=new Map();let discChecks=0, spacing=0, clockChecks=0;
 const key=(C,t)=>`${C}/${t}`;
 function classify(C,t,es,start) {
   let d=2*t-C;if(d<0||d>D)return false;
   let fresh=[],counts=new Map(),word=[],C0=C,t0=t,k=start;
   for(let n=t+1;n<=t+L;n++){
     if(k>=es.length)break;
     const e=es[k],p=e.v===n?e.p:0;word.push([n,p]);
     if(p){counts.set(p,(counts.get(p)||0)+1);if(p>S&&!fresh.some(a=>a[1]===p))fresh.push([n-t,p]);k++}
     if(fresh.length===jNeed)break;
   }
   for(const [p,m] of counts){check(m<=1+Math.floor((L+1)/p)&&(p-1)*m<L+p,"clock capacity");clockChecks++}
   if(fresh.length<jNeed)return false;
   const kk=key(C,t);rare.add(kk);
   let code=`${d}/${t%2}/${C%Psmall}/${fresh.map(a=>a.join(":")).join(",")}`;
   let modulus=4n*BigInt(Psmall), known=new Map(small.map(p=>[p,C%p])), gain=0;
   for(const [n,p] of word){const I=n%2,e=1-2*I,F=2*(n-1)-(C0+gain)+3-6*I;let candidates=[...known].filter(([q,r])=>F%q===0&&A(r+gain-e,q)===0).map(a=>a[0]);let least=candidates.length?Math.min(...candidates):0;
     const dis=fresh.find(a=>a[0]===n-t0);
     if(dis){check(p===dis[1]&&F%p===0&&(!least||p<least)&&A(C0+gain-e,p)===0,"discovery");known.set(p,A(e-gain,p));modulus*=BigInt(p)}else check(p===least,"reconstruct");
     if(p)gain+=p-1;discChecks++;
   }
   if(!codes.has(code))codes.set(code,{modulus,vals:new Set()});
   let row=codes.get(code);check(row.modulus===modulus,"modulus");row.vals.add(C);return true;
 }
 for(const tag of tags){let es=tag.es;tag.rarePre=es.map((e,i)=>classify(e.C,e.t,es,i));tag.rarePost=es.map((e,i)=>classify(e.J,e.v,es,i+1));}
 for(const r of codes.values()){let a=[...r.vals].sort((x,y)=>x-y);for(let i=1;i<a.length;i++){check(BigInt(a[i]-a[i-1])%r.modulus===0n,"CRT spacing");spacing++}}
 let b=Math.floor(Math.log(maxDef)/Math.log(S+1)), rareBound=(D+2)*L*(L-1)/2*b*b*(Psmall+G/(4*(S+1)**jNeed));check(rare.size<=rareBound,"rare count");
 const configs=[{R:5,l:2},{R:7,l:4},{R:11,l:8}], summaries=[];
 for(const {R,l} of configs){
  const primes=[];for(let p=3;p<=R;p+=2)if(spf[p]===p)primes.push(p);
  const Q=primes.reduce((x,p)=>x*p,1), allow=Array.from({length:Q},(_,z)=>primes.every(p=>z%p<=(p-3)/2)?1:0), alpha=allow.reduce((a,b)=>a+b,0)/Q;
  let sigma=0,zeros=0;for(let z=0;z<Q;z++){let s=0;for(let a=0;a<l;a++)s+=allow[(z+a)%Q];sigma+=(s/(l*alpha)-1)**2/Q;if(!s)zeros++}
  let longGain=0,longCount=0,barrierChecks=0,runChecks=0;
  for(const tag of tags){
   let es=tag.es;tag.runs=[];let i=0;
   while(i<es.length){if(es[i].p>R){i++;continue}let k=i;while(k+1<es.length&&es[k+1].p<=R)k++;
    const C=es[i].C,J=es[k].J;for(let z=C/2;z<J/2;z++){check(!allow[z%Q],"barrier crossed");barrierChecks++}
    if(J-C>=4*l){tag.runs.push([C,J]);longGain+=J-C;longCount++;for(let z=C/2;z<=J/2-l;z++){check(Array.from({length:l},(_,a)=>allow[(z+a)%Q]).every(v=>!v),"zero window");runChecks++}}i=k+1;
   }
   const g=tag.C-(2*tag.M-2), lg=tag.runs.reduce((s,r)=>s+r[1]-r[0],0);
   check(lg<=4*(g/2+Q)*sigma+1e-6,"variance bound");
  }
  const inside=(tag,C)=>tag.runs.find(r=>r[0]<=C&&C<r[1]);
  let rows=[];
  for(const P of [6,30,210]){
   let groups=new Map(), rareSource=0,rareDef=0,lowHigh=0,lowLow=0,lowBirth=0, pairChecks=0,defects=0,births=0,sourceAtoms=0;
   const highDist=Math.ceil(B/2), lowDist=T;
   for(let a=0;a<N;a++){let es=tags[a].es;for(let i=0;i<es.length;i++){let e=es[i];for(let K=Math.ceil(e.C/P)*P;K<e.J;K+=P){let k=`${K}/${e.C}/${e.p}`;if(!groups.has(k))groups.set(k,{K,list:[]});groups.get(k).list.push([a,i]);sourceAtoms++}}}
   const birthCache=new Map(), defectCache=new Map();
   const birth=(a,b)=>{let k=`${Math.min(a,b)}/${Math.max(a,b)}`;if(birthCache.has(k))return birthCache.get(k);let ea=tags[a].es,eb=tags[b].es,i=0,j=0;while(i<ea.length&&j<eb.length){let x=ea[i],y=eb[j];if(x.C===y.C){if(Math.max(x.t,y.t)<Math.min(x.v,y.v)){birthCache.set(k,x.C);return x.C}i++;j++}else if(x.C<y.C)i++;else j++}return null};
   const defect=(a,i,b,j)=>{let k=`${a}/${i}/${b}/${j}`;if(defectCache.has(k))return defectCache.get(k);let ea=tags[a].es,eb=tags[b].es,delta=eb[j].v-ea[i].v,J=ea[i].J;let z=null;
    for(let x=i+1,y=j+1;x<ea.length&&y<eb.length;x++,y++){let e=ea[x],f=eb[y];check(e.C===f.C&&f.t-e.t===delta,"translated prefix");if(e.p!==f.p||f.v-e.v!==delta){check(delta%(2*e.p)!==0||delta%(2*f.p)!==0,"nonperiodic defect");z=delta%(2*e.p)!==0?[a,x,J]:[b,y,J];break} }defectCache.set(k,z);return z};
   for(const {K,list} of groups.values()){
    let n=list.length,w=P/n,usedRows=new Float64Array(n),usedCols=new Float64Array(n);
    for(let ii=0;ii<n;ii++)for(let jj=0;jj<n;jj++){if(ii===jj)continue;let [a,i]=list[ii],[b,j]=list[jj],ta=tags[a],tb=tags[b],e=ta.es[i],f=tb.es[j];pairChecks++;
     if(ta.rarePost[i]||tb.rarePost[j])rareSource+=w;
     if(e.v===f.v){const C=birth(a,b);check(C!==null&&C<=K,"actual birth");births++;usedRows[ii]+=w;usedCols[jj]+=w;let r=inside(ta,C)||inside(tb,C);if(r){check(K>=r[0]&&K<r[1]+T+B,"birth halo");lowBirth+=w}}
     else {const z=defect(a,i,b,j);if(!z)continue;let [c,k,J]=z,tc=tags[c],dest=tc.es[k],hi=e.p>=Math.max(5,Math.floor(Math.sqrt(B))),dist=hi?highDist:lowDist;if(dest.C-J>=dist)continue;defects++;usedRows[ii]+=w;usedCols[jj]+=w;
      if(hi&&(tc.rarePre[k]||tc.rarePost[k])){check(dest.C-K<dist+B&&dest.J-K<dist+2*B,"rare destination halo");rareDef+=w}
      let r=inside(tc,dest.C);if(r){check(K>=r[0]-dist-B&&K<r[1],"defect halo");if(hi)lowHigh+=w;else lowLow+=w}
     }
    }
    for(let i=0;i<n;i++){check(usedRows[i]<=P+1e-7&&usedCols[i]<=P+1e-7,"joint kernel capacity")}
   }
   check(rareSource<=2*N*rare.size*(B+P)+1e-6,"rare source cap");check(rareDef<=2*N*rare.size*(highDist+2*B+P)+1e-6,"rare defect cap");
   check(lowHigh<=2*(longGain+longCount*(highDist+B+P))+1e-6,"high halo cap");check(lowLow<=2*(longGain+longCount*(lowDist+B+P))+1e-6,"low halo cap");check(lowBirth<=2*(longGain+longCount*(T+B+P))+1e-6,"birth halo cap");
   rows.push({P,sourceAtoms,pairChecks,defects,births,rareSource,rareDef,lowHigh,lowLow,lowBirth});
  }
  summaries.push({R,l,Q,sigma,zeros,longCount,longGain,barrierChecks,runChecks,rows});
 }
 return {X,focus,N,T,B,evCount,reaches,literal,rare:rare.size,rareBound,codes:codes.size,discChecks,spacing,clockChecks,summaries};
}
const xs=process.argv.slice(2).map(Number);for(const X of (xs.length?xs:[1024,4096,16384])){console.log(JSON.stringify(audit(X)));if(X>=16384)console.log(JSON.stringify(audit(X,true)));}
