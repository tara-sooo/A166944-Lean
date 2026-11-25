// Finite diagnostic of band terminal masks, radical-certified shorter pursuits and large destination counts.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,Ps=[6,30,210],Y=Math.max(5,Math.ceil(B**.1)),beta=[.25,.5,.75],delta=.125,sigma=.2,tau=.25,L=beta.map(b=>Math.ceil(B**(b+delta))),U=beta.map(b=>Math.floor(B**b)),Lold=focus?Math.floor(B/4):2*B,lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(b,m)=>{if(!b)throw Error(`${X}/${focus}: ${m}`)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)S[n]=S[n]||p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const tags=[],proj=new Map(),stats=beta.map((b,k)=>({b,L:L[k],U:U[k],blocks:0,paid:0,paidBound:0,rich:0,richChecks:0,sourceChecks:0,barrierChecks:0,certifiedRows:0,certifiedPairs:0,shortPairs:0,offPairs:0,shortClock:0,offClock:0,offFocal:0,offPartner:0,capacityChecks:0,capSum:0,globalCap:0,predecessorChecks:0,spatialChecks:0}));
 let N=0,events=0,hit=0;
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C=2*M-2,t=M+2,stop=Math.floor((7*M-1)/4),es=[],tag={M,es,end:0};
  while(C-(2*M-2)<T){let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>stop)break;let J=C+p-1,w=v-t,k=p>=Y&&w>=tau*(p-1)?U.findIndex(x=>p<=x):-1,e={C,J,p,t,v,w,r,k,i:es.length,tag,rich:false,tail:0,src:Ps.map(()=>[]),loads:Ps.map(()=>beta.map(()=>[0,0]))};es.push(e);events++;C=J;t=v;
   let key=e.C+"|"+p+"|"+mod(v,6),a=proj.get(key)||[];a.push(e);proj.set(key,a)
  }
  tag.end=C;if(C-(2*M-2)>=T)hit++;tags.push(tag);
  for(let k=0;k<beta.length;k++){let z=stats[k],D=Math.max(1,Math.floor(L[k]/2)),blocks=new Map();for(let e of es)if(e.k===k){let key=Math.floor(e.C/D),a=blocks.get(key)||[];a.push(e);blocks.set(key,a)}
   for(let a of blocks.values()){let tail=0,paid=0;for(let i=a.length-1;i>=0;i--){let e=a[i];e.tail=tail;e.rich=tail>=sigma*L[k];if(e.rich)z.rich++;else paid+=e.w;tail+=e.w}ok(paid<=sigma*L[k]+2*U[k]+1e-7,"terminal band budget");z.blocks++;z.paid+=paid;z.paidBound+=sigma*L[k]+2*U[k]}
  }
  for(let j=0;j<Ps.length;j++){let P=Ps[j],cell=[];for(let e of es){cell.push(e);let nk=Math.ceil(e.J/P)-Math.ceil(e.C/P);if(!nk)continue;let eligible=e.p<=P/2?cell.filter(f=>f.p<=P/2):e.p>=2*P?[e]:[];for(let f of eligible)if(f.k>=0&&f.rich&&e.p<=Math.max(U[f.k],P/2)&&L[f.k]<=Lold){let k=f.k,z=stats[k]; // finite geometry explicitly requires q<=U to match analytic band
     if(e.p>U[k])continue;
     ok(e.J-f.C<=U[k]+2*P,"source right-cell shift");e.src[j].push(f);z.sourceChecks++;
    }ok(e.src[j].reduce((a,f)=>a+f.w,0)<=9*P*nk,"row cell capacity");cell=[]}
  }
 }
 for(let a of proj.values()){let n=a.length,ready=a.filter(e=>e.tag.end-e.J>=Lold);if(!ready.length)continue;
  for(let e of ready)for(let j=0;j<Ps.length;j++){let P=Ps[j],es=e.tag.es;
   for(let k=0;k<beta.length;k++){let z=stats[k],foc=e.src[j].filter(f=>f.k===k),weight=foc.reduce((v,f)=>v+f.w,0);if(!weight)continue;let rich=0,rad=6,overflow=false,barrier=0;const prefixLabels=new Set();
    for(let i=e.i+1;i<es.length&&es[i].C<e.J+L[k];i++){let f=es[i];if(f.k===k)rich+=f.w;
     if(!overflow){if(rad%f.p!==0)rad*=f.p;if(rad% e.p!==0)rad*=e.p;if(rad>4*H)overflow=true;else{prefixLabels.add(f.p);if(f.k===k)barrier+=f.w}}
    }
    // Entire future band tail lies in the short horizon after the source except loss before J.
    for(let f of foc){let lost=0,block=Math.floor(f.C/Math.max(1,Math.floor(L[k]/2)));for(let i=f.i+1;i<=e.i;i++){let x=es[i];if(x.k===k&&Math.floor(x.C/Math.max(1,Math.floor(L[k]/2)))===block)lost+=x.w}ok(rich+lost+1e-7>=f.tail,"future band richness");z.richChecks++}
    let cert=rich>barrier;if(cert)z.certifiedRows++;z.barrierChecks++;
    for(let f of ready){if(f.v===e.v)continue;let lag=f.v-e.v,x=es,y=f.tag.es,i=e.i+1,b=f.i+1,rad0=6;if(rad0%e.p)rad0*=e.p;let before=0,first=null;
     while(i<x.length&&b<y.length&&x[i].C<e.J+Lold){let u=x[i],v=y[b];ok(u.C===v.C&&v.t-u.t===lag,"translated prefix");if(u.p!==v.p||u.w!==v.w){first=[u,v,i,b];break}ok(lag%(2*u.p)===0,"prefix period");if(rad0%u.p)rad0*=u.p;ok(rad0<=4*H,"prefix radical bound");if(u.C<e.J+L[k]&&u.k===k){before+=u.w;ok(u.r>=tau*(u.p-1)/2,"rough position");z.spatialChecks++}i++;b++}
     ok(before<=barrier+1e-7,"translated high mass below radical barrier");
     if(cert){ok(first&&first[0].C<e.J+L[k],"certified short first defect");z.certifiedPairs++}
     if(!first||first[0].C>=e.J+L[k])continue;z.shortPairs++;let [u,v,ii,bb]=first,charge=weight/n;z.shortClock+=charge;
     let q0=x[ii-1].p;ok(q0===y[bb-1].p&&q0<=Math.max(U[k],L[k]+1),"previous label bound");z.predecessorChecks++;
     let threshold=B**(beta[k]+2*delta);if(Math.max(u.p,v.p)<threshold)continue;z.offPairs++;z.offClock+=charge;
     let side=u.p>=threshold?0:1,d=side?v:u;d.loads[j][k][side]+=charge;if(side)z.offPartner+=charge;else z.offFocal+=charge;
    }
   }
  }
 }
 for(let k=0;k<beta.length;k++){let z=stats[k],threshold=B**(beta[k]+2*delta),sum=0;
  for(let tag of tags)for(let e of tag.es)for(let j=0;j<Ps.length;j++){let P=Ps[j],load=e.loads[j][k].reduce((a,b)=>a+b,0);if(!load)continue;ok(e.p>=threshold,"large destination");let cap=18*(L[k]+U[k]+P);ok(load<=cap+1e-7,"short two-role capacity");z.capSum+=cap;z.capacityChecks++;sum+=load}
  ok(eq(sum,z.offClock)&&eq(sum,z.offFocal+z.offPartner),"off-band conservation");let count=tags.reduce((s,t)=>s+t.es.filter(e=>e.p>=threshold).length,0);ok(count<=N*H/(threshold-1)+1e-7,"large destination count");z.globalCap=count*Ps.reduce((s,P)=>s+18*(L[k]+U[k]+P),0);ok(sum<=z.globalCap+1e-7,"global off-band cap");
  for(let key of Object.keys(z))if(typeof z[key]==="number")z[key]=+z[key].toFixed(6)
 }
 return {X,focus,B,T,H,N,events,hit,stats}
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
