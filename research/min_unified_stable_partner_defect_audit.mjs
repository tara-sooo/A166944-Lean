// Stable partner pools, common anchor groups, and constant-lag defect audit.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),D=Math.max(8,Math.floor(B/3)),S0=Math.max(2,Math.floor(B/16)),theta=.5,delta=.25,Ps=[6,30,210],lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(b,s)=>{if(!b)throw Error(`${X}/${focus} ${s}`)},mod=(a,b)=>(a%b+b)%b,eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b));
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)S[n]=S[n]||p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const tick=new Map(),proj=new Map(),paths=[],anchors=new Map();
 const key=(C,t)=>C+"|"+t;
 function inc(C,t,b){let k=key(C,t),z=tick.get(k)||{n:0,b:0};z.n++;z.b+=b;tick.set(k,z)}
 let N=0,events=0,G=0,W=0,hit=0,entropy=0,stable=0,unstable=0,stableFarChecks=0,positiveStableFar=0,anchorChecks=0,anchorActive=0,anchorStateChecks=0,rawBad=0,rawKeyPaid=0,rankChecks=0,stablePartners=0,repeatPairs=0,translationSteps=0,defects=0,lagChanges=0,splits=0,stops=0,radChecks=0,repeatedAfterDefect=0,signChecks=0,farMass=0;
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[],tag={es,C0,end:0,id:M,anchors:new Map()};
  while(C-C0<T){let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>cut)break;let g=p-1,J=C+g,w=v-t,k=C+"|"+p,o=proj.get(k)||{C,p,n:0,bad:0,slots:new Map()};proj.set(k,o);let sl=o.slots.get(v)||{v,b:0,bad:0,refs:[]};o.slots.set(v,sl);sl.b++;o.n++;
   let e={C,J,p,g,r,t,v,w,o,sl,i:es.length,tag};sl.refs.push(e);es.push(e);
   for(let j=t;j<v;j++)inc(C,j,1);
   G+=g;W+=w;events++;C=J;t=v;
  }inc(C,t,0);tag.end=C;if(C-C0>=T)hit++;paths.push(tag);
 }
 function lb(es,x){let l=0,r=es.length;while(l<r){let m=(l+r)>>1;if(es[m].C<x)l=m+1;else r=m}return l}
 function cross(es,K){let l=0,r=es.length;while(l<r){let m=(l+r)>>1;if(es[m].J<=K)l=m+1;else r=m}return l<es.length&&es[l].C<=K?l:-1}
 function getAnchor(tag,K){if(tag.anchors.has(K))return tag.anchors.get(K);let es=tag.es,l=cross(es,K-S0),r=cross(es,K+2*S0);if(l<0||r<0||l>=r){tag.anchors.set(K,null);return null}let a=es[l],b=es[r],k=[K,a.C,a.p,a.v,b.C,b.p,b.v].join("|"),z=anchors.get(k)||{K,lC:a.C,rC:b.C,n:0,rep:tag,l,r,active:false};anchors.set(k,z);z.n++;let ret={z,l,r};tag.anchors.set(K,ret);return ret}
 for(let tag of paths){let es=tag.es,pref=[0];for(let e of es){let val=0;for(let j=e.t;j<e.v;j++){let z=tick.get(key(e.C,j)),u=tick.get(key(j+1===e.v?e.J:e.C,j+1));val+=Math.log(z.n/z.b)+Math.log(u.n/z.b)}entropy+=val;pref.push(pref.at(-1)+val)}tag.pref=pref;
  for(let e of es){let lo=lb(es,e.C-D),hi=lb(es,e.C+D+1);e.stable=e.C-tag.C0>=D&&tag.end-e.C>=D&&pref[hi]-pref[lo]<=delta+1e-10;
   if(e.stable)stable++;else{unstable++;e.o.bad++;e.sl.bad++}
  }
 }
 // All tags in each anchor group, not only retained ones.
 for(let tag of paths){for(let K=S0*Math.floor(tag.C0/S0);K<=tag.end;K+=S0)getAnchor(tag,K)}
 for(let tag of paths)for(let e of tag.es)if(e.stable){let K=S0*Math.floor(e.C/S0),a=tag.anchors.get(K);if(!a||a.l>=e.i||a.r<=e.i||tag.es[a.l].C<e.C-D||tag.es[a.r].C>e.C+D)continue;
  let n=tick.get(key(e.C,e.t)).n;ok(a.z.n<=(e.sl.b)&&a.z.n>=(1-Math.exp(delta)*delta)*n-1e-7,"common anchor mass");a.z.active=true;anchorChecks++;
 }
 const used=new Map();
 for(let [k,z] of anchors)if(z.active){anchorActive++;let es=z.rep.es;for(let i=z.l;i<=z.r;i++){let e=es[i];for(let j=i===z.l?e.v-1:e.t;j<e.v;j++){let a=z.K+"|"+key(e.C,j),old=used.get(a);ok(!old||old===k,"noncollision");used.set(a,k);anchorStateChecks++}}let e=es[z.r],a=z.K+"|"+key(e.J,e.v),old=used.get(a);ok(!old||old===k,"noncollision terminal");used.set(a,k)}
 function radical(n){let a=2;while(n%2===0)n/=2;for(let p=3;p*p<=n;p+=2)if(n%p===0){a*=p;while(n%p===0)n/=p}if(n>1)a*=n;return a}
 let grids=Ps.map(P=>({P,raw:0,bad:0,keyPaid:0,rankPaid:0,stableFar:0,positive:0,checks:0}));
 for(let o of proj.values()){
  let slots=[...o.slots.values()].sort((a,b)=>a.b-b.b||a.v-b.v),cum=0,paid=0;
  for(let sl of slots){cum+=sl.b;sl.rankPaid=cum<=theta*o.n;if(sl.rankPaid)paid+=sl.b;rankChecks++}
  ok(paid<=theta*o.n,"rank payment");
  for(let z of grids){let P=z.P,n=Math.ceil((o.C+o.p-1)/P)-Math.ceil(o.C/P);if(!n)continue;let f=P*n;z.raw+=f*o.n;z.bad+=f*o.bad;z.rankPaid+=f*paid;
   let badKey=o.bad>theta*o.n/8;if(badKey){z.keyPaid+=f*o.n;continue}
   for(let s of slots)if(!s.rankPaid){let R=o.p,near=Math.floor(R/o.p)+1,far=0,good=0;for(let a of slots)if(a.b<=s.b&&Math.abs(a.v-s.v)>R){far+=a.b;good+=a.b-a.bad}
    ok(good>=far-o.bad,"stable far subtraction");z.checks++;stableFarChecks++;
    if(near*s.b<=theta*o.n/2){ok(good>3*theta*o.n/8-1e-7,"stable far lower");positiveStableFar++;z.positive++}
    if(good>0){stablePartners++;farMass+=good;z.stableFar+=good}
   }
  }
  // Audit actual representative pairs of distinct exit slots, and repeated projected hits.
  const byTime=slots.slice().sort((a,b)=>a.v-b.v);
  for(let i=0;i<byTime.length;i++)for(let j=i+1;j<Math.min(byTime.length,i+4);j++){
   let a=byTime[i].refs[0],b=byTime[j].refs[0],lag=b.v-a.v,L=radical(lag),start=a.J,enda=start,ia=a.i+1,ib=b.i+1,ea=a.tag.es,eb=b.tag.es;
   ok(lag%2===0&&lag%(2*o.p)===0,"shared exit lag");repeatPairs++;
   while(ia<ea.length&&ib<eb.length){let x=ea[ia],y=eb[ib];ok(x.C===y.C&&y.t-x.t===lag,"translated input");
    if(x.p!==y.p||y.v-x.v!==lag){defects++;if(x.p!==y.p)splits++;else lagChanges++;break}
    ok(lag%(2*x.p)===0&&Math.ceil(x.J/L)===Math.ceil(x.C/L),"lag radical barrier");translationSteps++;enda=x.J;ia++;ib++;
   }
   if(ia===ea.length||ib===eb.length)stops++;
   ok(enda-start<L,"translated span");radChecks++;
   let m=ia,n=ib;
   while(m<ea.length&&n<eb.length&&ea[m].C-start<=2*B&&eb[n].C-start<=2*B){let x=ea[m],y=eb[n];if(x.C<y.C){m++;continue}if(y.C<x.C){n++;continue}if(x.p===y.p){let h=y.v-x.v,dist=x.J-start;ok(Math.abs(h-lag)<=3*dist,"lag Lipschitz");if(Math.abs(lag)>3*dist){ok(Math.sign(h)===Math.sign(lag),"lag sign");signChecks++}if(ia<ea.length&&ib<eb.length)repeatedAfterDefect++}m++;n++}
  }
 }
 for(let z of grids){ok(z.keyPaid<=8*z.bad/theta+1e-7&&z.rankPaid<=theta*z.raw+1e-7,"uniform boundary bad key budget");rawBad+=z.bad;rawKeyPaid+=z.keyPaid}
 ok(entropy<=N*(2+Math.log(N))+1e-7&&stable+unstable===events,"entropy total");
 return {X,focus,B,T,D,S0,N,hit,events,G,W,entropy:+entropy.toFixed(6),stable,unstable,anchorChecks,anchorActive,anchorStateChecks,rankChecks,stableFarChecks,positiveStableFar,stablePartners,farMass,rawBad,rawKeyPaid,repeatPairs,translationSteps,defects,lagChanges,splits,stops,radChecks,repeatedAfterDefect,signChecks,grids};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
