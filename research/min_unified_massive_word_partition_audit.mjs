// Exact translated-word classes and massive-clock partner transport audit.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,L=Math.max(8,Math.floor(B/8)),Pset=[6,30,210],low=[2,Math.max(2,Math.floor(L/2)),0],hi=Math.max(2,Math.floor(L/4)),Y=Math.max(5,Math.ceil(Math.sqrt(B))),cut=focus?2:3,boost=2*cut,eta=.35,lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(v,m)=>{if(!v)throw Error(`${X}/${focus} ${m}`)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)S[n]=S[n]||p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 function gcd(a,b){while(b){let t=a%b;a=b;b=t}return a}
 const mk=()=>[0,0,0],proj=new Map(),tick=new Map(),tags=[];let N=0,events=0,W=0,hit=0,sourceCells=0,classes=0,wordGroups=0,wordSlots=0,radChecks=0,radSingleton=0,pairs=0,samePairs=0,defPairs=0,routeChecks=0,capChecks=0,wordBoundChecks=0;
 const key=(C,t)=>C+"|"+t,inc=(C,t)=>tick.set(key(C,t),(tick.get(key(C,t))||0)+1);
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,stop=Math.floor((7*M-1)/4),es=[],tag={es,end:0,M};
  while(C-C0<T){let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>stop)break;let J=C+p-1,g=p-1,w=v-t;ok(w<=2*r&&w<=3*g,"wait");let e={C,J,p,g,w,t,v,i:es.length,tag,Wl:mk(),Wh:mk(),Sl:mk(),Sh:mk(),dl:mk(),dh:mk()};es.push(e);
   let k=C+"|"+p,o=proj.get(k)||{C,p,n:0,slots:new Map()};proj.set(k,o);let sl=o.slots.get(v)||{v,b:0,refs:[]};o.slots.set(v,sl);sl.b++;sl.refs.push(e);o.n++;e.o=o;e.sl=sl;
   for(let j=t;j<v;j++)inc(C,j);events++;W+=w;C=J;t=v;
  }inc(C,t);tag.end=C;if(C-C0>=T)hit++;tags.push(tag);
 }
 const grids=Pset.map((P,j)=>({P,Ll:low[j],Lh:hi,source:0,compatible:0,unstable:0,defect:0,smallCompat:0,thinWord:0,heavyCompat:0,largeCompat:0,lowDef:0,highDef:0,maxLoad:0,highSingleton:0,wordCount:0}));
 for(let tag of tags)for(let j=0;j<Pset.length;j++){let P=Pset[j],z=grids[j],l=0,h=0,sl=0,sh=0;
  for(let e of tag.es){let n=tick.get(key(e.C,e.t)),isMass=n>cut;
   if(e.p<=P/2&&isMass){if(e.p<Y){l+=e.w;if(n<=boost)sl+=e.w;}else{h+=e.w;if(n<=boost)sh+=e.w;}}
   let k=Math.ceil(e.J/P)-Math.ceil(e.C/P);if(!k)continue;
   if(e.p>=2*P){l=isMass&&e.p<Y?e.w:0;h=isMass&&e.p>=Y?e.w:0;sl=n<=boost?l:0;sh=n<=boost?h:0;}else if(e.p>P/2){l=h=sl=sh=0}
   ok(l+h<=6*P*k&&sl<=l&&sh<=h,"cell cap");if(low[j]&&tag.end-e.J>=L){e.Wl[j]=l;e.Sl[j]=sl;}if(tag.end-e.J>=L){e.Wh[j]=h;e.Sh[j]=sh;}sourceCells++;l=h=sl=sh=0;
  }
 }
 function word(s,len,o){let e=s.ready[0],es=e.tag.es,i=e.i+1,rad=6,arr=[];rad=rad/gcd(rad,2*o.p)*2*o.p;while(es[i-1].J-e.J<len){let x=es[i++];ok(x,"room");arr.push(x.p+":"+x.w);if(rad<=4*H){rad=rad/gcd(rad,2*x.p)*2*x.p;if(rad>4*H)rad=4*H+1;}}
  ok(rad>len,"radical");radChecks++;return {sig:arr.join(","),rad};
 }
 for(let o of proj.values()){
  let cls=new Map();for(let s of o.slots.values()){s.ready=s.refs.filter(e=>e.tag.end-e.J>=L);let c=mod(s.v,6),a=cls.get(c)||[];a.push(s);cls.set(c,a)}
  for(let a of cls.values()){classes++;let n=a.reduce((v,s)=>v+s.b,0),stable=a.reduce((v,s)=>v+s.ready.length,0);
   for(let j=0;j<Pset.length;j++){let P=Pset[j],z=grids[j],ncross=Math.ceil((o.C+o.p-1)/P)-Math.ceil(o.C/P);if(!ncross)continue;
    for(let sector of ["l","h"]){let len=sector==="l"?low[j]:hi;if(!len)continue;let wf=sector==="l"?"Wl":"Wh",sf=sector==="l"?"Sl":"Sh",df=sector==="l"?"dl":"dh",groups=new Map(),ready=a.filter(s=>s.ready.length);
     for(let s of ready){s.word=word(s,len,o);let g=groups.get(s.word.sig)||{slots:[],mass:0,rad:s.word.rad,smallMass:0};ok(g.rad===s.word.rad,"same signature radical");g.slots.push(s);g.mass+=s.ready.length;g.smallMass+=s.ready.filter(e=>e[sf][j]>0).length;groups.set(s.word.sig,g);}
     for(let g of groups.values()){wordGroups++;z.wordCount++;wordSlots+=g.slots.length;let base=g.slots[0].v;for(let s of g.slots){ok(g.rad>4*H?s.v===base:(s.v-base)%g.rad===0,"word lag divisor");}ok(g.slots.length<=1+Math.floor(8*H/g.rad),"slot bound");if(g.rad>4*H){ok(g.slots.length===1,"singleton");radSingleton++;if(sector==="h")z.highSingleton++;}
      if(g.mass>eta*n)ok(g.mass/g.slots.length<=Math.max(...g.slots.map(s=>s.ready.length))+1e-7,"large word slot");
      let maxSmall=Math.max(0,...g.slots.map(s=>s.ready.filter(e=>e[sf][j]>0).length));ok(g.smallMass<=g.slots.length*maxSmall,"small mass packing");wordBoundChecks++;
     }
     for(let s of ready){let total=s.ready.reduce((v,e)=>v+e[wf][j],0),small=s.ready.reduce((v,e)=>v+e[sf][j],0);if(!total)continue;let g=groups.get(s.word.sig),comp=total*g.mass/n,un=total*(n-stable)/n;
      z.source+=total;z.compatible+=comp;z.unstable+=un;z.smallCompat+=small*g.mass/n;
      if(g.mass<=eta*n)z.thinWord+=comp;else{z.heavyCompat+=comp;z.largeCompat+=(total-small)*g.mass/n;}
      let routed=0;
      for(let t of ready){pairs++;let ea=s.ready[0],eb=t.ready[0],aa=ea.tag.es,bb=eb.tag.es,i=ea.i+1,k=eb.i+1,lag=eb.v-ea.v,dest=null,side=-1;
       while(aa[i-1].J-ea.J<len){let x=aa[i],y=bb[k];ok(x&&y&&x.C===y.C&&y.t-x.t===lag,"shared prefix");if(x.p!==y.p||y.v-x.v!==lag){side=lag%(2*x.p)!==0?0:1;dest=side===0?x:y;ok(lag!==0&&lag%6===0&&lag%(2*dest.p)!==0&&x.C-ea.J<len,"defect");break;}i++;k++;}
       ok(!dest===(s.word.sig===t.word.sig),"exact signature equivalence");
       if(!dest){samePairs++;continue;}defPairs++;let charge=total*t.ready.length/(6*n);routed+=charge;let refs=side===0?s.ready:t.ready,off=side===0?i-ea.i:k-eb.i;
       for(let e of refs){let x=e.tag.es[e.i+off];ok(x.C===dest.C&&x.v===dest.v&&x.p===dest.p,"actual destination");let val=side===0?e[wf][j]*t.ready.length/(6*n):total/(6*n);x[df][j]+=val;routeChecks++;}
      }
      ok(eq(total,comp+un+6*routed),"source exact partition");z.defect+=routed;if(sector==="l")z.lowDef+=routed;else z.highDef+=routed;
     }
    }
   }
  }
 }
 for(let j=0;j<Pset.length;j++){let z=grids[j],P=z.P,dl=0,dh=0;
  for(let tag of tags)for(let e of tag.es){let l=e.dl[j],h=e.dh[j];if(l+h)capChecks++;ok(l<=2*(low[j]+B+P)+1e-7&&h<=2*(hi+B+P)+1e-7,"capacity");dl+=l;dh+=h;z.maxLoad=Math.max(z.maxLoad,l+h)}
  ok(eq(dl,z.lowDef)&&eq(dh,z.highDef)&&eq(z.source,z.compatible+z.unstable+6*z.defect)&&eq(z.compatible,z.thinWord+z.heavyCompat),"global conservation");for(let k of Object.keys(z))if(typeof z[k]==="number")z[k]=+z[k].toFixed(6);
 }
 return {X,focus,B,T,L,hi,low,Y,cut,boost,N,events,hit,W,sourceCells,classes,wordGroups,wordSlots,radChecks,radSingleton,pairs,samePairs,defPairs,routeChecks,capChecks,wordBoundChecks,grids};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
