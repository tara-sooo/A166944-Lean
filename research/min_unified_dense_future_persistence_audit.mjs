// Dense future high-clock witness and persistence obstruction diagnostics.
function audit(X,focus=false,short=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(16*B,Math.floor(X/2)),H=T+B,L=short?8:Math.max(32,Math.floor(B*2)),block=Math.max(2,Math.floor(L/2)),Y=Math.max(5,Math.ceil(B**.25)),eta=.08,cheap=.25,L0=6,Ps=[6,30,210],lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(x,s)=>{if(!x)throw Error(`${X}/${focus}/${short} ${s}`)},mod=(a,b)=>(a%b+b)%b,eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b));
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)S[n]=S[n]||p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const tags=[],proj=new Map();let N=0,events=0,G=0,W=0,hit=0,cheapPaid=0,tailPaid=0,blocks=0,rich=0,richW=0,richChecks=0,blockChecks=0,rootBudget=0,readySlots=0,rankChecks=0,pairChecks=0,persistentPairs=0,defectPairs=0,richPersistent=0,richDefect=0,lowChecks=0,lagBoundChecks=0,richSlotChecks=0,productChecks=0,zeroProduct=0,localSupportChecks=0;
 const add=(m,k,v)=>m.set(k,(m.get(k)||0)+v);
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[],tag={es,end:0};
  while(C-C0<T){let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>cut)break;let g=p-1,J=C+g,w=v-t,high=p>=Y&&w>=cheap*g;ok(w<=2*r&&w<=3*g&&(!high||r>=cheap*g/2),"event");let e={C,J,p,g,r,w,t,v,high,i:es.length,tag};es.push(e);
   let k=C+"|"+p,o=proj.get(k)||{C,p,n:0,slots:new Map()};proj.set(k,o);let sl=o.slots.get(v)||{v,b:0,refs:[]};o.slots.set(v,sl);sl.b++;sl.refs.push(e);o.n++;e.o=o;e.sl=sl;
   if(p>=Y&&!high)cheapPaid+=w;G+=g;W+=w;events++;C=J;t=v;
  }
  tag.end=C;if(C-C0>=T)hit++;tags.push(tag);
  let b=-1,acc=0,pay=0,nb=0;
  for(let i=es.length-1;i>=0;i--){let e=es[i],k=Math.floor(e.C/block);if(k!==b){if(b>=0){ok(pay<=eta*L+3*B+1e-7,"tail block");blockChecks++;}b=k;acc=0;pay=0;nb++;blocks++;}
   e.future=acc;e.rich=e.high&&acc>=eta*L;
   if(e.high){if(e.rich){rich++;richW+=e.w;}else{tailPaid+=e.w;pay+=e.w;}acc+=e.w;}
  }
  if(b>=0){ok(pay<=eta*L+3*B+1e-7,"final tail");blockChecks++;}
  rootBudget+=nb*(eta*L+3*B);
  ok(nb<=Math.floor((C-C0)/block)+2,"block count");
 }
 ok(tailPaid<=rootBudget+1e-7,"total block budget");
 // Relaxed spatial support census for actual finite roughness threshold.
 const support=new Map();
 for(let C=2*X-2;C<7*X;C+=2){let f=[...fac(C-1),...fac(C+1)],r=Math.min(...f);for(let p of f)if(p>=Y&&r>=cheap*(p-1)/2){let a=support.get(p)||[];a.push(C);support.set(p,a)}}
 function lb(a,x){let l=0,r=a.length;while(l<r){let m=(l+r)>>1;if(a[m]<x)l=m+1;else r=m}return l}
 const Kmax=Math.floor(Math.log(4*H)/Math.log(Y)),gstats=Ps.map(P=>({P,readyWitness:0,richWitness:0,richTransfer:0,lossChecks:0,positiveFuture:0,low:0,source:0,pers:0,def:0,richSource:0,richPers:0}));
 for(let o of proj.values())for(let s of o.slots.values()){
  s.ready=s.refs.filter(e=>e.tag.end-e.J>=L);
  if(!s.ready.length)continue;readySlots++;let e=s.ready[0],a=e.tag.es,i=e.i+1,by=new Map(),total=0;
  while(a[i-1].J-e.J<L){ok(i<a.length,"future room");let x=a[i++];if(x.high){add(by,x.p,x.w);total+=x.w;}}
  s.high=total;s.labels=[...by.keys()];s.k=s.labels.length;s.prefixEnd=i;let prod=1;
  for(let p of s.labels){prod*=p;if(prod>4*H){prod=4*H+1;break}}s.product=prod;productChecks++;if(prod>4*H)zeroProduct++;
  for(let [p,w] of by){let ar=support.get(p)||[],n=lb(ar,e.J+L+B+1)-lb(ar,e.J);ok(w<=2*p*n,"local relaxed high support");localSupportChecks++}
 }
 for(let tag of tags){let a=tag.es;
  for(let z of gstats){let P=z.P,k=-1;for(let i=a.length-1;i>=0;i--){let e=a[i],n=Math.ceil(e.J/P)-Math.ceil(e.C/P);if(n)k=i;if(k<0)continue;let q=a[k];if(!q.sl.ready?.length||tag.end-q.J<L)continue;z.readyWitness++;
   if(e.p<Y&&q.p<=P){z.low++;lowChecks++}
   if(!e.rich)continue;z.richWitness++;
   let high=0,lost=0;for(let j=i+1;j<a.length&&Math.floor(a[j].C/block)===Math.floor(e.C/block);j++)if(a[j].high){if(j<=k)lost+=a[j].w;else high+=a[j].w}
   ok(eq(high+lost,e.future)&&lost<=3*(Math.max(0,q.J-e.J))+1e-7,"future loss");z.lossChecks++;richChecks++;
   ok(q.C-e.C<=P&&q.J-e.C<=P+B,"right geometry");
   ok(q.sl.high>=high-1e-7,"future rich transfer");z.richTransfer++;if(high>0)z.positiveFuture++;
  }}
 }
 for(let o of proj.values()){
  const classes=new Map();for(let s of o.slots.values()){let c=mod(s.v,L0),a=classes.get(c)||[];a.push(s);classes.set(c,a)}
  for(let a of classes.values()){let n=a.reduce((v,s)=>v+s.b,0),cum=0;a.sort((x,y)=>x.b-y.b||x.v-y.v);
   for(let s of a){cum+=s.b;rankChecks++;if(cum<=.5*n||!s.ready?.length)continue;let ea=s.ready[0],aa=ea.tag.es;
    for(let h of a){if(h.b>s.b||Math.abs(h.v-s.v)<=o.p||!h.ready?.length)continue;
     let eb=h.ready[0],bb=eb.tag.es,lag=h.v-s.v,i=ea.i+1,j=eb.i+1,persist=true;pairChecks++;ok(Math.abs(lag)<=4*H&&lag%L0===0&&lag%(2*o.p)===0,"lag");
     while(aa[i-1].J-ea.J<L){let x=aa[i],y=bb[j];ok(x&&y&&x.C===y.C&&y.t-x.t===lag,"translated");if(x.p!==y.p||y.v-x.v!==lag){persist=false;break}i++;j++;}
     if(persist){persistentPairs++;ok(s.k<=Kmax&&s.product<=4*H,"high distinct prime limit");for(let p of s.labels)ok(lag%(2*p)===0,"persistent high divisibility");lagBoundChecks++;if(s.high>=eta*L)richPersistent++;}
     else{defectPairs++;if(s.high>=eta*L)richDefect++;}
     if(s.high>=eta*L)richSlotChecks++;
     for(let z of gstats){let P=z.P,k=Math.ceil((o.C+o.p-1)/P)-Math.ceil(o.C/P);if(!k)continue;let w=P*k*s.ready.length*h.ready.length/n;z.source+=w;if(persist)z.pers+=w;else z.def+=w;if(s.high>=eta*L){z.richSource+=w;if(persist)z.richPers+=w}}
    }
   }
  }
 }
 for(let z of gstats){ok(eq(z.source,z.pers+z.def),"energy split");for(let k of ["source","pers","def","richSource","richPers"])z[k]=+z[k].toFixed(6)}
 return {X,focus,short,B,T,H,L,Y,Kmax,N,hit,G,W,events,cheapPaid,tailPaid,blocks,blockChecks,rootBudget:+rootBudget.toFixed(3),rich,richW,richChecks,readySlots,rankChecks,pairChecks,persistentPairs,defectPairs,richPersistent,richDefect,lowChecks,lagBoundChecks,richSlotChecks,productChecks,zeroProduct,localSupportChecks,grids:gstats};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));console.log(JSON.stringify(audit(65536,false,true)));
