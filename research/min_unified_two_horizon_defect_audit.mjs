// Two-horizon fractional first-defect transport audit.
function audit(X,focus=false,sharp=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,L=Math.max(8,Math.floor(B/8)),Y=Math.max(5,Math.ceil(Math.sqrt(B))),Lh=Math.max(2,Math.floor(L/4)),Ps=[6,30,210],Ls=[2,Math.max(2,Math.floor(L/2)),0],lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(x,m)=>{if(!x)throw Error(`${X}/${focus} ${m}`)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)S[n]=S[n]||p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const tags=[],proj=new Map();let N=0,events=0,W=0,hit=0,cellChecks=0,pairs=0,persistent=0,defects=0,routeChecks=0,capChecks=0,comparisonChecks=0,shortDefects=0,lateDefects=0;
 const mk=()=>[0,0,0];
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[],tag={es,end:0};
  while(C-C0<T){let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>cut)break;let J=C+p-1,g=p-1,w=v-t;ok(w<=2*r&&w<=3*g,"wait");let e={C,J,p,g,w,t,v,i:es.length,tag,lo:mk(),hi:mk(),old:mk(),dl:mk(),dh:mk()};es.push(e);let k=C+"|"+p,o=proj.get(k)||{C,p,n:0,slots:new Map()};proj.set(k,o);let sl=o.slots.get(v)||{v,b:0,refs:[]};o.slots.set(v,sl);sl.b++;sl.refs.push(e);o.n++;W+=w;events++;C=J;t=v;
  }tag.end=C;if(C-C0>=T)hit++;tags.push(tag);
  for(let j=0;j<Ps.length;j++){let P=Ps[j],lo=0,hi=0;for(let e of es){if(!sharp||e.p<=P/2){if(e.p<Y)lo+=e.w;else hi+=e.w;}let n=Math.ceil(e.J/P)-Math.ceil(e.C/P);if(!n)continue;if(sharp){if(e.p>=2*P){lo=e.p<Y?e.w:0;hi=e.p>=Y?e.w:0;}else if(e.p>P/2){lo=0;hi=0;}}let cap=(sharp?6:9)*P*n;ok(lo+hi<=cap,"cell capacity");e.lo[j]=Ls[j]?lo/cap:0;e.hi[j]=hi/cap;ok(e.lo[j]+e.hi[j]<=1+1e-9,"fraction sum");lo=hi=0;cellChecks++}}
 }
 let grids=Ps.map((P,j)=>({P,Ll:Ls[j],Lh,old:0,low:0,high:0,lowEligible:0,highEligible:0,lowLate:0,highLate:0,rawPairs:0,oldKeys:0,newKeys:0,lowKeys:0,highKeys:0,maxLow:0,maxHigh:0}));
 for(let o of proj.values()){let cls=new Map();for(let s of o.slots.values()){s.ready=s.refs.filter(e=>e.tag.end-e.J>=L);let c=mod(s.v,6),a=cls.get(c)||[];a.push(s);cls.set(c,a)}
  for(let a of cls.values()){let n=a.reduce((v,s)=>v+s.b,0),cum=0;a.sort((x,y)=>x.b-y.b||x.v-y.v);
   for(let s of a){cum+=s.b;if(cum<=n/2||!s.ready.length)continue;
    for(let h of a){if(h.b>s.b||Math.abs(h.v-s.v)<=o.p||!h.ready.length)continue;
     pairs++;let ea=s.ready[0],eb=h.ready[0],aa=ea.tag.es,bb=eb.tag.es,i=ea.i+1,j=eb.i+1,lag=eb.v-ea.v,dest=null,side=-1,d=0;
     while(aa[i-1].J-ea.J<L){let x=aa[i],y=bb[j];ok(x&&y&&x.C===y.C&&y.t-x.t===lag,"translated");if(x.p!==y.p||y.v-x.v!==lag){side=lag%(2*x.p)!==0?0:1;dest=side===0?x:y;d=x.C-ea.J;ok(d>=0&&d<L&&lag%(2*dest.p)!==0,"first defect");break}i++;j++}
     if(dest)defects++;else persistent++;
     for(let k=0;k<Ps.length;k++){let z=grids[k],P=z.P,nn=Math.ceil((o.C+o.p-1)/P)-Math.ceil(o.C/P);if(!nn)continue;z.rawPairs++;let sumL=s.ready.reduce((a,e)=>a+e.lo[k],0),sumH=s.ready.reduce((a,e)=>a+e.hi[k],0),mul=P*nn/n,old=mul*s.ready.length*h.ready.length,lo=mul*sumL*h.ready.length,hi=mul*sumH*h.ready.length;
      z.lowEligible+=lo;z.highEligible+=hi;if(!dest||d>=Ls[k]){z.lowLate+=lo;lo=0}if(!dest||d>=Lh){z.highLate+=hi;hi=0}if(!dest)continue;
      z.old+=old;z.low+=lo;z.high+=hi;ok(lo+hi<=old+1e-7,"pair domination");if(lo+hi>0)shortDefects++;else lateDefects++;
      let refs=side===0?s.ready:h.ready,off=side===0?i-ea.i:j-eb.i;
      for(let e of refs){let x=e.tag.es[e.i+off];ok(x.C===dest.C&&x.p===dest.p&&x.v===dest.v,"destination");let base=old/refs.length,vl=side===0?(Ls[k]&&d<Ls[k]?mul*h.ready.length*e.lo[k]:0):lo/refs.length,vh=side===0?(d<Lh?mul*h.ready.length*e.hi[k]:0):hi/refs.length;x.old[k]+=base;x.dl[k]+=vl;x.dh[k]+=vh;ok(vl+vh<=base+1e-7,"tag pair domination");routeChecks++}
     }
    }
   }
  }
 }
 for(let k=0;k<Ps.length;k++){let z=grids[k],P=z.P,old=new Map(),lo=new Map(),hi=new Map();let sl=0,sh=0,so=0;
  function add(m,key,v){if(v)m.set(key,(m.get(key)||0)+v)}
  for(let tag of tags)for(let e of tag.es){let l=e.dl[k],h=e.dh[k],o=e.old[k];ok(l+h<=o+1e-7,"tag domination");ok(l<=2*(Ls[k]+B+P)+1e-7&&h<=2*(Lh+B+P)+1e-7,"short capacities");if(l||h||o)capChecks++;z.maxLow=Math.max(z.maxLow,l);z.maxHigh=Math.max(z.maxHigh,h);let key=e.C+"|"+e.p;add(old,key,o);add(lo,key,l);add(hi,key,h);sl+=l;sh+=h;so+=o}
  for(let [key,v] of old){ok((lo.get(key)||0)+(hi.get(key)||0)<=v+1e-7,"projected domination");comparisonChecks++}
  ok(eq(sl,z.low)&&eq(sh,z.high)&&eq(so,z.old)&&eq(z.low+z.lowLate,z.lowEligible)&&eq(z.high+z.highLate,z.highEligible),"conservation");
  z.oldKeys=old.size;z.lowKeys=lo.size;z.highKeys=hi.size;z.newKeys=new Set([...lo.keys(),...hi.keys()]).size;
  for(let p of Object.keys(z))if(typeof z[p]==="number")z[p]=+z[p].toFixed(6)
 }
 return {X,focus,sharp,B,T,L,Lh,Ls,Y,N,hit,events,W,cellChecks,pairs,persistent,defects,shortDefects,lateDefects,routeChecks,capChecks,comparisonChecks,grids};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));

for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,false,true)));
