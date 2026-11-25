// Nested rank and short-pursuit fractional defect transport audit.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,L=Math.max(8,Math.floor(B/8)),Y=Math.max(5,Math.ceil(Math.sqrt(B))),Ps=[6,30,210],Lo=[Math.max(2,Math.floor(L/2)),L,0],Ln=[2,Math.max(2,Math.floor(L/4)),0],Ho=Math.max(2,Math.floor(L/2)),Hn=Math.max(1,Math.floor(L/4)),theta=.25,tau=.6,lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(x,m)=>{if(!x)throw Error(`${X}/${focus} ${m}`)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)S[n]=S[n]||p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const tags=[],proj=new Map();let N=0,events=0,W=0,hit=0,cells=0,rankChecks=0,rankClassChecks=0,pairs=0,defects=0,persistent=0,routeChecks=0,tagChecks=0,keyChecks=0,rankFarChecks=0,positiveRankBounds=0;
 const mk=()=>[0,0,0];
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C=2*M-2,C0=C,t=M+2,cut=Math.floor((7*M-1)/4),es=[],tag={es,end:0};
  while(C-C0<T){let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>cut)break;let J=C+p-1,g=p-1,w=v-t;ok(w<=2*r&&w<=3*g,"wait");let e={C,J,p,g,w,t,v,i:es.length,tag,lo:mk(),hi:mk(),newlo:mk(),newhi:mk(),ol:mk(),oh:mk(),nl:mk(),nh:mk()};es.push(e);let k=C+"|"+p,o=proj.get(k)||{C,p,n:0,slots:new Map()};proj.set(k,o);let sl=o.slots.get(v)||{v,b:0,refs:[]};o.slots.set(v,sl);sl.b++;sl.refs.push(e);o.n++;e.o=o;e.sl=sl;W+=w;events++;C=J;t=v;
  }tag.end=C;if(C-C0>=T)hit++;tags.push(tag);
 }
 for(let o of proj.values()){let cl=new Map();for(let s of o.slots.values()){let c=mod(s.v,6),a=cl.get(c)||[];a.push(s);cl.set(c,a);s.ready=s.refs.filter(e=>e.tag.end-e.J>=L)}o.classes=[...cl.values()];
  for(let a of o.classes){a.sort((x,y)=>x.b-y.b||x.v-y.v);let n=a.reduce((v,s)=>v+s.b,0),cum=0,paidOld=0,paidNew=0;for(let s of a){cum+=s.b;s.old=cum>theta*n;s.new=cum>tau*n;if(!s.old)paidOld+=s.b;if(!s.new)paidNew+=s.b;ok(!s.new||s.old,"nested rank");let r=a.filter(t=>t.b<=s.b).reduce((v,t)=>v+t.b,0);ok(!s.new||r>tau*n,"rank lower");rankChecks++;if(s.new){let far=a.filter(t=>t.b<=s.b&&Math.abs(t.v-s.v)>o.p).reduce((v,t)=>v+t.ready.length,0),bad=a.reduce((v,t)=>v+t.b-t.ready.length,0),near=Math.floor(o.p/(3*o.p))+1;ok(far>=r-near*s.b-bad-1e-7,"rank far subtraction");rankFarChecks++;if(tau*n-near*s.b-bad>0)positiveRankBounds++;}}ok(paidOld<=theta*n&&paidNew<=tau*n&&paidOld<=paidNew,"rank prefix budget");rankClassChecks++}
 }
 let grids=Ps.map((P,j)=>({P,Lo:Lo[j],Ln:Ln[j],Ho,Hn,old:0,new:0,oldLow:0,oldHigh:0,newLow:0,newHigh:0,rankRaw:0,rankPaid:0,rankClockPaid:0,rawCellClock:0,pairGrid:0,oldKeys:0,newKeys:0,maxNewLow:0,maxNewHigh:0}));
 for(let tag of tags)for(let j=0;j<Ps.length;j++){let z=grids[j],P=z.P,lo=0,hi=0;for(let e of tag.es){if(e.p<=P/2){if(e.p<Y)lo+=e.w;else hi+=e.w;}let n=Math.ceil(e.J/P)-Math.ceil(e.C/P);if(!n)continue;
  if(e.p>=2*P){lo=e.p<Y?e.w:0;hi=e.p>=Y?e.w:0;}else if(e.p>P/2){lo=0;hi=0;}let cap=6*P*n;ok(lo+hi<=cap,"sharp finite capacity");z.rawCellClock+=lo+hi;z.rankRaw+=P*n;if(!e.sl.new){z.rankPaid+=P*n;z.rankClockPaid+=lo+hi;}e.lo[j]=e.sl.old&&Lo[j]?lo/cap:0;e.hi[j]=e.sl.old?hi/cap:0;e.newlo[j]=e.sl.new&&Ln[j]?lo/cap:0;e.newhi[j]=e.sl.new?hi/cap:0;ok(e.newlo[j]<=e.lo[j]+1e-9&&e.newhi[j]<=e.hi[j]+1e-9&&e.lo[j]+e.hi[j]<=1+1e-9,"fraction nesting");cells++;lo=hi=0;
 }}
 for(let o of proj.values())for(let a of o.classes){let n=a.reduce((v,s)=>v+s.b,0);
  for(let s of a){if(!s.old||!s.ready.length)continue;for(let h of a){if(h.b>s.b||Math.abs(h.v-s.v)<=o.p||!h.ready.length)continue;
   pairs++;let ea=s.ready[0],eb=h.ready[0],aa=ea.tag.es,bb=eb.tag.es,i=ea.i+1,j=eb.i+1,lag=eb.v-ea.v,dest=null,side=-1,d=0;
   while(aa[i-1].J-ea.J<L){let x=aa[i],y=bb[j];ok(x&&y&&x.C===y.C&&y.t-x.t===lag,"translated");if(x.p!==y.p||y.v-x.v!==lag){side=lag%(2*x.p)!==0?0:1;dest=side===0?x:y;d=x.C-ea.J;ok(d>=0&&d<L&&lag%(2*dest.p)!==0,"defect");break}i++;j++}
   if(!dest){persistent++;continue}defects++;
   for(let k=0;k<Ps.length;k++){let z=grids[k],P=z.P,nn=Math.ceil((o.C+o.p-1)/P)-Math.ceil(o.C/P);if(!nn)continue;z.pairGrid++;
    const mul=P*nn/n,oldl=Lo[k]&&d<Lo[k],oldh=d<Ho,newl=Ln[k]&&d<Ln[k],newh=d<Hn,tot=(arr,flag,field)=>flag?arr.reduce((v,e)=>v+e[field][k],0):0;
    let a0=tot(s.ready,oldl,"lo"),b0=tot(s.ready,oldh,"hi"),a1=tot(s.ready,newl,"newlo"),b1=tot(s.ready,newh,"newhi");
    ok(a1<=a0+1e-7&&b1<=b0+1e-7,"pair domination");z.oldLow+=mul*a0*h.ready.length;z.oldHigh+=mul*b0*h.ready.length;z.newLow+=mul*a1*h.ready.length;z.newHigh+=mul*b1*h.ready.length;
    let refs=side===0?s.ready:h.ready,off=side===0?i-ea.i:j-eb.i;
    for(let e of refs){let x=e.tag.es[e.i+off];ok(x.C===dest.C&&x.p===dest.p&&x.v===dest.v,"actual destination");let ol=side===0?mul*h.ready.length*(oldl?e.lo[k]:0):mul*a0,oh=side===0?mul*h.ready.length*(oldh?e.hi[k]:0):mul*b0,nl=side===0?mul*h.ready.length*(newl?e.newlo[k]:0):mul*a1,nh=side===0?mul*h.ready.length*(newh?e.newhi[k]:0):mul*b1;ok(nl<=ol+1e-7&&nh<=oh+1e-7,"tag pair domination");x.ol[k]+=ol;x.oh[k]+=oh;x.nl[k]+=nl;x.nh[k]+=nh;routeChecks++}
   }
  }}
 }
 for(let k=0;k<Ps.length;k++){let z=grids[k],P=z.P,old=new Map(),nw=new Map(),ol=0,oh=0,nl=0,nh=0;function add(m,key,v){if(v)m.set(key,(m.get(key)||0)+v)}
  for(let tag of tags)for(let e of tag.es){let a=e.ol[k],b=e.oh[k],c=e.nl[k],d=e.nh[k];ok(c<=a+1e-7&&d<=b+1e-7,"tag nesting");ok(c<=2*(Ln[k]+B+P)+1e-7&&d<=2*(Hn+B+P)+1e-7,"short capacity");if(a+b+c+d)tagChecks++;z.maxNewLow=Math.max(z.maxNewLow,c);z.maxNewHigh=Math.max(z.maxNewHigh,d);let key=e.C+"|"+e.p;add(old,key,a+b);add(nw,key,c+d);ol+=a;oh+=b;nl+=c;nh+=d}
  for(let [key,v] of nw){ok(v<=(old.get(key)||0)+1e-7,"projected nesting");keyChecks++}
  ok(eq(ol,z.oldLow)&&eq(oh,z.oldHigh)&&eq(nl,z.newLow)&&eq(nh,z.newHigh),"conservation");ok(z.rankPaid<=tau*z.rankRaw+1e-7&&z.rankClockPaid<=6*z.rankPaid+1e-7,"rank clock budget");
  z.old=ol+oh;z.new=nl+nh;z.oldKeys=old.size;z.newKeys=nw.size;
  for(let p of Object.keys(z))if(typeof z[p]==="number")z[p]=+z[p].toFixed(6)
 }
 return {X,focus,B,T,L,Lo,Ln,Ho,Hn,Y,theta,tau,N,hit,events,W,cells,rankChecks,rankClassChecks,rankFarChecks,positiveRankBounds,pairs,defects,persistent,routeChecks,tagChecks,keyChecks,grids};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
