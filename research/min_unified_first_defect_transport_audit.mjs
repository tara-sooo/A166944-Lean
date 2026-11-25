// Phase-conditioned first-defect transport and radical persistence envelope.
function audit(X,focus=false,short=false){
const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,L=short?2:Math.max(8,Math.floor(B/8)),L0=6,theta=.5,Ps=[6,30,210],lim=7*X+B+20,S=new Int32Array(lim);
const ok=(x,s)=>{if(!x)throw Error(`${X}/${focus} ${s}`)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)S[n]=S[n]||p}
function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
function gcd(a,b){while(b){let t=a%b;a=b;b=t}return a}
function lcm(a,b){if(a>4*H)return a;let v=a/gcd(a,b)*b;return v>4*H?4*H+1:v}
let proj=new Map(),tags=[],N=0,hit=0,G=0,W=0,events=0,slots=0,readySlots=0,radChecks=0,zeroRad=0;
for(let M=X;M<2*X;M++)if(S[M]===M){
 N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[],tag={es,end:0};
 while(C-C0<T){let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
 if(!p||v>cut)break;let g=p-1,J=C+g,w=v-t;ok(w<=2*r&&w<=3*g,"wait");
 let e={C,J,p,g,r,t,v,w,i:es.length,tag,loads:[0,0,0]};es.push(e);
 let k=C+"|"+p,o=proj.get(k)||{C,p,n:0,slots:new Map()};proj.set(k,o);let a=o.slots.get(v)||{v,b:0,all:[]};o.slots.set(v,a);a.b++;a.all.push(e);o.n++;
 G+=g;W+=w;events++;C=J;t=v;
 }tag.end=C;if(C-C0>=T)hit++;tags.push(tag);
}
let gs=Ps.map(P=>({P,source:0,persistent:0,defect:0,upper:0,atoms:0,pairs:0,trans:0,split:0,same:0,routeChecks:0,radChecks:0,zero:0,maxLoad:0,thin:0,heavy:0,paid:0,keys:0,map:new Map()}));
for(let o of proj.values()){
 let classes=new Map();
 for(let s of o.slots.values()){
  slots++;s.ready=s.all.filter(e=>e.tag.end-e.J>=L);
  if(s.ready.length){readySlots++;let a=s.ready[0],es=a.tag.es,d=lcm(L0,2*a.p),i=a.i+1;
   while(es[i-1].J-a.J<L){ok(i<es.length,"ready prefix");d=lcm(d,2*es[i].p);i++}
   s.d=d;s.end=i;radChecks++;ok(d>L,"radical barrier");if(d>4*H)zeroRad++;
  }
  let c=mod(s.v,L0),arr=classes.get(c)||[];arr.push(s);classes.set(c,arr);
 }
 for(let a of classes.values()){
 let n=a.reduce((v,s)=>v+s.b,0),cum=0;
 a.sort((x,y)=>x.b-y.b||x.v-y.v);
 for(let s of a){cum+=s.b;if(cum<=theta*n||!s.ready.length)continue;
  let m=s.ready.length,upper=Math.min(1,2*Math.floor(4*H/s.d)*s.b/n);
  let pers=0;
  for(let z of gs){let P=z.P,k=Math.ceil((o.C+o.p-1)/P)-Math.ceil(o.C/P);if(k){ok(P%o.p!==0,"barrier");z.upper+=P*k*m*upper;z.atoms+=k*m;}}
  for(let h of a){
   if(h.b>s.b||Math.abs(h.v-s.v)<=o.p||!h.ready.length)continue;
   let lag=h.v-s.v;ok(lag%L0===0&&lag%(2*o.p)===0&&Math.abs(lag)<=4*H,"lag");
   let ea=s.ready[0],eb=h.ready[0],aa=ea.tag.es,bb=eb.tag.es,i=ea.i+1,j=eb.i+1,dest=null,side=-1,same=false,steps=0;
   while(aa[i-1].J-ea.J<L){
    ok(i<aa.length&&j<bb.length,"ready pair");let x=aa[i],y=bb[j];
    ok(x.C===y.C&&y.t-x.t===lag,"translated inputs");
    if(x.p!==y.p||y.v-x.v!==lag){
      same=x.p===y.p;side=lag%(2*x.p)!==0?0:1;dest=side===0?x:y;
      ok(lag%(2*dest.p)!==0&&dest.p>3,"nonperiodic defect");break;
    }
    ok(lag%(2*x.p)===0,"translated label");i++;j++;steps++;
   }
   if(!dest){ok(s.d<=4*H&&lag%s.d===0,"persistent radical");pers+=h.ready.length;}
   for(let z of gs){let P=z.P,k=Math.ceil((o.C+o.p-1)/P)-Math.ceil(o.C/P);if(!k)continue;
    let f=P*k*m*h.ready.length/n;z.source+=f;z.pairs++;z.trans+=steps;
    if(!dest){z.persistent+=f;z.radChecks++;continue}
    z.defect+=f;if(same)z.same++;else z.split++;
    let refs=side===0?s.ready:h.ready,ix=side===0?i-ea.i:j-eb.i;
    for(let e of refs){let t=e.tag.es[e.i+ix];ok(t.C===dest.C&&t.p===dest.p&&t.v===dest.v,"common routed event");let w=f/refs.length;t.loads[gs.indexOf(z)]+=w;z.routeChecks++;}
   }
  }
  ok(pers/n<=upper+1e-7,"persistent bound per focal slot");
 }
 }
}
for(let tag of tags)for(let e of tag.es)for(let i=0;i<gs.length;i++){
 let z=gs[i],v=e.loads[i];if(!v)continue;
 let cap=2*(L+B+z.P);ok(v<=cap+1e-7,"linear per-tag defect capacity");z.maxLoad=Math.max(z.maxLoad,v);let key=e.C+"|"+e.p;z.map.set(key,(z.map.get(key)||0)+v);
}
for(let z of gs){
 let sum=0;for(let v of z.map.values()){sum+=v;if(v<=2*(L+B+z.P)*(focus?.02:.2)){z.paid+=v;z.thin++}else z.heavy++;}
 ok(eq(sum,z.defect)&&eq(z.source,z.persistent+z.defect)&&z.persistent<=z.upper+1e-7,"global transport");z.keys=z.map.size;delete z.map;
 for(let k of ["source","persistent","defect","upper","maxLoad","paid"])z[k]=+z[k].toFixed(6)
}
return {X,focus,short,B,T,H,L,L0,N,hit,G,W,events,slots,readySlots,radChecks,zeroRad,grids:gs};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));

console.log(JSON.stringify(audit(65536,false,true)));
