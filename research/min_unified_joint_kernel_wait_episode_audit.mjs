// Joint forward/backward clock kernel and long-wait episode envelope.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,Ps=[6,30,210],Lh=Math.max(2,Math.floor(B/32)),Ll=Math.max(Lh,Math.floor(B/8)),Y=Math.max(5,Math.ceil(Math.sqrt(B))),R=8,cut=3,c=9,lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(b,m)=>{if(!b)throw Error(`${X}/${focus} ${m}`)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)S[n]=S[n]||p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 let N=0,W=0,events=0,hit=0,paths=[],proj=new Map(),episodes=new Map(),birthCache=new Map();
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C=2*M-2,C0=C,t=M+2,stop=Math.floor((7*M-1)/4),es=[],tag={M,es,end:0};while(C-C0<T){
   let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>stop)break;let J=C+p-1,g=p-1,w=v-t;ok(w<=2*r&&w<=3*g,"wait");let k=C+"|"+p,o=proj.get(k)||{C,p,slots:new Map()};proj.set(k,o);let sl=o.slots.get(v)||{v,refs:[],o};o.slots.set(v,sl);
   let e={C,J,p,w,t,v,r,tag,i:es.length,sl,lo:[0,0,0],hi:[0,0,0]};es.push(e);sl.refs.push(e);W+=w;events++;C=J;t=v;
  }tag.end=C;if(C-C0>=T)hit++;paths.push(tag);
  for(let j=0;j<Ps.length;j++){let P=Ps[j],l=0,h=0;for(let e of es){if(e.p<Y)l+=e.w;else h+=e.w;let k=Math.ceil(e.J/P)-Math.ceil(e.C/P);if(k){ok(l+h<=c*P*k,"cell");e.lo[j]=l;e.hi[j]=h;l=h=0}}}
 }
 function word(e,L){let a=e.tag.es,i=e.i+1,s=[];while(a[i-1].J-e.J<L){let x=a[i++];ok(x,"room");s.push(x.p+":"+x.w)}return s.join(",")}
 function birth(e,f){let a=e.tag,b=f.tag,k=Math.min(a.M,b.M)+"|"+Math.max(a.M,b.M);if(birthCache.has(k))return birthCache.get(k);let i=0,j=0;while(i<a.es.length&&j<b.es.length){let x=a.es[i],y=b.es[j];if(x.C<y.C){i++;continue}if(y.C<x.C){j++;continue}if(Math.max(x.t,y.t)<Math.min(x.v,y.v)){ok(x.v===y.v&&x.p===y.p,"shared exit");let z={x,y,J:x.C,h:Math.abs(x.t-y.t),later:x.t>y.t?x:y};birthCache.set(k,z);return z}i++;j++}throw Error("missing common birth")}
 const stats=Ps.map(P=>({P,source:0,back:0,forward:0,unstable:0,diag:0,recent:0,small:0,long:0,other:0,highPaid:0,columns:0,rows:0,kernelChecks:0,defectChecks:0,longPairs:0,episodes:0,envelope:0,oldPairEnvelope:0,targetActual:0,targetBack:0,targetForward:0,unionBound:0,intersectionBound:0,targetChecks:0,jointCap:0,separateCap:0}));
 for(let o of proj.values()){let cls=new Map();for(let sl of o.slots.values()){sl.ready=sl.refs.filter(e=>e.tag.end-e.J>=Ll);if(sl.ready.length){sl.wl=word(sl.ready[0],Ll);sl.wh=word(sl.ready[0],Lh)}let c0=mod(sl.v,6),a=cls.get(c0)||[];a.push(sl);cls.set(c0,a)}
  for(let a of cls.values()){let n=a.reduce((v,s)=>v+s.refs.length,0),stable=a.reduce((v,s)=>v+s.ready.length,0),long=new Map(),short=new Map();for(let s of a)if(s.ready.length){long.set(s.wl,(long.get(s.wl)||0)+s.ready.length);short.set(s.wh,(short.get(s.wh)||0)+s.ready.length)}
   for(let j=0;j<Ps.length;j++){let z=stats[j],P=Ps[j],k=Math.ceil((o.C+o.p-1)/P)-Math.ceil(o.C/P);if(!k)continue;let cap=c*P*k,cols=new Map(),bc=new Map(),dc=new Map(),rows=new Map(),live=[];
    const add=(m,key,v)=>m.set(key,(m.get(key)||0)+v);
    const Bmask=new Map(),Dmask=new Map(),Bcount=new Map(),Dword=new Map();let Dtotal=0;
    for(let s of a)for(let f of s.refs){let b=f.tag.es.slice(0,f.i).some(x=>x.C<=o.C-2&&x.C%10===0),d=f.tag.end-f.J>=Ll&&f.tag.es.slice(f.i+1).some(x=>x.C<f.J+Ll&&x.C%10===0);Bmask.set(f,b);Dmask.set(f,d);if(b)add(Bcount,s,1);if(d){Dtotal++;add(Dword,s.wl,1)}}
    for(let s of a)for(let e of s.ready){let l=e.lo[j],h=e.hi[j],mass=short.get(s.wh);if(h&&mass!==s.ready.length){z.highPaid+=h;h=0}let w=l+h;if(!w)continue;ok(w<=cap,"row clock");let A=long.get(s.wl);if(h)ok(A===s.ready.length,"positive high singleton nested");if(Bmask.get(e)||Dmask.get(e))z.unionBound+=w;
     z.intersectionBound+=w*((Bmask.get(e)?A/n*(Bcount.get(s)||0)/s.refs.length:0)+(Dmask.get(e)?(Dtotal-(Dword.get(s.wl)||0))/n:0));
     z.source+=w;z.unstable+=w*(n-stable)/n;rows.set(e,w);live.push(e);
     for(let t of a){if(!t.ready.length)continue;if(h){ok((s.wh===t.wh)===(s.wl===t.wl),"common forward kernel");z.kernelChecks++}
      if(s.wl===t.wl)continue;
      let q=w/n;for(let f of t.ready){add(cols,f,q);add(dc,f,q);z.forward+=q}
      // Long/short actual first defect comparison for each positive row sector.
      for(let [weight,L] of [[l,Ll],[h,Lh]])if(weight){let x=e.tag.es,y=t.ready[0].tag.es,i=e.i+1,b=t.ready[0].i+1,lag=t.v-s.v,found=false;while(x[i-1].J-e.J<L){let u=x[i],v=y[b];ok(u&&v&&u.C===v.C&&v.t-u.t===lag,"translated");if(u.p!==v.p||u.w!==v.w){ok(lag%(2*u.p)!==0||lag%(2*v.p)!==0,"nonperiodic");if(u.C%10===0){ok(Dmask.get(e)&&t.ready.every(f=>Dmask.get(f)),"defect target intersection");let amount=weight*t.ready.length/n;z.targetActual+=amount;z.targetForward+=amount;z.targetChecks++;}found=true;break}i++;b++}ok(found,"word defect");z.defectChecks++}
     }
     const bw=w*A/n/s.refs.length;for(let f of s.refs){add(cols,f,bw);add(bc,f,bw);z.back+=bw;if(f===e){z.diag+=bw;continue}if(s.refs.length<cut){z.small+=bw;continue}let b=birth(e,f);if(o.C-b.J<2){z.recent+=bw;continue}if(b.h>R&&b.later.i>0){z.long+=bw;z.longPairs++;if(b.J%10===0){ok(Bmask.get(e)&&Bmask.get(f),"birth target intersection");z.targetActual+=bw;z.targetBack+=bw;z.targetChecks++;}let slot=b.x.sl,ep=episodes.get(slot)||{slot,charge:[0,0,0]};episodes.set(slot,ep);ep.charge[j]+=bw;}else z.other+=bw}
    }
    for(let s of a)for(let f of s.refs){let v=cols.get(f)||0,b=bc.get(f)||0,d=dc.get(f)||0;ok(eq(v,b+d)&&v<=cap+1e-7,"combined column");if(v){z.columns++;z.jointCap+=cap;z.separateCap+=cap*((b>0?1:0)+(d>0?1:0))}}
    z.rows+=rows.size;
   }
  }
 }
 for(let ep of episodes.values()){let sl=ep.slot,J=sl.o.C,groups=new Map();for(let e of sl.refs){let a=groups.get(e.t)||[];a.push(2*e.tag.M-2+H);groups.set(e.t,a)}let g=[...groups].sort((a,b)=>a[0]-b[0]);
  for(let j=0;j<Ps.length;j++){let charge=ep.charge[j];if(!charge)continue;let z=stats[j],P=Ps[j],sum=0,old=0;
   for(let K=P*Math.ceil(J/P);K<J+H;K+=P){let a=g.map(([t,v])=>[t,v.filter(x=>x>K).length]),L=a.reduce((v,x)=>v+x[1],0);if(!L)continue;let pair=0,old0=0,max=0;for(let i=0;i<a.length;i++){let q=0;for(let k=i;k<a.length&&a[k][0]-a[i][0]<=R;k++)q+=a[k][1];max=Math.max(max,q);for(let k=i+1;k<a.length;k++)if(a[k][0]-a[i][0]>R){pair+=a[i][1]*a[k][1];old0+=a[i][1]*a[k][1]/Math.max(cut,a[i][1]+a[k][1])}}
    let out=L-max,env=Math.min(pair/cut,L/2,out-out*out/(2*L),old0);sum+=2*c*P*env;old+=2*c*P*old0;
   }ok(charge<=sum+1e-7&&sum<=old+1e-7,"episode envelope");z.episodes++;z.envelope+=sum;z.oldPairEnvelope+=old;
  }
 }
 for(let z of stats){ok(z.targetActual<=z.intersectionBound+1e-7&&z.intersectionBound<=z.unionBound+1e-7&&eq(z.targetActual,z.targetBack+z.targetForward),"joint target cover");ok(eq(z.source,z.back+z.forward+z.unstable)&&eq(z.back,z.diag+z.recent+z.small+z.long+z.other),"partition");for(let k of Object.keys(z))if(typeof z[k]==="number")z[k]=+z[k].toFixed(6)}
 return {X,focus,B,T,Ll,Lh,N,W,events,hit,birthCache:birthCache.size,stats};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
