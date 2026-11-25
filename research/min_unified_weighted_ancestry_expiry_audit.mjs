// Variable reverse Kraft weight and mixed expiry reindex audit.
function audit(X,focus=false,scale=1){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,Ps=[6,30,210],L=6,y=3,theta=scale*L*Math.max(2,Math.floor(Math.sqrt(B))),logTheta=Math.log(theta),bmin=3,lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(v,m)=>{if(!v)throw Error(`${X}/${focus}: ${m}`)},eq=(a,b)=>Math.abs(a-b)<1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b, key=(a,b)=>Math.min(a,b)+"|"+Math.max(a,b);
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)S[n]=S[n]||p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const tags=[],at=new Map(),slots=new Map(),costs=new Map(),weights=new Map();let events=0,hit=0;
 function cost(J,p){if(p<=y)return 0;let k=J+"|"+p;if(costs.has(k))return costs.get(k);let a=weights.get(J);if(!a){let ps=[...new Set([...fac(J),...fac(J+2)])].filter(q=>q>y),sum=ps.reduce((v,q)=>v+Math.log(q),0);a=new Map(ps.map(q=>[q,1/(2*ps.length)+Math.log(q)/(2*sum)]));ok(eq([...a.values()].reduce((v,w)=>v+w,0),ps.length?1:0),"probability mass");weights.set(J,a)}let pi=a.get(p);ok(pi>0,"actual reverse prime");let v=Math.log(L/pi);costs.set(k,v);return v}
 for(let M=X;M<2*X;M++)if(S[M]===M){let C=2*M-2,t=M+2,stop=Math.floor((7*M-1)/4),es=[],tag={M,id:tags.length,es,byC:new Map()};tags.push(tag);
  for(;;){let e={C,t,end:t,p:0,w:0,tag,i:es.length};es.push(e);tag.byC.set(C,e);let ar=at.get(C)||[];ar.push(e);at.set(C,ar);if(C-(2*M-2)>=T){hit++;break}
   let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>stop)break;Object.assign(e,{p,w:v-t,v,r,J:C+p-1,end:v-1});let k=C+"|"+p+"|"+v,a=slots.get(k)||[];a.push(e);slots.set(k,a);events++;C=e.J;t=v;
  }
 }
 let scoreChecks=0,witnessChecks=0,rootWitnesses=0,ordinaryWitnesses=0,maxMoving=0,moving=0,oldMoving=0,newOnly=0,oldOnly=0,expiries=0,reset=0;
 for(let tag of tags){let es=tag.es,z=Math.log(L),start=0,type=0,depth=0,last=0,lastLight=0,finalExp=null;
  for(let i=0;i<es.length;i++){let e=es[i];if(i){z+=cost(es[i-1].J,es[i-1].p);if(es[i-1].p>y)depth++}
   let a=at.get(e.C).length,v=Math.log(L*a);if(v<z){z=v;start=i;type=1}
   e.score=z;e.start=start;e.type=type;e.moving=z<=logTheta+1e-12;e.depth=depth;
   if(a<=Math.floor(theta/L))lastLight=i;e.lastLight=lastLight;
   if(a<=Math.floor(Math.sqrt(B)))last=i;e.oldMoving=depth-es[last].depth<=3;
   if(e.oldMoving)oldMoving++;if(e.moving){moving++;finalExp=e;if(!e.oldMoving)newOnly++}else if(e.oldMoving)oldOnly++;
   e.finalExp=finalExp;
   if(i&&es[i-1].moving&&!e.moving){ok(es[i-1].p>y&&a>theta/L,"expiry jump");expiries++}
   if(i&&!es[i-1].moving&&e.moving){ok(a<=theta/L,"light reset");reset++}
   let slow=Infinity,acc=0,word=[],off=0,found=false;
   for(let j=i;j>=0;j--){let f=es[j];slow=Math.min(slow,Math.log(L*at.get(f.C).length)+acc);if(j===0)slow=Math.min(slow,Math.log(L)+acc);
    if(j===start){e.kappa=Math.log(L)+acc;e.word=word.join(",")+"|"+off;ok(eq(e.score,e.kappa+(type?Math.log(at.get(f.C).length):0)),"selected witness");found=true}
    if(j){let p=es[j-1].p;if(p<=y){off+=p-1;ok(off<L,"LOW barrier")}else{word.push(off+":"+p);off=0;acc+=cost(f.C,p)}}
   }
   ok(found&&eq(slow,z),"weighted score recurrence");scoreChecks++;
  }
 }
 let kraftChecks=0,maxKraft=0;for(let ar of at.values()){let mv=ar.filter(e=>e.moving),leaves=new Map();maxMoving=Math.max(maxMoving,mv.length);ok(mv.length<=theta,"moving mass cap");
  for(let e of mv){let s=e.tag.es[e.start],k=e.word,g=leaves.get(k)||{start:s.C,kappa:e.kappa,root:0,ordinary:0};ok(g.start===s.C&&eq(g.kappa,e.kappa),"same reverse word");if(e.type){g.ordinary++;ordinaryWitnesses++}else{g.root++;rootWitnesses++}leaves.set(k,g)}
  let sum=0;for(let g of leaves.values()){let w=Math.exp(-g.kappa);sum+=w;ok(g.root<=1&&g.ordinary<=at.get(g.start).length&&g.root+g.ordinary<=at.get(g.start).length&&g.root+g.ordinary<=theta*w+1e-7,"leaf cap");witnessChecks++}
  ok(sum<=1+1e-7,"Kraft cap");maxKraft=Math.max(maxKraft,sum);kraftChecks++;
 }
 const cache=new Map();function meet(a,b){let k=key(a.tag.id,b.tag.id),q=cache.get(k);if(q)return a.tag.id<b.tag.id?q:[q[1],q[0],q[2]];let x=a.tag.es,y=b.tag.es,i=0,j=0;while(i<x.length&&j<y.length){let u=x[i],v=y[j];if(u.C<v.C){i++;continue}if(v.C<u.C){j++;continue}let t=Math.max(u.t,v.t);if(t<=Math.min(u.end,v.end)){q=[u,v,t];cache.set(k,a.tag.id<b.tag.id?q:[v,u,t]);return q}i++;j++}throw Error("missing birth")}
 function occupied(e,C,t){let x=e.tag.byC.get(C);return x&&x.i<=e.i&&x.t<=t&&t<=x.end?x:null}
 let groups=new Map(),sourceChecks=0,lightPairs=0,bothPairs=0,mixedPairs=0,oldPairs=0,sourceMovingPairs=0,expiryChecks=0,mixedSmall=0,mixedLarge=0,sourceCohorts=0;
 let rows=Ps.map(P=>({P,mixed:0,both:0,light:0,old:0,expiryCap:0,oldCap:0,expiryKeys:0,resetKeys:0,sourceMoving:0,sourceMovingCap:0,mixedSmall:0}));
 for(let a of slots.values()){let b=a.length;if(b<bmin)continue;sourceCohorts++;let e=a[0],mv=a.filter(f=>f.moving).length,exp=new Map(),expCount=0;
  for(let f of a){let x=f.finalExp,k=x.C+"|"+x.end,g=exp.get(k)||{C:x.C,t:x.end,n:0};g.n++;exp.set(k,g)}
  for(let g of exp.values()){let n=a.filter(f=>{let x=occupied(f,g.C,g.t);return x&&x.i>=f.lastLight&&x.i<=f.finalExp.i&&x.moving}).length;ok(n>=g.n&&n<=theta,"final run occupancy");expCount+=g.n*(n-g.n)+g.n*(g.n-1)/2;}
  let both=0,light=0,mixed=0,old=0,small=0,sm=0,counts=new Map(),byTag=new Map();
  for(let i=0;i<b;i++)for(let j=i+1;j<b;j++){let f=a[i],h=a[j];if(f.moving||h.moving){sm++;sourceMovingPairs++;continue}let [u,v,t]=meet(f,h);
   let fs=f.tag.es[f.lastLight],hs=h.tag.es[h.lastLight];if((fs.C>=u.C&&at.get(fs.C).length<=theta/L)||(hs.C>=u.C&&at.get(hs.C).length<=theta/L)){light++;lightPairs++;continue}
   if(u.moving&&v.moving){both++;bothPairs++;ok(u.i>=f.lastLight&&v.i>=h.lastLight,"both final");continue}
   if(!u.moving&&!v.moving){old++;oldPairs++;continue}
   mixed++;mixedPairs++;let m=u.moving?f:h,o=u.moving?h:f,x=m.finalExp,me=u.moving?u:v;ok(x.i>=me.i&&x.i<m.i,"expiry after birth before source");
   let y0=occupied(o,x.C,x.end);ok(y0&&!y0.moving&&y0.v===x.v&&y0.p===x.p,"old partner at expiry");let xn=x.tag.es[x.i+1],yn=y0.tag.es[y0.i+1];ok(!xn.moving&&!yn.moving&&xn.C===yn.C&&xn.t===yn.t&&x.p>y,"expiry poststate");
   let k=x.C+"|"+x.p+"|"+x.v,g=groups.get(k);if(!g){let all=slots.get(k),fresh=all.filter(f=>f.moving&&!f.tag.es[f.i+1].moving),older=all.filter(f=>!f.moving&&!f.tag.es[f.i+1].moving);g={x,fresh,older,load:Ps.map(()=>0)};groups.set(k,g)}
   ok(g.fresh.includes(x)&&g.older.includes(y0),"actual expiry branch sets");let q=counts.get(k)||{g,n:0};q.n++;counts.set(k,q);expiryChecks++;
   let n=a.filter(f=>{let z=occupied(f,x.C,x.end);return z&&!z.moving}).length;if(n<=b/2){small++;mixedSmall++;let id=m.tag.id;byTag.set(id,(byTag.get(id)||0)+1)}else mixedLarge++;
  }
  ok(both<=expCount&&small<=b*b/2+1e-7&&[...byTag.values()].every(n=>n<=b/2),"expiry pair counts");
  ok(sm+both+light+mixed+old===b*(b-1)/2,"pair partition");
  for(let [k,{g,n}] of counts){let l=g.fresh.filter(f=>a.some(t=>t.tag===f.tag)).length,r=g.older.filter(f=>a.some(t=>t.tag===f.tag)).length;ok(n<=l*r,"source cohort expiry product");sourceChecks++;
   for(let j=0;j<Ps.length;j++){let P=Ps[j],nk=Math.ceil(e.J/P)-Math.ceil(e.C/P);g.load[j]+=2*P*nk*n/b}
  }
  for(let z of rows){let P=z.P,nk=Math.ceil(e.J/P)-Math.ceil(e.C/P),w=2*P*nk/b;z.mixed+=w*mixed;z.both+=w*both;z.light+=w*light;z.old+=w*old;z.sourceMoving+=w*sm;z.sourceMovingCap+=2*P*nk*mv;z.mixedSmall+=w*small}
 }
 for(let j=0;j<Ps.length;j++){let z=rows[j],sum=0,P=z.P;
  for(let g of groups.values()){let w=g.load[j];if(!w)continue;let x=g.x,p=x.p,J=x.J,s=x.v%2,k=(2*x.v-J-6*s)/2;ok(k>=0&&k%p===0&&(J+2*s)%p===0,"expiry CRT");let cap=0,old=0;
   for(let K=P*Math.ceil(J/P);K<J+H;K+=P){let a=g.fresh.filter(f=>f.tag.es.at(-1).C>K).length,b=g.older.filter(f=>f.tag.es.at(-1).C>K).length;cap+=2*P*a*b/Math.max(bmin,a+b);old+=2*P*Math.min(a,b)}
   ok(w<=cap+1e-7&&cap<=old+1e-7,"expiry lifetime cap");sum+=w;z.expiryCap+=cap;z.oldCap+=old;z.expiryKeys++;if(k===0)z.resetKeys++;
  }ok(eq(sum,z.mixed)&&z.sourceMoving<=z.sourceMovingCap+1e-7,"global mixed conservation");for(let k of Object.keys(z))z[k]=+z[k].toFixed(6)
 }
 return {X,focus,scale,B,T,N:tags.length,events,hit,theta,moving,oldMoving,newOnly,oldOnly,maxMoving,scoreChecks,witnessChecks,kraftChecks,maxKraft,rootWitnesses,ordinaryWitnesses,expiries,reset,sourceCohorts,sourceChecks,lightPairs,bothPairs,mixedPairs,oldPairs,sourceMovingPairs,expiryChecks,mixedSmall,mixedLarge,keys:groups.size,rows}
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
console.log(JSON.stringify(audit(65536,false,2)));
