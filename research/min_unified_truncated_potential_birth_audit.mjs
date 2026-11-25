// Truncated quadratic birth potential, physical maturity and source-cohort audit.
function audit(X,focus=false,scale=1,gainFactor=8){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(Math.floor(gainFactor*B),Math.floor(X/2)),H=T+B,Ps=[6,30,210],L=6,y=3,theta=scale*L*Math.max(2,Math.floor(Math.sqrt(B))),logTheta=Math.log(theta),bmin=3,lim=7*X+B+20,S=new Int32Array(lim);
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

 const m=Math.max(2,Math.floor(scale*Math.sqrt(B)/3)),eta=.25,verts=new Map(),all=[];
 let degree=1;
 function branch(e,t){return e.t<t?"w":e.i===0?"r":String(e.tag.es[e.i-1].p)}
 for(let [C,ar] of at){let times=[...new Set(ar.map(e=>e.t))];for(let t of times){let present=ar.filter(e=>e.t<=t&&t<=e.end),groups=new Map();for(let e of present){let k=branch(e,t),a=groups.get(k)||[];a.push(e);groups.set(k,a)}
  let n=present.length,ret=present.filter(e=>!e.p).length;degree=Math.max(degree,groups.size);let U={C,t,n,ret,present,groups,loads:Ps.map(()=>0)};verts.set(C+"|"+t,U);all.push(U);
 }}
 const F=(n,k)=>n<=k?n*n:2*k*n-k*k;
 let pot=0,pot2=0,loss=0,loss2=0,smallPairs=0,attach=0,heavyNodes=0,heavyExcess=0,seedMass=0,seedNodes=0,seedAge=0,matureTags=0,firstAge=0,firstChecks=0,mergeChecks=0;
 all.sort((a,b)=>a.t-b.t||a.C-b.C);
 for(let U of all){let {n,ret,groups}=U,a=[...groups.values()].map(a=>a.length),h=a.filter(x=>x>=m).length,s=a.filter(x=>x<m).reduce((x,y)=>x+y,0),D=F(n,m)-a.reduce((v,x)=>v+F(x,m),0),D2=F(n,degree*m)-a.reduce((v,x)=>v+F(x,degree*m),0),ss=s*s-a.filter(x=>x<m).reduce((v,x)=>v+x*x,0);
  ok(D>=0&&D2>=ss,"potential and small pairs");pot+=D;pot2+=D2;loss+=F(n,m)-F(n-ret,m);loss2+=F(n,degree*m)-F(n-ret,degree*m);smallPairs+=ss;U.h=h;U.s=s;U.ss=ss;
  if(h){ok(D>=(h-1)*m*m+m*s,"heavy attachment potential");attach+=s;heavyExcess+=h-1;if(h>=2)heavyNodes++;}
  if(n>=m){let newTags=U.present.filter(e=>!e.tag.firstHeavy);if(newTags.length===n){seedNodes++;seedMass+=n;seedAge+=newTags.reduce((v,e)=>v+U.C-e.tag.es[0].C,0);let ages=newTags.map(e=>U.C-e.tag.es[0].C).sort((a,b)=>a-b);ok(ages.every((x,i)=>x>=4*i),"seed root spacing");}
   for(let e of newTags){e.tag.firstHeavy=U;matureTags++;firstAge+=U.C-e.tag.es[0].C;}
  }
  mergeChecks++;
 }
 ok(pot===loss-tags.length&&pot2===loss2-tags.length,"exact retirement telescope");ok(pot<=2*m*tags.length&&pot2<=2*degree*m*tags.length&&smallPairs<=pot2&&attach<=2*tags.length&&heavyExcess*m<=2*tags.length&&seedMass<=tags.length&&seedNodes*m<=seedMass,"global potential budget");
 const cache=new Map();function meet(a,b){let k=key(a.tag.id,b.tag.id),q=cache.get(k);if(q)return a.tag.id<b.tag.id?q:[q[1],q[0],q[2]];let x=a.tag.es,y=b.tag.es,i=0,j=0;while(i<x.length&&j<y.length){let u=x[i],v=y[j];if(u.C<v.C){i++;continue}if(v.C<u.C){j++;continue}let t=Math.max(u.t,v.t);if(t<=Math.min(u.end,v.end)){q=[u,v,t];cache.set(k,a.tag.id<b.tag.id?q:[v,u,t]);return q}i++;j++}throw Error("missing birth")}
 let rows=Ps.map(P=>({P,raw:0,smallSmall:0,heavyHeavy:0,mixed:0,thinHeavy:0,thinAttachment:0,thinAttachmentCap:0,smallSmallCap:0,heavyThinCap:0,maturityStrip:0,maturityStripCap:0,residence:0,postMaturity:0})),sources=0,pairChecks=0,attachmentChecks=0,heavyBirthKeys=new Set();
 const hAge=.05*H;
 for(let a of slots.values()){let b=a.length;if(b<Math.max(bmin,m))continue;sources++;let e=a[0],counts=new Map();
  for(let f of a){ok(f.tag.firstHeavy&&f.tag.firstHeavy.C<=e.C,"first physical maturity");firstChecks++}
  for(let i=0;i<b;i++)for(let j=i+1;j<b;j++){let f=a[i],g=a[j],[u,v,t]=meet(f,g),U=verts.get(u.C+"|"+t),i0=branch(u,t),j0=branch(v,t);ok(U&&i0!==j0&&U.groups.has(i0)&&U.groups.has(j0),"actual birth groups");
   let x=U.groups.get(i0).length,y=U.groups.get(j0).length,type=x<m&&y<m?0:x>=m&&y>=m?2:1,thin=false;
   if(type===2){heavyBirthKeys.add(U);ok(U.h>=2,"heavy node")}
   if(type===1){let n=a.filter(k=>{let z=k.tag.byC.get(U.C);return z&&z.i<=k.i&&z.t<=t&&t<=z.end&&U.groups.get(branch(z,t)).length>=m}).length;thin=n<=eta*b;attachmentChecks++}
   for(let jj=0;jj<Ps.length;jj++){let P=Ps[jj],z=rows[jj],nk=Math.ceil(e.J/P)-Math.ceil(e.C/P),w=2*P*nk/b;z.raw+=w;z[["smallSmall","mixed","heavyHeavy"][type]]+=w;if(type===2)U.loads[jj]+=w;if(thin)z.thinAttachment+=w;
    for(let K=P*Math.ceil(e.C/P);K<e.J;K+=P){if(K<Math.max(f.tag.firstHeavy.C,g.tag.firstHeavy.C)+hAge)z.maturityStrip+=2*P/b;else z.postMaturity+=2*P/b;}
   }pairChecks++;
  }
 }
 for(let j=0;j<Ps.length;j++){let z=rows[j],P=z.P;
  for(let U of heavyBirthKeys)if(U.loads[j]<=H*m*eta)z.thinHeavy+=U.loads[j];
  z.heavyThinCap=heavyNodes*H*m*eta;z.smallSmallCap=(H+P)*smallPairs/Math.max(bmin,m);z.thinAttachmentCap=2*eta*(H+P)*attach;z.maturityStripCap=2*tags.length*(hAge+P);
  for(let tag of tags)if(tag.firstHeavy)z.residence+=Math.max(0,tag.es.at(-1).C-tag.firstHeavy.C-hAge)+P;
  ok(eq(z.raw,z.smallSmall+z.mixed+z.heavyHeavy)&&eq(z.raw,z.maturityStrip+z.postMaturity),"charge partition");
  ok(z.thinHeavy<=z.heavyThinCap+1e-6&&z.smallSmall<=z.smallSmallCap+1e-6&&z.thinAttachment<=z.thinAttachmentCap+1e-6&&z.maturityStrip<=z.maturityStripCap+1e-6&&z.postMaturity<=z.residence+1e-6,"global birth and maturity caps");
  for(let k of Object.keys(z))z[k]=+z[k].toFixed(6);
 }
 return {X,focus,scale,gainFactor,B,T,H,N:tags.length,events,hit,m,degree,mergeChecks,pot,pot2,loss,loss2,smallPairs,attach,heavyNodes,heavyExcess,seedNodes,seedMass,seedAge,matureTags,firstAge,firstChecks,sources,pairChecks,attachmentChecks,heavyBirthKeys:heavyBirthKeys.size,rows}
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));
for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
console.log(JSON.stringify(audit(65536,false,.5,2)));
