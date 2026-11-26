// Actual arrival-edge virtual survival and signed graph clock ledger.
function audit(Xs=[4096,16384,65536]){
 const ok=(v,m)=>{if(!v)throw Error(m)},near=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(x,m)=>(x%m+m)%m;
 let lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1);for(let p=2;p<=lim;p++)if(!spf[p])for(let j=p;j<=lim;j+=p)spf[j]=p;
 let results=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),h=Math.max(2,Math.floor(B/16)),age=h,N=0,events=0,tags=[],edges=new Map(),W=0,G=0,Z=0;
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let id=N++,C0=2*M-2,C=C0,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity;for(let I=0;I<2;I++){let v=C-1+2*I;while(v>1){let f=spf[v];while(v%f===0)v/=f;if(f*f>C+1)continue;let r=mod((I?f+2:0)-t,2*f)||2*f;if(r<w||r===w&&f<p){p=f;w=r}}}if(!p)break;
    let J=C+p-1,n=t+w,d=2*t-C,dp=2*n-J,key=C+"/"+t;
    if(!edges.has(key))edges.set(key,{C,t,J,n,d,dp,p,w,ids:[]});let e=edges.get(key);ok(e.J===J&&e.n===n,"determinism");e.ids.push(id);path.push(e);events++;W+=w;G+=p-1;C=J;t=n;
   }Z+=2*t-C;tags.push({id,C0,F:C,expiry:C-h,df:2*t-C,path})
  }
  ok(2*W===G+Z-6*N,"global clock");
  let ordered=[...edges.values()].sort((a,b)=>a.C-b.C||a.t-b.t),first=new Map(),pkey=(i,j)=>i<j?i+"/"+j:j+"/"+i;
  for(let e of ordered)for(let i=0;i<e.ids.length;i++)for(let j=i+1;j<e.ids.length;j++){let k=pkey(e.ids[i],e.ids[j]);if(!first.has(k))first.set(k,e.C+age)}
  for(let masked of [false,true]){
   let vertices=new Map(),U=0,clock=0,allVirtual=0,merge=0,activation=0,ret=0,retEx=0,retUpper=0,terminal=0,termErr=0,initial=0,retSteps=0,exSteps=0,mergeSteps=0,activeSteps=0,edgesUsed=0,cohorts=0,fullClock=0,physicalSlots=new Map();
   for(let e of ordered){let key=e.C+"/"+e.p+"/"+e.n;physicalSlots.set(key,(physicalSlots.get(key)||0)+e.ids.length)}
   const vert=(C,t)=>{let k=C+"/"+t;if(!vertices.has(k))vertices.set(k,{C,t,ins:[],out:null,roots:0});return vertices.get(k)};
   const A=(ids,pairs,x,strict)=>{let s=new Set(ids),a=0;for(let z of pairs)if(s.has(z.i)&&s.has(z.j)&&(strict?z.start<x:z.start<=x))a+=2;return a};
   const D=(e,x)=>e.d+(x-e.C)*(e.dp-e.d)/(e.J-e.C);
   for(let e of ordered){
    let ids=e.ids.filter(i=>tags[i].expiry>e.C);if(!ids.length)continue;edgesUsed++;
    let pairs=[];for(let a=0;a<ids.length;a++)for(let b=a+1;b<ids.length;b++){let i=ids[a],j=ids[b];if(masked&&(i+j)%3===0)continue;let start=first.get(pkey(i,j));if(start<Math.min(tags[i].expiry,tags[j].expiry,e.J))pairs.push({i,j,start})}
    let cuts=[e.C,e.J,...ids.map(i=>tags[i].expiry).filter(x=>e.C<x&&x<e.J),...pairs.map(z=>z.start).filter(x=>e.C<x&&x<e.J)];cuts=[...new Set(cuts)].sort((a,b)=>a-b);
    let live=ids.slice(),a=A(live,pairs,e.C,true),b=live.length,pre=a/b,after=A(live,pairs,e.C,false)/b;
    let v=vert(e.C,e.t);ok(!v.out,"unique out");v.out={b,A:a,ids:live.slice()};activation+=D(e,e.C)*(after-pre);if(after>pre)activeSteps++;
    for(let k=0;k+1<cuts.length;k++){
     let x=cuts[k],y=cuts[k+1],b=live.length,a=A(live,pairs,x,false),wgt=b?a/b:0,dx=y-x;
     U+=wgt*dx;clock+=wgt*dx*e.w/(e.J-e.C);allVirtual+=b*dx;fullClock+=b*dx*e.w/(e.J-e.C);
     let remaining=live.filter(i=>tags[i].expiry>y),s=remaining.length,r=b-s,Aafter=A(remaining,pairs,y,true),next=s?Aafter/s:0;
     if(r){let Aold=A(live,pairs,y,true),drop=Aold/b-next,base=D(e,y)*r,ex=D(e,y)*(drop-r),bound=s?D(e,y)*r*(s-next)/b:0;
      ok(ex<=bound+1e-7,"retirement excess");ret+=D(e,y)*drop;terminal+=base;retEx+=ex;retUpper+=bound;retSteps++;if(ex>1e-8)exSteps++;
      for(let i of live)if(tags[i].expiry===y){ok(D(e,y)<=tags[i].df+h+1e-7&&D(e,y)>=tags[i].df-5*h-1e-7,"terminal shift");termErr+=D(e,y)-tags[i].df}
     }
     live=remaining;
     if(y<e.J&&s){let plus=A(live,pairs,y,false)/s;ok(plus>=next-1e-9,"activation");activation+=D(e,y)*(plus-next);if(plus>next)activeSteps++}
    }
    if(live.length){let a=A(live,pairs,e.J,true);vert(e.J,e.n).ins.push({b:live.length,A:a,ids:live})}
   }
   for(let v of vertices.values()){
    if(!v.out){ok(!v.ins.length,"no ghost successor");continue}
    let b=v.out.b,A=v.out.A,ib=v.ins.reduce((s,z)=>s+z.b,0),ia=v.ins.reduce((s,z)=>s+z.A,0),root=b-ib;
    ok(root>=0&&root<=1,"root injection");ok(A===ia,"no active cross pair at merge");let union=new Set(v.ins.flatMap(z=>z.ids));ok(union.size===ib&&[...union].every(i=>v.out.ids.includes(i)),"actual survivor sets");
    let loss=v.ins.reduce((s,z)=>s+z.A/z.b,0)-A/b;ok(loss>=-1e-9,"merge loss");merge+=(2*v.t-v.C)*loss;if(loss>1e-8)mergeSteps++;
    if(root)initial+=6*root;cohorts++;
   }
   ok(near(2*clock,U+merge+ret-activation),"global signed graph balance");ok(near(ret,terminal+retEx)&&retEx<=retUpper+1e-7,"ret decomposition");
   ok(terminal<=Z+N*h+1e-6,"terminal upper");
   ok(U<=allVirtual+1e-6&&clock<=fullClock+1e-6,"coverage");
   results.push({X,focus,masked,N,events,h,age,edgesUsed,cohorts,U,clock,allVirtual,fullClock,G,W,Z,merge,activation,ret,terminal,termErr,retEx,retUpper,retSteps,exSteps,mergeSteps,activeSteps,initial,objective:U+merge+retEx-activation,upperObjective:U+merge+retUpper-activation});
  }
 }
 // Star graph retirement and complete graph retirement: show surplus can be positive,
 // and complete surviving graph leaves no positive surplus (up to diagonal).
 let b=10,s=9,k=1,old=18,after=0,star=old/b-after/s-k;ok(star>0&&star<=k*(s-after/s)/b,"star surplus");
 let full=b*(b-1)/b-s*(s-1)/s-k;ok(full===0,"complete graph");
 return {results,synthetic:{star,full}}
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
