// Occupation-packing certificate and small-label first/repeat gain coefficients on actual all-root slabs.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=4000005,spf=new Int32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)if(!spf[a])spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const f=x=>x?x*Math.log(x):0,add=(m,k,v=1)=>m.set(k,(m.get(k)||0)+v);
 let out={roots:0,events:0,segments:0,capacityChecks:0,firstGainChecks:0,scoreChecks:0,rows:[]};
 for(let R of [12000,48000,192000,480000,1000000,2000000]){
  let S=Math.sqrt(2*R+1),T=Math.ceil(S),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nr=(hi-lo)/6+1,B=3*T+6,L=Math.log(S),B0=Math.ceil(B/W)+2;
  function q(a){return Math.min(spf[a-1]||a-1,spf[a+1]||a+1)}
  function C(p){let t=Math.log(Math.min(p,S)),d=L-t;return 2*Math.log(L/t)+Math.log1p(d)+2*Math.log1p(Math.log1p(d))}
  function weight(a){return Math.exp(-C(q(a)))}
  let ends=new Map(),endsW=new Map(),paths=[],rep=new Map(),terminal=0,nonterminal=0,proxy=0,actual=0,groups=[1/8,1/6,1/5,0.24].map(e=>({e,Y:Math.max(3,Math.ceil(R**e)),smallTime:0,first:0,repeat:0,smallCost:0,largeCost:0}));
  for(let A=lo;A<=hi;A+=6){
   let l=lo+Math.floor((A-lo)/W)*W,n0=3-l/2,end=n0+T,a=A,n=3-A/2,path=[],seen=new Set(),V=0,cp=0,ca=0,term=0,gm=groups.map(()=>[0,0,0,0,0]);
   for(;;){let e=next(a,n),fire=n+e.w,stop=Math.min(fire,end),begin=Math.max(n,n0),dt=Math.max(0,stop-begin),last=fire>end;
    if(dt){let w=weight(a),pc=last?0:C(e.p);V+=dt*w/T;cp+=dt*pc/T;ca+=dt*C(q(a))/T;path.push({a,dt,begin:begin-n0,stop:stop-n0,w});out.segments++;if(last)term=dt/T;else for(let i=0;i<groups.length;i++){if(e.p<groups[i].Y){gm[i][0]+=dt;gm[i][3]+=dt*pc}else gm[i][4]+=dt*pc}}
    if(last)break;
    for(let i=0;i<groups.length;i++)if(e.p<groups[i].Y)gm[i][seen.has(e.p)?2:1]+=e.p-1;
    seen.add(e.p);a-=e.p-1;n=fire;out.events++;
   }
   ck(A-a<=B,"gain");terminal+=term;nonterminal+=1-term;proxy+=cp;actual+=ca;
   for(let i=0;i<groups.length;i++){let g=groups[i],x=gm[i];let maxFirst=0;for(let p=3;p<g.Y;p+=2)if(!spf[p])maxFirst+=p-1;ck(x[1]<=maxFirst&&x[0]<=3*(x[1]+x[2])+1e-9,"first/rep gain");out.firstGainChecks++;
    g.smallTime+=x[0]/T;g.first+=x[1]/T;g.repeat+=x[2]/T;g.smallCost+=x[3]/T;g.largeCost+=x[4]/T;
   }
   let k=l+":"+a;add(ends,a);add(endsW,k);let v={A,l,y:a,k,path,V,term,cp,ca};paths.push(v);if(!rep.has(k)||rep.get(k).V<V)rep.set(k,v);out.roots++;
  }
  let weights=new Map(),weightsG=new Map(),repWeights=new Map(),terminalCert=0,terminalProxyCert=0,simple=0,simpleG=0,repSimple=0,exact=0,visited=new Map(),local=new Map();
  for(let v of paths){
   let m=endsW.get(v.k),mg=ends.get(v.y);simple+=v.V/m;simpleG+=v.V/mg;
   terminalCert+=v.term*weight(v.y)/mg;let z=T*v.term/2;terminalProxyCert+=v.term*(z>=3?Math.exp(-C(z)):Math.exp(-C(3)))/mg;
   for(let s of v.path){let w=s.dt/T/m,gg=s.dt/T/mg;add(weights,s.a,w);add(weightsG,s.a,gg);let k=v.l+":"+s.a;add(local,k,w);visited.set(s.a,s.w)}
  }
  for(let v of rep.values()){repSimple+=v.V;for(let s of v.path)add(repWeights,s.a,s.dt/T)}
  for(let v of local.values()){ck(v<=1+1e-8,"window capacity");out.capacityChecks++}
  let clamp=0,clampG=0,clampRep=0,cap=0,maxWeight=0,capT=0,capacity=0;
  for(let [a,w] of visited){let z=weights.get(a)||0,zg=weightsG.get(a)||0,zr=repWeights.get(a)||0;ck(z<=B0+1e-8&&zg<=z+1e-8&&zr<=B0+1e-8,"global cap");maxWeight=Math.max(maxWeight,z);clamp+=w*Math.min(1,z);clampG+=w*Math.min(1,zg);clampRep+=w*Math.min(1,zr);capacity+=w;out.capacityChecks++}
  ck(simple/B0<=clamp+1e-8&&simpleG/B0<=clampG+1e-8&&repSimple/B0<=clampRep+1e-8&&terminalProxyCert<=terminalCert+1e-8&&clamp<=capacity+1e-8&&clampRep<=capacity+1e-8,"cert");out.scoreChecks++;
  let badWeight=0;for(let a=2*Math.ceil((lo-B)/2);a<=hi;a+=2)if(q(a)<=S)badWeight+=weight(a);
  let Lend=[...ends.values()].reduce((s,m)=>s+f(m),0)/nr,LendW=[...endsW.values()].reduce((s,m)=>s+f(m),0)/nr;
  let G=groups.map(g=>{let x={e:g.e,Y:g.Y};for(let k of ["smallTime","first","repeat","smallCost","largeCost"])x[k]=g[k]/nr;let coeff=nonterminal/nr+2*x.smallTime,coarse=nonterminal/nr+6*(x.first+x.repeat);return {...x,coeff,coarse}});
  out.rows.push({R,T,W,nr,Lend,LendW,terminal:terminal/nr,nonterminal:nonterminal/nr,meanProxy:proxy/nr,meanActual:actual/nr,visited:visited.size,weightedVisited:capacity,badWeight,B0,maxWeight,simple,simpleG,repSimple,clamp,clampG,clampRep,terminalCert,terminalProxyCert,groups:G});
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
