function gcd(a,b){return b?gcd(b,a%b):a}
function v2(n){let k=0;while(n%2===0){k++;n/=2}return k}
function graphAnchor(labels,D,W,r){
 let S=[...new Set(labels)],root=S[0],adj=S.map(()=>[]),Q=1;
 for(let a=1;a<=D;a++)Q=Q/gcd(Q,a)*a;
 Q=Q**r;
 let edges=0;
 for(let i=0;i<S.length;i++)for(let j=i+1;j<S.length;j++){
  let cert=null;outer:for(let a=1;a<=D;a++)for(let b=1;b<=D;b++)if(gcd(a,b)===1&&Math.abs(a*S[i]-b*S[j])<=W){cert={a,b};break outer}
  if(cert){adj[i].push({j,...cert});adj[j].push({j:i,a:cert.b,b:cert.a});edges++}
 }
 let dist=Array(S.length).fill(-1),C=Array(S.length).fill(0),queue=[0];dist[0]=0;C[0]=Q;
 for(let i=0;i<queue.length;i++){let v=queue[i];if(dist[v]>=r)continue;
  for(let e of adj[v])if(dist[e.j]<0){dist[e.j]=dist[v]+1;C[e.j]=C[v]*e.a/e.b;if(!Number.isSafeInteger(C[e.j])||C[e.j]<=0)throw Error("integer tree coefficient");queue.push(e.j)}
 }
 if(queue.length!==S.length)return null;
 let cs=labels.map(p=>C[S.indexOf(p)]);
 return {Q,Z:root/Q,cs,S,dist,C,edges}
}
// Bounded-length closed transport excursions: rational-chain capacity obstruction.
function audit(Xs=[4096,16384,65536]){
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 let lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1);
 for(let p=2;p<=lim;p++)if(!spf[p])for(let j=p;j<=lim;j+=p)spf[j]=p;
 let out=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,tags=[],events=0;
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let C0=2*M-2,C=C0,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity;for(let I=0;I<2;I++){let v=C-1+2*I;while(v>1){let f=spf[v];while(v%f===0)v/=f;if(f*f>C+1)continue;let r=mod((I?f+2:0)-t,2*f)||2*f;if(r<w||r===w&&f<p){p=f;w=r}}}if(!p)break;
    let J=C+p-1,n=t+w,I=n%2,d=2*t-C,dp=2*n-J;path.push({C,t,J,n,I,e:1-2*I,p,w,g:p-1,d,dp,j:path.length});events++;C=J;t=n;
   }tags.push({M,C0,F:C,path})
  }
  for(let Y of [11,17,31,61])for(let mode of [0,1]){
   let L=mode?Math.max(1,Math.floor(H/2)):H,K=6;
   let st={X,focus,N:tags.length,events,Y,L,K,tags:0,edges:0,M:0,endpointN:0,transitions:0,upUp:0,upDown:0,downUp:0,downDown:0,oddChecks:0,baselineChecks:0,sameLabel:0,excursions:0,shortExc:0,shortMass:0,shortSplit:0,cheap:0,expensive:0,chainChecks:0,parityChecks:0,capacityChecks:0,denominatorChecks:0,tagChecks:0,graphControls:0,graphCovered:0,graphMass:0,graphLabels:0,graphEdges:0,graphAnchorChecks:0,graphParityChecks:0,graphLong:0,thresholds:[]};
   for(let R of [2,3,4,6])st.thresholds.push({R,M:0,exc:0,split:0,weighted:0,lower:0,rawLower:0});
   for(let tag of tags){
    let path=tag.path,G=path.reduce((v,e)=>v+e.g,0),last=new Map(),edges=new Map(),eligible=e=>e.p>=Y&&e.p<=K*Y,bin=e=>Math.floor((e.C-tag.C0)/L);
    for(let e of path){
     if(e.dp>e.d){for(let a=Math.max(6,e.d);a<e.dp;a++)last.set(a,e.j)}
     else if(e.dp<e.d)for(let a=Math.max(6,e.dp);a<e.d;a++){let j=last.get(a);last.delete(a);if(j===undefined)continue;let s=path[j];if(!eligible(s)||!eligible(e)||bin(s)!==bin(e))continue;let key=j+"/"+e.j;edges.set(key,(edges.get(key)||0)+1)}
    }
    if(!edges.size)continue;
    let jumps=new Int32Array(path.length),outdeg=new Map(),indeg=new Map(),M=0;
    for(let [key,m] of edges){let [s,t]=key.split("/").map(Number);jumps[s]+=m;jumps[t]-=m;M+=m;outdeg.set(s,(outdeg.get(s)||0)+1);indeg.set(t,(indeg.get(t)||0)+1)}
    let sources=path.filter(e=>jumps[e.j]>0),targets=path.filter(e=>jumps[e.j]<0),ep=path.filter(e=>jumps[e.j]!==0);
    let Gu=sources.reduce((v,e)=>v+e.g,0),Gd=targets.reduce((v,e)=>v+e.g,0),Go=G-Gu-Gd,A=3*Gu+4*sources.length-M,Dn=Gd-M,Delta=A/3+Dn+Go;
    ok(A>=0&&Dn>=2*targets.length&&Go>=0&&Math.abs(Delta-(G-4*M/3+4*sources.length/3))<1e-7,"general adjusted slack");
    let O=0,P=0,b=6,TV=0,late=0,down=0,ex=[],exs=[];
    for(let e of path){let x=jumps[e.j],dz=e.dp-e.d;ok(b===e.d-O,"actual baseline pre");
     if(x>0){ok(x<=dz,"source mass capacity");late+=2*(2*e.p-e.w)}
     else if(x<0){ok(-x<=-dz,"target mass capacity");down+=2*e.w}
     O+=x;b+=dz-x;TV+=Math.abs(dz-x);P=Math.max(P,O);ok(O>=0&&O<=Math.max(0,e.dp-6)&&b===e.dp-O,"actual open inventory");
     if(x)ex.push(e);if(!O&&ex.length){ok(ex.length>=2&&ex.reduce((v,f)=>v+jumps[f.j],0)===0,"closed excursion");exs.push(ex);ex=[]}
     st.baselineChecks++;
    }
    ok(O===0&&!ex.length&&late<=A&&down<=Dn&&TV<=5*Delta+1e-7,"general residual and endpoint slack");
    let allC=0,allE=0,trs=[];
    for(let j=1;j<ep.length;j++){let s=ep[j-1],t=ep[j],p=s.p,q=t.p,h=(s.dp-6*s.I)/(2*p),k=(t.dp-6*t.I)/(2*q),up=jumps[t.j]>0,sg=up?-3:1,clock=up?2*(2*q-t.w):-2*t.w,E=path.slice(s.j+1,t.j).reduce((v,e)=>v+e.g,0),relay=t.d-s.dp;
     let c=6*(t.I-s.I)-1+clock-relay;
     ok(Number.isInteger(h)&&h>=0&&Number.isInteger(k)&&k>=0&&2*h*p-(2*k+sg)*q===c&&Math.abs(c)%2===1,"adjacent selected endpoint odd identity");
     ok(Math.abs(relay)<=5*E&&Math.abs(c)<=5*E+Math.abs(clock)+7&&s.dp<=6+5*Delta+P+1e-7,"actual relay and canonical height");
     allC+=Math.abs(c);allE+=E;trs.push({s,t,p,q,h,k,sg,c});st.oddChecks++;if(p===q)st.sameLabel++;if(jumps[s.j]>0){if(up)st.upUp++;else st.upDown++}else{if(up)st.downUp++;else st.downDown++}
    }
    ok(allE<=Go&&allC<=5*Delta+7*trs.length+1e-7,"disjoint complementary gaps");
    let trMap=new Map(trs.map(z=>[z.s.j+"/"+z.t.j,z])),heightFactor=1+(6+5*Delta+P)/Y;
    let data=[];
    for(let ex of exs){
     let n=ex.length,m=ex.reduce((v,e)=>v+Math.max(0,jumps[e.j]),0),As=0,Ds=0;
     for(let e of ex){if(jumps[e.j]>0)As+=3*e.p+1-jumps[e.j];else Ds+=e.p-1+jumps[e.j]}
     let z=ex.slice(1).map((t,j)=>trMap.get(ex[j].j+"/"+t.j)),cost=z.reduce((v,e)=>v+Math.abs(e.c),0),S=3*ex.filter(e=>jumps[e.j]>0).reduce((v,e)=>v+e.p,0)-ex.filter(e=>jumps[e.j]<0).reduce((v,e)=>v+e.p,0);
     ok(As>=0&&Ds>=0&&As-Ds===S+n&&Ds>=2&&m<= (3*K+1)*Y*n,"actual closed capacity ledger");
     let isSplit=ex.some(e=>(outdeg.get(e.j)||0)>1||(indeg.get(e.j)||0)>1),B=1,coeff=1,cheap=z.every(e=>Math.abs(e.c)<Y);
     // Only bounded n need the product; exact parity checked with BigInt.
     if(n<=6){
      st.shortExc++;st.shortMass+=m;if(isSplit)st.shortSplit++;
      if(!cheap){ok(cost>=Y,"expensive transition");st.expensive++}
      else {
       st.cheap++;
       let a=z.map(e=>2*e.h),b=z.map(e=>2*e.k+e.sg);
       ok(a.every(v=>v>0&&v%2===0)&&b.every(v=>v>0&&v%2===1),"positive even/odd chain");
       ok(a.every((v,j)=>v/b[j]<=K+1+1e-9)&&b.every(v=>v<=heightFactor+1e-9),"bounded actual coefficients");
       let cs=ex.map((e,i)=>a.slice(0,i).reduce((v,u)=>v*BigInt(u),1n)*b.slice(i).reduce((v,u)=>v*BigInt(u),1n)),T=cs.reduce((v,c,i)=>v+BigInt(jumps[ex[i].j]>0?3:-1)*c,0n);
       ok(cs[0]%2n===1n&&cs.slice(1).every(c=>c%2n===0n)&&T%2n!==0n,"odd signed capacity integer");st.parityChecks++;
       B=Number(cs[0]);let pred=Number(ex[0].p),err=0;
       for(let i=0;i<z.length;i++){ok(cs[i]*BigInt(a[i])===cs[i+1]*BigInt(b[i]),"exact common rational coefficients");pred=pred*a[i]/b[i];err=Math.max(err,Math.abs(ex[i+1].p-pred));ok(Math.abs(ex[i+1].p-pred)<=(K+1)**(n-2)*cost+1e-7,"propagated cofactor error");st.chainChecks++}
       coeff=3*n*(K+1)**(n-2);
       ok(Math.abs(S-Number(T)*ex[0].p/B)<=coeff*cost+1e-6,"integer balance approximation");
       ok(Y/B<=As+Ds+n+coeff*cost+1e-6&&B<=heightFactor**(n-1)+1e-6,"local denominator lower");st.denominatorChecks++;
      }
      ok(m/B<=(3*K+1)*n*Math.max(1,coeff)*(As+Ds+n+cost)+1e-6,"local weighted capacity");st.capacityChecks++;
     }
     data.push({n,m,As,Ds,cost,B,cheap,isSplit});
     for(let Dstar of [2,4,6])for(let W of [0,1,Math.max(2,Math.floor(Y/8))]){
      st.graphControls++;let r=3,hit=graphAnchor(ex.map(e=>e.p),Dstar,W,r);if(!hit)continue;
      st.graphCovered++;st.graphMass+=m;st.graphLabels+=hit.S.length;st.graphEdges+=hit.edges;if(n>4)st.graphLong++;
      let W0=r*(K+1)**(r-1)*W,Dnew=hit.Q*(K+1)**r;
      ok(hit.cs.every(c=>Number.isSafeInteger(c)&&c>0&&c<=Dnew),"bounded graph anchor coefficients");
      ok(ex.every((e,i)=>Math.abs(e.p-hit.cs[i]*hit.Z)<=W0+1e-7),"graph-derived common anchor");st.graphAnchorChecks+=n;
      if(hit.cs.slice(1).every((c,i)=>v2(c)>v2(hit.cs[i]))){let T=hit.cs.reduce((v,c,i)=>v+BigInt(jumps[ex[i].j]>0?3:-1)*BigInt(c),0n);ok(T!==0n,"graph strict rank capacity");st.graphParityChecks++}
     }
    }
    for(let ctl of st.thresholds){let R=ctl.R,C=3*R*(K+1)**(R-2),F=(3*K+1)*R*C*(8+4*R),sel=data.filter(v=>v.n<=R),m=sel.reduce((v,e)=>v+e.m,0),cost=sel.reduce((v,e)=>v+e.As+e.Ds+e.n+e.cost,0),w=sel.reduce((v,e)=>v+e.m/e.B,0);
     ok(cost<=(8+4*R)*Delta+1e-7&&w<=F*Delta+1e-6,"disjoint bounded-excursion weighted budget");
     ok(m<=F*Delta*heightFactor**(R-1)+1e-6,"bounded excursion polynomial bound");
     let k0=P/Y,base=2+k0+5,constant=F*(2*base)**(R-1),lower=m*(Y/H)**((R-1)/R)/constant;
     ok(Delta+1e-7>=lower&&G-4*M/3+4*sources.length/3+1e-7>=lower,"linearized whole-tag lower");
     ctl.M+=m;ctl.exc+=sel.length;ctl.split+=sel.filter(e=>e.isSplit).length;ctl.weighted+=w;ctl.lower+=lower;ctl.rawLower+=lower-4*sources.length/3;st.tagChecks++;
    }
    st.tags++;st.edges+=edges.size;st.M+=M;st.endpointN+=ep.length;st.transitions+=trs.length;st.excursions+=exs.length;
   }
   ok(st.transitions===st.upUp+st.upDown+st.downUp+st.downDown&&st.thresholds.every(v=>v.M<=st.M),"aggregate source/target ledger");out.push(st)
  }
 }
 return out
}
function independent(){
 let cases=0,checks=0,graphs=0,graphLong=0;
 // Arbitrary signed rational chains, exact dyadic integer parity; not MIN paths.
 for(let n=2;n<=6;n++)for(let t=1;t<=12;t++)for(let mask=1;mask<(1<<n)-1;mask++){
  let a=Array.from({length:n-1},(_,j)=>BigInt(2*(1+(t+j)%5))),b=Array.from({length:n-1},(_,j)=>BigInt(1+2*((3*t+j)%5)));
  let C=Array.from({length:n},(_,i)=>a.slice(0,i).reduce((v,u)=>v*u,1n)*b.slice(i).reduce((v,u)=>v*u,1n)),T=C.reduce((v,c,i)=>v+BigInt(mask>>i&1?3:-1)*c,0n);
  if(T%2n===0n)throw Error("abstract odd capacity");cases++;for(let i=1;i<n;i++){if(C[i]*b[i-1]!==C[i-1]*a[i-1])throw Error("abstract chain");checks++}
 }
 for(let D of [2,3,4,6])for(let r of [1,2,3])for(let W of [0,1,3])for(let off of [0,1,2]){
  let labels=Array.from({length:9},(_,i)=>(1+i%4)*101+((i+off)%3-1)*W),z=graphAnchor(labels,D,W*4,r);
  if(!z)continue;graphs++;if(labels.length>4)graphLong++;
  if(!labels.every((p,i)=>Math.abs(p-z.cs[i]*z.Z)<=r*6**(r-1)*W*4+1e-7))throw Error("abstract graph anchor")
 }
 return {cases,checks,graphs,graphLong}
}
console.log(JSON.stringify({actual:audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),independent:independent()},null,2));
