// Exact integer inventory-grid re-pairing and endpoint-size dispersion.
function grid(jumps,a){
 const ok=(x,m)=>{if(!x)throw Error(m)};
 let M0=jumps.reduce((v,x)=>v+Math.max(0,x),0),P0=0,O=0,disp=0;
 for(let x of jumps){O+=x;P0=Math.max(P0,O);ok(O>=0,"nonnegative inventory");if(x)disp+=2*Math.max(0,Math.abs(x)-a)+Math.max(0,a-Math.abs(x))}
 ok(O===0,"closed inventory");
 let best=null,sumMass=0,sumGrid=0,sumMulti=0,sumSmall=0,checks=0;
 for(let shift=0;shift<a;shift++){
  let O=0,stack=[],all=[],counts=[],g=0,lossMulti=0,lossSmall=0,inv=0,P=0;
  for(let j=0;j<jumps.length;j++){let next=O+jumps[j],c=Math.floor((next+a-1-shift)/a)-Math.floor((O+a-1-shift)/a);
   counts[j]=Math.abs(c);g+=Math.max(c,0);
   if(c>0)for(let k=0;k<c;k++)stack.push(j);else for(let k=0;k<-c;k++){ok(stack.length,"grid stack underflow");all.push({s:stack.pop(),t:j})}
   O=next;ok(stack.length===Math.floor((O+a-1-shift)/a),"grid count");checks++;
  }
  ok(!stack.length,"closed grid stack");
  let pairs=[],m=0,events=new Set();
  for(let z of all){if(counts[z.s]!==1||counts[z.t]!==1){lossMulti+=a;continue}
   let w=Math.min(a,jumps[z.s],-jumps[z.t]);ok(w>0&&!events.has(z.s)&&!events.has(z.t),"unique capacity endpoints");events.add(z.s);events.add(z.t);lossSmall+=a-w;m+=w;pairs.push({...z,m:w});
  }
  let dv=new Int32Array(jumps.length);for(let z of pairs){dv[z.s]+=z.m;dv[z.t]-=z.m}
  O=0;for(let j=0;j<jumps.length;j++){O+=jumps[j];inv+=dv[j];P=Math.max(P,inv);ok(inv>=0&&inv<=O+a-1,"rounded open inventory bound")}
  ok(inv===0&&m===a*g-lossMulti-lossSmall&&m<=M0,"grid weight ledger");
  sumMass+=m;sumGrid+=a*g;sumMulti+=lossMulti;sumSmall+=lossSmall;
  if(!best||m>best.m)best={m,pairs,P,shift};
 }
 ok(sumGrid===a*M0&&sumMass>=a*(M0-disp)&&best.m>=M0-disp,"exact mean rounding guarantee");
 return {...best,M0,P0,disp,sumGrid,sumMulti,sumSmall,sumMass,checks};
}
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
   let st={X,focus,N:tags.length,events,Y,L,K,edges:0,M0:0,mutual:0,impurity:0,roundMass:0,roundLoss:0,disp:0,better:0,betterMass:0,excursions:0,shifts:0,gridChecks:0,gridPairs:0,oldEdgeChecks:0,oldEdgeInflated:0,baselineChecks:0,relayChecks:0,budgetChecks:0,primeDispChecks:0,primeDisp:0,endpointSlack:0,maxOpen:0,maxRounded:0,lower:0};
   for(let tag of tags){
    let path=tag.path,G=path.reduce((v,e)=>v+e.g,0),last=new Map(),edges=new Map(),eligible=e=>e.p>=Y&&e.p<=K*Y,bin=e=>Math.floor((e.C-tag.C0)/L);
    for(let e of path){
     if(e.dp>e.d){for(let a=Math.max(6,e.d);a<e.dp;a++)last.set(a,e.j)}
     else if(e.dp<e.d)for(let a=Math.max(6,e.dp);a<e.d;a++){let j=last.get(a);last.delete(a);if(j===undefined)continue;let s=path[j];if(!eligible(s)||!eligible(e)||bin(s)!==bin(e))continue;let key=j+"/"+e.j;edges.set(key,(edges.get(key)||0)+1)}
    }
    if(!edges.size)continue;
    let jumps=new Int32Array(path.length),sb=new Map(),tb=new Map(),M0=0;
    for(let [key,m] of edges){let [s,t]=key.split("/").map(Number);jumps[s]+=m;jumps[t]-=m;M0+=m;for(let [map,j] of [[sb,s],[tb,t]])if(!map.has(j)||map.get(j).m<m)map.set(j,{key,m})}
    let mutual=0,iu=M0-[...sb.values()].reduce((v,z)=>v+z.m,0),id=M0-[...tb.values()].reduce((v,z)=>v+z.m,0);
    for(let z of sb.values())if(tb.get(Number(z.key.split("/")[1])).key===z.key)mutual+=z.m;
    // Reconstruct the retained physical edge table by LIFO on compressed open mass.
    let stack=[],rebuilt=new Map(),P0=0,O=0;
    for(let j=0;j<jumps.length;j++){let v=jumps[j];if(v>0)stack.push({j,m:v});else if(v<0){let need=-v;while(need){let z=stack.at(-1);ok(z,"compressed stack underflow");let take=Math.min(need,z.m),key=z.j+"/"+j;rebuilt.set(key,(rebuilt.get(key)||0)+take);need-=take;z.m-=take;if(!z.m)stack.pop()}}O+=v;P0=Math.max(P0,O);ok(O>=0&&O<=Math.max(0,path[j].dp-6),"actual original inventory")}
    ok(O===0&&!stack.length&&rebuilt.size===edges.size&&[...edges].every(([k,m])=>rebuilt.get(k)===m),"compressed LIFO reconstructs retained physical edges");
    let begin=0,acc=0,sel=[],disp=0,maxA=0,primeDisp=0,endpointSlack=0;
    // Choose independent reference sizes on actual zero-inventory excursions.
    for(let j=0;j<jumps.length;j++){if(!acc&&jumps[j]===0){begin=j+1;continue}acc+=jumps[j];if(acc!==0)continue;
     let list=Array.from(jumps.slice(begin,j+1)),vals=list.filter(Boolean).map(Math.abs).sort((a,b)=>a-b),a=vals[Math.floor(vals.length/2)],z=grid(list,a);
     st.excursions++;st.shifts+=a;st.gridChecks+=z.checks;disp+=z.disp;maxA=Math.max(maxA,a);
     for(let i=0;i<list.length;i++)if(list[i]){let e=path[begin+i],cap=list[i]>0?3*e.p+1:e.p-1;ok(Math.abs(list[i])<=cap,"actual endpoint capacity");primeDisp+=Math.abs(cap-a);endpointSlack+=cap-Math.abs(list[i])}
     for(let v of z.pairs){let s=begin+v.s,t=begin+v.t,key=s+"/"+t;ok(edges.has(key),"grid pair supported by physical edge");st.oldEdgeChecks++;if(v.m>edges.get(key))st.oldEdgeInflated++;sel.push({s:path[s],t:path[t],m:v.m})}
     begin=j+1;
    }
    ok(acc===0&&disp<=2*(primeDisp+endpointSlack),"capacity dispersion inequality");st.primeDispChecks++;
    let M=sel.reduce((v,z)=>v+z.m,0),Gu=sel.reduce((v,z)=>v+z.s.g,0),Gd=sel.reduce((v,z)=>v+z.t.g,0),n=sel.length,Go=G-Gu-Gd,A=3*Gu+4*n-M,D=Gd-M,Delta=A/3+D+Go,raw=G-4*M/3;
    ok(M<=M0&&M>=M0-disp&&A>=0&&D>=2*n&&Go>=0&&raw+1e-7>=Delta/3,"rounded endpoint and slack ledger");
    let start=new Map(),end=new Map();for(let z of sel){ok(!start.has(z.s.j)&&!end.has(z.t.j),"unique endpoints globally");start.set(z.s.j,z);end.set(z.t.j,z)}
    let inv=0,P=0,base=6,TV=0,before=[],after=[],res=[];
    for(let e of path){before[e.j]=inv;let ds=e.dp-e.d,zs=start.get(e.j),zt=end.get(e.j);if(zs){inv+=zs.m;ds-=zs.m}if(zt){inv-=zt.m;ds+=zt.m}
     res[e.j]=ds;TV+=Math.abs(ds);base+=ds;after[e.j]=inv;P=Math.max(P,inv);ok(inv>=0&&inv<=P0+maxA&&base===e.dp-inv&&e.dp<=6+5*Delta+P0+maxA+1e-7,"virtual residual baseline");st.baselineChecks++;
    }
    ok(inv===0&&TV<=5*Delta+1e-7,"rounded variation");let inverse=0,wr=0;
    for(let z of sel){let {s,t,m}=z,p=s.p,r=t.p,k=(t.dp-6*t.I)/(2*r),h=(s.dp-6*s.I)/(2*p),relay=t.d-s.dp,c=-relay-1-2*t.w+6*(t.I-s.I);
     ok(after[s.j]===before[t.j]&&relay===res.slice(s.j+1,t.j).reduce((v,a)=>v+a,0)&&2*h*p-(2*k+1)*r===c,"virtual laminar signed relay and odd shift");inverse+=m/(2*k+1);wr+=m/p*Math.abs(relay);st.relayChecks++;
    }
    ok(wr<=P/Y*TV+1e-7&&inverse<=(42+5*P/Y)*Delta+1e-6,"virtual weighted relay budget");
    let lam=(P0+maxA)/Y,f=Math.min(1/(1+lam)**2,Math.sqrt(Y/((1+lam)*H)));
    ok(raw+1e-7>=M*f/600&&G-4*M0/3+2*disp+1e-7>=M0*f/600,"virtual original dispersion tradeoff");st.budgetChecks++;
    st.edges+=edges.size;st.M0+=M0;st.mutual+=mutual;st.impurity+=iu+id;st.roundMass+=M;st.roundLoss+=M0-M;st.disp+=disp;st.gridPairs+=n;if(M>mutual){st.better++;st.betterMass+=M-mutual}st.primeDisp+=primeDisp;st.endpointSlack+=endpointSlack;st.maxOpen=Math.max(st.maxOpen,P0);st.maxRounded=Math.max(st.maxRounded,P);st.lower+=M0*f/600;
   }
   ok(st.M0===st.roundMass+st.roundLoss&&st.roundLoss<=st.disp,"aggregate rounding");out.push(st)
  }
 }
 return out
}
function independent(){
 let cases=0,checks=0,perfect=0,best=0,disp=0;
 for(let a of [2,3,5,11,31])for(let n of [2,3,7,19])for(let b=1;b<a;b++){
  let v=[...Array(n).fill(a),-b,...Array(n-1).fill(-a),-(a-b)],z=grid(v,a);
  cases++;checks+=z.checks;best+=z.m;disp+=z.disp;if(z.m===z.M0)perfect++;
 }
 return {cases,checks,perfect,best,disp};
}
console.log(JSON.stringify({actual:audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),independent:independent()},null,2));
