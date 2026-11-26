// General original transport: consecutive endpoint odd-ratio obstruction, without pruning.
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
   let st={X,focus,N:tags.length,events,Y,L,K,tags:0,edges:0,M:0,endpointN:0,sourceN:0,targetN:0,splitSources:0,mergeTargets:0,transitions:0,upUp:0,upDown:0,downUp:0,downDown:0,oddChecks:0,baselineChecks:0,excursions:0,excursionChecks:0,relationChecks:0,relationBoundChecks:0,nontrivialBounds:0,sameLabel:0,oddRational:0,rawNegative:0,adjusted:0,maxInventory:0,lower:0,controls:[]};
   let controls=[];for(let D of [1,3,5])for(let W of [...new Set([0,2,Math.floor(Y/4)])])controls.push({D,W,J:0,bound:0,excMass:0,excJ:0,positive:0});
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
    let gcd=(a,b)=>b?gcd(b,a%b):a;
    for(let ctl of controls){let {D,W}=ctl,J=0,cost=0,err=0,good=new Set();
     for(let z of trs){let cert=null;outer:for(let a=1;a<=D;a+=2)for(let b=1;b<=D;b+=2)if(gcd(a,b)===1&&Math.abs(a*z.p-b*z.q)<=W){cert={a,b,ell:a*z.p-b*z.q};break outer}
      if(!cert)continue;let {a,b,ell}=cert,v=2*z.h*b-(2*z.k+z.sg)*a;
      ok(Math.abs(v)%2===1&&v*z.q===a*z.c-2*z.h*ell&&z.q<=a*Math.abs(z.c)+2*z.h*Math.abs(ell),"odd rational determinant");
      J++;cost+=Math.abs(z.c);err+=2*z.h*Math.abs(ell);good.add(z.s.j+"/"+z.t.j);st.relationChecks++;if(D===5&&W===Math.floor(Y/4))st.oddRational++;
     }
     ok(J*Y<=D*cost+err+1e-7&&cost<=5*Delta+7*J+1e-7&&err<=J*W*(6+5*Delta+P)/Y+1e-7,"general weighted odd budget");
     let lower=J*Math.max(0,Y-7*D-W*(6+P)/Y)/(5*(D+W*J/Y));
     ok(Delta+1e-7>=lower,"exact general adjusted loss");
     if(Y>=28*D&&W*(6+P)<=Y*Y/4){let l=J*Y/(10*(D+W*J/Y));ok(Delta+1e-7>=l,"simplified loss")}
     let excMass=0,excJ=0;
     for(let ex of exs){if(ex.slice(1).every((t,j)=>good.has(ex[j].j+"/"+t.j))){let m=ex.reduce((v,e)=>v+Math.max(0,jumps[e.j]),0);excMass+=m;excJ+=ex.length-1;ok((ex.length-1)*Y>=m/(3*K+1/Y)-1e-7,"complete good excursion count");st.excursionChecks++}}
     ctl.J+=J;ctl.bound+=lower;ctl.excMass+=excMass;ctl.excJ+=excJ;if(lower>0){ctl.positive++;st.nontrivialBounds++}st.relationBoundChecks++;st.lower+=lower;
    }
    st.tags++;st.edges+=edges.size;st.M+=M;st.endpointN+=ep.length;st.sourceN+=sources.length;st.targetN+=targets.length;st.splitSources+=[...outdeg.values()].filter(x=>x>1).length;st.mergeTargets+=[...indeg.values()].filter(x=>x>1).length;st.transitions+=trs.length;st.excursions+=exs.length;st.adjusted+=Delta;st.maxInventory=Math.max(st.maxInventory,P);if(G-4*M/3<0)st.rawNegative++;
   }
   st.controls=controls;ok(st.transitions===st.upUp+st.upDown+st.downUp+st.downDown&&st.transitions===st.endpointN-st.tags,"aggregate transitions");out.push(st)
  }
 }
 return out
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
