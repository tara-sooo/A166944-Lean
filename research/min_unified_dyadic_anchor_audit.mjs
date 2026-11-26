// Closed inventory excursions: dyadic rank descent or signed capacity imbalance.
function v2(n){let k=0;while(n%2===0){n/=2;k++}return k}
function gcd(a,b){return b?gcd(b,a%b):a}
function anchor(labels,D,W){
 // Exact interval sweep over all possible coefficients of the first endpoint.
 for(let c=1;c<=D;c++){
  let lo=(labels[0]-W)/c,hi=(labels[0]+W)/c;
  if(hi<=0)continue;
  let cand=[lo,hi];
  for(let p of labels)for(let b=1;b<=D;b++)for(let z of [(p-W)/b,(p+W)/b])if(z>=lo&&z<=hi)cand.push(z);
  for(let Z of cand)if(Z>0){let cs=labels.map(p=>Math.max(1,Math.min(D,Math.round(p/Z))));
   if(labels.every((p,i)=>Math.abs(p-cs[i]*Z)<=W+1e-8))return {Z,cs};
  }
 }
 return null
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
   let st={X,focus,N:tags.length,events,Y,L,K,tags:0,edges:0,M:0,endpointN:0,sourceN:0,targetN:0,splitSources:0,mergeTargets:0,transitions:0,upUp:0,upDown:0,downUp:0,downDown:0,oddChecks:0,baselineChecks:0,excursions:0,excursionChecks:0,relationChecks:0,relationBoundChecks:0,nontrivialBounds:0,sameLabel:0,oddRational:0,rawNegative:0,adjusted:0,maxInventory:0,lower:0,controls:[],anchorControls:0,anchorExc:0,anchorMass:0,anchorEnds:0,dyadicEdges:0,dyadicAsc:0,dyadicNonasc:0,strictExc:0,strictMass:0,strictImbalance:0,strictPositive:0,strictSimple:0,dyadicIdentity:0,dyadicBound:0,dyadicCombined:0,dyadicMacroEligible:0,dyadicLower:0,dyadicSplitExc:0};
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
    // Retain actual whole zero-inventory excursions; no edge pruned or reweighted.
    let trMap=new Map(trs.map(z=>[z.s.j+"/"+z.t.j,z]));
    for(let Dstar of [2,4,8])for(let W0 of [0,1,Math.max(2,Math.floor(Y/16))]){
     let R=1+Math.floor(Math.log2(Dstar)),W=2*Dstar*W0,Ck=3*K+1,J=0,Mg=0,strictSlack=0,certCost=0,certErr=0,strictN=0,strictLower=0,nonascN=0;
     for(let ex of exs){
      let hit=anchor(ex.map(e=>e.p),Dstar,W0);if(!hit)continue;let {Z,cs}=hit;
      let m=ex.reduce((v,e)=>v+Math.max(0,jumps[e.j]),0),n=ex.length,As=0,Ds=0,T=0,localJ=0,asc=0;
      for(let i=0;i<n;i++){let e=ex[i],sg=jumps[e.j]>0?3:-1;T+=sg*cs[i];if(sg===3)As+=3*e.p+1-jumps[e.j];else Ds+=e.p-1+jumps[e.j];}
      ok(As>=0&&Ds>=0&&Math.abs(As-Ds-Z*T-n)<=3*n*W0+1e-7,"closed signed capacity balance");
      ok(Z+1e-7>=(Y-W0)/Dstar&&m<=Ck*Y*n,"anchor and mass count");
      for(let i=1;i<n;i++){
       let g=gcd(cs[i-1],cs[i]),a=cs[i]/g,b=cs[i-1]/g,z=trMap.get(ex[i-1].j+"/"+ex[i].j);
       ok(z&&Math.abs(a*z.p-b*z.q)<=W+1e-7,"actual adjacent rational anchor");
       if(v2(cs[i])>v2(cs[i-1])){ok(a%2===0&&b%2===1,"dyadic ascent");asc++;continue}
       ok(a%2===1,"nonascending reduced numerator odd");
       let ell=a*z.p-b*z.q,v=2*z.h*b-(2*z.k+z.sg)*a;
       ok(Math.abs(v)%2===1&&v*z.q===a*z.c-2*z.h*ell&&z.q<=a*Math.abs(z.c)+2*z.h*Math.abs(ell),"nonascending odd determinant");
       localJ++;certCost+=Math.abs(z.c);certErr+=2*z.h*Math.abs(ell);st.dyadicIdentity++;
      }
      ok(n<=R*(localJ+1)&&localJ+asc===n-1,"bounded strict dyadic runs");
      if(localJ){ok(n<=2*R*localJ,"nonascending count charge");nonascN+=n}
      else{
       ok(T!==0&&Math.abs(T)%2**v2(cs[0])===0&&Math.abs(T/2**v2(cs[0]))%2===1,"unique minimal dyadic term");
       let l=Math.max(0,(Y-W0)/Dstar-n*(3*W0+1));
       ok(As+Ds+1e-7>=l,"strict excursion imbalance lower");strictSlack+=As+Ds;strictN+=n;strictLower+=l;
       st.strictExc++;st.strictMass+=m;st.strictImbalance+=As+Ds;if(l>0)st.strictPositive++;
       if((Y-W0)/Dstar-R*(3*W0+1)>=Y/(2*Dstar)){ok(As+Ds+1e-7>=Y/(2*Dstar),"uniform strict imbalance");st.strictSimple++}
      }
      J+=localJ;Mg+=m;st.anchorExc++;st.anchorMass+=m;st.anchorEnds+=n;st.dyadicEdges+=n-1;st.dyadicAsc+=asc;st.dyadicNonasc+=localJ;if(ex.some(e=>(outdeg.get(e.j)||0)>1||(indeg.get(e.j)||0)>1))st.dyadicSplitExc++;
     }
     ok(strictSlack<=A+Dn+1e-7&&strictLower<=strictSlack+1e-7&&nonascN<=2*R*J,"disjoint excursion slack");
     ok(J*Y<=Dstar*certCost+certErr+1e-7&&certCost<=5*Delta+7*J+1e-7&&certErr<=J*W*(6+5*Delta+P)/Y+1e-7,"dyadic subset determinant budget");
     let l=J*Math.max(0,Y-7*Dstar-W*(6+P)/Y)/(5*(Dstar+W*J/Y));
     ok(Delta+1e-7>=l,"exact dyadic adjusted lower");st.dyadicLower+=l;st.dyadicBound++;
     if((Y-W0)/Dstar-R*(3*W0+1)>=Y/(2*Dstar)){
      let Cstar=6*Ck*Dstar*R;
      ok(Mg<=Cstar*(Y*J+Delta)+1e-7,"mass versus odd transition or imbalance");st.dyadicCombined++;
      if(Y>=28*Dstar&&W*(6+P)<=Y*Y/4){
       let lower=Mg/(Cstar*(1+10*Dstar+10*W*H/(Y*(Y-1))));
       ok(Delta+1e-7>=lower,"combined per-tag saturation lower");st.dyadicMacroEligible++;
      }
     }
     st.anchorControls++;
    }
    st.tags++;st.edges+=edges.size;st.M+=M;st.endpointN+=ep.length;st.sourceN+=sources.length;st.targetN+=targets.length;st.splitSources+=[...outdeg.values()].filter(x=>x>1).length;st.mergeTargets+=[...indeg.values()].filter(x=>x>1).length;st.transitions+=trs.length;st.excursions+=exs.length;st.adjusted+=Delta;st.maxInventory=Math.max(st.maxInventory,P);if(G-4*M/3<0)st.rawNegative++;
   }
   st.controls=controls;ok(st.transitions===st.upUp+st.upDown+st.downUp+st.downDown&&st.transitions===st.endpointN-st.tags,"aggregate transitions");out.push(st)
  }
 }
 return out
}
function independent(){
 let cases=0,strict=0,strictOdd=0,closed=0,nonasc=0,maxRun=0;
 for(let D of [2,4,8,12])for(let n=2;n<=5;n++){
  let cs=[];
  function visit(){
   if(cs.length<n){for(let c=1;c<=D;c++){cs.push(c);visit();cs.pop()}return}
   let J=0;for(let i=1;i<n;i++)if(v2(cs[i])<=v2(cs[i-1]))J++;
   let R=1+Math.floor(Math.log2(D));if(n>R*(J+1))throw Error("abstract dyadic run");cases++;
   if(J){nonasc++;return}
   strict++;maxRun=Math.max(maxRun,n);
   for(let mask=1;mask<(1<<n)-1;mask++){let T=cs.reduce((v,c,i)=>v+((mask>>i)&1?3:-1)*c,0);
    if(T===0||Math.abs(T/2**v2(cs[0]))%2!==1)throw Error("abstract strict imbalance");strictOdd++}
  }visit()
 }
 // Exact capacity-balanced integer coefficient words, including even coefficients.
 for(let D of [3,6,9])for(let a=1;a<=D;a++)for(let b=1;b<=D;b++)for(let c=1;c<=D;c++)for(let d=1;d<=D;d++){
  if(3*(a+b)!==c+d)continue;let cs=[a,b,c,d];if(cs.slice(1).every((v,i)=>v2(v)>v2(cs[i])))throw Error("balanced strict ascent");closed++
 }
 return {cases,strict,strictOdd,closed,nonasc,maxRun}
}
console.log(JSON.stringify({actual:audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),independent:independent()},null,2));
