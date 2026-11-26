// Last-up laminar transport, weighted open inventory and branching-loss audit.
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
   let st={X,focus,N:tags.length,events,Y,L,K,edges:0,allMass:0,splitLoss:0,mergeLoss:0,removed:0,selected:0,M:0,G:0,nested:0,noncross:0,allOpenMax:0,selectedOpenMax:0,selectedDepthMax:0,inventoryChecks:0,baselineChecks:0,residualVariation:0,relayChecks:0,weightedRelay:0,weightedRelayCap:0,inverseChecks:0,inverseSum:0,quadraticChecks:0,impurityChecks:0,tagWithSelected:0,rawSlack3:0,selectedSlack3:0,lowerBound:0};
   for(let tag of tags){
    let path=tag.path,G=path.reduce((v,e)=>v+e.g,0),last=new Map(),edges=new Map();
    let eligible=e=>e.p>=Y&&e.p<=K*Y,bin=e=>Math.floor((e.C-tag.C0)/L);
    for(let e of path){
     if(e.dp>e.d){for(let a=Math.max(6,e.d);a<e.dp;a++)last.set(a,e.j)}
     else if(e.dp<e.d)for(let a=Math.max(6,e.dp);a<e.d;a++){
      let j=last.get(a);last.delete(a);if(j===undefined)continue;let s=path[j];
      if(!eligible(s)||!eligible(e)||bin(s)!==bin(e))continue;
      let key=j+"/"+e.j,z=edges.get(key)||{s,t:e,m:0,levels:[]};z.m++;z.levels.push(a);edges.set(key,z)
     }
    }
    let all=[...edges.values()],M0=all.reduce((v,z)=>v+z.m,0),su=new Map(),td=new Map(),sbest=new Map(),tbest=new Map();
    for(let z of all){let {s,t,m}=z;su.set(s.j,(su.get(s.j)||0)+m);td.set(t.j,(td.get(t.j)||0)+m);
     if(!sbest.has(s.j)||sbest.get(s.j).m<m)sbest.set(s.j,z);
     if(!tbest.has(t.j)||tbest.get(t.j).m<m)tbest.set(t.j,z);
     ok(z.levels.every(a=>a>=Math.max(6,s.d,t.dp)&&a<Math.min(s.dp,t.d)),"actual edge levels");
    }
    for(let [j,m] of su)ok(m<=path[j].dp-path[j].d,"source capacity");
    for(let [j,m] of td)ok(m<=path[j].d-path[j].dp,"target capacity");
    let Iu=M0-[...sbest.values()].reduce((v,z)=>v+z.m,0),Id=M0-[...tbest.values()].reduce((v,z)=>v+z.m,0);
    let sel=all.filter(z=>sbest.get(z.s.j)===z&&tbest.get(z.t.j)===z),M=sel.reduce((v,z)=>v+z.m,0),loss=M0-M;
    ok(loss<=Iu+Id&&Iu>=0&&Id>=0,"mutual largest edge union bound");
    // Noncrossing property of actual chronological level matches, including split/merge endpoints.
    for(let i=0;i<all.length;i++)for(let j=i+1;j<all.length;j++){
     let a=all[i],b=all[j];if(a.s.j>b.s.j)[a,b]=[b,a];
     ok(!(a.s.j<b.s.j&&b.s.j<a.t.j&&a.t.j<b.t.j),"no strictly crossing last-up arcs");st.noncross++;
    }
    let inv0=0,P0=0,start0=new Map(),end0=new Map(),start=new Map(),end=new Map();
    for(let [j,m] of su)start0.set(j,m);for(let [j,m] of td)end0.set(j,m);
    for(let z of sel){ok(!start.has(z.s.j)&&!end.has(z.t.j),"unique selected endpoints");start.set(z.s.j,z);end.set(z.t.j,z)}
    let Gu=sel.reduce((v,z)=>v+z.s.g,0),Gd=sel.reduce((v,z)=>v+z.t.g,0),n=sel.length,Go=G-Gu-Gd,A=3*Gu+4*n-M,D=Gd-M,Delta=A/3+D+Go,raw=G-4*M/3;
    ok(A>=0&&D>=2*n&&Go>=0&&raw+1e-7>=Delta/3&&M<=G,"selected slack");
    let O=0,P=0,base=6,open=new Set(),maxDepth=0,res=[],before=[],after=[],weightedCap=0,TV=0;
    for(let e of path){
     before[e.j]=O;ok(base===e.d-O,"inventory baseline pre");
     inv0+=(start0.get(e.j)||0)-(end0.get(e.j)||0);P0=Math.max(P0,inv0);ok(inv0>=0&&inv0<=Math.max(0,e.dp-6),"all open units actual distinct heights");
     let dz=e.dp-e.d,zs=start.get(e.j),zt=end.get(e.j);
     let W=[...open].filter(z=>z!==zt).reduce((v,z)=>v+z.m/z.s.p,0);
     if(zs){O+=zs.m;open.add(zs);dz-=zs.m}
     if(zt){ok(open.has(zt),"actual open selected target");O-=zt.m;open.delete(zt);dz+=zt.m}
     res[e.j]=dz;base+=dz;after[e.j]=O;TV+=Math.abs(dz);weightedCap+=W*Math.abs(dz);P=Math.max(P,O);maxDepth=Math.max(maxDepth,open.size);
     ok(O>=0&&O<=inv0&&base===e.dp-O&&base<=6+5*Delta+1e-7,"inventory residual post and baseline");st.inventoryChecks++;st.baselineChecks++;
    }
    ok(inv0===0&&O===0&&open.size===0&&TV<=A+D+5*Go+1e-7&&TV<=5*Delta+1e-7&&weightedCap<=P/Y*TV+1e-7,"residual variation and weighted overlap budget");
    let wr=0,inverse=0,ratio=0,wt=0,un=0;
    for(let z of sel){
     let {s,t,m}=z,p=s.p,r=t.p,h=(s.dp-6*s.I)/(2*p),k=(t.dp-6*t.I)/(2*r),relay=t.d-s.dp,c=-relay-1-2*t.w+6*(t.I-s.I),u=s.dp-s.d,v=t.d-t.dp;
     ok(Number.isInteger(h)&&Number.isInteger(k)&&h>=0&&k>=0&&2*h*p-(2*k+1)*r===c&&Math.abs(c)%2===1,"actual odd multiplier with signed relay");
     ok(after[s.j]===before[t.j]&&relay===res.slice(s.j+1,t.j).reduce((v,a)=>v+a,0),"nested relay baseline cancellation");
     ok(p<=(2*k+1)*Math.abs(r-3*p)+Math.abs(c),"odd parity obstruction");
     wr+=(m/p)*Math.abs(relay);inverse+=m/(2*k+1);ratio+=Math.abs(r-3*p);wt+=2*t.w;un+=Math.abs(u-v);
     if(sel.some(v=>s.j<v.s.j&&v.t.j<t.j))st.nested++;
     st.relayChecks++;st.inverseChecks++;
    }
    ok(un<=A+D&&ratio<=2*(A+D)+2*n&&wt<=D&&wr<=weightedCap+1e-7,"actual weighted relay and endpoint slacks");
    ok(inverse<=(42+5*P/Y)*Delta+1e-6,"weighted inverse budget");
    ok(M<=47*(1+P/Y)*Delta*(1+(6+5*Delta+P)/Y)+1e-6,"tag inventory quadratic");
    let f=Math.min(1/(1+P0/Y)**2,Math.sqrt(Y/((1+P0/Y)*H)));
    ok(raw+1e-7>=M*f/600&&G-4*M0/3+2*(Iu+Id)+1e-7>=M0*f/600,"selected and branching tradeoff");
    st.edges+=all.length;st.allMass+=M0;st.splitLoss+=Iu;st.mergeLoss+=Id;st.removed+=loss;st.selected+=n;st.M+=M;st.G+=G;st.allOpenMax=Math.max(st.allOpenMax,P0);st.selectedOpenMax=Math.max(st.selectedOpenMax,P);st.selectedDepthMax=Math.max(st.selectedDepthMax,maxDepth);st.residualVariation+=TV;st.weightedRelay+=wr;st.weightedRelayCap+=weightedCap;st.inverseSum+=inverse;st.quadraticChecks++;st.impurityChecks++;st.rawSlack3+=3*G-4*M0;st.selectedSlack3+=3*G-4*M;st.lowerBound+=M0*f/600;if(n)st.tagWithSelected++;
   }
   ok(st.allMass===st.M+st.removed&&st.removed<=st.splitLoss+st.mergeLoss&&st.weightedRelay<=st.weightedRelayCap+1e-5,"aggregate matching and residual ledgers");out.push(st)
  }
 }
 return out
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
