// Actual first-high product-strip rectangle and saturation prime-ratio ledger.
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
   let L=mode?Math.max(1,Math.floor(H/2)):H,K=6,b=Math.min(Y-4,Math.ceil(Math.log(Y)**2)),tol=Math.max(2,Math.floor(Y/Math.log(Y))),R=Math.max(1,Math.floor(L*Y/X));
   let st={X,focus,N:tags.length,events,Y,L,K,b,tol,R,bins:0,firstPairs:0,firstMass:0,lowTail:0,lowGain:0,lowChecks:0,sourceLabels:0,hyperbolaChecks:0,threeConditions:0,zeroProductCases:0,boxGroups:0,rectangles:0,boxCandidates:0,boxSurvivors:0,boxActual:0,boxMembership:0,directPairs:0,directMass:0,directGain:0,upGain:0,downGain:0,otherGain:0,delta3:0,ratioSum:0,ratioTailMass:0,nearMass:0,ratioChecks:0,lateSlack:0,waitSlack:0,matchChecks:0,disjointChecks:0,primeCheck:0};
   for(let tag of tags){
    let bins=new Map();for(let e of tag.path){let id=Math.floor((e.C-tag.C0)/L);if(!bins.has(id))bins.set(id,[]);bins.get(id).push(e)}
    for(let [bi,es] of bins){st.bins++;let lo=tag.C0+bi*L,hi=lo+L,G=es.reduce((s,e)=>s+e.g,0),high=es.filter(e=>e.p>=Y),low=es.filter(e=>e.p<Y).reduce((s,e)=>s+e.g,0),S=new Set(),groups=new Map(),pairs=[],lowUsed=0;
     for(let j=1;j<high.length;j++){let s=high[j-1],t=high[j],p=s.p,r=t.p;if(p>K*Y||r>K*Y||2*s.w<=s.g)continue;
      let relay=tag.path.slice(s.j+1,t.j),E=relay.reduce((v,e)=>v+e.g,0),V=relay.reduce((v,e)=>v+e.w,0),a=E+s.e-1-t.e,q=(s.C-s.e)/p,k=(t.C-t.e)/r,weight=s.dp-s.d;
      ok(relay.every(e=>e.p<Y)&&t.C-s.J===E&&V<=3*E&&r*k===p*(q+1)+a&&a%2!==0,"actual first pair clock/product");st.firstPairs++;st.firstMass+=weight;lowUsed+=E;S.add(p);
      if(E>b){st.lowTail+=weight;continue}
      ok(p!==r&&Math.abs(a)<p&&mod(r*k-a,p)===0,"nonzero hyperbola");st.hyperbolaChecks++;
      let primes=[];for(let f=5;f<Y&&4*f<p-1;f+=2)if(spf[f]===f){ok(mod(r,f)!==0&&mod(r*k-p-a,f)!==0&&mod(r*k-p-a+2*s.e,f)!==0,"three local exclusions");st.threeConditions++;if(mod(p+a,f)===0||mod(p+a-2*s.e,f)===0)st.zeroProductCases++;primes.push(f)}
      if(Math.abs(r-3*p)<=tol){let id=[p,s.I,t.I,E].join("/"),z=groups.get(id)||{p,e:s.e,f:t.e,E,a,primes,actual:[]};z.actual.push({r,k,C:s.C});groups.set(id,z)}
      if(t.dp<t.d){let u=s.dp-s.d,v=t.d-t.dp,upper=Math.min(s.dp,t.d,...relay.map(e=>e.dp)),lower=Math.max(6,s.d,t.dp),m=Math.max(0,upper-lower);
       ok(m<=Math.min(u,v)&&u===3*s.g+4-2*(2*p-s.w)&&v===t.g-2*t.w,"direct last-up overlap and endpoint slack");st.matchChecks++;
       if(m>0)pairs.push({s,t,m,u,v});
      }
     }
     ok(lowUsed<=low,"disjoint low relays");st.lowGain+=lowUsed;st.lowChecks++;st.sourceLabels+=S.size;
     // Exact finite cover of the curved cofactor strip by integer rectangles.
     // Restrict the target prime to the near-saturation ratio window.
     for(let z of groups.values()){let {p,e,f,E,a,primes,actual}=z,l=Math.max(Y,3*p-tol),h=Math.min(K*Y,B,3*p+tol),actualSeen=new Set(),surv=0;ok(l<=h,"nonempty ratio interval");st.boxGroups++;st.boxActual+=actual.length;
      for(let x=l;x<=h;x+=R){let y=Math.min(h,x+R-1),smin=Math.max(1,Math.floor((lo+p-1+E-f)/y)),smax=Math.ceil((hi+p-1+E-f)/x);
       ok(smax>=smin,"positive rectangle");st.rectangles++;
       for(let w of actual)if(w.r>=x&&w.r<=y){ok(w.k>=smin&&w.k<=smax,"actual product-strip membership");actualSeen.add(w.C);st.boxMembership++}
       for(let rr=x;rr<=y;rr++){if(rr%p===0)continue;for(let ss=smin;ss<=smax;ss++){if(mod(rr*ss-a,p))continue;st.boxCandidates++;if(primes.some(f0=>rr%f0===0||mod(rr*ss-p-a,f0)===0||mod(rr*ss-p-a+2*e,f0)===0))continue;surv++}}
      }
      ok(actualSeen.size===actual.length&&surv>=actual.length,"finite rectangle capacity");st.boxSurvivors+=surv;
     }
     if(pairs.length){let used=new Set(),M=0,Gu=0,Gd=0,u=0,v=0,ratio=0,late=0,wait=0,tail=0,near=0;
      for(let z of pairs){let {s,t,m}=z;ok(!used.has(s)&&!used.has(t),"disjoint direct pairs");used.add(s);used.add(t);M+=m;Gu+=s.g;Gd+=t.g;u+=z.u;v+=z.v;late+=2*(2*s.p-s.w);wait+=2*t.w;ratio+=Math.abs(t.p-3*s.p);if(Math.abs(t.p-3*s.p)>tol)tail+=m;else near+=m;ok(t.p-3*s.p===z.v-z.u+2-2*(2*s.p-s.w)+2*t.w,"exact prime ratio relation");st.ratioChecks++}
      let n=pairs.length,Go=G-Gu-Gd,A=3*Gu+4*n-M,D=Gd-M,d3=3*G-4*M+4*n;
      ok(Go>=0&&A>=0&&D>=0&&late<=A&&wait<=D&&ratio<=2*(A+D)+2*n&&ratio<=2*d3+2*n,"ratio slack inequality");
      ok(tail*tol<=(3*K*Y+1)*ratio&&tail+near===M,"weighted ratio tail");st.directPairs+=n;st.directMass+=M;st.directGain+=G;st.upGain+=Gu;st.downGain+=Gd;st.otherGain+=Go;st.delta3+=d3;st.ratioSum+=ratio;st.ratioTailMass+=tail;st.nearMass+=near;st.lateSlack+=late;st.waitSlack+=wait;st.disjointChecks++;
     }
    }
   }
   ok(st.lowGain<=tags.reduce((a,t)=>a+t.path.filter(e=>e.p<Y).reduce((a,e)=>a+e.g,0),0)&&st.directMass===st.nearMass+st.ratioTailMass&&st.ratioSum<=2*st.delta3+2*st.directPairs,"aggregate ledgers");
   out.push(st)
  }
 }
 // Exact local densities including zero forbidden product residues.
 let densities=0;for(let f of [5,7,11,13,17,19])for(let u=0;u<f;u++)for(let e of [-1,1]){
  let n=0;for(let r=0;r<f;r++)for(let s=0;s<f;s++)if(r===0||mod(r*s-u,f)===0||mod(r*s-u+2*e,f)===0)n++;
  ok(n===3*f-2,"exact three-condition density");densities++;
 }
 return {out,densities}
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
