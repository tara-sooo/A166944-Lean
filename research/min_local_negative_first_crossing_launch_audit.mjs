// First-crossing synchronized launches, exact root lists and stationary residue/phase controls.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=2200000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let a=p*p;a<=N+2;a+=p)if(!spf[a])spf[a]=p;
 function fs(n){let f=[];while(n>1){let p=spf[n]||n;f.push(p);while(n%p===0)n/=p}return f}
 function next(a,n){let p=Infinity,w=Infinity,side=0,q=Infinity;for(let [d,s] of [[a+1,0],[a-1,2]])for(let r of fs(d)){q=Math.min(q,r);let t=mod((s===0?0:r+2)-n,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;side=s}}return {p,w,side,q}}
 function localHit(b,g){let d=g,h=3,t=0,par=mod(b/2,2),T=Math.floor(9*g/4+8);
  while(d>0&&t<T){let B=h+1,np=mod(B-par-d/2,2),f=Math.abs(np?2*B-5:2*B+1),p=1;for(let q of fs(f))if(mod(b+d+(np?-1:1),q)===0){p=q;break}d-=p-1;h=B-(p-1)/2;t++}
  return d===0?{t,h}:null
 }
 let out={roots:0,events:0,firstCrossings:0,completedByT:0,largeLaunchRoots:0,largeLaunchByT:0,roughChecks:0,stationaryKeyChecks:0,phaseChecks:0,sourceControls:0,localOffsetChecks:0,exactRootListChecks:0,exactTimedListChecks:0,canonicalResetChecks:0,staticCertificateControls:0,staticResidueChecks:0,staticProductChecks:0,convolutionControls:0,convolutionMarginalChecks:0,rows:[],static:[]};
 for(let R of [12000,48000,192000,480000,1000000])for(let J of [6,12,24,48,96]){
  let T=Math.ceil(8*Math.sqrt(2*R+1)),Y=64*(J+1),Z=2*Math.floor(9*J/4+8)+7,lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),keys=new Map(),row={R,J,T,Y,roots:0,first:0,byT:0,launch:0,launchByT:0,short:0,long:0,shortByT:0,canonical:0,canonicalByT:0,launchEnergy:0,launchEnergyByT:0,stoppedGainSum:0,fullGainSum:0,launchGainSum:0,maxLaunchMass:0,largeBands:{}};
  for(let A=lo;A<=hi;A+=6){let a=A,n=3-A/2,h=3,first=null,GT=0;
   for(;;){let e=next(a,n),G=A-a,newG=G+e.p-1,t=n+e.w-(3-A/2);
    if(!first&&newG>J){first={a,n,h,G,t,...e};out.firstCrossings++;row.first++;
     ck(G<=J&&h<=11+7*G/4+1e-9,"pre gain");
     if(t<=T){row.byT++;out.completedByT++;row.stoppedGainSum+=newG}else row.stoppedGainSum+=G;
     if(e.p>=Y){
      out.largeLaunchRoots++;row.launch++;if(t<=T){out.largeLaunchByT++;row.launchByT++;row.launchGainSum+=e.p-1}
      ck(e.w>=e.p/4&&e.q>=e.p/8&&e.q>Z&&a%6===0,"rough synchronized source");out.roughChecks++;
      let c=next(a,3-a/2),height=3+c.w;
      ck(c.p===e.p&&c.side===e.side&&height===h+e.w&&t===height+G/2-3,"same stationary key");out.stationaryKeyChecks++;
      let short=mod(e.p,4)===mod(a+1,4),post=height-(e.p-1)/2;
      ck(post===(e.side===0?0:3)+(short?0:e.p),"phase");out.phaseChecks++;
      if(short){row.short++;if(t<=T)row.shortByT++}else row.long++;
      if(short&&e.side===2&&e.p%3===1){ck(post===3&&(a-e.p+1)%12===0,"canonical reset");row.canonical++;if(t<=T)row.canonicalByT++;out.canonicalResetChecks++}
      let rec=keys.get(a)||{a,p:e.p,height,all:[],timed:[]};ck(rec.p===e.p&&rec.height===height,"one source one key");rec.all.push(A);if(t<=T)rec.timed.push(A);keys.set(a,rec);
     }
    }
    if(t>T&&first)break;if(t<=T)GT=newG;if(a-e.p+1<=0)break;
    a-=e.p-1;n+=e.w;h+=e.w-(e.p-1)/2;out.events++;
   }
   ck(first!==null,"cross exists");row.fullGainSum+=GT;row.roots++;out.roots++;
  }
  for(let [a,r] of keys){let roots=[],timed=[];
   for(let g=0;g<=J;g+=6){let A=a+g;if(A<lo||A>hi)continue;let hit=localHit(a,g);out.localOffsetChecks++;if(hit){ck(hit.h<r.height&&hit.h<=11+7*g/4+1e-9,"arrive before clock");roots.push(A);if(r.height+g/2-3<=T)timed.push(A)}}
   ck(JSON.stringify(roots)===JSON.stringify(r.all),{a,R,J,roots,actual:r.all});out.exactRootListChecks++;
   ck(JSON.stringify(timed)===JSON.stringify(r.timed),"exact timed roots");out.exactTimedListChecks++;
   row.launchEnergy+=roots.length**2;row.launchEnergyByT+=timed.length**2;row.maxLaunchMass=Math.max(row.maxLaunchMass,roots.length);out.sourceControls++;
   let band=Math.floor(Math.log2(r.p)),d=row.largeBands[band]||[0,0,0,0];d[0]+=roots.length;d[1]+=timed.length;d[2]+=roots.length**2;d[3]+=timed.length**2;row.largeBands[band]=d;
  }
  row.meanStoppedGain=row.stoppedGainSum/row.roots;row.meanFullGain=row.fullGainSum/row.roots;out.rows.push(row)
 }
 const pr=[];for(let p=3;p<=20000;p+=2)if(!spf[p])pr.push(p);
 function clock(q,s,par){let x=s===0?(q-1)/2:(q+1)/2;if(mod(x,2)!==par)x+=q;let c=s===0?0:q+2;return 3+(mod(x+c-3,2*q)||2*q)}
 for(let p of [449,769,1601,3203]){ck(!spf[p],"control prime");for(let par of [0,1])for(let side of [0,2]){
   let H=clock(p,side,par),prod=1,V=1,small=0;ck(H===((p-1)/2+(side===2?3:0)+(mod(p,4)===mod(2*par+1,4)?0:p)),"formula static");
   for(let q of pr){if(q>4*p+20)break;if(q===p||q===3)continue;let nu=0;
    for(let s of [0,2]){let h=clock(q,s,par),bad=h<H||h===H&&q<p;nu+=+bad;let x=s===0?(q-1)/2:(q+1)/2;if(mod(x,2)!==par)x+=q;let hh=4;while(mod(hh-x-(s===0?0:q+2),2*q)!==0)hh++;ck(hh===h,"clock scan");out.staticResidueChecks++}
    if(q<=p/8){ck(nu===2,"rough guaranteed");small++}if(q>2*H+1)ck(nu===0,"finite height cutoff");prod*=1-nu/q;if(q<=p)V*=1-2/q;
   }
   out.staticCertificateControls++;out.staticProductChecks++;out.static.push({p,par,side,H,short:H<p,prod,V,ratio:prod/V,small});
  }}
 for(let Q of [[5],[7],[5,7],[5,7,11]]){
  let M=Q.reduce((x,y)=>x*y,1),units=[],src=[],den=0,output=new Float64Array(M);
  for(let x=0;x<M;x++){if(Q.every(q=>x%q!==0))units.push(x);if(Q.every(q=>x%q!==1&&x%q!==q-1)){let w=1+mod(x*x+3*x+1,17);src.push([x,w]);den+=w}}
  for(let [a,w] of src)for(let p of units)output[mod(a-p+1,M)]+=w;
  for(let q of Q)for(let r=0;r<q;r++){let lhs=0,S=0;for(let x=0;x<M;x++)if(x%q===r)lhs+=output[x];for(let [a,w] of src)if(a%q===mod(r-1,q))S+=w;ck(lhs*(q-1)===(den-S)*units.length,"marginal convolution");out.convolutionMarginalChecks++}
  let tv=0;for(let x of output)tv+=Math.abs(x/(den*units.length)-1/M)/2;ck(tv<=Q.reduce((s,q)=>s+1/q,0)+1e-12,"TV mixing");out.convolutionControls++;
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
