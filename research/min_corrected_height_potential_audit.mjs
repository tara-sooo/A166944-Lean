// Exact corrected-height potential and admissible high-clock envelope.
function potentialAudit(Y){
 const ps=[];for(let p=3;p<Y;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const L=2*ps.reduce((a,b)=>a*b,1),N=L/2,states=N*L;
 if(L>2310)throw Error("finite exact cap");
 const D=new Uint16Array((N+1)*L),U=new Int16Array(states),gap=new Uint16Array(states),R=new Uint16Array(N),B0=new Int16Array(states);
 const ck=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 let sum=0,mx=0,neg=0,zero=0,tie=0,maxRowMean=0;
 for(let i=N-1;i>=0;i--){
  let C=2*i,eligible=ps.filter(p=>(C-1)%p===0||(C+1)%p===0);if(!eligible.length){zero+=L;continue}
  R[i]=eligible[0];let rowmax=0;
  for(let t=0;t<L;t++){
   let w=L+1,p0=0,g=L;
   for(let p of eligible){let ph=(C-1)%p===0?0:p+2,back=mod(t-ph,2*p),forward=2*p-back;if(forward<w||(forward===w&&p<p0)){w=forward;p0=p}g=Math.min(g,back)}
   let k=i*L+t,u=2*w-(p0-1)+D[(i+(p0-1)/2)*L+(t+w)%L],v=Math.max(0,u);
   U[k]=u;D[k]=v;gap[k]=g;B0[k]=Math.min(2*g,-u);sum+=v;mx=Math.max(mx,v);rowmax=Math.max(rowmax,v);if(u<0)neg++;if(!g)tie++;
  }maxRowMean+=rowmax;
 }
 const histogram=new Uint32Array(mx+1);for(let i=0;i<states;i++)histogram[D[i]]++;
 let prime=[];for(let q=Y;q<=mx+Y;q++){if(q<2)continue;let ok=true;for(let d=2;d*d<=q;d++)if(q%d===0){ok=false;break}if(ok)prime.push(q)}
 let gamma=0,gammaTail=0,gammaRaw=0,gammaLow=0,gammaNone=0,checks=0,details=[];
 for(let q of prime){
  let exact=0,tail=0,raw=0,lo=0,none=0,nonzero=0,shift=(q-1)/2;
  for(let d=q;d<=mx;d++)tail+=(d-q+1)*histogram[d];
  // Include d=q-1 with zero weight.
  for(let i=0;i<N;i++){let j=(i+shift)%N,rr=R[i],base=i*L,post=j*L;
   for(let t=0;t<L;t++){let k=base+t,after=D[post+t],v=0,vraw=0;
    if(!rr){v=Math.max(0,after-q+1);none+=v;vraw=v}
    else if(gap[k]){vraw=Math.max(0,after-q+1+B0[k]);v=Math.max(0,vraw-4*rr);lo+=v;
     if(Y<=7||((k+q*1237)%997===0)){
      let best=0;
      for(let w=1;w<=gap[k];w++){let prior=D[base+mod(t-w,L)];ck(prior===Math.max(0,U[k]+2*w),"unclipped shift");best=Math.max(best,2*w-(q-1)+after-prior);}
      ck(best===vraw,"max wait envelope");checks++;
     }
    }
    ck(v<=Math.max(0,after-q+1),"tail domination");exact+=v;raw+=vraw;if(v)nonzero++;
   }
  }
  ck(exact===lo+none&&exact<=tail,"sum bound");gamma+=exact/states/q**2;gammaTail+=tail/states/q**2;gammaRaw+=raw/states/q**2;gammaLow+=lo/states/q**2;gammaNone+=none/states/q**2;
  if(exact||raw||tail)details.push({q,mean:exact/states,tailMean:tail/states,rawMean:raw/states,nonzero:nonzero/states});
 }
 return {Y,L,states,mean:sum/states,max:mx,maxPhaseMean:maxRowMean/N,oldRatio:sum/states/(Y*Math.log(Y)),gamma,gammaTail,gammaRaw,gammaLow,gammaNone,negativeU:neg/states,noLow:zero/states,tie:tie/states,checks,details};
}
for(const Y of process.argv.slice(2).map(Number)) console.log(JSON.stringify(potentialAudit(Y)));
