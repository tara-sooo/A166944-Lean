// Dwell-time capacity, gain-distribution packing, variable barrier initial-cell time.
// node research/min_local_negative_dwell_gain_capacity_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+5),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){const out=[];while(n>1){let p=spf[n]||n;out.push(p);while(n%p===0)n/=p}return out}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},add=(m,k,v=1)=>m.set(k,(m.get(k)||0)+v);
 const q=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1);
 let sets=[{z:3,K:1,B:[0]}],K=1,B=[0];
 for(let p of [5,7,11,13,17,19]){
  let C=[];for(let b of B)for(let j=0;j<p;j++){let k=b+j*K;if(mod(-3*k,p)<=(p-3)/2)C.push(k)}K*=p;B=C.sort((a,b)=>a-b);sets.push({z:p,K,B});
 }
 function cell(a,s){let t=a/6,k=Math.floor(t/s.K),u=t-k*s.K,l=0,r=s.B.length;while(l<r){let m=(l+r)>>1;if(s.B[m]<=u)l=m+1;else r=m}return [6*(k*s.K+(l?s.B[l-1]:s.B.at(-1)-s.K)),6*(k*s.K+(l<s.B.length?s.B[l]:s.K+s.B[0]))]}
 const rows=[];
 for(let R of Rs){
  const S=Math.sqrt(2*R+1),T=Math.ceil(S),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
  const left=2*Math.ceil((lo-2*T-6)/2),t=a=>Math.min(1,2*q(a)/T);
  const tab=[{name:"all visits",map:new Map(),tot:0,log:0,half:0,first:0,cap:0,bad:0,twin:0},{name:"terminal",map:new Map(),tot:0,log:0,half:0,first:0,cap:0,bad:0,twin:0}];
  const ds=[0,6,12,24,48,96,192,384,768,1536,3072,6144,12288].filter(d=>d<=2*T+6);
  let grid=tab.map(()=>ds.map(d=>({d,all:0,bad:0}))),events=0,segments=0,checks=0,nearSq=0;
  let cs=R===480000||R===2000000?sets.map(s=>({s,pre:0,exit:0,noExit:0,exitLabel:0,cap:0,badCap:0,allCap2:0,badCap2:0,twinCap:0,tm:new Map(),badTm:new Map(),end:new Map(),left:cell(left,s)[0],right:cell(hi,s)[1]})):[];
  function record(k,x,g,w){
   if(!w)return;
   const a=tab[k],v=a.map.get(x)||{m:0,log:0,half:0,first:0},h=1+g/6,l=Math.log(h),b=Math.sqrt(h);
   ck(w<=t(x)+1e-10,"dwell cap");v.m+=w;v.log+=w*l;v.half+=w*b;v.first+=w*h;a.map.set(x,v);a.tot+=w;a.log+=w*l;a.half+=w*b;a.first+=w*h;
   for(let d of grid[k])if(g<=d.d){d.all+=w;if(q(x)<=S)d.bad+=w;}
   if(q(x)<=S)a.bad+=w;else a.twin+=w;
  }
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,birth=n,end=n+T,seen=0,cv=cs.map(c=>{let [l,r]=cell(A,c.s);return {c,l,r,done:false}});
   for(;;){
    let e=next(a,n),fire=n+e.w,last=fire>end,dt=Math.min(fire,end)-n;
    if(dt>0){let w=dt/T;record(0,a,A-a,w);if(last)record(1,a,A-a,w);segments++;seen+=dt}
    for(let v of cv){
     if(a>=v.l&&a<v.r)v.c.pre+=dt/T;
     if(!v.done){
      if(last){v.c.noExit++;v.done=true}
      else if(a-e.p+1<v.l){
       v.c.exit++;v.c.exitLabel+=e.p;v.done=true;
       ck(e.p>v.c.s.z&&fire-birth>=(e.p-1)/2-3,"exit label and age");checks++;
      }
     }
    }
    if(last)break;
    a-=e.p-1;n=fire;events++;
   }
   ck(seen===T&&A-a<=2*T+6,"own elapsed horizon");checks++;
   for(let c of cs){let [l]=cell(a,c.s);add(c.end,l)}
  }
  let cap=0,cap2=0,badCap=0,badCap2=0,twinCount=0;
  for(let a=left;a<=hi;a+=2){
   let v=t(a),r=q(a),bad=r<=S;cap+=v;cap2+=v*v;if(bad){badCap+=v;badCap2+=v*v}else twinCount++;
   if(bad&&r>=R**.4){
    let n=(a-1)%r===0?a-1:a+1;ck(n%r===0,"least-factor choice");let u=n/r;ck(u>=r&&fs(u).length===1&&(spf[u]||u)===u,"balanced semiprime");nearSq++;
   }
   for(let c of cs){
    let [l,h]=cell(a,c.s),M=(h-l)/6;c.cap+=M*v;c.allCap2+=M*v*v;c.tm.set(l,Math.max(c.tm.get(l)||0,v));
    if(bad){c.badCap+=M*v;c.badCap2+=M*v*v;c.badTm.set(l,Math.max(c.badTm.get(l)||0,v))}else c.twinCap+=M;
   }
  }
  for(let k=0;k<tab.length;k++){
   let a=tab[k],used=0,badUsed=0;
   for(let [x,v] of a.map){let c=t(x),m=v.m;used+=c;if(q(x)<=S)badUsed+=c;
    ck(v.first+1e-7>=m*m/(2*c)&&v.half+1e-7>=m**1.5/(1.5*Math.sqrt(c))&&v.log+1e-7>=m*Math.log(m/c)-m,"weighted per-center gain packing");checks++;
   }
   const req1=a.tot*a.tot/(2*a.first),reqHalf=(a.tot**1.5/(1.5*a.half))**2,reqLog=a.tot*Math.exp(-a.log/a.tot-1);
   ck(Math.max(req1,reqHalf,reqLog)<=used+1e-6,"global gain packing");
   for(let d of grid[k]){
    let m=1+Math.floor(d.d/6);ck(d.all<=m*used+1e-7*N&&d.bad<=m*badUsed+1e-7*N,"gain CDF packing");
    d.req=d.all/m;d.frac=d.all/N;d.badFrac=d.bad/N;checks++;
   }
   let best=grid[k].reduce((u,v)=>u.req>v.req?u:v);
   a.out={name:a.name,fraction:a.tot/N,badFraction:a.bad/N,twinFraction:a.twin/N,conditionalMeanGain:6*(a.first/a.tot-1),conditionalLogGamma:a.log/a.tot,conditionalHalfGamma:a.half/a.tot,req1,reqHalf,reqLog,bestCut:best,used,badUsed,badCap,cap,controls:grid[k]};
  }
  ck(Math.abs(tab[0].tot-N)<=1e-6*N,"all time conserved");
  let cellRows=[];
  for(let c of cs){
   let total=0,chi=0,P2=0,badP2=0,sumM=0;
   for(let l=c.left;l<c.right;){
    let [b,h]=cell(l,c.s),M=(h-l)/6;ck(b===l,"cell iteration");
    let a=Math.max(0,Math.min(hi,h-6)-Math.max(lo,l)+6)/6,m=c.end.get(l)||0,d=m-a;ck(M+d>=0,"ghost mass");
    total+=M;chi+=d*d/M;P2+=M*(c.tm.get(l)||0)**2;badP2+=M*(c.badTm.get(l)||0)**2;sumM+=M*M;l=h;checks++;
   }
   const theta=tab[1].tot/N,X=chi/total,terminalBound2=total/N**2*(1+X)*P2;
   ck(c.pre<=c.cap+1e-6*N&&P2<=c.allCap2+1e-6*N&&badP2<=c.badCap2+1e-6*N,"weighted cell capacity");
   ck(theta*theta<=terminalBound2+1e-8,"terminal chi-square inequality");
   // At elapsed T the monotone root either leaves its initial cell or stays.
   ck(c.exit+c.noExit===N,"exit partition");
   let meanPeriodM=0;for(let i=0;i<c.s.B.length;i++){let g=(i===c.s.B.length-1?c.s.B[0]+c.s.K:c.s.B[i+1])-c.s.B[i];meanPeriodM+=g*g/c.s.K}
   cellRows.push({z:c.s.z,K:c.s.K,meanPeriodM,pre:c.pre/N,exit:c.exit/N,noExit:c.noExit/N,meanExitLabel:c.exitLabel/Math.max(1,c.exit),X,theta,terminalBound2,terminalBadBound2:total/N**2*(1+X)*badP2,weightedCap:c.cap,weightedBadCap:c.badCap,weightedBadCap2:c.badCap2,weightedTwinCap:c.twinCap});
  }
  rows.push({R,N,T,events,segments,checks,nearSq,twinCount,cap,badCap,cap2,badCap2,stats:tab.map(a=>a.out),cells:cellRows});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000,1000000,2000000]),null,2));
