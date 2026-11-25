// Canonical-gap weighted gain-target audit. Finite diagnostic parameters.
function audit(X,stress=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),H=T+B,Q=Math.max(5,Math.ceil(B/10)),amin=Math.max(4,Math.ceil(B/(stress?8:2))),lo=2*X-2,hi=7*X,lim=hi+B+20;
 const spf=new Int32Array(lim),r=new Int32Array(lim),fail=(b,s)=>{if(!b)throw Error(X+" "+s)},mod=(a,m)=>((a%m)+m)%m;
 function gcd(a,b){while(b){let c=a%b;a=b;b=c}return a}
 for(let p=2;p<lim;p++)if(!spf[p]){spf[p]=p;if(p*p<lim)for(let j=p*p;j<lim;j+=p)if(!spf[j])spf[j]=p}
 function factors(n){let a=[];while(n>1){let p=spf[n];if(p!==2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const labels=new Map();for(let C=lo;C<=hi;C+=2){let a=factors(C-1),b=factors(C+1);r[C]=Math.min(a[0]||B+1,b[0]||B+1);labels.set(C,[...a.map(p=>[p,-1]),...b.map(p=>[p,1])]);}
 const phase=(p,s)=>s===-1?0:p+2,high=(C,p)=>p>=Q&&r[C]>3&&2*r[C]>p;
 let N=0,events=0,raw=0,rawHigh=0,paidRaw=0,rawReset=0,rawCanonicalClock=0,canonicalPoints=0,virtual=0,arcs=0,longArcs=0,shortGapGain=0,longGapGain=0,targets=0,reached=0,unreached=0,rawWeighted=0,paidWeighted=0,remWeighted=0,highWeighted=0,resetWeighted=0,lowerSum=0,directChecks=0,tickChecks=0,maxTickWeight=0,weightedGapLength=0,wholeWeight=0,literal=0,rootTerminated=0,artificialGapTargets=0,completeGapTargets=0;
 for(let M=X;M<2*X;M++)if(spf[M]===M){
   N++;let t=M+2,C=2*M-2,C0=C,cut=Math.floor((7*M-1)/4),es=[],can=[{g:0,t}],wp=[0];
   while(C-C0<T){
     let v=Infinity,p=0,s=0;for(let [q,sg] of labels.get(C)){let j=t+1+mod(phase(q,sg)-t-1,2*q);if(j<v||(j===v&&q<p)){v=j;p=q;s=sg}}
     if(X<=1024){let vv=Infinity,pp=0;for(let j=t+1;j<=Math.min(cut,t+2*B);j++){let g=j%2?gcd(j-2,C+1):gcd(j,C-1),q=factors(g)[0];if(q){vv=j;pp=q;break}}fail((!p||v>cut)?vv===Infinity:vv===v&&pp===p,"literal MIN");literal++;}
     if(!p||v>cut)break;
     let J=C+p-1,w=v-t,k=(2*v-J-6*(v%2))/(2*p),hh=high(C,p);
     fail(w<=2*r[C]&&w<=3*(p-1)&&Number.isInteger(k)&&2*t>=C,"clock");
     let tc=C/2+3;if(C%4===0&&tc>=t&&tc<v&&tc>can[can.length-1].t){can.push({g:C-C0,t:tc});if(tc>t)virtual++;}
     let age=v-can[can.length-1].t,mark=w<=.2*(p-1)||(hh&&k===0&&age>p*2);
     es.push({g:C-C0,G:J-C0,t,v,w,p,high:hh,reset:k===0,mark});wp.push(wp[wp.length-1]+(mark?w:0));
     events++;raw+=w;if(hh){rawHigh+=w;if(k===0)rawReset+=w;}if(mark)paidRaw+=w;
     C=J;t=v;
     if(C%4===0&&2*t-C===6&&t>can[can.length-1].t)can.push({g:C-C0,t});
   }
   let endGain=C-C0,endTime=t;if(endGain<T)rootTerminated++;
   canonicalPoints+=can.length;
   for(let i=1;i<can.length;i++){fail(can[i].g>can[i-1].g&&2*(can[i].t-can[i-1].t)===can[i].g-can[i-1].g,"canonical neutral");arcs++;rawCanonicalClock+=can[i].t-can[i-1].t}
   const gaps=can.filter(c=>c.g<T);let weights=new Float64Array(T+1),pre=new Float64Array(T+1),ci=0,ei=0,startE=0,dr=0,dp=0,dh=0,dreset=0,localTargets=0,localGapGain=0;
   for(let i=0;i<gaps.length;i++){let c=gaps[i],end=i+1<gaps.length?gaps[i+1].g:T,L=end-c.g;fail(L>0,"gap partition");localGapGain+=L;
     if(L<amin){shortGapGain+=L;continue;}longArcs++;longGapGain+=L;weightedGapLength+=L;
     const first=c.g+Math.floor(L/2)+1;for(let x=first;x<=end;x++)weights[x]=1/(x-c.g);
   }
   fail(localGapGain===T,"target partition");
   for(let x=1;x<=T;x++)pre[x]=pre[x-1]+weights[x];
   for(let x=1;x<=T;x++)if(weights[x]){
     while(ci+1<gaps.length&&gaps[ci+1].g<x)ci++;
     let c=gaps[ci];while(ei<es.length&&es[ei].G<x)ei++;
     let last=ei<es.length?ei:es.length-1,et=last>=0?es[last].v:endTime,eg=last>=0?es[last].G:0;
     fail(c.t<=et&&c.g<x,"actual tail");
     let R=x-c.g,wait=et-c.t;fail(R>amin/2&&weights[x]===1/R,"relative half");
     if(eg>=x){reached++;fail(2*wait>=R-6,"reached lower");lowerSum+=.5-3/R;}else{unreached++;}
     if(ci+1<gaps.length)completeGapTargets++;else artificialGapTargets++;
     while(startE<es.length&&es[startE].v<=c.t)startE++;
     let paid=0,hs=0,rs=0;
     for(let j=startE;j<=last;j++){let a=es[j],w=a.v-Math.max(a.t,c.t);fail(w>=0,"tail overlap");if(a.mark)paid+=w;if(a.high){hs+=w;if(a.reset)rs+=w;}}
     fail(paid<=wait&&hs<=wait,"subledger");dr+=wait/R;dp+=paid/R;dh+=hs/R;dreset+=rs/R;localTargets++;directChecks++;
   }
   let tr=0,tp=0,th=0,trs=0,next=1;
   for(let a of es)for(let j=a.t;j<a.v;j++){
     while(next<can.length&&can[next].t<=j)next++;
     let h=next<can.length?can[next].g:T,end=Math.min(T,h),begin=Math.min(T,a.g);
     let w=end>begin?pre[end]-pre[begin]:0;
     fail(w>=-1e-9&&w<=1+1e-9,"bounded tick load");maxTickWeight=Math.max(maxTickWeight,w);tickChecks++;
     tr+=w;if(a.mark)tp+=w;if(a.high){th+=w;if(a.reset)trs+=w;}
   }
   let close=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b));fail(close(tr,dr)&&close(tp,dp)&&close(th,dh)&&close(trs,dreset),"direct and transpose");
   fail(tp<=wp[wp.length-1]+1e-7,"paid transfer");targets+=localTargets;rawWeighted+=tr;paidWeighted+=tp;remWeighted+=tr-tp;highWeighted+=th;resetWeighted+=trs;wholeWeight+=pre[T];
 }
 fail(targets===reached+unreached&&shortGapGain+longGapGain===N*T&&rawWeighted+1e-7*Math.max(1,lowerSum)>=lowerSum,"global checks");
 const round=n=>+n.toFixed(6);
 return {X,B,T,Q,amin,N,events,raw,rawHigh,paidRaw,rawReset,rootTerminated,canonicalPoints,virtual,arcs,rawCanonicalClock,longArcs,shortGapGain,longGapGain,targets,reached,unreached,completeGapTargets,artificialGapTargets,rawWeighted:round(rawWeighted),paidWeighted:round(paidWeighted),remWeighted:round(remWeighted),highWeighted:round(highWeighted),resetWeighted:round(resetWeighted),lowerSum:round(lowerSum),rawRatio:targets?round(rawWeighted/targets):null,remRatio:targets?round(remWeighted/targets):null,paidRatio:paidRaw?round(paidWeighted/paidRaw):null,directChecks,tickChecks,maxTickWeight:round(maxTickWeight),wholeWeight:round(wholeWeight),literal};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));console.log(JSON.stringify(audit(65536,true)));
