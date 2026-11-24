// Two local exits and bounded-gain high extension; exact integer audit.
function audit(X,W,H=6){
 const B=Math.ceil(Math.sqrt(7*X)),U=Math.floor((14*X-1)/4),N=X/2,T=Math.max(3,Math.floor(B/8)),f=32,s=2,lim=7*X+2*B+2*W+100;
 const spf=new Int32Array(lim+1);for(let p=2;p<=lim;p++)if(!spf[p]){spf[p]=p;if(p*p<=lim)for(let j=p*p;j<=lim;j+=p)if(!spf[j])spf[j]=p;}
 const mod=(x,p)=>(x%p+p)%p,cell=C=>Math.floor((C-1)/W),ck=(b,m)=>{if(!b)throw Error(m)};
 function next(C,t){let p=0,n=Infinity,r=Infinity,side=0;
  for(let a of [-1,1]){let v=C+a;while(v>1){let q=spf[v];if(!q)throw Error("factor "+v);if(q>B)break;
   r=Math.min(r,q);let u=t+2*q-mod(t-(a===-1?0:q+2),2*q);if(u<n||(u===n&&q<p)){p=q;n=u;side=a;}do{v/=q;}while(v%q===0);}
  }return {p,n,r,side};
 }
 function two(C0,t0,check=false){
  let C=C0,t=t0,c=cell(C),g0=0,g1=0,p=0,q=0,A=0,D=0,sgn=0,sgn2=0,cost=0,star=0,internal=0,large=0;
  for(;;){let a=next(C,t);if(!a.p)break;let C1=C+a.p-1;ck(a.n>t&&a.n-t<=2*a.r&&2*a.n-C1>=0,"clock");
   let cross=cell(C1)!==c;cost+=a.r;star+=cross?a.p:a.r;
   if(!cross){internal+=a.p-1;ck(a.p<=W,"internal prime");}
   else if(!p){p=a.p;A=C;sgn=a.side;g0=C-C0;}
   else {q=a.p;D=C;sgn2=a.side;g1=D-(A+p-1);ck(g0<W&&g1<W&&g0>=0&&g1>=0&&D===C0+g0+p-1+g1,"two gains");
    if(q>f*(p+W+H)&&q>Math.sqrt(B)){ck(q>p&&8*a.r>q&&mod(A+sgn,p)===0&&mod(D+sgn2,q)===0,"large second CRT/roughness");large=1;}
    break;
   }
   C=C1;t=a.n;c=cell(C);
  }
  ck(internal<2*W&&star>=cost&&star<=3*W+p+q,"block bound");return {p,q,cost,star,large};
 }
 let hypo={states:0,F1:0,F2:0,star:0,first:0,second:0,firstSum:0,secondSum:0,comparableSecond:0,smallSecond:0,separatedSecond:0,separatedSum:0,smallParent:0,largeParent:0,termBeforeSecond:0};
 for(let h=0;h<=H;h+=2)for(let u=X+3;u<=U;u++){let a=two(2*u-h,u);hypo.states++;hypo.F2+=a.cost;hypo.star+=a.star;hypo.first+=!!a.p;hypo.second+=!!a.q;hypo.firstSum+=a.p;hypo.secondSum+=a.q;hypo.termBeforeSecond+=!a.q;if(a.q){if(a.q<=f*(a.p+W+H))hypo.comparableSecond++;else if(a.q<=Math.sqrt(B))hypo.smallSecond++;else{ck(a.large,"separated check");hypo.separatedSecond++;hypo.separatedSum+=a.q;if(a.p<=B**.25)hypo.smallParent++;else hypo.largeParent++;}}}
 ck(hypo.second===hypo.comparableSecond+hypo.smallSecond+hypo.separatedSecond,"hypo partition");
 // Actual source-specific cutoffs, low-height physical stopping rule.
 const head=new Int32Array(Math.floor((7*X+4)/2)+1).fill(-1),link=new Int32Array(N),time=new Int32Array(N),K=new Int32Array(N),alive=new Uint8Array(N),crosses=new Uint8Array(N),mode=new Uint8Array(N),p1=new Int32Array(N),p2=new Int32Array(N),g=new Int32Array(N),costA=new Int32Array(N),costE=new Int32Array(N),budget=new Int32Array(N),active=new Uint8Array(N);
 let stats={X,W,H,B,T,f,s,N,stops:0,natural:0,twin:0,nontwin:0,starts:0,startVertices:0,segments:0,secondCross:0,prefix:0,extension:0,remainder:0,total:0,extensionBound:0,actualStartBudget:0,actualStar:0,actualStartsWithSecond:0,highRemainderStarts:0,longStarts:0,giantStarts:0,maxRemainderLabel:0,checks:0};
 function add(i,C){let ix=C/2;link[i]=head[ix];head[ix]=i;}
 function finish(i){if(!active[i])return;ck(costA[i]<=budget[i],"actual prefix <= hypothetical");let z=p1[i]+p2[i]+W+H;if(crosses[i]>=2)ck(costE[i]<=100*s*z,"extension bound");else ck(costE[i]===0,"no extension");stats.segments++;active[i]=0;}
 for(let i=0;i<N;i++){let M=X+1+2*i;time[i]=M+2;K[i]=Math.floor((7*M-1)/4);alive[i]=1;add(i,2*M-2);}
 for(let C=2*X;C<=7*X-2;C+=2){let idx=head[C/2];if(idx<0)continue;head[C/2]=-1;let V=new Map();while(idx>=0){let n=link[idx];if(!V.has(time[idx]))V.set(time[idx],[]);V.get(time[idx]).push(idx);idx=n;}
  for(let [t,ids] of V){let h=2*t-C;ck(h>=0,"actual height");if(h<=H){for(let i of ids)finish(i);if(ids.length>=T){stats.stops+=ids.length;for(let i of ids)alive[i]=0;continue;}let z=two(C,t);stats.starts+=ids.length;stats.startVertices++;stats.actualStartBudget+=ids.length*z.cost;stats.actualStar+=ids.length*z.star;stats.actualStartsWithSecond+=ids.length*Number(!!z.q);stats.extensionBound+=100*s*ids.length*(z.p+z.q+W+H);
    for(let i of ids){active[i]=1;crosses[i]=0;mode[i]=0;p1[i]=0;p2[i]=0;g[i]=0;costA[i]=0;costE[i]=0;budget[i]=z.cost;}
   }
   let a=next(C,t);for(let i of ids){ck(active[i],"active segment");if(!a.p||a.n>K[i]){finish(i);stats.natural++;if(!a.p)stats.twin++;else stats.nontwin++;alive[i]=0;continue;}
    let C1=C+a.p-1,cross=cell(C1)!==cell(C);stats.total+=a.r;
    if(mode[i]===0){stats.prefix+=a.r;costA[i]+=a.r;if(cross){crosses[i]++;if(crosses[i]===1)p1[i]=a.p;else{ck(crosses[i]===2,"second crossing");p2[i]=a.p;mode[i]=1;stats.secondCross++;}}}
    else if(mode[i]===1){ck(h>H&&crosses[i]===2,"high extension");let z=p1[i]+p2[i]+W+H;
      if(g[i]>=s*z||a.p>64*s*z){mode[i]=2;stats.highRemainderStarts++;if(g[i]>=s*z)stats.longStarts++;else{stats.giantStarts++;ck(8*a.r>a.p,"giant overshoot roughness");}stats.remainder+=a.r;stats.maxRemainderLabel=Math.max(stats.maxRemainderLabel,a.p);}
      else{g[i]+=a.p-1;costE[i]+=a.r;stats.extension+=a.r;ck(g[i]<65*s*z,"bounded extension gain");}
    }else{ck(h>H&&crosses[i]===2,"high remainder");stats.remainder+=a.r;}
    time[i]=a.n;add(i,C1);
   }
  }
 }
 ck(alive.every(x=>!x)&&stats.natural+stats.stops===N,"source conservation");ck(stats.total===stats.prefix+stats.extension+stats.remainder&&stats.prefix<=stats.actualStartBudget&&stats.actualStartBudget<=T*hypo.F2&&stats.extension<=stats.extensionBound,"global cost ledger");ck(stats.highRemainderStarts===stats.longStarts+stats.giantStarts,"residual type");
 return {hypo,stats};
}
for(const x of process.argv.slice(2).map(Number))for(const w of [2,6,30])console.log(JSON.stringify(audit(x,w)));
