// Exact short/long clock and low-height nonreset top-semiprime audit.
function audit(X) {
 const B=Math.ceil(Math.sqrt(7*X)),K=Math.floor((7*X-1)/4),spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=(b,m="assertion")=>{if(!b)throw Error(m)},gcd=(a,b)=>{while(b){let r=a%b;a=b;b=r}return a};
 function factors(v){let f=[];while(v>1){let q=spf[v];f.push(q);while(v%q===0)v/=q}return f}
 function hit(t,C){let n=K+1,p=0;for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(q>B)break;let a=t+1+(((s===-1?0:q+2)-t-1)%(2*q)+2*q)%(2*q);if(a<n||(a===n&&q<p)){n=a;p=q}while(v%q===0)v/=q}}return [n,p]}
 const st={X,B,K,origins:K-X-2,events:0,high:0,highNonreset:0,highNonresetCost:0,lowHeightEvents:0,lowHeightNonreset:0,lowHeightNonresetCost:0,largeJump:0,largeJumpReset:0,largeJumpNonreset:0,largeJumpNonresetCost:0,largeJumpTop:0,largeJumpTopReset:0,largeJumpTopNonreset:0,topNonreset:0,topNonresetCost:0,topNonresetHighHeight:0,topNonresetPrimeOther:0,topNonresetPlus:0,topNonresetMinus:0,nonminNonreset:0,nonminNonresetCost:0,nonminNonresetMinHeight:Infinity,firstHeightCrossings:[0,0,0,0],firstHeightCrossingsByLargeJump:[0,0,0,0],firstHeightCrossingsByReset:[0,0,0,0],totalCost:0,literal:0,clockChecks:0,examples:[]};
 for(let u=X+3;u<=K;u++){
  let t=u,C=2*u-(u%2?6:0),cross=[false,false,false,false];
  for(;;){let [n,p]=hit(t,C);if(X<=1024){let nn=K+1,pp=0;for(let j=t+1;j<=K;j++){let g=gcd(j%2?j-2:j,C+(j%2?1:-1));if(g>1&&spf[g]<=B){nn=j;pp=spf[g];break}}ck(nn===n&&pp===p,"literal");st.literal++}
   if(!p)break;
   let h=2*t-C,b=n%2?6:0,hp=2*n-(C+p-1),r=Math.min(spf[C-1],spf[C+1]),nr=hp!==b,large=p>2*h+20,top=p>=B/2;
   ck(h>=0&&hp>=0&&n-t<=2*r&&r<=p);
   st.events++;st.totalCost+=r;
   if(p>7){st.high++;if(nr){st.highNonreset++;st.highNonresetCost+=r;ck(hp>=2*p+b&&hp%(2*p)===b);if(p!==r){st.nonminNonreset++;st.nonminNonresetCost+=r;st.nonminNonresetMinHeight=Math.min(st.nonminNonresetMinHeight,h);ck(h>=r-1)}}}
   if(h<r-1){
    st.lowHeightEvents++;
    // For all eligible q, verify first clock formula independently, no cutoff applied to the comparison.
    for(let s of [-1,1])for(let q of factors(C+s)){
     if(q>B||q<=5)continue;let bq=s===-1?0:6,m=(C+s)/q,k=s===-1?+(m%4===1):+(m%4===3);
     let a=(C+q-1+bq)/2+k*q,phase=s===-1?0:q+2;
     let exact=t+1+((phase-t-1)%(2*q)+2*q)%(2*q);
     ck(a===exact,"short long clock");st.clockChecks++;
    }
    if(nr&&p>7){st.lowHeightNonreset++;st.lowHeightNonresetCost+=r;ck(p===r&&hp===2*p+b,"low height min")}
   }
   if(large){
    st.largeJump++;if(nr){st.largeJumpNonreset++;st.largeJumpNonresetCost+=r;ck(p===r&&hp===2*p+b&&h<r-1,"large nonreset");ck(p*p<=C+(b?1:-1),"min factor square")}
    else st.largeJumpReset++;
    if(top){st.largeJumpTop++;if(nr){st.largeJumpTopNonreset++;
      let sigma=b?1:-1,a=C+sigma,m=a/p,other=C-sigma;
      ck(Number.isInteger(m)&&m>=p&&m<=B&&spf[m]===m,"semiprime");
      ck(spf[other]===other,"other prime");
      ck(p%4===(sigma===-1?1:3)&&m%4===p%4,"mod4");
      if(sigma===1)st.topNonresetPlus++;else st.topNonresetMinus++;
      if(st.examples.length<6)st.examples.push({u,t,C,h,p,r,n,hp,sigma,m,other});
    }else st.largeJumpTopReset++}
   }
   if(top&&nr&&p>7){st.topNonreset++;st.topNonresetCost+=r;if(!large)st.topNonresetHighHeight++;if(spf[C-1]===C-1||spf[C+1]===C+1)st.topNonresetPrimeOther++}
   for(let i=0;i<4;i++){let z=B*2**(i-1);if(!cross[i]&&hp>=z){cross[i]=true;st.firstHeightCrossings[i]++;if(large)st.firstHeightCrossingsByLargeJump[i]++;if(!nr)st.firstHeightCrossingsByReset[i]++}}
   C+=p-1;t=n;if(!nr)break
  }
 }
 ck(st.largeJump===st.largeJumpReset+st.largeJumpNonreset&&st.largeJumpTop===st.largeJumpTopReset+st.largeJumpTopNonreset);ck(st.largeJumpTopNonreset===st.topNonresetPlus+st.topNonresetMinus);
 if(st.nonminNonresetMinHeight===Infinity)st.nonminNonresetMinHeight=null;
 return st
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
