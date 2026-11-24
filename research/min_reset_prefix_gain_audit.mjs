// Reset first-excursion prefix and gain-limited jump audit, exact common cutoff.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),K=Math.floor((7*X-1)/4),L=210,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=(b,m="assertion")=>{if(!b)throw Error(m)},mod=(x,m)=>(x%m+m)%m,gcd=(a,b)=>{while(b){let r=a%b;a=b;b=r}return a};
 function hit(t,C){let n=K+1,q=0;for(let s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let h=t+1+mod((s===-1?0:p+2)-t-1,2*p);if(h<n||(h===n&&p<q)){n=h;q=p}while(v%p===0)v/=p}}return [n,q]}
 const depths=[1,2,4,8,16,32,64],stats=depths.map(k=>({k,cost:0,elapsed:0,labels:0,tailHigh:0,tailCost:0,tailElapsed:0,over:0,powerLarge:0,maxPrefixP:0})),Glist=[0,10,34,100,500],jump=Glist.map(G=>({G,Z:Math.max(11,10*G+14),count:0,sumP:0,maxP:0}));
 let R=0,E=0,Hsum=0,Hmax=0,A=0,A2=0,Acost=0,nonresetFirst=0,nonresetLarge=0,largeFirst=0,largeFirstK1=0,largeFirstK2=0,multi=0,multiTerm=0,multiReset=0,first2=0,first2Cost=0,p2Large=0,p2Rough=0,p2Dom=0,p2DomCost=0,p2DomSmallQ=0,p2DomBigQ=0,maxG=0,maxH=0,lit=0,maxExc=0,tailExamples=[],hist=new Array(12).fill(0),firstHighCount=0;
 for(let u=X+3;u<=K;u++){
  let b=u%2?6:0,initial=2*u-b,t=u,C=initial,Ru=0,high=[],cuts=[],reset=false,q1=0,t1=0,seenJump=new Uint8Array(jump.length),lowG=0;
  for(;;){
   let [n,p]=hit(t,C);if(X<=1024){let a=K+1,z=0;for(let j=t+1;j<=K;j++){let g=gcd(j%2?j-2:j,C+(j%2?1:-1));if(g>1&&spf[g]<=B){a=j;z=spf[g];break}}ck(a===n&&z===p,"literal");lit++}
   if(!p)break;
   let r=Math.min(spf[C-1],spf[C+1]),G=C-initial,h=2*t-C,hh=2*n-(C+p-1),dt=n-t;
   ck(G>=0&&h>=0&&hh>=0&&dt<=2*r&&t-u<=3*G&&h<=6+5*G&&p-1<=h+4*r);
   ck(4*r>=p-7-5*G);
   for(let j=0;j<jump.length;j++)if(G<=jump[j].G&&p>=jump[j].Z){
    ck(r>=p/8,"rough gain-limited jump");if(!seenJump[j]){seenJump[j]=1;jump[j].count++;jump[j].sumP+=p;jump[j].maxP=Math.max(jump[j].maxP,p)}
   }
   Ru+=r;C+=p-1;t=n;maxG=Math.max(maxG,C-initial);maxH=Math.max(maxH,hh);
   if(p>7){
    high.push(p);cuts.push({r:Ru,e:t-u});ck(lowG<L);lowG=0;
    if(high.length===1){firstHighCount++;q1=p;t1=t;if(hh!==(t%2?6:0))nonresetFirst++;
     if(p>12*L+14){largeFirst++;ck(r>=p/8);let k=(hh-(t%2?6:0))/(2*p);ck(k===0||k===1||k===2);if(k){nonresetLarge++;if(k===1)largeFirstK1++;else largeFirstK2++}}
    }
    if(high.length===2){
     first2++;first2Cost+=Ru;ck(G<=q1-1+2*L&&t-u<=2*(q1+p)+6*L);
     if(p>16*(q1+L)){p2Dom++;p2DomCost+=p;ck(q1!==p&&r>=p/8);if(q1<=B**.25)p2DomSmallQ++;else p2DomBigQ++}
     if(p>=Math.sqrt(B)){p2Large++;if(r>=p/8)p2Rough++}
    }
   }else{lowG+=p-1;ck(lowG<L)}
   if(C===2*t-(t%2?6:0)){reset=true;break}
  }
  let H=high.length,e=t-u;R+=Ru;E+=e;Hsum+=H;Hmax=Math.max(Hmax,H);maxExc=Math.max(maxExc,e);hist[Math.min(11,H?1+Math.floor(Math.log2(H)):0)]++;
  if(H>=2){multi++;A+=e;Acost+=Ru;if(reset)multiReset++;else multiTerm++;if(H===2)A2+=e}
  let prefSum=0,pmax=0,j=0;
  for(let s of stats){
   for(;j<Math.min(s.k,H);j++){prefSum+=high[j];pmax=Math.max(pmax,high[j])}
   let c=H<=s.k?Ru:cuts[s.k-1].r,ell=H<=s.k?e:cuts[s.k-1].e;
   ck(c<=prefSum+1.5*L*(Math.min(H,s.k)+1)&&ell<=2*c);
   s.cost+=c;s.elapsed+=ell;s.labels+=prefSum;s.tailHigh+=Math.max(0,H-s.k);s.tailCost+=Ru-c;s.tailElapsed+=e-ell;if(H>s.k)s.over++;if(pmax>=Math.sqrt(B))s.powerLarge++;s.maxPrefixP=Math.max(s.maxPrefixP,pmax);
  }
  if(H>=8){let ex={u,H,elapsed:e,cost:Ru,first:high.slice(0,12),maxP:Math.max(...high),reset};if(tailExamples.length<3)tailExamples.push(ex);else{let j=0;for(let i=1;i<3;i++)if(tailExamples[i].elapsed<tailExamples[j].elapsed)j=i;if(e>tailExamples[j].elapsed)tailExamples[j]=ex}}
 }
 for(let s of stats)ck(s.cost+s.tailCost===R&&s.elapsed+s.tailElapsed===E);
 return {X,B,K,origins:K-X-2,R,E,Hsum,Hmax,A,A2,Acost,multi,multiTerm,multiReset,firstHighCount,nonresetFirst,nonresetLarge,largeFirst,largeFirstK1,largeFirstK2,first2,first2Cost,p2Large,p2Rough,p2Dom,p2DomCost,p2DomSmallQ,p2DomBigQ,maxG,maxH,lit,maxExc,hist,stats,jump,tailExamples}
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
