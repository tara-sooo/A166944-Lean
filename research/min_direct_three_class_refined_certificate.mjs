// Exact rational certificate: three-class smoothing with delta=7/11.
function certificate(){
 const D=10n**30n,ceil=(x,y)=>(x+y-1n)/y;
 function reduced(a,b){let zl=D*(a-b)/(a+b),zu=zl+1n,lo=0n,hi=0n,pl=zl,ph=zu;for(let i=0;i<120;i++){lo+=2n*pl/BigInt(2*i+1);hi+=ceil(2n*ph,BigInt(2*i+1));pl=pl*zl*zl/(D*D);ph=ceil(ph*zu*zu,D*D)}hi+=ceil(2n*ph*D*D,241n*(D*D-zu*zu));return[lo,hi]}
 const ln2=reduced(2n,1n);
 function log(a,b){a=BigInt(a);b=BigInt(b);if(a<b){let [l,u]=log(b,a);return[-u,-l]}let k=0n;while(a>=2n*b){b*=2n;k++}let [l,u]=reduced(a,b);return[l+k*ln2[0],u+k*ln2[1]]}
 let A=314159n,B=314160n,J=100000n,Q=100000n;
 if(4n*J*J*Q>=40530n*A*A||4n*J*J*Q>=4504n*9n*A*A||8n*J*J*Q>=81060n*A*A||32n*J**4n*Q>=32860n*A**4n)throw Error("top constants");
 if((Q-18950n)*B*B>=8n*J*J*Q||(Q-3n*490n)*B**4n>=96n*J**4n*Q)throw Error("remainder constants");
 for(let [a,b,c] of [[100000,40530,903],[100000,4504,3100],[100000,81060,209],[100000,18950,1660],[100000,32860,1112],[100000,490,5300]])if(log(a,b)[0]*1000n<=BigInt(c)*D)throw Error("log constant "+b);
 if(log(1000,367)[0]<=D||log(1000,368)[1]>=D)throw Error("entropy max");
 const N=1000,HD=100000,sd=2*N*N;
 let ent=Array.from({length:N+1},(_,i)=>i===0?0n:ceil(-BigInt(i)*log(i,N)[0],BigInt(N)));
 let em=(a,b)=>b<=367?ent[b]:a>=368?ent[a]:368n*D/1000n;
 let worst=null,witness,cells=0,counts=[0,0],minGap=Infinity,maxH=0;
 for(let i=0;i<=640;i++)for(let j=0;j<N-i;j++){
  let u=Math.max(0,N-i-j-2),U=N-i-j, sn=2*i*i+j*j;
  let H=Math.max(1,Math.ceil(HD*(7*sd-11*sn)/(11*(sd-sn)))+1);
  let gap=11*(sn*(HD-H)+sd*H)-7*sd*HD;
  if(gap<=0||H>=HD)throw Error("gap");
  minGap=Math.min(minGap,gap/(11*sd*HD));maxH=Math.max(maxH,H);
  let e=em(i,i+1)+em(j,j+1)+em(u,U),best=null,ss;
  for(let s of [1,2]){if(s*H>=HD)continue;let m=BigInt(HD-s*H)*BigInt(903*j+3100*u)*D+BigInt(H)*BigInt((s===1?209:1112)*j+(s===1?1660:5300)*u)*D-BigInt(H)*e*BigInt(N*1000);
   if(best===null||m>best){best=m;ss=s}
  }
  if(best===null||best*1000n<=3n*BigInt(HD*N*1000)*D)throw Error("margin "+i+","+j);
  if(worst===null||best<worst){worst=best;witness={i,j,H,s:ss}}
  cells++;counts[ss-1]++;
 }
 return {cells,counts,minimumMargin:Number(worst)/Number(BigInt(HD*N*1000)*D),minGap,maxH,witness};
}
console.log(JSON.stringify(certificate(),null,2));
