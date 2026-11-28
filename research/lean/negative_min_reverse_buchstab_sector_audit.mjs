// Exact exponent/finite identity checks and exploratory (NOT certified) Buchstab recursion.
function audit(){
 const ok=(x,m)=>{if(!x)throw Error(m)};
 // All exponents for the explicit switched sector are integer millionths.
 const S=1000000, p0=374900,p1=374950,a=374800,b=249800,d=a+b,eps=10;
 ok(a<=p0-eps&&2*p1+b<=S-15*eps&&2*p1+5*b<=2*S-40*eps,"forward distribution slack");
 const q1=[230000,246000],q2=[170000,182000],q3=[165000,169900];
 const U0=q1[0]+q2[0]+q3[0],U1=q1[1]+q2[1]+q3[1];
 ok(q1[0]>q2[1]&&q2[0]>q3[1]&&q2[1]+q3[1]<a&&q1[1]<b&&U1<d,"forward packed appended primes");
 const W0=S-U1,W1=S-U0;
 ok(W0>p1&&W1<S/2&&W0>2*q3[1]&&W1<3*q3[0],"reverse residual factors");
 // Reverse allocation chosen per dyadic block: A_r=w-.0005, B_r=1-2w-.0005.
 // Thus total U-.001. Uniform all w in interval and p in fixed band.
 let sectorChecks=0;
 for(let x=q1[0];x<=q1[1];x+=1000)for(let y=q2[0];y<=q2[1];y+=1000)for(let z=q3[0];z<=q3[1];z+=100){
  let U=x+y+z,W=S-U,ar=W-500,br=S-2*W-500,dr=ar+br;
  ok(ar>=p1&&ar<=W-eps&&2*W+br<=S-15*eps&&2*W+5*br<=2*S-40*eps,"reverse distribution");
  ok(dr-p1>0&&ar-p1>0&&br>0&&W>2*z&&W<3*z,"reverse cutoff and two-factor residual");sectorChecks++;
 }
 // omega(u) <= .6 on [2,3]: (1+log(u-1))/u<=.6.
 // Instead use elementary log x<=x-1 and u<=W1/q3[0]<2.637 to bound
 // omega <= (u-1)/u < .621. Use a simple .625 bound, avoiding floating.
 ok(8*(W1-q3[0])<5*W1,"omega<=5/8 via log");
 // reverse normalized coefficient <= (1-p0)*(5/8)/(q3min*(Umin-.001-p1)).
 // forward normalized coefficient >= 1/(d-Umin).
 const revNum=BigInt(S-p0)*5n*BigInt(S),revDen=8n*BigInt(q3[0])*BigInt(U0-1000-p1);
 ok(revNum<13n*revDen,"reverse normalized coefficient <13");
 ok(BigInt(S)>16n*BigInt(d-U0),"forward normalized coefficient >16");
 const thresholds=[.313,.315,.32,.325,1/3,.34,.35,.375,.4].map(t=>({t,needed:(1/.625)*Math.log(t/(.625-t)),ordinary:(1/.625)*Math.log((.625-t)/t)}));
 // Exact finite Buchstab identity (including repeats) on semiprime source.
 let max=600010,sp=new Int32Array(max);for(let i=2;i<max;i++)if(!sp[i]){sp[i]=i;if(i*i<max)for(let j=i*i;j<max;j+=i)if(!sp[j])sp[j]=i}
 let sources=0,base=0,final=0,removed=0,innerBase=0,innerFinal=0,innerRemoved=0,triples=0,allChecks=0;
 const aa=7,bb=31,cc=11,dd=19;
 for(let n=30001;n<=600000;n+=2){
  const p=sp[n],v=n/p;if(p<31||p>181||v<=p||sp[v]!==v)continue;sources++;
  let m=n-2,l=sp[m];
  const ps=[];for(let k=m;k>1;){let r=sp[k];ps.push(r);while(k%r===0)k/=r}
  if(l>=aa){base++;if(l>=bb)final++;else removed++}
  ok(+(l>=bb)===+(l>=aa)-ps.filter(q=>q>=aa&&q<bb&&l>=q).length,"first Buchstab exact");
  for(let q of ps.filter(q=>q>=dd&&q<bb)){
   let B=+(l>=cc),F=+(l>=q),D=ps.filter(r=>r>=cc&&r<q&&l>=r).length;
   ok(B-F===D,"second Buchstab exact");innerBase+=B;innerFinal+=F;innerRemoved+=D;allChecks++;
   for(let r of ps.filter(r=>r<q&&r>=cc))for(let t of ps.filter(t=>t<r&&t>=aa)){
    if(l>=t){let rem=m/(q*r*t);ok(Number.isInteger(rem)&&rem>=1&&(rem===1||sp[rem]>=t),"reverse rough quotient");triples++}
   }
  }
 }
 ok(base-final===removed&&innerBase-innerFinal===innerRemoved&&triples>0,"nonvacuous identities");
 // Exploratory numerical recursive ledger, depth <=3, only positive residual
 // exponent W: no exact-product hypersurface U=1 is crossed.
 const h=.0002,m=Math.round(12/h)+1, FF=new Float64Array(m).fill(1),ff=new Float64Array(m),ww=new Float64Array(m).fill(1),shift=Math.round(1/h);
 for(let j=0;j<shift;j++)ww[j]=0;
 for(let j=2*shift+1;j<m;j++){let i=j-shift;ff[j]=ff[j-1]+h/2*(FF[i-1]/((i-1)*h)+FF[i]/(i*h));if(j>3*shift)FF[j]=FF[j-1]+h/2*(ff[i-1]/((i-1)*h)+ff[i]/(i*h));ww[j]=ww[j-1]+h/2*(ww[i-1]/((i-1)*h)+ww[i]/(i*h))}
 function interp(v,t){let x=Math.min(m-1,t/h),i=Math.floor(x);return i===m-1?v[i]:v[i]+(v[i+1]-v[i])*(x-i)}
 function scan(rev,depth){
  const ts=Array.from({length:50},(_,i)=>.08+.005*i),D=.625,P=.375,cache=new Map();let improvements=0,reverseFinite=0,reverseNew=0;
  function dp(pref){
   let key=pref.join(","),old=cache.get(key);if(old)return old;
   let us=pref.map(i=>ts[i]),U=us.reduce((x,y)=>x+y,0),W=1-U,dr=D-U;
   let pack=false,best=0;
   for(let mask=0;mask<1<<us.length;mask++){let n=us.reduce((s,t,i)=>s+((mask>>i&1)?t:0),0);
    if(n<=P+1e-9&&U-n<=D-P+1e-9)pack=true;n=Math.min(n,1-n);
    if(n>P+1e-8&&n<.5-1e-8)best=Math.max(best,1-n-P)
   }
   let arr=[],limit=pref.length?pref[pref.length-1]:ts.length-1;
   for(let i=0;i<=limit;i++){
    let t=ts[i],l=0,u=1e9;
    if(pack&&dr>1e-10){let ss=dr/t;l=ss>2?interp(ff,ss)/dr:0;u=interp(FF,Math.max(1,ss))/dr}
    if(rev&&pref.length&&W>0){if(W<t-1e-9)u=0;else if(best>0){let x=(1-P)*interp(ww,W/t)/(W*best);if(x<u){if(u<1e8)reverseFinite++;else reverseNew++;u=x}}}
    if(i&&pref.length<depth){let prev=arr[i-1],cl=dp([...pref,i-1]).at(-1),ch=dp([...pref,i]).at(-1),w=Math.log(t/ts[i-1]);let L=prev[0]-w*(cl[1]+ch[1])/2,H=prev[1]-w*(cl[0]+ch[0])/2;if(L>l+1e-8)improvements++;l=Math.max(l,L);u=Math.min(u,H)}
    arr.push([Math.max(0,l),Math.max(0,u)])
   }cache.set(key,arr);return arr
  }
  let r=dp([]);return{depth,rev,states:cache.size,reverseFinite,reverseNew,improvements,root:ts.map((t,i)=>({t,lower:r[i][0],upper:r[i][1]})).filter(r=>r.t>=.3)}
 }
 const scans=[scan(false,2),scan(true,2),scan(false,3),scan(true,3)];
 return {sectorChecks,reverseUpper:Number(revNum)/Number(revDen),forwardBaseline:S/(d-U0),thresholds,sources,base,final,removed,innerBase,innerFinal,innerRemoved,allChecks,triples,scans};
}
console.log(JSON.stringify(audit(),null,2));
