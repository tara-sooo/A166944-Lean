// Weighted padded parity obstruction, exact integral and asymmetric minus-first controls.
// Run: node research/lean/negative_min_padded_parity_and_bridge_audit.mjs
function audit(){
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,m)=>(a%m+m)%m;
 const MAX=1600010,sp=new Int32Array(MAX),pr=[];
 for(let p=2;p<MAX;p++)if(!sp[p]){sp[p]=p;pr.push(p);if(p*p<MAX)for(let j=p*p;j<MAX;j+=p)if(!sp[j])sp[j]=p}
 function factors(n){let a=[];while(n>1){let p=sp[n];ok(p>0,"factor domain");a.push(p);while(n%p===0)n/=p}return a}
 function parity(n){let s=1;while(n>1){n/=sp[n];s=-s}return s}
 function gcd(a,b){while(b){let t=a%b;a=b;b=t}return a}
 function w(n){let a=1n,b=1n;for(let p of factors(n))if(p>2){a*=BigInt(p-1);b*=BigInt(p-2)}return[a,b]}
 let localDensityChecks=0,weightChecks=0;
 for(let p of pr.filter(p=>p>2&&p<10000)){
  let P=BigInt(p);ok((P-1n)*(P-1n)===P*(P-2n)+1n,"g(p) identity");localDensityChecks++;
 }
 for(let d=3;d<=301;d+=2)for(let k=1;k<=301;k+=2){
  let [a,b]=w(d*k),[c,e]=w(d),[f,g]=w(k),[h,i]=w(gcd(d,k));
  ok(a*e*g*h===b*c*f*i,"w(dk) exact multiplicative correction");weightChecks++;
 }
 const M=100000,P=1009,upper=110000,Z=Math.floor(Math.sqrt(upper))+1;
 let modelStarts=0,evenParity=0,roughTargets=0,Jchecks=0,Jpositive=0,switchedTripleChecks=0;
 for(let m=M|1;m<=upper;m+=2){
  modelStarts++;if(parity(m)!==1)continue;evenParity++;ok(sp[m]<=Math.sqrt(m),"core composite");ok(P>Z,"padding outside cutoff");
  if(sp[m]>=Z)roughTargets++;
  let f=factors(m);
  for(let q of f.filter(q=>q>=61&&q<=97))for(let r of f.filter(r=>r>=13&&r<=29)){
   if(q*r*r*r<=upper||q*r>=M)continue;Jchecks++;
   if(sp[m]>=r)Jpositive++;
  }
  for(let q1 of f)for(let q2 of f.filter(q=>q<q1))for(let q3 of f.filter(q=>q<q2)){
   if(q1*q2*q3<M&&q1*q2*q3*q3>upper){ok(sp[m]<q3,"impossible switched triple in parity core");switchedTripleChecks++}
  }
 }
 ok(roughTargets===0&&Jpositive===0&&Jchecks>0,"model targets vanish");
 const S=10000n,K=10n**18n;
 let low=0n,upperInt=0n,cells=0;
 for(let t=2360;t<3000;t++)for(let u=1300;u<2000;u++){
  let T=BigInt(t),U=BigInt(u);
  // 1/(2tu(1-t-u)) decreases in both coordinates on this rectangle.
  let a=2n*(T+1n)*(U+1n)*(S-T-U-2n),b=2n*T*U*(S-T-U);
  low+=K*S/a;upperInt+=(K*S+b-1n)/b;cells++;
 }
 ok(low>9070n*K/100000n&&upperInt<9082n*K/100000n,"certified integral .09070-.09082");
 function logBounds(n,d){
  ok(n>=d&&d>0n,"log argument");
  const a=n-d,b=n+d;let ln=0n,un=0n,ap=a,bp=b;
  for(let j=0;j<24;j++){const den=BigInt(2*j+1)*bp,num=2n*K*ap;ln+=num/den;un+=(num+den-1n)/den;ap*=a*a;bp*=b*b}
  const tailNum=2n*K*ap*b*b,tailDen=49n*bp*(b*b-a*a);un+=(tailNum+tailDen-1n)/tailDen;
  return[ln,un]
 }
 let thresholds=[];
 for(let B of [3130,3150,3200,3250]){
  let [a,b]=logBounds(BigInt(B),6246n-BigInt(B));a=a*10000n/6246n;b=(b*10000n+6245n)/6246n;
  thresholds.push({b:B/10000,lower:Number(a)/Number(K),upper:Number(b)/Number(K),neededFractionUpper:Number(b)/Number(low)});
 }
 let roots=0,asym=0,minusFirst=0,firstCalendar=0,literalTicks=0,postPin=0,repeatChecks=0,lowWordChecks=0,high=0,reset=0,examples=[];
 function next(x,n){let w=Infinity,p=0,s=0;for(let t of [-1,1])for(let q of factors(x+t)){let u=mod((t===1?0:q+2)-n,2*q)||2*q;if(u<w||u===w&&q<p){w=u;p=q;s=t}}return{w,p,s}}
 function literal(x,n){let s=mod(n,2)?-1:1;return factors(x+s).find(p=>mod(n,2*p)===(s===1?0:p+2))||0}
 for(let A=60000;A<=1500000;A+=6){
  roots++;let P0=sp[A+1],v0=(A+1)/P0,q=sp[A-1];
  if(P0<101||P0>401||v0<=P0||sp[v0]!==v0||q<11||4*q>=P0)continue;
  asym++;let n=3-A/2,e=next(A,n),p=e.p,co=(A-1)/p;
  ok(e.s===-1&&p<=3*q&&p>=q,"minus dominance");
  let w=mod(co,4)===1?(3*p-1)/2:(p-1)/2;ok(w===e.w,"minus first calendar");firstCalendar++;minusFirst++;
  for(let i=1;i<=w;i++){n++;ok(literal(A,n)===(i===w?p:0),"first literal tick");literalTicks++}
  let x=A-p+1,h=x/2+n;ok(mod(x, p)===2&&h===(mod(co,4)===1?p+3:3),"minus post pin");postPin++;
  if(h===3)reset++;else high++;
  let g=0;for(let j=0;j<5;j++){
   if(g>=p-3)break;let z=next(x,n);ok(z.p!==p,"no repeated large label");repeatChecks++;
   if(z.p>11||g+z.p-1>=p-3)break;
   x-=z.p-1;n+=z.w;g+=z.p-1;
   ok(mod(x+g-2,p)===0&&mod(x-(1-z.s),z.p)===0&&(x+g+p-2)/p===co,"mixed low word pins");lowWordChecks++;
  }
  if(examples.length<5)examples.push({A,P0,q,p,w,h});
 }
 ok(asym>0&&high>0&&reset>0,"nonvacuous asymmetric roots");
 let pairControls=0;
 for(let p of pr.filter(p=>p>23&&p<301))for(let s of [-1,1])for(let t of [-1,1])for(let d=-(p-3);d<=p-3;d+=2){
  if(mod(d-((1-t)-(1-s)),p)!==0)continue;
  ok(d===1-t-(1-s),"small displacement exact");ok(d===0||d%6!==0,"canonical same prime separation");pairControls++;
 }
 return{localDensityChecks,weightChecks,modelStarts,evenParity,roughTargets,Jchecks,Jpositive,switchedTripleChecks,integral:{cells,low:String(low),high:String(upperInt),scale:String(K)},thresholds,roots,asym,minusFirst,firstCalendar,literalTicks,postPin,repeatChecks,lowWordChecks,high,reset,pairControls,examples}
}
console.log(JSON.stringify(audit(),null,2));
