// Exact exponent margins, squarefree mask cancellation and finite calendar controls; not a proof of the distribution theorem.
function audit(){
 const ok=(x,msg)=>{if(!x)throw Error(msg)},gcd=(a,b)=>{while(b){let t=a%b;a=b;b=t}return a},mod=(a,m)=>(a%m+m)%m;
 // Exact rational margins in units 1/(8000000) for delta=j/100000.
 let margins=0; const S=8000000;
 for(let j=1;j<=99;j++){let d=80*j,eps=d/100; // rational calculation scaled by 100 below
  for(let k=0;k<=20;k++){let nu=3*S/8-d*k/20,D=5*S/8-d,Q1=nu-d/10,Q2=D-Q1;
   ok(Q1>0&&Q2>0,"positive levels");
   ok(Q1<=nu-eps&&2*nu+Q2<=S-15*eps&&2*nu+5*Q2<=2*S-40*eps,"Pascadi margins");
   ok(D>2*(5*S/16-2*d),"lower sieve slack");
   for(let i=0;i<=10;i++){let p=5*S/16-3*d+d*i/10,v=S-nu-p;ok(p<v&&v<nu,"ordered prime scales");margins++}
  }
 }
 const MAX=5000010,sp=new Int32Array(MAX),pr=[];for(let p=2;p<MAX;p++)if(!sp[p]){sp[p]=p;pr.push(p);if(p*p<MAX)for(let m=p*p;m<MAX;m+=p)if(!sp[m])sp[m]=p}
 function mu(n){let m=1;while(n>1){let p=sp[n];n/=p;if(n%p===0)return 0;m=-m}return m}
 function smooth(n,z){while(n>1){let p=sp[n];if(p===2||p>=z)return false;n/=p}return true}
 // Arbitrary bounded convolution factors, exact mask identity (including squares).
 let identities=0,nontrivialCancellations=0,tailChecks=0;const N1=120,N2=150;
 for(let z of [11,23,47,101])for(let seed=0;seed<5;seed++){
  let a=Array.from({length:N1+1},(_,i)=>i?((i*13+seed*7)%3)-1:0),b=Array.from({length:N2+1},(_,i)=>i?((i*i+seed*11)%3)-1:0);
  let direct=new Int32Array(N1*N2+1),expanded=new Int32Array(direct.length);
  for(let i=1;i<=N1;i++)for(let j=1;j<=N2;j++){if(mu(i*j)!==0&&smooth(i*j,z))direct[i*j]+=a[i]*b[j];if(mu(i)&&mu(j)&&smooth(i,z)&&smooth(j,z)){
   let g=gcd(i,j),t=0;for(let e=1;e<=g;e++)if(g%e===0)t+=mu(e);
   if(g>1&&a[i]*b[j])nontrivialCancellations++;
   expanded[i*j]+=a[i]*b[j]*t;
  }}
  for(let n=1;n<direct.length;n++){ok(direct[n]===expanded[n],"mask identity");identities++}
  for(let E of [1,2,4,8,16]){let actual=0,upper=0;for(let e=E+1;e<=N1;e++)if(mu(e)){let x=0,y=0;for(let i=e;i<=N1;i+=e)x+=1/i;for(let j=e;j<=N2;j+=e)y+=1/j;actual+=x*y}upper=(1+Math.log(N1))*(1+Math.log(N2))/E;ok(actual<=upper,"tail bound");tailChecks++}
 }
 // Literal first-event controls for finite three-prime proxies.
 function fac(n){let a=[];while(n>1){let p=sp[n];a.push(p);while(n%p===0)n/=p}return a}
 let roots=0,qualifying=0,ticks=0,reset=0,high=0,examples=[];
 for(let A=60000;A<=3000000;A+=6){roots++;let f=fac(A+1);if(f.length!==3||f[0]*f[1]*f[2]!==A+1)continue;let [p,v,u]=f;if(p<11||p%6!==1||v<=4*p||sp[A-1]<=3*p)continue;
  qualifying++;let w=(mod(v*u,4)*p-7)/2,x=A,n=3-A/2;
  for(let j=1;j<=w;j++){n++;let s=mod(n,2)?-1:1,label=fac(x+s).find(q=>mod(n,2*q)===(s===1?0:q+2))||0;ok(label===(j===w?p:0),"literal first winner");if(label)x-=label-1;ticks++}
  let h=x/2+n;ok(x===p*(v*u-1)&&x%6===0&&h===(mod(v*u,4)===1?0:p),"destination");if(h===0)reset++;else high++;
  if(examples.length<6)examples.push({A,p,v,u,w,h})
 }
 ok(qualifying>0&&nontrivialCancellations>0,"nonvacuous");
 return {margins,identities,nontrivialCancellations,tailChecks,roots,qualifying,ticks,reset,high,examples}
}
console.log(JSON.stringify(audit(),null,2));
