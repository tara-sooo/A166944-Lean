// Scale-local bounded-discovery A1 recovery construction; exact BigInt clocks.
function audit(){
 const limit=200000,spf=new Int32Array(limit),primes=[];for(let i=2;i<limit;i++)if(!spf[i]){spf[i]=i;if(i%2)primes.push(i);if(i*i<limit)for(let k=i*i;k<limit;k+=i)if(!spf[k])spf[k]=i}
 const mod=(x,p)=>(x%p+p)%p, modb=(x,p)=>(x%p+p)%p, assert=(x,m)=>{if(!x)throw Error(m)};
 function inv(a,p){let x=1,y=0,b=p;while(b){let q=Math.floor(a/b);[a,b]=[b,a%b];[x,y]=[y,x-q*y]}assert(a===1,"inverse");return mod(x,p)}
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a<0n?-a:a};
 let st={cases:[],literalTicks:0,stageResidues:0,progressionCandidates:0,progressionRejected:0,smallPrimeClasses:0};
 for(let minp of [1000,3000,8000]){
  let word=null,R,X;
  outer:for(let p of primes){if(p<minp||p%60!==31||3*p+6>=limit)continue;let k=Math.ceil(12*p/5);X=1n<<BigInt(k);let P=1n;R=1;for(let q of primes){if((P*BigInt(q))**2n>X)break;P*=BigInt(q);R=q}
   if(p<=R)continue;
   for(let s of primes){if(s%60!==1||100*s<=67*p)continue;if(100*s>=70*p)break;if(s>R)continue;
    for(let q of primes){if(q%60!==1||100*q<=67*s)continue;if(100*q>=70*s)break;if(q<=R&&2*q+3<=p){word=[p,s,q];break outer}}
   }
  }
  assert(word,"prime word");let [p,s,q]=word,k=Math.ceil(12*p/5);X=1n<<BigInt(k);
  let shifts=[0,p-1,p+s-2],bound=3*p+6,Y=Math.floor(p/10),small=primes.filter(f=>f<=Y),sel=new Map(word.map((f,i)=>[f,mod(1-shifts[i],f)])),all=primes.filter(f=>f<=bound);
  let forbidden=f=>new Set(shifts.flatMap(g=>[mod(1-g,f),mod(-1-g,f)]));
  for(let i=0;i<3;i++)for(let j=0;j<3;j++)if(i!==j){let f=word[i],v=mod(sel.get(f)+shifts[j],f);assert(v!==1&&v!==f-1,"selected cross compatibility")}
  let A=0n,Q=4n,allowedCount=1n;
  function add(f,v){let z=BigInt(f),step=mod((v-Number(A%z))*inv(Number(Q%z),f),f);A+=Q*BigInt(step);Q*=z}
  for(let f of small){let F=forbidden(f);let v=0;while(F.has(v))v++;assert(v<f,"allowed small");allowedCount*=BigInt(f-F.size);add(f,v);st.smallPrimeClasses++}
  for(let [f,v] of sel){assert(f>Y,"selected outside small");add(f,v)}
  let first=A+((X-A+Q-1n)/Q)*Q;assert(first>=X&&first<X+Q&&first<2n*X,"first");
  let checks=all.filter(f=>f>Y&&!sel.has(f)).map(f=>({f,F:forbidden(f),base:Number(first%BigInt(f)),step:Number(Q%BigInt(f))}));
  let found=0,lastOffset=-1;for(let i=0;i<20000&&found<3;i++){st.progressionCandidates++;if(checks.some(a=>a.F.has(mod(a.base+i*a.step,a.f)))){st.progressionRejected++;continue}
   let H0=first+BigInt(i)*Q;assert(H0>=X&&H0<2n*X,"absolute interval");
   for(let j=0;j<3;j++){let H=H0+BigInt(shifts[j]);for(let f of all){let v=Number(H%BigInt(f));assert(f===word[j]?v===1:v!==1&&v!==f-1,"full stage residues");st.stageResidues++}}
   let H=H0,t=H0/2n+3n,d=6,waits=[(3*p-7)/2,(3*s-2*p-1)/2,(3*q-2*s-1)/2];
   for(let j=0;j<3;j++){
    let a=word[j],w=waits[j];assert(w>0&&BigInt(a*a)<=H+1n,"eligibility");
    for(let z=1;z<=w;z++){let n=t+BigInt(z),I=Number(n%2n),e=1-2*I,F=d+2*z+1-6*I;let g=gcd(n-2n*BigInt(I),H-BigInt(e));assert(g===gcd(BigInt(F),H-BigInt(e)),"relative gcd");if(z<w)assert(g===1n,"quiet");else assert(I===0&&g===BigInt(a),"selected");st.literalTicks++}
    H+=BigInt(a-1);t+=BigInt(w);d=Number(2n*t-H);assert(d===2*a,"post deficit")
   }
   assert(2*s+3>p&&d+3<=p,"exact recovery at second event");found++;lastOffset=i;
  }
  assert(found===3,"three actual lifts");st.cases.push({p,s,q,R,k,logX:k*Math.log(2),pOverLogX:p/(k*Math.log(2)),waits:[(3*p-7)/2,(3*s-2*p-1)/2,(3*q-2*s-1)/2],Y,Qdigits:String(Q).length,Xdigits:String(X).length,allowedSmallResidueDigits:String(allowedCount).length,largeRivals:checks.length,found,lastOffset});
 }
 return st
}
console.log(JSON.stringify(audit(),null,2));
