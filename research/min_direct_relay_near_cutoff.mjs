// Exact independent near-cutoff audit. node min_direct_relay_near_cutoff.mjs [103..50000]
function scan(P=50000){
 if(!Number.isInteger(P)||P<103||P>50000)throw Error('range');
 const prime=new Uint8Array(P+1);prime.fill(1,2);
 for(let i=2;i*i<=P;i++)if(prime[i])for(let j=i*i;j<=P;j+=i)prime[j]=0;
 const mod=(x,m)=>(x%m+m)%m;
 function inv(x,m){let a=mod(x,m),b=m,u=1,v=0;while(b){let q=Math.floor(a/b);[a,b]=[b,a-q*b];[u,v]=[v,u-q*v]}return a===1?mod(u,m):null}
 function fac(n){let f=[];for(let r=3;r*r<=n;r+=2)if(n%r===0){f.push(r);while(n%r===0)n/=r}if(n>1)f.push(n);return f}
 let s={P,pairs:0,crt:0,scale:0,identities:0,composite:0,lagChecks:0,eligibleLagChecks:0,ineligibleFactors:0,sameLabelFactors:0,lagRejected:0,shorterThan2r:0,shorterThan2rSurvivingLag:0,minGap:null,minGapSurvivingLag:null};
 for(let p=103;p<=P;p+=12)if(prime[p])for(let b=Math.floor((p+1)/4)+1;b<(p+1)/2;b++){
  if(!prime[b]||b%3!==1)continue;let a=p+1-b,c=a-b;if(!prime[a]||a%3!==1)continue;s.pairs++;
  let A=inv(c+1,a),B=inv(c-1,b),bi=inv(a,b);if(A===null||B===null)continue;
  for(let ea of [1,-1])for(let eb of [1,-1]){
   let ra=mod(1-ea*A,a),rb=mod(eb*B,b),Q=ra+a*mod((rb-ra)*bi,b);s.crt++;
   if(Q<p+2||Q>=p*p/64||Q%12!==1)continue;s.scale++;
   let u=((c+1)*(Q-1)+ea)/a,v=((c-1)*Q-eb)/b,j=u-v,d=Q-p;
   if(!Number.isInteger(u)||!Number.isInteger(v)||j%2===0||c%12!==6||d%12!==6)throw Error('parameters');
   let C=BigInt(c),D=BigInt(d),J=BigInt(j),E=BigInt(ea),F=BigInt(eb),L=4n-J,S=BigInt(p+1),N=4n*L*S-(16n*C*C+8n*C-4n*D*J-8n*E-8n*F+J*J+2n*J);
   let R16=-8n*(4n*D-4n*E+4n*F-J-2n)*C+(4n*D-J-6n)*(4n*D*J+8n*E+8n*F-J*J-2n*J);
   let Fp2=-(8n*C*C+4n*C-4n*D*J+8n*D-4n*E-4n*F+J*J+2n*J-12n);
   if(mod(N,16n)!==(mod(J,4n)===1n?5n:9n)||mod(N+J*(J+2n),3n)!==0n||L*R16+2n*Fp2*N-N*N!==0n)throw Error('exact elimination');
   if(J===3n&&N===9n)throw Error('impossible Pell branch');
   s.identities++;
   let w=(c+4-3*(1-eb))/2,fs=fac(Q),r=fs[0];
   if(w<=6||r===Q||w>=2*r||c>4*r)continue;s.composite++;
   let rec={p,a,b,c,Q,d,r,j,n:String(N),ea,eb,w,delta:d/Math.sqrt(p)};
   const better=(x,y)=>!y||BigInt(x.d)**2n*BigInt(y.p)<BigInt(y.d)**2n*BigInt(x.p);
   if(better(rec,s.minGap))s.minGap=rec;
   if(d<2*r)s.shorterThan2r++;
   let passes=true;
   for(let f of fs){
    if(f===p){s.sameLabelFactors++;continue;}
    // Smallest h=2 mod 4 with h*f>d; no slow loop over d/f.
    let m=2+4*Math.max(0,Math.floor((d-2*f)/(4*f))+1),lag=(m*f-d)/2,n2=p*(Q+1)/2+2;
    if(lag<=0||lag>=2*f||lag%2||lag!==mod(n2-f-2,2*f))throw Error('lag');
    s.lagChecks++;
    if(BigInt(f)**2n>BigInt(p)*BigInt(Q)){s.ineligibleFactors++;continue;}
    s.eligibleLagChecks++;if(w>lag)passes=false;
   }
   if(!passes)s.lagRejected++;
   else{if(d<2*r)s.shorterThan2rSurvivingLag++;if(better(rec,s.minGapSurvivingLag))s.minGapSurvivingLag=rec}
  }
 }
 return s
}
function limits(){
 const unit=1000000n;
 function isqrt(n){let lo=0n,hi=n+1n;while(hi-lo>1n){let m=(hi+lo)/2n;if(m*m<=n)lo=m;else hi=m}return lo}
 function floor(a,b){return a>=0n?a/b:-((-a+b-1n)/b)}
 function ceil(a,b){return -floor(-a,b)}
 const rows=[],possible=[];
 for(let L=1;L<=19;L+=2){
  let j=4-L,l=BigInt(L),J=BigInt(j),s=isqrt(l*unit*unit),sHi=s*s===l*unit*unit?s:s+1n;
  let n0=Array.from({length:48},(_,n)=>n).find(n=>n%16===((j%4+4)%4===1?5:9)&&((n+j*(j+2))%3+3)%3===0);
  function bounds(regime){
   const den=4n*unit,lo=regime==='A'?0n:s,hi=regime==='A'?8n*unit-2n*s:44n*unit/10n;
   if(lo>hi)return null;
   let v=[lo,hi].map(t=>[4n*J*t*t-16n*sHi*t,4n*J*t*t-16n*s*t]);
   let mn=v.reduce((a,b)=>a<b[0]?a:b[0],v[0][0]),mx=v.reduce((a,b)=>a>b[1]?a:b[1],v[0][1]);
   if(j>0&&2n*s<=hi*J&&2n*sHi>=lo*J){let low=floor(-l*den*den,J);if(low<mn)mn=low}
   const low=Number(ceil(mn,den*den)),high=Number(floor(mx,den*den)),ns=[];
   for(let n=low;n<=high;n++)if((n-n0)%48===0){ns.push(n);possible.push({regime,L,j,n})}
   return {low,high,ns}
  }
  rows.push({L,j,n0,A:bounds('A'),B:bounds('B')})
 }
 if(possible.length!==2||possible.some(x=>x.j!==3||x.n!==9))throw Error('limiting candidates');
 let seeds=[];for(let y=1;y<=5;y++)for(let x=1;x<=15;x++)if(x*x-7*y*y===-3)seeds.push([x,y]);
 if(JSON.stringify(seeds)!==JSON.stringify([[2,1],[5,2]]))throw Error('seeds');
 let cycles=[];
 for(let [x0,y0] of seeds){let x=x0,y=y0,seen=[];
  do{seen.push([x,y]);[x,y]=[(8*x+21*y)%12,(3*x+8*y)%12]}while(x!==x0||y!==y0);
  if(seen.length!==4||seen.some(([x,y])=>x===2&&y===11))throw Error('Pell cycle');
  cycles.push(seen)
 }
 return {rows,possible,seeds,cycles}
}
console.log(JSON.stringify({scan:scan(Number(process.argv[2]||50000)),limits:limits()},null,2));
