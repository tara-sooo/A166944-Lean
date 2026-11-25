// Finite local sieve for three-factor Q<=2p asymptotic families.
function audit(){
 const mod=(a,b)=>(a%b+b)%b, primes=[5,7,11,13,17,19,23,29,31,37,41,43,47];
 let families=0,integral=0,survive=0,baseClasses=0,baseSurvive=0,primeReject={},byType={},survivors=[],minExample=null;
 function vals(c,k,j,ea,eb){
 c=BigInt(c);k=BigInt(k);j=BigInt(j);ea=BigInt(ea);eb=BigInt(eb);
 let u=(k+(c+1n)*j)/2n,C=-(c*c-1n)+(c-1n)*ea+(c+1n)*eb,B=c*(c-1n)*u-C;
 if(B%k)return null;let b=B/k,a=b+c,p=a+b-1n;
 if((a*u-ea)%(c+1n))return null;let Q=(a*u-ea)/(c+1n)+1n;
 return {p,a,b,Q,c,u};
 }
 for(let [j,ea,eb,start,end] of [[5,-1,-1,11,400],[7,1,-1,13,784],[7,-1,1,9,784]])for(let k=start;k<end;k+=12){
  families++;let M=48*k,ic=0,sc=0,ty=[j,ea,eb].join("/");
  for(let c=6;c<M;c+=12){
   let v=vals(c,k,j,ea,eb);if(!v)continue;let {p,a,b,Q}=v;
   if(mod(p,12n)!==7n||mod(a,3n)!==1n||mod(b,3n)!==1n||mod(a,2n)!==1n||mod(b,2n)!==1n||mod(Q,12n)!==1n)continue;
   ic++;baseClasses++;
   let failed=0;
   for(let l of primes){let ll=BigInt(l),ok=false;for(let t=0;t<l;t++){
    let v=vals(c+M*t,k,j,ea,eb);if(!v)throw Error("integrality period");
    let {p,a,b,Q}=v,hs=[p*(Q-1n),p*Q-b,p*Q-1n];let nums=[p,a,b,Q-2n,...hs.flatMap(h=>[h-1n,h+1n])];
    if(nums.every(n=>n%ll!==0n)){ok=true;break}
   }if(!ok){failed=l;break}}
   if(failed){primeReject[failed]=(primeReject[failed]||0)+1;continue}
   sc++;baseSurvive++;if(!minExample)minExample={j,k,ea,eb,c,M};
  }
  if(ic)integral++;if(sc){survive++;survivors.push({j,k,ea,eb,classes:sc})}
  byType[ty]??={total:0,integral:0,survive:0};byType[ty].total++;if(ic)byType[ty].integral++;if(sc)byType[ty].survive++;
 }
 return {families,integral,survive,baseClasses,baseSurvive,primeReject,byType,survivors,minExample}
}
const result=audit();
if(result.families!==163||result.survive!==25||result.baseSurvive!==86)throw Error("regression");
console.log(JSON.stringify(result,null,2));
