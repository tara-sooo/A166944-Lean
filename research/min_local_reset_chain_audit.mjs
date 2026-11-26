// Constructed exact four-reset non-twin prefix; standard BigInt GCD tick oracle.
function chainAudit() {
  const ps=[13,37,61,97], bound=ps[ps.length-1]+6;
  const prime=n=>n>=2&&Array.from({length:Math.max(0,Math.floor(Math.sqrt(n))-1)},(_,i)=>i+2).every(p=>n%p);
  const primes=Array.from({length:bound-2},(_,i)=>i+3).filter(prime);
  const mod=(x,m)=>(x%m+m)%m;
  const assert=(x,msg)=>{if(!x)throw Error(msg)};
  let shifts=[0];for(let p of ps)shifts.push(shifts.at(-1)+p-1);
  let conditions=[[4,0]],densityN=1n,densityD=4n;
  for(let q of primes){
    let forced=ps.indexOf(q),eligible=[];
    for(let r=0;r<q;r++){
      if(q===3&&r!==0)continue;
      let ok=true;
      for(let i=0;i<ps.length;i++){
        if(q>ps[i]+6)continue;
        let x=mod(r+shifts[i],q);
        if(q===ps[i]){if(x!==q-1)ok=false}
        else if(x===1||x===q-1)ok=false;
      }
      if(ok)eligible.push(r);
    }
    assert(eligible.length,"empty residue set "+q);
    conditions.push([q,eligible[0]]);
    densityN*=BigInt(eligible.length);densityD*=BigInt(q);
  }
  let fresh=[107,109,113,127];
  for(let i=0;i<ps.length;i++)conditions.push([fresh[i],mod(1-shifts[i],fresh[i])]);
  let x=0n,M=1n;
  for(let [q,r] of conditions){
    let k=0n,Q=BigInt(q);while((x+k*M)%Q!==BigInt(r))k++;
    x+=k*M;M*=Q;
  }
  x+=M;
  const gcd=(x,y)=>{while(y){let z=x%y;x=y;y=z}return x<0n?-x:x};
  let u=x,v=x/2n+3n,events=[],ticks=0;
  for(let i=0;i<ps.length;i++){
    let p=BigInt(ps[i]),w=(p-1n)/2n;
    assert(u%6n===0n&&2n*v-u===6n,"pre reset");
    assert((u+1n)%p===0n&&(u-1n)%BigInt(fresh[i])===0n,"composite certificate");
    assert(u-1n>BigInt(fresh[i])&&u+1n>p,"proper factors");
    for(let k=1n;k<=w;k++){
      let n=v+k,d=gcd(n%2n?n-2n:n,n%2n?u+1n:u-1n);
      assert(k===w?d===p:d===1n,"literal first gcd");ticks++;
    }
    events.push({p:Number(p),wait:Number(w),shift:Number(u-x),minusFactor:fresh[i]});
    u+=p-1n;v+=w;assert(2n*v-u===6n&&u%6n===0n,"post reset");
  }
  return {x:x.toString(),modulus:M.toString(),ticks,events,gain:Number(u-x),deficit:Number(2n*v-u),sufficientCylinderDensityNumerator:densityN.toString(),sufficientCylinderDensityDenominator:densityD.toString()};
}
console.log(JSON.stringify(chainAudit(),null,2));
