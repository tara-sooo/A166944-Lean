// Consecutive long two-event odd-reset returns: exact CRT and GCD checks.
function audit(){
 const prime=n=>{if(n<2)return false;for(let i=2;i*i<=n;i++)if(n%i===0)return false;return true};
 const ps=[];for(let p=3;p<=15000;p+=2)if(prime(p))ps.push(p);
 const mod=(a,b)=>(a%b+b)%b;
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a<0n?-a:a};
 function constraints(rs){
  let shifts=[0];for(let r of rs)shifts.push(shifts.at(-1)+r+5);
  let sets=[];
  for(let l of ps){if(l>Math.max(21,rs.at(-1)+4))break;
   let forced=null,bad=new Set();
   for(let i=0;i<rs.length;i++){
    let r=rs[i],s=shifts[i];
    if(l===3||l===7||l===5||l===r){
     let v=l===3?2:l===7?3:l===5?(i%2?4:3):l-5;
     let a=mod(v-s,l);if(forced!==null&&forced!==a)return null;forced=a;
    }
    if(l<=21&&![3,5,7].includes(l)){bad.add(mod(1-s,l));bad.add(mod(3-s,l));}
    if(l<r){bad.add(mod(-3-s,l));bad.add(mod(-5-s,l))}
    if(l===r+4)bad.add(mod(-3-s,l));
   }
   if(forced!==null&&bad.has(forced)||forced===null&&bad.size===l)return null;
   let a=forced??0;while(bad.has(a))a++;
   sets.push({l,a,count:forced!==null?1:l-bad.size});
  }
  return {shifts,sets};
 }
 let rs=[],attempts=0;
 for(let i=0;i<8;i++){
  let found=false;for(let r of ps){if(r<=Math.max(23,rs.at(-1)||0)||r%4!==3||r%3!==1||r%7!==2||r%5!==(i%2?4:1))continue;attempts++;
   if(constraints([...rs,r])){rs.push(r);found=true;break}
  }if(!found)break;
 }
 if(rs.length<4)throw Error("insufficient chain");
 let result={rs,attempts,chains:[],literalTicks:0,eventChecks:0,residueChecks:0};
 for(let k of [2,4,rs.length]){
  let chosen=rs.slice(0,k),{shifts,sets}=constraints(chosen);
  let M=1n,Q=2n,allowed=1n;
  for(let {l,a,count} of sets){let L=BigInt(l),v=BigInt(a)*BigInt((l+1)/2)%L;while(M%L!==v)M+=Q;Q*=L;allowed*=BigInt(count)}
  let min=BigInt(chosen.at(-1)**2);if(M<min)M+=Q*((min-M+Q-1n)/Q);
  for(let lift=0;lift<2;lift++){
   let root=M+BigInt(lift)*Q,H=2n*root-2n,t=root+2n,seq=[];
   for(let i=0;i<k;i++){let r=chosen[i],base=t,dmax=0n,high=0,ev=[],gap=(r+5)/2;
    if(2n*root%3n!==2n||2n*root%7n!==3n)throw Error("small phase");
    for(let {l} of sets){if(l>=r)break;let f=BigInt(l);
      if((H+5n)%f===0n||(H+7n)%f===0n)throw Error("roughness");result.residueChecks++}
    for(let j=1;j<=gap;j++){let d=2n*t-H;dmax=d>dmax?d:dmax;if(2n*d>=BigInt(r))high++;
     let n=++t,e=n%2n?-1n:1n,g=gcd(e===1n?n:n-2n,H-e);
     if(g!==1n){if(g!==7n&&g!==BigInt(r)||g*g>H+1n)throw Error("gcd/eligibility");H+=g-1n;ev.push([j,Number(g),Number(2n*n-H)]);result.eventChecks++}
     if(j<gap&&H%4n===0n&&2n*t-H===6n)throw Error("early return");result.literalTicks++;
    }
    if(JSON.stringify(ev)!==JSON.stringify([[7,7,14],[gap,r,6]])||H!==2n*(root+BigInt(gap))-2n||t!==base+BigInt(gap)||dmax!==BigInt(r+3)||high!==(r+9)/4)throw Error("segment "+JSON.stringify({r,ev,dmax:String(dmax),high}));
    root+=BigInt(gap);seq.push({r,gap,peak:Number(dmax),high});
   }
   if((H-1n)%7n||49n>H+1n)throw Error("target active");
   if(lift===0)result.chains.push({k,digits:M.toString().length,periodDigits:Q.toString().length,allowedDigits:allowed.toString().length,totalTicks:seq.reduce((a,v)=>a+v.gap,0),seq})
  }
 }
 return result
}
console.log(JSON.stringify(audit(),null,2));
