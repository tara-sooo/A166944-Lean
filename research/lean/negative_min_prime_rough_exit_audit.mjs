// Prime-rough canonical births, exact first firing and fixed reset class audit.
// Run: node research/lean/negative_min_prime_rough_exit_audit.mjs
// Finite controls only; no numerical inference of sieve asymptotics.
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},mod=(a,p)=>(a%p+p)%p;
 const max=1000000,sp=new Int32Array(max+3);for(let p=2;p<sp.length;p++)if(!sp[p]){sp[p]=p;if(p*p<sp.length)for(let n=p*p;n<sp.length;n+=p)if(!sp[n])sp[n]=p}
 function factors(n){let a=[];while(n>1){let p=sp[n];a.push(p);while(n%p===0)n/=p}return a}
 function least(x){return Math.min(sp[x-1],sp[x+1])}
 function event(x,n){let t=Infinity,p=0,side=0;for(let s of [-1,1])for(let q of factors(x+s)){let c=s===1?0:q+2,w=mod(c-n,2*q)||2*q;if(w<t||(w===t&&q<p)){t=w;p=q;side=s}}return {w:t,p,side}}
 function literal(x,n,t){for(let j=1;j<=t;j++){let c=n+j,p=0;for(let q of factors(c%2===0?x+1:x-1))if(mod(c,2*q)===(c%2===0?0:q+2)){p=q;break}if(p)return {w:j,p}}return null}
 let resets=0,resetTicks=0,calChecks=0,formulaChecks=0,sourceChecks=0,shiftChecks=0,postExitChecks=0,rows=[];
 const B=12*13*5*7*11;
 // CRT residue: x=0 mod 12,13,5,7; x=2 mod11.
 let a=-1;for(let x=0;x<B;x+=12)if(x%13===0&&x%5===0&&x%7===0&&x%11===2){ok(a===-1,"unique CRT");a=x}
 ok(a>=0,"CRT class");for(let q of [2,3,5,7,11,13]){ok(mod(a-1,q)!==0&&mod(a+1,q)!==0,"target reduced");if(q<13)ok(mod(a+13,q)!==0&&mod(a+11,q)!==0,"source rough")}
 for(let x=a;x<max-20;x+=B){if(x<20)continue;const A=x+12,n=3-A/2;const e=event(A,n);ok(e.p===13&&e.w===3,"reset first event");let y=A-e.p+1;ok(y===x,"reset center");let l=literal(A,n,3);ok(l.p===13&&l.w===3,"literal reset");ok(n+3+3===3-x/2,"reset birth clock");ok(literal(x,n+3,3)===null,"three quiet ticks");resets++;resetTicks+=6;
  if(sp[x-1]===x-1){sourceChecks++;let H=Math.min(100,Math.floor((least(x)-8)/2));if(H>0)ok(literal(x,3-x/2,H)===null,"prime rough target stationary")}
 }
 for(let R of [12000,48000,192000,384000]){
  let z=Math.floor(R**.285),eta=Math.max(31,Math.floor(R**.15)),rough=0,primeRough=0,twins=0,exit=0,successorRough=0,fast=0,avgGain=0,smallest=0,noRoughNeighborhood=0,smallNeighborhoodBound=0;
  for(let x=Math.ceil(R/6)*6;x<=2*R;x+=6){
   let q=least(x);if(q<z||q<11)continue;rough++;
   let one=sp[x-1]===x-1,other=sp[x+1]===x+1;if(!one&&!other)continue;primeRough++;
   let n=3-x/2,e=event(x,n);
   for(let s of [-1,1])for(let p of factors(x+s)){ok(p>=11,"rough formula domain");let r=(x+s)/p,k=r%4,formula=s===1?(k*p-7)/2:(k===1?(3*p-1)/2:(p-1)/2);
    let c=s===1?0:p+2;ok(formula===(mod(c-n,2*p)||2*p),"birth wait formula");formulaChecks++}
   if(one&&other){twins++;continue}
   exit++;let l=literal(x,n,e.w);ok(l.w===e.w&&l.p===e.p,"literal first event");calChecks++;
   ok(e.w>=(q-7)/2&&e.w<=2*q&&e.p<=4*q+7,"first bounds");
   if(e.p===q)smallest++;
   let y=x-e.p+1,r=(x+e.side)/e.p;
   ok(r>1&&e.p>=z,"factorized source");ok(y===e.p*(r-1)+(1-e.side),"successor form");
   let forms=[r,e.p*r-2*e.side,y-1,y+1];ok(forms[1]===x-e.side,"opposite form");
   ok(sp[r]>=z&&sp[forms[1]]>=z,"source rough factors");
   if(least(y)>=eta){successorRough++;ok(forms.every(v=>sp[v]>=Math.min(z,eta)),"four form sieve input")}
   const H=Math.floor(Math.log(R)**1.5);let clear=true;for(let d=0;d<=H;d+=2){let u=y-d;ok(u>2,'shifted center domain');let b=1-e.side-d;ok(u===e.p*(r-1)+b,'shifted four-form identity');let fs=[r,e.p*r-2*e.side,u-1,u+1];if(least(u)>=eta){clear=false;ok(fs.every(v=>sp[v]>=Math.min(z,eta)),'shifted rough forms');}if(e.p>H+4){let cs=[0,-2*e.side,-e.p+b-1,-e.p+b+1];ok(new Set(cs).size===4,'distinct form roots');}shiftChecks++;}if(clear){noRoughNeighborhood++;let u=y,t=n+e.w,elapsed=0,g=0;while(g<=H){let v=event(u,t);ok(v.w<2*eta,'short neighborhood wait');elapsed+=v.w;t+=v.w;g+=v.p-1;u-=v.p-1;postExitChecks++;}ok(elapsed<=2*eta*(Math.floor(H/2)+1),'gain crossing time');smallNeighborhoodBound=Math.max(smallNeighborhoodBound,elapsed);}
   let ne=event(y,n+e.w);ok(ne.w<=2*least(y),"next wait");if(ne.w<2*eta)fast++;
   avgGain+=e.p-1;
  }
  rows.push({R,z,eta,rough,primeRough,twins,exit,successorRough,fast,smallest,avgGain:exit?avgGain/exit:null,noRoughNeighborhood,smallNeighborhoodBound});
 }
 return {B,a,resets,resetTicks,sourceChecks,calChecks,formulaChecks,shiftChecks,postExitChecks,rows}
}
console.log(JSON.stringify(audit(),null,2));
