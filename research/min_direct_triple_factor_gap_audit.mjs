// Fourth-root triple-factor gap/capacity diagnostics, abstract plateaus only.
function audit(){
 const prime=n=>{if(n<2)return false;if(n%2===0)return n===2;for(let d=3;d*d<=n;d+=2)if(n%d===0)return false;return true};
 const ps=[];for(let p=5001;ps.length<15;p+=2)if(prime(p))ps.push(p);
 const Y=ps.at(-1)**3+1,B=1+Math.floor(8*Math.sqrt(Math.sqrt(Y+1))),mod=(x,p)=>(x%p+p)%p;
 function gcd(a,b){while(b){[a,b]=[b,a%b]}return a}
 function fac(n){let fs=[];for(let d=3;d*d<=n;d+=2)while(n%d===0){fs.push(d);n/=d}if(n>1)fs.push(n);return fs}
 function next(t,H){let best=null;for(let e of [1,-1])for(let p of new Set(fac(H-e))){if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}return best}
 const s={ps,Y,B,candidates:0,ticks:0,actual:0,literalJumpComparisons:0,roughChecks:0,cofactorSquare:0,selectedRepeated:0,allDistinct:0,closeCofactor20:0,closeSelected20:0,bandChecks:0,sieveResidueChecks:0,examples:{},relaxedPacking:0};
 let candidates=[],hits=[];
 for(let p of ps)for(let i=0;i<ps.length;i++)for(let j=i;j<ps.length;j++)for(let e of [1,-1]){
  let a=ps[i],b=ps[j],H=p*a*b+e,w=Math.ceil((p-1)/4),base=e===1?0:p+2,n=base+2*p*Math.ceil((H/2+w-base)/(2*p)),t=n-w;
  if(p<=B||4*w<p-1||p*p>H+1||2*t<H||a<p/8||b<a)throw Error("candidate");
  s.candidates++;
  let A=2**Math.floor(Math.log2(a)),T=Math.min(16*A+1,Math.floor((Y+1)/A**2));
  if(p>T||a<A||a>=2*A)throw Error("dyadic capacity");s.bandChecks++;
  candidates.push({p,a,b,e,H,w,t,n});
  let winner=null;
  for(let k=1;k<=w;k++){let m=t+k,f=m%2?-1:1,g=gcd(f===1?m:m-2,H-f);s.ticks++;if(g>1){let l=fac(g)[0];if(l*l<=H+1){winner={p:l,e:f,w:k};break}}}
  if(winner?.p!==p||winner.e!==e||winner.w!==w)continue;
  let fs=fac(H+e);for(let f of [p,a,b,...fs]){if(2*f<w||BigInt(f)**4n<=BigInt(Y+1))throw Error("rough");s.roughChecks++}
  if(fs.length>3)throw Error("opposite omega");
  for(let l of [3,5,7,11,13,17,19,23,29,31,37,41,43,47]){if(p%l===0||a%l===0||b%l===0||(H+e)%l===0)throw Error("sieve root");s.sieveResidueChecks++}
  let row={p,a,b,e,H,w,t,n,opposite:fs};hits.push(row);s.actual++;
  if(a===b){s.cofactorSquare++;s.examples.square??=row}
  if(p===a||p===b){s.selectedRepeated++;s.examples.selectedRepeated??=row}
  if(p!==a&&p!==b&&a!==b){s.allDistinct++;s.examples.distinct??=row}
  if(b-a<=20)s.closeCofactor20++;
  if(Math.min(Math.abs(p-a),Math.abs(p-b))<=20)s.closeSelected20++;
  if(s.literalJumpComparisons<50){let v=next(t,H);if(JSON.stringify(v)!==JSON.stringify(winner))throw Error("jump");s.literalJumpComparisons++}
 }
 // For every possible fixed pair and sign, the missing factor is unique for
 // a fixed H. Verify the counting injection on a relaxed monotone path.
 candidates.sort((a,b)=>a.H-b.H);let end=-1,keys=new Set();
 for(let v of candidates)if(v.H>=end){let key=[v.p,v.a,v.b,v.e].join(":");if(keys.has(key))throw Error("injectivity");keys.add(key);end=v.H+v.p-1;s.relaxedPacking++}
 return s
}
console.log(JSON.stringify(audit(),null,2));
