// Fixed-depth sharp completed-wait efficiency, non-twin CRT examples, and independent height relaxation.
// Run: node research/lean/negative_min_fixed_depth_efficiency_audit.mjs
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},mod=(a,m)=>(a%m+m)%m;
 const Zmax=180000,comp=new Uint8Array(Zmax+1),primes=[];
 for(let p=2;p<=Zmax;p++)if(!comp[p]){primes.push(p);if(p*p<=Zmax)for(let n=p*p;n<=Zmax;n+=p)comp[n]=1}
 const bm=(a,p)=>Number((a%BigInt(p)+BigInt(p))%BigInt(p));
 function inv(a,p){let t=0,u=1,r=p,s=a;while(s){let q=Math.floor(r/s);[r,s]=[s,r-q*s];[t,u]=[u,t-q*u]}ok(r===1,"inverse");return mod(t,p)}
 function crt(a,m,b,p){let c=mod((b-bm(a,p))*inv(bm(m,p),p),p);return [a+m*BigInt(c),m*BigInt(p)]}
 function offsets(ps){let ds=[0];for(let j=ps.length-1;j>=0;j--)ds.unshift(ds[0]+ps[j]-1);return ds}
 function alpha(k){return [3*4**(k-1),2*4**(k-1)+1]}
 let tuples=0,pinChecks=0,localChecks=0,events=0,ticks=0,eligibleChecks=0,crtChecks=0,relaxedChecks=0,relaxedStates=0,examples=[];
 function compatible(ps){let ds=offsets(ps),k=ps.length;
 for(let j=0;j<k;j++)for(let i=0;i<=k;i++)for(let s of [-1,1]){pinChecks++;if((mod(ds[i]-ds[j+1]+s,ps[j])===0)!==(i===j&&s===1))return false}
 for(let q of primes){if(q<=3)continue;if(q>2*k+2)break;let bad=new Set(ds.flatMap(d=>[mod(-d-1,q),mod(-d+1,q)]));localChecks++;if(bad.size===q)return false}
 return true}
 for(let k=1;k<=5;k++){
  let ps=null;
  function search(arr){if(ps)return;if(arr.length===k){tuples++;if(compatible(arr))ps=arr;return}
   let j=arr.length+1;
   for(let p of primes){if(p<11||p%12!==(j<=2?7:1))continue;
    if(j===1){if(p<31||p>400)continue}else{let prev=(j===2?1:2)*arr[j-2];if(p>2*prev)break;if(p<=arr[j-2]||prev/p<.5||prev/p>.54)continue}
    search([...arr,p]);if(ps)return;
   }
  }
  search([]);ok(ps,"find labels "+k);
  let ds=offsets(ps),h=3,ws=[],W=0,G=0;
  for(let j=0;j<k;j++){let p=ps[j],next=(j===0?1:2)*p,w=next-h+(p-1)/2;ok(w>0&&w<=2*p,"planned wait");ws.push(w);W+=w;G+=p-1;h=next}
  const T=3*G,Z=2*T+8,r=primes.find(p=>p>Z);ok(r&&Z<Zmax&&W<T,"finite cutoff");
  let a=BigInt(k===1?6:0),m=12n;
  for(let q of primes){if(q<5)continue;if(q>Z)break;let b;
   if(ps.includes(q)){b=mod(-ds[ps.indexOf(q)+1],q)}else{let bad=new Set(ds.flatMap(d=>[mod(-d-1,q),mod(-d+1,q)]));b=0;while(bad.has(b))b++;ok(b<q,"free residue")}
   [a,m]=crt(a,m,b,q);ok(bm(a,q)===b,"CRT immediate");crtChecks++;
  }
  [a,m]=crt(a,m,r-1,r);crtChecks++;
  const x=a+m,A=x+BigInt(ds[0]);ok(A%12n===0n&&x+1n>BigInt(r)&&bm(x+1n,r)===0,"non-twin target and birth");
  for(let j=0;j<k;j++){let p=ps[j],z=x+BigInt(ds[j+1]);ok(bm(z,4*p)===mod(2*(j===0?1:2)*p,4*p),"clock pin");ok(z>BigInt(p),"non-twin source range")}
  let pos=A,n=3n-A/2n,t=0,j=0,g=0,wait=0;
  function getCandidates(z){return primes.filter(p=>p>2&&p<=Z&&(bm(z+1n,p)===0||bm(z-1n,p)===0)).map(p=>({p,plus:bm(z+1n,p)===0}))}
  let cs=getCandidates(pos);
  for(let i=0;i<T;i++){let nn=n+1n,par=bm(nn,2),p=0;wait++;
   for(let c of cs){eligibleChecks++;if(c.plus!==(par===0))continue;if(bm(nn,2*c.p)===(c.plus?0:c.p+2)){p=c.p;break}}
   if(p){ok(j<k&&p===ps[j]&&wait===ws[j],"actual prescribed event");pos-=BigInt(p-1);g+=p-1;j++;
    ok(pos===x+BigInt(ds[j])&&nn+pos/2n===BigInt((j===1?1:2)*p),"actual height");
    const [u,v]=alpha(j);ok(v*Number(nn+pos/2n)<=u*(g+4*j),"fixed-depth bound");
    wait=0;events++;cs=getCandidates(pos);
   }
   n=nn;t++;ticks++;ok(n+pos/2n===BigInt(3+t-g/2),"height ledger");
  }
  ok(j===k&&g===G&&pos===x&&wait===T-W&&cs.length===0,"non-twin terminal quiet");
  const nextR=mod(-bm(n,2*r),2*r)||2*r;ok(nextR<=2*r,"future event within composite-factor period");
  const [u,v]=alpha(k);
  examples.push({k,labels:ps,waits:ws,W,G,T,ratio:W/G,ideal:.5+u/v,completedFraction:W/T,forcedCompositeFactor:r,exitWithin:nextR,rootDigits:A.toString().length});
 }
 // Independent height relaxation: track minimal sum(p+3) reaching a height,
 // allowing either height residue and every positive wait <=2p.
 let states=new Map([[3,0]]),small=primes.filter(p=>p>=11&&p<=97);
 for(let k=1;k<=8;k++){let next=new Map();let [u,v]=alpha(k);
  for(let [h,S] of states)for(let p of small)for(let c of [0,3]){
   for(let hp=c;hp<=h+2*p-(p-1)/2;hp+=p){
    let w=hp-h+(p-1)/2;if(w<1||w>2*p)continue;
    let SS=S+p+3;ok(v*hp<=u*SS,"uniform height upper");relaxedChecks++;
    if(!next.has(hp)||next.get(hp)>SS)next.set(hp,SS);
   }
  }states=next;relaxedStates+=states.size;
 }
 return {tuples,pinChecks,localChecks,crtChecks,events,ticks,eligibleChecks,relaxedChecks,relaxedStates,examples};
}
console.log(JSON.stringify(audit(),null,2));
