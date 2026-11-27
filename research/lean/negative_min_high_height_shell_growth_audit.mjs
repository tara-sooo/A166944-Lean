// High-height shell growth and second quiet phase: finite arithmetic controls, not asymptotic sieve validation.
// Run: node research/lean/negative_min_high_height_shell_growth_audit.mjs
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},mod=(a,m)=>(a%m+m)%m;
 const MAX=1600010,sp=new Int32Array(MAX);
 for(let p=2;p<MAX;p++)if(!sp[p]){sp[p]=p;if(p*p<MAX)for(let j=p*p;j<MAX;j+=p)if(!sp[j])sp[j]=p}
 function fac(n){let a=[];while(n>1){let p=sp[n];ok(p>0,"factor domain");a.push(p);while(n%p===0)n/=p}return a}
 function trial(n){let a=[];for(let p=3;p*p<=n;p+=2)if(n%p===0){a.push(p);while(n%p===0)n/=p}if(n>1)a.push(n);return a}
 function win(x,n){let s=mod(n,2)?-1:1;return fac(x+s).find(p=>mod(n,2*p)===(s===1?0:p+2))||0}
 function literal(x,n){let s=mod(n,2)?-1:1,a=trial(x+s);ok(a[0]===sp[x+s],"SPF oracle");return a.find(p=>mod(n,2*p)===(s===1?0:p+2))||0}
 function next(x,n){let w=Infinity,p=0;for(let s of [-1,1])for(let q of fac(x+s)){let u=mod((s===1?0:q+2)-n,2*q)||2*q;if(u<w||u===w&&q<p){w=u;p=q}}return{w,p}}
 function checkCandidate(a,g,u,q,s){let b=s===1?0:3,F=2*a.p+2*u-g+1-2*b;ok(F>0&&F%q===0,"height divisor");ok(q!==a.p&&mod(a.p*(a.v-1)-g+s,q)===0,"spatial divisor");let inv=0;for(let j=1;j<q;j++)if(mod(a.p*j,q)===1){inv=j;break}ok(inv>0&&mod(a.v-1-inv*(g-s),q)===0,"v residue");}
 let rows=[],sources=0,firstTicks=0,shellPins=0,shellCandidates=0,shellBad=0,actualBad=0,shellTicks=0,shellEvents=0,shellFull=0,earlyExits=0,heightChecks=0,nearPairs=0,commonStates=0,quietCandidates=0,quietInterrupted=0,quietPass=0,quietPins=0,quietTicks=0,quietHigh=0,smallQ=0,largeQ=0;
 for(let [R,H,M,J] of [[12000,8,2,2],[48000,10,2,2],[192000,12,2,3],[768000,16,2,3]]){
  let D=(2*M)**J, arr=[], localSources=0,localBad=0,localFull=0,localExit=0,localQuiet=0,localQuietPass=0;
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   let p=sp[A+1],v=(A+1)/p;if(p<11||v<=4*p||sp[v]!==v||v%12!==7||sp[A-1]<4*p)continue;
   let x=A-p+1,n=p-x/2,w=(3*p-7)/2,e=next(A,3-A/2);
   ok(e.w===w&&e.p===p&&3-A/2+w===n,"first high anchor");
   sources++;localSources++;firstTicks+=w;
   let a={A,p,v,x,n};
   // Finite quiet proxy: full source family condition at 5 or 7 or 11.
   for(let K of [5,7,11]){
    if(facProductCondition(v,K)){
     quietCandidates++;localQuiet++;let hs=Math.max(1,Math.floor(K/2)),bad=false;
     for(let u=1;u<=hs;u++){let q=literal(x,n+u);if(!q)continue;let s=mod(n+u,2)?-1:1;ok(q>=K,"target roughness");checkCandidate(a,0,u,q,s);quietPins++;if(q<=Math.sqrt(p))smallQ++;else largeQ++;bad=true;break}
     if(bad)quietInterrupted++;else{quietPass++;localQuietPass++;quietTicks+=hs;ok(x/2+n+hs===p+hs,"actual height gain");quietHigh++}
    }
   }
   if(p<=4*D+4*H)continue;
   let bad=false;
   // Enumerate ALL potential eligible large primes at shell positions/ticks,
   // not just those on the actual path. Integer factors from the height pin.
   for(let j=0;j<J;j++){
    let dmax=(2*M)**j,Z=M*dmax;
    for(let g=0;g<=dmax;g+=2)for(let u=1;u<=H;u++){
     let s=mod(n+u,2)?-1:1,b=s===1?0:3,F=2*p+2*u-g+1-2*b;
     for(let q of fac(F))if(q>=Z&&q!==p&&q>2&&mod(x-g+s,q)===0&&mod(n+u,2*q)===(s===1?0:q+2)){
      checkCandidate(a,g,u,q,s);shellPins++;shellCandidates++;bad=true;
     }
    }
   }
   if(bad){shellBad++;localBad++}
   let y=x,nn=n,j=0,g=0,records=[[x,n]],viol=false;
   for(let u=1;u<=H;u++){
    let q=win(y,nn+1);ok(q===literal(y,nn+1),"suffix literal");shellTicks++;
    if(q){shellEvents++;if(j<J&&q>=M*(2*M)**j){checkCandidate(a,g,u,q,mod(nn+1,2)?-1:1);ok(bad,"actual large jump included in union");viol=true;break}
     y-=q-1;g+=q-1;j++;}
    nn++;
    if(j<=J&&!bad){ok(g<=(2*M)**j,"shell induction");ok(y/2+nn>=p-D/2,"height lower");heightChecks++}
    records.push([y,nn]);
    if(j>=J)break;
   }
   if(viol)actualBad++;
   if(bad)continue;
   if(j>=J){earlyExits++;localExit++}else{shellFull++;localFull++}
   arr.push({...a,records});
  }
  arr.sort((a,b)=>a.x-b.x);let badSet=new Set();
  for(let i=0;i<arr.length;i++)for(let j=i+1;j<arr.length&&arr[j].x-arr[i].x<=D;j++){
   let a=arr[i],b=arr[j];if(Math.abs(a.n-b.n)>H)continue;
   ok(a.p!==b.p&&Math.abs(a.p-b.p)<=H+D/2,"near anchor pins");nearPairs++;badSet.add(a);badSet.add(b);
  }
  let states=new Set();
  for(let a of arr)if(!badSet.has(a))for(let [x,n] of a.records){ok(!states.has(x+","+n),"separated records");states.add(x+","+n);commonStates++}
  rows.push({R,H,M,J,D,sources:localSources,bad:localBad,full:localFull,depthStop:localExit,quietCandidates:localQuiet,quietPass:localQuietPass,separatedStates:states.size});
 }
 function facProductCondition(v,K){if(v%12!==7)return false;for(let q=5;q<K;q++)if(sp[q]===q&&v%q!==1)return false;return true}
 // Nonvacuous shell proof on synthetic high anchor states: enumerate actual
 // clock transitions, regardless of canonical ancestry, to exercise cutoffs.
 let arithmeticControls=0;
 for(let p=101;p<=199;p++)if(sp[p]===p)for(let v=13;v<=151;v+=6){
  let x=p*(v-1),n=p-x/2;if(x%2||mod(n,2*p)!==0)continue;
  for(let u=1;u<=12;u++)for(let g=0;g<=8;g+=2){let s=mod(n+u,2)?-1:1,q=win(x-g,n+u);if(q&&q!==p){checkCandidate({p,v},g,u,q,s);arithmeticControls++}}
 }
 return {rows,sources,firstTicks,shellPins,shellCandidates,shellBad,actualBad,shellTicks,shellEvents,shellFull,earlyExits,heightChecks,nearPairs,commonStates,quietCandidates,quietInterrupted,quietPass,quietPins,quietTicks,quietHigh,smallQ,largeQ,arithmeticControls};
}
console.log(JSON.stringify(audit(),null,2));
