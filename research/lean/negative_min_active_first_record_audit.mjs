// First-height deficit and genuinely active two-event first-record construction.
// Finite CRT examples and exact integer tests; not an asymptotic sieve verification.
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)}, mod=(a,m)=>(a%m+m)%m;
 const MAX=1600010,sp=new Int32Array(MAX),ps=[];
 for(let p=2;p<MAX;p++)if(!sp[p]){sp[p]=p;ps.push(p);if(p*p<MAX)for(let j=p*p;j<MAX;j+=p)if(!sp[j])sp[j]=p}
 function factors(x){let a=[];while(x>1){let p=sp[x];ok(p>0,"factor range");a.push(p);while(x%p===0)x/=p}return a}
 function next(x,n){let w=Infinity,p=0;for(let s of [-1,1])for(let q of factors(x+s)){let t=mod((s===1?0:q+2)-n,2*q)||2*q;if(t<w||(t===w&&q<p)){w=t;p=q}}return{w,p}}
 let rows=[],roots=0,hits=0,activeHits=0,deficitChecks=0,lastChecks=0,firstChecks=0,suffixChecks=0,activeOne=0,activeTwo=0,sectionTransfer=0;
 for(let R of [12000,48000,192000,768000]){
  let H=Math.floor(R**.4),B=4*H,all=0,ah=0,depths={},records=new Map();
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   roots++;let x=A,n=3-A/2,t=0,h=3,d=H-3,k=0,last=0,rec=3;
   while(true){
    let e=next(x,n),idle=H-h;
    if(e.w>idle){
     ok(idle>0,"first section reached by idle");ok(idle<2*Math.min(sp[x-1],sp[x+1]),"terminal calendar");
     if(A-x>B)break;
     hits++;all++;lastChecks++;let qmin=Math.min(sp[x-1],sp[x+1]);
     if(last)ok(last<=2*idle+1&&last<4*qmin+1,"last label / terminal roughness");
     ok(BigInt(3*H-7)<=4n**BigInt(k)*BigInt(3*idle+2),"deficit depth");if(k)ok(BigInt(6*qmin-1)*4n**BigInt(k-1)>=BigInt(H-2),"sharper first-event depth");
     if(qmin<H/16){ah++;activeHits++;depths[k]=(depths[k]||0)+1;if(k===1)activeOne++;if(k===2){activeTwo++;ok(qmin>=H/24-3,"two-event obstruction")};let old=records.get(x);if(!old||A<old.A)records.set(x,{A,x,n:n+idle,qmin,k});}
     break;
    }
    ok(e.w<=idle,"strict pre-record");let pre=h+e.w-1,hn=h+e.w-(e.p-1)/2;
    ok(pre<H&&hn<H&&hn>=0,"pre and post heights");let dn=H-hn;
    ok(e.p<=2*dn+1,"label deficit");ok(d<=4*dn+2,"one-step deficit");deficitChecks++;
    if(k===0){ok(3*hn<=2*H+4,"first record deficit");firstChecks++}
    last=e.p;k++;x-=e.p-1;n+=e.w;t+=e.w;h=hn;d=dn;ok(h===x/2+n&&t===h-3+(A-x)/2,"ledger");if(A-x>B)break;
   }
  }
  // Active sinks have a representative; independently check the first-H state
  // is the same when stopping at a smaller height and continuing.
  for(let a of records.values()){
   let x=a.A,n=3-x/2,h=3,mid=Math.max(4,Math.floor(H/2)),reached=false;
   while(h<H){let p=0,s=mod(n+1,2)?-1:1;for(let q of factors(x+s))if(mod(n+1,2*q)===(s===1?0:q+2)){p=q;break}
    n++;if(p)x-=p-1;h=x/2+n;if(h===mid)reached=true;suffixChecks++;
   }
   ok(reached&&x===a.x&&n===a.n,"active intermediate transfer");sectionTransfer++;
  }
  rows.push({R,H,hits:all,activeRootHits:ah,distinctActive:records.size,depths});
 }
 // Exact rational margins of the asymptotic fixed-height construction.
 // Scale 100000: p [.6199,.6201], q [.21999,.22001], r [.06064,.06066].
 const S=100000n,pl=61990n,pu=62010n,ql=21999n,qu=22001n,rl=6064n,ru=6066n;
 ok(3n*pu<2n*S&&9n*qu<2n*S,"no earlier record");
 ok(9n*ql>2n*pu&&5n*qu<2n*pl,"second wait between 0 and 2q");
 ok(16n*ru<S&&33n*rl>2n*S&&29n*ru<8n*ql,"terminal quiet and active");
 // Check every unintended forced prime congruence by interval bounds.
 function noMultiple(lo,hi,a,b){ // shift positive between consecutive multiples
  for(let j=0n;j<=20n;j++)if(lo<=j*b&&hi>=j*a)return false;
  return true;
 }
 ok(qu<pl&&noMultiple(pl,pu,ql,qu)&&noMultiple(ql,qu,rl,ru)&&noMultiple(pl+ql,pu+qu,rl,ru),"pin interval separation");
 // Finite CRT demonstrations: use relaxed narrow-band parameters with the
 // exact required integer inequalities; enforce ALL prime exclusions <=Z.
 const bigmod=(a,m)=>(a%m+m)%m;
 function inv(a,m){let t=0n,nt=1n,r=m,nr=bigmod(a,m);while(nr){let q=r/nr;[t,nt]=[nt,t-q*nt];[r,nr]=[nr,r-q*nr]}ok(r===1n,"inverse");return bigmod(t,m)}
 let examples=[],crtPins=0,crtTicks=0,crtEvents=0,allFactorChecks=0;
 for(let r of ps.filter(r=>r>=37&&r<=500&&r%12===1)){
  let q=ps.find(q=>q%12===7&&29*r<=8*q+1&&9*q<33*r-4);
  if(!q)continue;
  let H=Math.max(16*r+1,Math.floor((9*q-3)/2)+1,4*q+1);
  let p=ps.find(p=>p%12===7&&5*q-1<=2*p&&3*p-3<2*H&&p>q);
  if(!p||16*r>=H||H<=4*q||9*q-3>=2*H)continue;
  let g=p+q-2,w1=(3*p-7)/2,w2=(9*q-2*p-1)/2,I=H-4*q,wr=(33*r-8*q-1)/2,Z=4*H+10;
  if(!(w1>0&&w2>0&&w2<=2*q&&I>0&&wr>I&&wr<=2*r&&wr%2===0))continue;
  let shifts=[g,q-1,0],pins=new Map([[p,mod(-(q-1),p)],[q,0],[r,r-1]]);
  let valid=true;
  for(let [s,a] of pins){for(let i=0;i<3;i++)for(let t of [-1,1]){let intended=(s===p&&i===0&&t===1)||(s===q&&i===1&&t===1)||(s===r&&i===2&&t===1);if((mod(a+shifts[i]+t,s)===0)!==intended)valid=false;crtPins++}}
  if(!valid)continue;
  let x=0n,M=4n;
  for(let s of ps){if(s===2)continue;if(s>Z)break;let a=pins.get(s);
   if(a===undefined){a=-1;for(let j=0;j<s;j++)if(shifts.every(d=>mod(j+d-1,s)!==0&&mod(j+d+1,s)!==0)){a=j;break}if(a<0){valid=false;break}}
   let b=BigInt(s),j=bigmod((BigInt(a)-x)*inv(M,b),b);x+=M*j;M*=b;
  }
  if(!valid)continue;
  // x divisible by 3 follows because all shifts 0 mod3, only residue 0 works.
  x+=M;let A=x+BigInt(g),y=A,n=3n-A/2n,h=3,t=0,events=[];
  ok(A%6n===0n&&x>BigInt(Z),"canonical large CRT root");
  let eligible=new Map();
  for(let d of shifts){let a=x+BigInt(d),f=[[],[]];for(let s of ps){if(s===2)continue;if(s>Z)break;for(let e of [-1,1]){allFactorChecks++;if((a+BigInt(e))%BigInt(s)===0n)f[e===1?0:1].push(s)}}eligible.set(String(a),f)}
  ok(eligible.get(String(A))[0].join(",")===String(p)&&eligible.get(String(x+BigInt(q-1)))[0].join(",")===String(q)&&eligible.get(String(x))[0].join(",")===String(r),"unique designated labels");
  while(h<H){let nn=n+1n,s=Number(bigmod(nn,2n)),f=eligible.get(String(y));ok(!!f,"known center");let a=f[s].filter(z=>bigmod(nn,2n*BigInt(z))===BigInt(s?z+2:0));let label=a.length?Math.min(...a):0;
   if(label){events.push({p:label,age:t+1,pre:h});y-=BigInt(label-1);crtEvents++}
   n=nn;t++;h=Number(y/2n+n);crtTicks++;ok(h>=0&&t<=2*H,"height and time");
  }
  ok(events.length===2&&events[0].p===p&&events[1].p===q&&events[0].age===w1&&events[1].age===w1+w2&&y===x&&h===H&&t===H-3+g/2,"actual first-hit pattern");
  let extra=wr-I-1;ok(extra>=0,"continued quiet band");for(let j=0;j<extra;j++){n++;ok(bigmod(n,2n*BigInt(r))!==0n,"quiet extension");crtTicks++}
  examples.push({H,p,q,r,w1,w2,I,wr,age:t,g,extra,rootDigits:String(A).length});
  if(examples.length>=8)break;
 }
 ok(examples.length>0&&examples.some(e=>e.extra>0),"nonvacuous CRT and continued record examples");
 return{rows,roots,hits,activeHits,deficitChecks,lastChecks,firstChecks,suffixChecks,activeOne,activeTwo,sectionTransfer,examples,crtPins,crtTicks,crtEvents,allFactorChecks}
}
console.log(JSON.stringify(audit(),null,2));
