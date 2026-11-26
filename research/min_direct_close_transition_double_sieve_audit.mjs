// Bounded-multiplier close transitions: exact linear, CRT, double-sieve residue and gain-partition checks.
function audit(N=40000){
 const limit=1000000,spf=new Int32Array(limit),pr=[];
 for(let i=2;i<limit;i++)if(!spf[i]){spf[i]=i;if(i%2)pr.push(i);if(i*i<limit)for(let j=i*i;j<limit;j+=i)if(!spf[j])spf[j]=i}
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function inv(a,b){let x=1,y=0,c=b;a=mod(a,b);while(c){let q=Math.floor(a/c);[a,c]=[c,a-q*c];[x,y]=[y,x-q*y]}ok(a===1,"inverse");return mod(x,b)}
 function factors(x){ok(x>0&&x<limit,"range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<=1;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g,D=dp-6*I;z={H,t,p,I,e:1-2*I,w,d,dp,D,h:D/(2*p),g}}}return z}
 const st={roots:0,events:0,cap:0,blocks:0,selected:0,pairs:0,near:0,nearDirect:0,nearRelay:0,nearZeroChange:0,nearDifferentH:0,nearDown:0,nearUp:0,largeRelay:0,largeVariation:0,linear:0,crt:0,roughChecks:0,progressionChecks:0,samePExcluded:0,sameMultiplier:0,gcdDivisibility:0,tradeoffChecks:0,tupleGroups:0,tupleCapacity:0,primeLineControls:0,primeLineResidueChecks:0,horizonControls:0,horizonResidueChecks:0,examples:[]};
 function inspect(rows,T,Hmax,B,A,mode){
  if(!rows.length)return;
  let list=[],G=rows.reduce((s,z)=>s+z.g,0),V=rows.reduce((s,z)=>s+Math.abs(z.dp-z.d),0),F=0,nearG=0,relayG=0,moveG=0,Etotal=0,changeTotal=0,groups=new Map;
  for(let i=0;i<rows.length;i++){let z=rows[i];if(z.p>=T&&z.h>=1&&z.h<=Hmax&&Number.isInteger(z.h)&&(mode===0?4*z.w>=z.g:true)){list.push({...z,i});F+=z.g;st.selected++}}
  for(let j=1;j<list.length;j++){
   let a=list[j-1],b=list[j],E=b.H-a.H-a.g,diff=b.dp-a.dp,c=diff/2-3*(b.I-a.I);
   ok(E>=0&&E%2===0&&c===b.h*b.p-a.h*a.p,"linear");st.linear++;st.pairs++;Etotal+=E;changeTotal+=Math.abs(diff);
   ok(c%gcd(a.h,b.h)===0,"gcd");st.gcdDivisibility++;
   if(a.h===b.h&&a.p!==b.p){ok(Math.abs(diff)>=4*a.h-6,"same multiplier");st.sameMultiplier++}
   if(a.p===b.p){ok(E>=a.p-3,"same p relay");st.samePExcluded++}
   if(E>B){relayG+=b.g;st.largeRelay++;continue}
   if(Math.abs(diff)>A){moveG+=b.g;st.largeVariation++;continue}
   if(4*a.w<a.g){ // mode 1: no first-long assumption; record only raw arithmetic, no roughness claim
    moveG+=b.g;continue
   }
   ok(a.p!==b.p&&c!==0,"near distinct");ok(b.p*2*Hmax>=a.p&&b.p<=2*Hmax*a.p,"comparable");
   let r=b.p,p=a.p,P=p*r,x=a.e+p*mod((b.e-a.g-E-a.e)*inv(p,r),r);
   ok(mod(a.H-x,P)===0,"CRT");st.crt++;
   let z=Math.min(97,Math.floor((a.w-1)/2),p-1,r-1);
   for(let f of pr){if(f>z)break;ok(mod(a.H-1,f)!==0&&mod(a.H+1,f)!==0,"rough");let x1=mod((1-x)*inv(P,f),f),x2=mod((-1-x)*inv(P,f),f),u=(a.H-x)/P;ok(x1!==x2&&mod(u,f)!==x1&&mod(u,f)!==x2,"progression roots");st.roughChecks++;st.progressionChecks++}
   let k=[a.h,b.h,c,a.p,b.p,a.I,b.I,E].join(","),q=groups.get(k)||{min:a.H,max:a.H,n:0,P,x,hs:new Set};ok(!q.hs.has(a.H),"distinct H");q.hs.add(a.H);q.min=Math.min(q.min,a.H);q.max=Math.max(q.max,a.H);q.n++;groups.set(k,q);
   nearG+=b.g;st.near++;if(E===0)st.nearDirect++;else st.nearRelay++;if(diff===0)st.nearZeroChange++;if(a.h!==b.h)st.nearDifferentH++;if(diff<0)st.nearDown++;if(diff>0)st.nearUp++;
   if(st.examples.length<5&&E>0&&a.h!==b.h)st.examples.push({p:a.p,r:b.p,h:a.h,k:b.h,E,diff,c,H:a.H,H2:b.H,w:a.w,w2:b.w,relay:rows.slice(a.i+1,b.i).map(z=>z.p)})
  }
  for(let q of groups.values()){ok(q.n<=Math.floor((q.max-q.min)/q.P)+1,"tuple capacity");st.tupleGroups++;st.tupleCapacity++}
  ok(Etotal<=G-F&&changeTotal<=V,"disjoint relay and variation");
  let first=list[0]?.g||0;ok(F===first+nearG+relayG+moveG,"partition gain");
  if(mode===0){let C=Math.max(...rows.map(z=>z.p));ok((F-first-nearG)*(B+1)*(A+1)<=C*((A+1)*(G-F)+(B+1)*V),"gain tradeoff");st.tradeoffChecks++}
  st.blocks++;
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
  // Small finite thresholds: A/2+3 <= T/2, B<T-3.
  for(let [T,h,B,A] of [[11,4,4,4],[17,8,8,8],[29,16,12,16]])inspect(rows,T,h,B,A,0);
 }
 // Exhaust exact linear parametrizations and forbidden residues for fixed positive multipliers.
 for(let h=1;h<=8;h++)for(let k=1;k<=8;k++)for(let c=-18;c<=18;c++)if(c!==0){
  let g=gcd(h,k);if(c%g)continue;let a=h/g,b=k/g,d=c/g,p0=b===1?0:mod(-d*inv(a,b),b),r0=(a*p0+d)/b;ok(Number.isInteger(r0)&&b*r0-a*p0===d,"line determinant");
  for(let f of pr.filter(f=>f<=47&&f>8)){let u=mod(-p0*inv(b,f),f),v=mod(-r0*inv(a,f),f);ok((u===v)===(d%f===0),"line collision");for(let x=0;x<f;x++){ok((mod(p0+b*x,f)===0)===(x===u)&&(mod(r0+a*x,f)===0)===(x===v),"line root");st.primeLineResidueChecks++}}
  st.primeLineControls++;
 }
 for(let p of [31,43,61,101])for(let r of [37,47,67,103])for(let e of [-1,1])for(let f of [-1,1])for(let E of [0,2,6,12]){
  let P=p*r,x=e+p*mod((f-p+1-E-e)*inv(p,r),r);ok(mod(x,p)===mod(e,p)&&mod(x+p-1+E,r)===mod(f,r),"abstract CRT");
  for(let l of pr.filter(l=>l<31)){let a=mod((1-x)*inv(P,l),l),b=mod((-1-x)*inv(P,l),l);ok(a!==b,"two roots");for(let u=0;u<l;u++){ok([a,b].includes(u)===[1,l-1].includes(mod(x+P*u,l)),"horizon root");st.horizonResidueChecks++}}
  st.horizonControls++;
 }
 ok(st.nearDirect&&st.nearRelay&&st.nearDifferentH&&st.nearUp&&st.nearDown&&st.largeRelay&&st.largeVariation&&st.roughChecks&&st.tradeoffChecks,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||40000)),null,2));
