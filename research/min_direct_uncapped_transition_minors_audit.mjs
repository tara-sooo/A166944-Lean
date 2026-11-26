// Uncapped close-transition determinant identities and zero-minor variation accounting.
function audit(N=60000){
 const lim=2000000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i%2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 const st={roots:0,events:0,cap:0,blocks:0,pairs:0,close:0,detChecks:0,nonzero:0,zero:0,zeroC:0,positiveBoundChecks:0,zeroSpacingChecks:0,partitionChecks:0,bandBlocks:0,bandPairs:0,bandZeroC:0,bandZeroCNoTwinChecks:0,bandTwinBlocks:0,abstractCandidates:0,abstractActual:0,abstractZero1:0,abstractZero2:0,abstractReplayTicks:0,abstractBlocks:0,syntheticPackingChecks:0,syntheticWeightedChecks:0,nearSquareChecks:0,minorCoprimeChecks:0,examples:[],abstractExamples:[]};
 function factors(x){ok(x>0&&x<lim,"range "+x);let a=[];while(x>1){let p=spf[x];a.push(p);x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g,D=dp-6*I,e=1-2*I;z={H,t,p,w,I,e,d,dp,D,h:D/(2*p),g,q:(H-e)/p}}}return z}
 const qual=(z,T)=>z.p>=T&&z.h>0&&z.w>6&&4*z.w>=z.g&&spf[z.q]===z.q;
 function inspect(rows,T,A,B,band,abstract=false){
  let l=rows.map((z,i)=>({...z,i})).filter(z=>qual(z,T)&&(!band||(z.p<2*T&&z.D/2<T**3)));if(!l.length)return;
  let P=[0],G=0,F=0;for(let z of rows){P.push(P.at(-1)+Math.max(0,z.dp-z.d));G+=z.g}for(let z of l)F+=z.g;
  let zlists=[[],[],[]],total0=0,totalC=0,totalNZ=0,far=0,prevZero=false,chain=[l[0]],hasTwin=false,allChain=[],totalWeight=0;
  function endChain(){if(chain.length>2){for(let i=2;i<chain.length;i++){let a=chain[i-2],b=chain[i];if(a.p===b.p&&b.q-a.q===2)hasTwin=true}}allChain.push(chain.length);chain=[]}
  for(let i=1;i<l.length;i++){let u=l[i-1],v=l[i],E=v.H-u.H-u.g,delta=v.dp-u.dp,c=delta/2-3*(v.I-u.I),a=E+u.e-1-v.e,h=u.h,k=v.h,p=u.p,r=v.p,q=u.q,s=v.q;
   st.pairs++;if(band)st.bandPairs++;
   if(E>B||Math.abs(delta)>A){far+=v.g;prevZero=false;endChain();chain=[v];continue}
   st.close++;ok(a%2!==0&&a!==0&&Math.abs(a)<T&&p!==r,"close parameters");
   let j=h*s-k*(q+1),L=p*(q+1),x=h*p;
   ok(c===k*r-h*p&&a===r*s-L,"two displacements");
   ok(j*r===a*h-c*(q+1)&&j*p===a*k-c*s&&j*p*r===a*x-c*L,"minors");
   ok(mod(j-h,2)===0,"parity");st.detChecks++;
   ok(Math.abs(j)*p*r<=Math.abs(a)*x+Math.abs(c)*L,"minor bound");st.nearSquareChecks++;
   if(j!==0&&Math.abs(j)<s){ok(gcd(q+1,s)===1,"coprime cofactors");st.minorCoprimeChecks++}
   ok(u.dp<=5*(u.H+u.g)+6&&v.dp<=5*(v.H+v.g)+6,"envelope");
   if(c===0){ok(j!==0&&u.D===v.D&&u.D%(2*p*r)===0,"zero displacement");totalC+=v.g;st.zeroC++;if(band){st.bandZeroC++;chain.push(v)}else{endChain();chain=[v]}}else{endChain();chain=[v]}
   if(j===0){
    ok(c!==0&&c%a===0&&c/a>=1&&c/a<=2,"integer slope");
    let m=c/a;ok(h===m*(q+1)&&k===m*s&&u.dp===2*m*(u.H+u.g+2*u.I)+6*u.I,"zero exact");
    ok(!prevZero,"nonadjacent zero");prevZero=true;zlists[m].push({u,v,m});total0+=v.g;st.zero++;
    if(abstract){if(m===1)st.abstractZero1++;else st.abstractZero2++}
    if(st.examples.length<4)st.examples.push({abstract,p,r,q,s,h,k,a,c,j,E,H:u.H,H2:v.H,w:u.w,w2:v.w});
   }else{prevZero=false;st.nonzero++;if(c!==0)totalNZ+=v.g}
  }
  endChain();
  let cap=0;
  for(let m=1;m<=2;m++){let z=zlists[m],paid=0,prevEnd=-1;for(let i=1;i<z.length;i++){
   let a=z[i-1].v,b=z[i].u;ok(a.i<b.i&&a.i>=prevEnd,"nonoverlap");prevEnd=b.i;
   let gain=a.g,inc=b.dp-a.dp,v=P[b.i+1]-P[a.i+1];
   ok(inc>=2*m*(gain-1)-6&&v>=inc,"positive supply");paid+=v;st.zeroSpacingChecks++;
  }ok(paid<=P.at(-1),"positive budget");if(z.length){let w=z.slice(0,-1).reduce((v,z)=>v+z.v.g,0);ok((2*m*(T-1)-(2*m+6))*w<= (T-1)*paid,"weighted positive");cap+=z.at(-1).v.g} }
  // p>=T implies g>=T-1; use a deliberately looser common coefficient.
  ok(total0<=cap+(1/(2-8/(T-1))+1/(4-10/(T-1)))*P.at(-1)+1e-8,"aggregate zero variation");st.positiveBoundChecks++;
  ok(F===l[0].g+total0+totalC+totalNZ+far,"partition");st.partitionChecks++;
  if(band){st.bandBlocks++;if(!hasTwin){ok((3*T-2)*totalC<=(2*T-1)*F,"band zero capacity");st.bandZeroCNoTwinChecks++}else st.bandTwinBlocks++}
  st.blocks++;if(abstract)st.abstractBlocks++;
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;for(let i=0;i<180;i++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
  for(let T of [17,31,61]){let B=Math.floor(T/5),A=Math.floor(T/3);inspect(rows,T,A,B,false);inspect(rows,T,A,B,true)}
 }
 // Search actual MIN transitions from an abstract high-deficit plateau, not a canonical reachability claim.
 // j=0 with E=0 prescribes the first event tick exactly; then test the actual earliest second tick.
 outer:for(let p of pr.filter(x=>x>=31&&x<=500))for(let q of pr.filter(x=>x>=p&&x<=1600))for(let I=0;I<2;I++){
  let e=1-2*I,H=p*q+e;if(H+1>=lim||H%3)continue;let g=p-1,H2=H+g;if(H2%3)continue;
  for(let m=1;m<=2;m++){let n=p*(2*m+1)*(q+1)/2+2*I;if(n%2!==I)continue;let t=n-Math.ceil(g/4),u=next(H,t);st.abstractCandidates++;if(!u||u.p!==p||u.w!==n-t||u.I!==I)continue;
   let v=next(H2,n);if(!v||!qual(v,17)||!qual(u,17)||u.p===v.p)continue;
   let a=u.e-1-v.e,c=v.h*v.p-u.h*u.p,j=u.h*v.q-v.h*(u.q+1);if(j!==0)continue;
   if(Math.abs(c)>10||Math.abs(v.dp-u.dp)>12)continue;
   ok(v.h===m*v.q&&c===m*a,"constructed zero");
   for(let z of [u,v]){let found=null;for(let n=z.t+1;n<=z.t+z.w;n++){let I=n%2,e=1-2*I,d=gcd(n-2*I,z.H-e),p=factors(d).filter(f=>f%2&&f*f<=z.H+1).sort((a,b)=>a-b)[0];st.abstractReplayTicks++;if(p){found={p,I,w:n-z.t};break}}ok(found&&found.p===z.p&&found.I===z.I&&found.w===z.w,"raw replay")}
   st.abstractActual++;inspect([u,v],17,12,0,false,true);if(st.abstractExamples.length<6)st.abstractExamples.push({m,H,t,p,q,r:v.p,s:v.q,a,c,post:[u.dp,v.dp],waits:[u.w,v.w]});
   if(st.abstractActual>=20)break outer;
  }
 }
 // Algebraic packing of any two zero edges of the same positive integer slope.
 for(let m=1;m<=2;m++)for(let r of [17,31,73])for(let f of [-1,1])for(let J of [0,1])for(let I of [0,1])for(let gap of [0,2,18]){
  let H=10000,Z=H+r-1+gap,d2=2*m*(H-f)+6*J,d3=2*m*(Z+2*I)+6*I;ok(d3-d2>=2*m*(r-2)-6,"synthetic packing");st.syntheticPackingChecks++;ok((2*m*(r-1)-(2*m+6))<=d3-d2,"weighted step");st.syntheticWeightedChecks++;
 }
 ok(st.detChecks&&st.zeroC&&st.abstractActual&&st.abstractZero1&&st.abstractZero2&&st.positiveBoundChecks,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
