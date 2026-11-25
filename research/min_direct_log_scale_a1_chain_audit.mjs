// Absolute log-scale consecutive A1 chains; exact CRT lifts and complete relative gcd audit.
function audit(){
 const words=[
 [78031,54181,37501,25321,17401,11821,8161,5521,81001,56101,37861,25741,17881,12421,8581,5881],
 [91291,61441,41341,27901,19501,13441,9241,6301,95401,64921,43801,30241,21061,14461,9901,6661,96601,67021,46681,32341,21841,15121,10501,7321],
 [87931,59341,39841,27541,19081,12841,8641,5881,92581,63361,42901,29101,20161,13921,9421,6481,92401,62581,42061,29221,20101,13681,9181,6421,94261,64081,42961,29881,20521,14281,9661,6661],
 [86311,59581,41341,27901,19141,12841,8761,5881,87481,58741,39841,26701,18541,12721,8821,6121,88861,60961,41941,28921,19801,13381,9241,6421,88741,61381,42181,29221,20101,13681,9421,6361,92221,62581,43801,30241,21061,14401,9781,6661,92581,63421,42841,29581,20641,14221,9901,6781]
 ];
 const lim=400010,spf=new Int32Array(lim),primes=[];
 for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i%2)primes.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b,assert=(v,m)=>{if(!v)throw Error(m)},gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a<0n?-a:a};
 function inv(a,p){let x=1,y=0,b=p;while(b){let q=Math.floor(a/b);[a,b]=[b,a%b];[x,y]=[y,x-q*y]}assert(a===1,"inverse");return mod(x,p)}
 let st={cases:[],roots:0,marks:0,events:0,exactRelativeTicks:0,literalBigIntTicks:0,residueChecks:0,smallPrimeChecks:0,progressionCandidates:0,progressionRejected:0,goodCorridors:0,localGainChecks:0};
 for(let word of words){
  let p=word[0],m=word.length/8,N=word.length,k=Math.ceil(12*p/5),X=1n<<BigInt(k),B=4*p;
  assert(B<lim&&new Set(word).size===N&&p%4===3&&word.slice(1).every(q=>q%4===1&&spf[q]===q)&&spf[p]===p,"word primes");
  let shifts=[0];for(let s of word)shifts.push(shifts.at(-1)+s-1);
  let selected=new Map(word.map((s,i)=>[s,mod(1-shifts[i],s)])),all=primes.filter(f=>f<=B),maxP=1n<<BigInt(Math.floor(.97*k)),sqrtFloor=1n<<BigInt(Math.floor(k/2)),PP=1n,R=1,Y=1,L=4n;
  for(let f of all){let n=PP*BigInt(f);if(n<=sqrtFloor||((n<=2n*sqrtFloor)&&n*n<=X)){R=f;PP=n}else break}
  let A=0n;
  for(let f of all){
   let bf=BigInt(f);if(L*bf>maxP)break;
   let F=new Set(shifts.slice(0,-1).flatMap((g,i)=>word[i]===f?[]:[mod(1-g,f),mod(-1-g,f)])),r=selected.has(f)?selected.get(f):0;
   if(!selected.has(f))while(r<f&&F.has(r))r++;
   assert(r<f&&!F.has(r),"CRT compatibility f="+f);
   let a=mod(r-Number(A%bf),f),step=mod(a*inv(Number(L%bf),f),f);
   A+=L*BigInt(step);L*=bf;Y=f;st.smallPrimeChecks++;
  }
  assert(word.every(s=>s<=Y),"all selected in CRT");
  let first=A+((X-A+L-1n)/L)*L;assert(first>=X&&first<2n*X,"lift");
  let tail=all.filter(f=>f>Y).map(f=>({f,base:Number(first%BigInt(f)),step:Number(L%BigInt(f)),bad:new Set(shifts.slice(0,-1).flatMap(g=>[mod(1-g,f),mod(-1-g,f)]))}));
  let offset=-1;
  for(let i=0;i<100000;i++){
   st.progressionCandidates++;if(tail.some(a=>a.bad.has(mod(a.base+i*a.step,a.f)))){st.progressionRejected++;continue}offset=i;break
  }
  assert(offset>=0,"finite lift not found for "+m);
  let H0=first+BigInt(offset)*L;assert(H0>=X&&H0<2n*X&&H0%4n===0n,"absolute horizon");
  let residues=new Int32Array(B+1);
  for(let f of all)residues[f]=Number(H0%BigInt(f));
  for(let i=0;i<N;i++)for(let f of all){let v=mod(residues[f]+shifts[i],f);assert(f===word[i]?v===1:v!==1&&v!==f-1,"all stage residues");st.residueChecks++}
  let H=H0,t=H0/2n+3n,rows=[],markHorizons=[],corridors=[],tickNo=0;
  for(let i=0;i<N;i++){
   let s=word[i],d=Number(2n*t-H),w=(3*s-d-1)/2;
   assert(w>0&&Number.isInteger(w)&&BigInt(s)**2n<=H+1n,"wait eligibility");
   let isMark=i%8===0;assert(isMark?s>=47&&s>=5*(d+3)&&s>=p&&s<2*p&&s>R:s<=R&&s>.67*word[i-1]&&s<.70*word[i-1],"mark/low ratio");
   if(isMark)markHorizons.push(H);
   let preH=H,preT=t;
   for(let j=1;j<=w;j++){
    let n=t+BigInt(j),I=Number(n%2n),e=1-2*I,F=d+2*j+1-6*I;
    assert(F>0&&F<=B,"defect");
    let z=F,raw=1;
    while(z>1){let f=spf[z],power=1;while(z%f===0){z/=f;power*=f}if(mod(residues[f]+shifts[i]-e,f)===0){if(power===f)raw*=f;else{let h=H-BigInt(e),v=1;while(power% (v*f)===0&&h%BigInt(v*f)===0n)v*=f;raw*=v}}}
    assert(raw===(j===w?s:1),"relative gcd exact");
    if(j===w||tickNo%4093===0){assert(gcd(n-2n*BigInt(I),H-BigInt(e))===BigInt(raw),"literal big gcd");st.literalBigIntTicks++}
    tickNo++;st.exactRelativeTicks++;
   }
   t+=BigInt(w);H+=BigInt(s-1);
   assert(t%2n===0n&&2n*t-H===2n*BigInt(s),"post state");
   rows.push({s,d,dp:2*s,w,H:preH,t:preT});st.events++;if(isMark)st.marks++;
  }
  for(let i=0;i<N;i+=8){
   let a=i+1,b=a;while(b<N&&5*(rows[b].dp+3)>2*p)b++;
   assert(b<i+8&&10*(rows[a].d+3)>=19*p&&rows.slice(a,b+1).every(z=>z.s<=R&&10*(z.dp+3)<19*p&&z.dp>6),"full last-exit corridor");
   let gain=rows.slice(a,b+1).reduce((u,z)=>u+z.s-1,0),wait=rows.slice(a,b+1).reduce((u,z)=>u+z.w,0),drop=rows[a].d-rows[b].dp;
   assert(2*drop>=3*p&&gain===drop+2*wait,"corridor gain");
   corridors.push({mark:word[i],labels:word.slice(a,b+1),gain,wait,drop});st.goodCorridors++;
  }
  let G=Number(H-H0),elapsed=Number(t-(H0/2n+3n));assert(G===shifts[N]&&G<4*m*p&&elapsed<4*m*p,"dense chain gain/time");
  assert(markHorizons.every((h,i)=>!i||h>markHorizons[i-1]),"monotone actual marks");st.localGainChecks++;
  st.roots++;st.cases.push({m,p,R,Y,offset,rootDigits:(H0/2n+1n).toString().length,Xdigits:X.toString().length,G,elapsed,word,corridors});
 }
 assert(st.goodCorridors===15,"coverage");return st
}
console.log(JSON.stringify(audit(),null,2));
