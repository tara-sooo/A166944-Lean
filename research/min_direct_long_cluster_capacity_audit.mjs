// Deterministic disjoint barrier-free runs and long-run smoothing capacity.
function audit(){
 const st={periods:0,positions:0,tests:0,longRuns:0,zeroStarts:0,nonzeroGainTests:0,maxGain:0};
 const ps=[3,5,7,11,13,17,19];let seed=12345;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n},mod=(a,p)=>(a%p+p)%p;
 for(let n=2;n<=6;n++){
  let p=ps.slice(0,n),P=p.reduce((a,b)=>a*b,1),pre=new Int32Array(P+1);
  for(let j=0;j<P;j++)pre[j+1]=pre[j]+(p.every(s=>j%s<=(s-3)/2)?1:0);
  let A=pre[P],cnt=j=>Math.floor(j/P)*A+pre[mod(j,P)];st.periods++;
  for(let K of [4,8,16,32,64,Math.ceil(P**(4/11))*8,4*P]){
   let l=Math.min(P,Math.floor(K/4)),zpre=new Int32Array(P+1),sum=0;
   for(let j=0;j<P;j++){let c=cnt(j+l)-cnt(j);zpre[j+1]=zpre[j]+(c===0);sum+=(P*c/(A*l)-1)**2;st.positions++}
   let var0=sum/P,zcount=j=>Math.floor(j/P)*zpre[P]+zpre[mod(j,P)];
   if(zpre[P]/P>var0+1e-10)throw Error("zero");
   for(let trial=0;trial<100;trial++){
    let a=rnd(2*P)-P,b=a+1+rnd(2*P),pos=a,G=0,starts=0;
    while(pos<b){
     if(cnt(pos+1)!==cnt(pos)){pos++;continue}
     let end=pos+1;while(end<b&&cnt(end+1)===cnt(pos))end++;
     // select a subinterval of the barrier-free interval
     let x=pos+rnd(end-pos),y=x+1+rnd(end-x);
     if(2*(y-x)>K){if(cnt(y)!==cnt(x)||y-x<2*l)throw Error("run");let s=y-x-l+1;if(zcount(y-l+1)-zcount(x)!==s)throw Error("starts");G+=2*(y-x);starts+=s;st.longRuns++;st.zeroStarts+=s}
     pos=end;
    }
    if(l===P&&G!==0||G>4*starts||starts>zcount(b)-zcount(a)||G>4*(b-a+P)*var0+1e-7)throw Error("gain");
    st.tests++;if(G){st.nonzeroGainTests++;st.maxGain=Math.max(st.maxGain,G)}
   }
  }
 }
 return st
}
console.log(JSON.stringify(audit(),null,2));
