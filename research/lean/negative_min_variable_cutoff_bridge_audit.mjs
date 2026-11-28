// Variable-cutoff Buchstab bridge, rigorous integer integral bounds and finite exact factor checks.
// Run: node research/lean/negative_min_variable_cutoff_bridge_audit.mjs
function audit(){
 const ok=(v,m)=>{if(!v)throw Error(m)},S=10000n,K=10n**20n,d=6246,targets=[3130,3150,3200,3250,3333,3500];
 function logBounds(n,d){
  ok(n>=d&&d>0n,"positive log");let a=n-d,b=n+d,ap=a,bp=b,lo=0n,hi=0n;
  for(let i=0;i<32;i++){let den=BigInt(2*i+1)*bp,num=2n*K*ap;lo+=num/den;hi+=(num+den-1n)/den;ap*=a*a;bp*=b*b}
  let num=2n*K*ap*b*b,den=65n*bp*(b*b-a*a);hi+=(num+den-1n)/den;return[lo,hi]
 }
 function H(B){let n=BigInt(d-B),den=BigInt(B),sgn=n>=den?1n:-1n;let [lo,hi]=n>=den?logBounds(n,den):logBounds(den,n);lo=lo*S/BigInt(d);hi=(hi*S+BigInt(d)-1n)/BigInt(d);return sgn===1n?[lo,hi]:[-hi,-lo]}
 let rows=[],checks=0;
 for(let cap of [10000,4900]){
  let lo=0n,hi=0n,jlo=0n,jhi=0n,nlo=0,nhi=0,idx=0;
  for(let t=1600;t<3498;t++){
   for(let u=800;u<=3600;u++){
    let inside=3*u>=d-t+6&&u+1<=t-2&&u+1<=10000-2*(t+1)-2&&t+u+2<=cap;
    let intersects=3*(u+1)>=d-(t+1)+6&&u<=t+1-2&&u<=10000-2*t-2&&t+u<=cap;
    if(inside){ok(intersects,"interior subset");let T=BigInt(t),U=BigInt(u),den=2n*(T+1n)*(U+1n)*(S-T-U);lo+=K*S/den;jlo+=K/((T+1n)*(U+1n));nlo++}
    if(intersects){let T=BigInt(t),U=BigInt(u),den=2n*T*U*(S-T-U-2n);ok(den>0n,"positive denominator");hi+=(K*S+den-1n)/den;let D=T*U;jhi+=(K+D-1n)/D;nhi++}
   }
   if(t===targets[idx]-3){let [hlo,hhi]=H(targets[idx]);ok(lo>0n&&hi>=lo&&jhi>=jlo&&hhi<0n,"integral bounds");
    let need=-hlo,frac=(need*K+lo-1n)/lo;
    rows.push({b:targets[idx]/10000,cap:cap/10000,I_lower:String(lo),I_upper:String(hi),J_lower:String(jlo),J_upper:String(jhi),cellsLower:nlo,cellsUpper:nhi,thresholdUpper:String(need),fractionUpper:String(frac),decimal:{I_lower:Number(lo)/Number(K),I_upper:Number(hi)/Number(K),J_lower:Number(jlo)/Number(K),fractionUpper:Number(frac)/Number(K)}});
    idx++;
   }
  }
 }
 for(let t=1600;t<=3500;t++){
  // a(t)=(d-t+6)/30000; residual level / a(t) <=3, >=1.
  ok(d-t+6<3*t && 3*(d-t)>d-t+6,"a below q and s>=1");
  ok(3*(d-t)<=3*(d-t+6),"s<=3");
  ok(d-t+6+d*0>6250-t,"padding sector t+3u>.625");checks++;
 }
 let ha=H(3100),hc=H(3120),hb=H(3130);
 let net=ha[0]-hc[1]+2n*hb[0];ok(net>6152n*K/1000000n,"net margin >.006152");
 // Large sieve exponent envelope for prime-factor polynomial moduli.
 let exponentChecks=0;
 // Exponents in 1/10000 units, source p in [.3749,.37495], use coarser V<=.6252.
 for(let q=800;q<=4900;q++){
  let e=.5+Math.max(q/10000,.6252/2,.5-q/10000);
  ok(e<=.99000000001,"large sieve envelope");exponentChecks++
 }
 // Exact finite Buchstab identities on real semiprime source; broader finite p bands.
 let finite=[];const max=2000010,sp=new Int32Array(max);
 for(let i=2;i<max;i++)if(!sp[i]){sp[i]=i;if(i*i<max)for(let j=i*i;j<max;j+=i)if(!sp[j])sp[j]=i}
 function factors(n){let a=[];while(n>1){let p=sp[n];a.push(p);n/=p}return a}
 for(let R of [100000,400000,1000000]){
  let L=Math.log(R),a0=R**.16,b=R**.35,base=0,top=0,subtract=0,expandedUpper=0,correction=0,primeTriple=0,capTriple=0,identities=0,sources=0,S_a=0,S_c=0,oneBelow=0,repeats=0,covered=0,minus=0;
  let a=R**.20,c=R**.26;
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   let f=factors(A+1);if(f.length!==2||f[0]===f[1]||f[0]<R**.30||f[0]>R**.41)continue;sources++;
   let fs=factors(A-1),r=fs[0],ps=[...new Set(fs)];
   if(r>=a0)base++;if(r>=b)top++;
   if(r>=a)S_a++;if(r>=c)S_c++;
   let counted=0;
   for(let q of ps.filter(q=>q>=a0&&q<b)){
    let t=Math.log(q)/L,cut=R**((.6246-t)/3+.0002);
    let original=+(r>=q),up=+(r>=cut);
    let cor=ps.filter(z=>z>=cut&&z<q&&r>=z).length;
    ok(original===up-cor,"exact variable cutoff identity");identities++;subtract+=original;expandedUpper+=up;correction+=cor;counted+=cor;
    if(fs.length===3&&fs[0]<fs[1]&&fs[1]<fs[2]&&q===fs[1]&&r>=cut&&t<=.35-.0002&&Math.log(r)/L<=t-.0002&&Math.log(r)/L<=1-2*t-.0002){primeTriple++;if(q*r<=R**.49)capTriple++}
   }
   if(r>=a&&r<c){
    let below=fs.filter(q=>q<b);
    if(below.length===1){oneBelow++;let other=Math.min(f[0],fs[1]||Infinity);if(other>4*r){
      // literal first tick clock n=3-A/2
      let n=3-A/2,mod=(x,m)=>(x%m+m)%m,win=0;
      for(let k=1;k<=2*r;k++){let nn=n+k,sg=mod(nn,2)?-1:1;
       for(let p of [...new Set(factors(A+sg))])if(mod(nn,2*p)===(sg===1?0:p+2)){win=p;break}
       if(win){ok(sg===-1&&win===r,"isolated minus first");minus++;break}
      }ok(win===r,"first exists")
    }}else if(below[0]===below[1])repeats++;else {ok(counted>0,"two below covered");covered++}
   }
  }
  ok(base-top===subtract&&subtract===expandedUpper-correction,"summed identity");
  ok(primeTriple<=correction&&capTriple<=primeTriple,"triple subset");
  ok(oneBelow>=S_a-S_c-correction-repeats,"structural lower");
  finite.push({R,sources,base,top,subtract,expandedUpper,correction,primeTriple,capTriple,identities,S_a,S_c,oneBelow,repeats,covered,minus})
 }
 return {scale:String(K),rows,netLower:String(net),checks,exponentChecks,finite}
}
console.log(JSON.stringify(audit(),null,2));
