// First-significant stopping and weighted first-bad arrival controls.
function audit(){
 const maxR=1000000,limit=4*maxR,spf=new Uint32Array(limit+1);
 for(let p=2;p*p<=limit;p++)if(!spf[p])for(let n=p*p;n<=limit;n+=p)if(!spf[n])spf[n]=p;
 const mod=(a,b)=>(a%b+b)%b;
 function ck(c,m){if(!c)throw Error(m)}
 function fs(n){ck(n>=1&&n<=limit,"factor domain "+n);let out=[];while(n>1){let p=spf[n]||n;out.push(p);while(n%p===0)n/=p}return out}
 function gcd(a,b){while(b){let z=a%b;a=b;b=z}return Math.abs(a)}
 function ev(u,v){let fm=fs(u-1),fp=fs(u+1),w=Infinity,p=Infinity,e=0;for(let [f,s] of [[fm,1],[fp,-1]])for(let r of f){let t=mod((s===1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){w=t;p=r;e=s}}return {p,w,e,twin:fm[0]===u-1&&fp[0]===u+1,q:Math.min(fm[0],fp[0])}}
 function choose(n,k){if(n<k)return 0;let v=1;for(let i=1;i<=k;i++)v=v*(n-i+1)/i;return v}
 let out=[];
 for(let [R,T,y,m] of [[100000,127,3,3],[100000,251,3,4],[1000000,127,3,4],[1000000,503,5,4],[1000000,997,5,5]]){
  // Exact restricted gains from the already audited tables (3 -> 4, 5 -> 14).
  const Q=y===3?4:14,C=1,B=4,j=Math.floor(B/2)+1;
  ck(20*Q<=T-1,"small relay hypothesis");
  const K=40*(C+1)*(m+1),P=100*(C+1)*(m+1)*T;
  const deg=U=>fs(U).filter(p=>p>y&&p<=P).length+fs(U+2).filter(p=>p>y&&p<=P).length;
  let a={R,T,y,m,Q,K,P,B,roots:0,events:0,low:0,medium:0,fastHigh:0,significantStop:0,mediumStop:0,twinSignificantStop:0,firstBadRoots:0,goodSignificantRoots:0,maxGain:0,maxNonlow:0,maxHigh:0,maxLowRelay:0,maxMediumStopGain:0,maxFirstBadMultiplicity:0,maxGoodCarrierMultiplicity:0,degreeTail:0,degreeMomentUpper:0,reverseChecks:0,deficitChecks:0,literalTicks:0,firstBadControls:0,roughChecks:0,example:null};
  const bad=new Map(),good=new Map();
  for(let U=R;U<3*R;U+=2){let c=fs(U).filter(p=>p>y&&p<=P).length,d=fs(U+2).filter(p=>p>y&&p<=P).length;if(c+d>B)a.degreeTail+=c+d;a.degreeMomentUpper+=2*j*(choose(c,j)+choose(d,j))}
  ck(a.degreeTail<=a.degreeMomentUpper,"weighted degree tail");
  for(let X=Math.ceil(R/6)*6;X<2*R;X+=6){
   a.roots++;let u=X,v=X/2+3,H=0,M=0,L=0,h=0,b=0,run=0,firstBad=null,nonlow=0;
   while(true){
    let z=ev(u,v),{p,w,e,twin,q}=z,g=p-1,d=2*v-u;
    ck(u-X===H+M+L,"gain partition");ck(d>=0,"deficit");
    ck(3*H<=4*6+20*(M+L),"deficit budget");
    ck(L<=Q*(h+b+1),"low relay budget");ck(u-X<=P&&h+b<=K,"prefix cap");
    a.deficitChecks++;a.maxGain=Math.max(a.maxGain,u-X);a.maxNonlow=Math.max(a.maxNonlow,nonlow);a.maxHigh=Math.max(a.maxHigh,h);
    if(p>=T&&8*w>=g){
     a.significantStop++;if(twin)a.twinSignificantStop++;
     ck(16*q>=T-1,"roughness");a.roughChecks++;
     if(firstBad===null){a.goodSignificantRoots++;good.set(u,(good.get(u)||0)+1)}
     if(!a.example&&b===m&&firstBad===null)a.example={X,u,d,p,w,h,b,H,M,L};
     break;
    }
    if(p>y&&p<T&&b===m){a.mediumStop++;a.maxMediumStopGain=Math.max(a.maxMediumStopGain,u-X+g);break}
    if(X<R+30&&w<1000)for(let i=1;i<=w;i++){let n=v+i,G=gcd(n%2?n-2:n,n%2?u+1:u-1);ck(i===w?(spf[G]||G)===p:G===1,"literal GCD");a.literalTicks++}
    let U=u+g;ck((e===1?U:U+2)%p===0,"reverse identity");a.reverseChecks++;
    if(p<=y){L+=g;run+=g;a.low++;ck(run<=Q,"low run");a.maxLowRelay=Math.max(a.maxLowRelay,run)}
    else{
     nonlow++;run=0;
     ck(p<=P,"preceding label bound");
     if(p<T){b++;M+=g;a.medium++}else{h++;H+=g;a.fastHigh++;ck(8*w<g,"fast high")}
     let D=deg(U);
     if(D>B&&firstBad===null){firstBad=U;bad.set(U,(bad.get(U)||0)+1);a.firstBadControls++}
    }
    u=U;v+=w;a.events++;
   }
   if(firstBad!==null)a.firstBadRoots++;
  }
  ck(a.significantStop+a.mediumStop===a.roots,"partition");
  for(let n of bad.values())a.maxFirstBadMultiplicity=Math.max(a.maxFirstBadMultiplicity,n);
  for(let n of good.values())a.maxGoodCarrierMultiplicity=Math.max(a.maxGoodCarrierMultiplicity,n);
  a.firstBadOffsets=bad.size;a.goodSignificantOffsets=good.size;
  out.push(a);
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
