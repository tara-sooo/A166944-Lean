// Coarse scalar model diagnostic, NOT MIN. Run: node research/infinite-orbit/coarse_scale_audit.mjs
function scaleAudit(){
 const N=500000, s=new Uint8Array(N+1);let primes=[];for(let i=2;i<=N;i++)if(!s[i]){primes.push(i);if(i*i<=N)for(let j=i*i;j<=N;j+=i)s[j]=1}
 function ok(x,m){if(!x)throw Error(m)}
 let results=[];
 for(let X of [65536,262144,1048576,4194304]){
   let S=7,K=210,V=12; // finite diagnostic parameters, not asymptotic S(X)
   let safe=h=>Math.min(h%K,K-h%K)>V;
   let H=X;while(!safe(H))H+=2;let start=H,t=(H+6)/2,d=6,events=0,G=0,W=0,cut=0,bypass=0,clockViolations=0,divisibilityViolations=0,prev=0,unique=new Set(),band=primes.filter(p=>p>=Math.ceil(Math.sqrt(X)/2)&&p<=Math.floor(Math.sqrt(X)));
   while(H<16*X){
     let p=band.find(p=>p!==prev&&safe(H+p-1));ok(p!==undefined,"safe prime");
     let g=p-1,w=p,post=H+g,oldD=d;
     for(let J=Math.ceil(H/K)*K;J<post;J+=K){ok(J>H,"no anchor");cut++;if(J-H>V&&post-J>V/2)bypass++}
     t+=w;d+=2*w-g;G+=g;W+=Math.abs(d-oldD);events++;unique.add(p);
     ok(d===2*t-post&&d>=0&&w<=2*p&&p*p<=H+1,"coarse constraints");
     ok(safe(H)&&safe(post),"safe endpoints");
     if((t%2===0?H-1:H+1)%p!==0)divisibilityViolations++;
     if((t%2===0?t:t-2)%p!==0)clockViolations++;
     H=post;prev=p
   }
   ok(cut===bypass,"all lattice cuts bypass");ok(W>=G,"variation");
   results.push({X,S,K,V,events,gain:G,variation:W,distinctLabels:unique.size,cut,bypass,divisibilityViolations,clockViolations,initialH:start,finalH:H});
 }
 return results;
}
console.log(JSON.stringify(scaleAudit(),null,2));
