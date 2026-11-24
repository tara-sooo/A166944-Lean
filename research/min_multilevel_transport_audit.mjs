// Two-tier projected stopping and exact dyadic first-mark/transport budget audit.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,L=210,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=b=>{if(!b)throw Error("assertion")},mod=(x,m)=>(x%m+m)%m,gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return a};
 function hit(t,C,K){let u=K+1,q=0;for(let s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let h=t+1+mod((s===-1?0:p+2)-t-1,2*p);if(h<u||(h===u&&p<q)){u=h;q=p}while(v%p===0)v/=p}}return [u,q]}
 function rAt(C){let r=Math.min(spf[C-1],spf[C+1]);return r<=B?r:0}
 let Skey=0,keys=0;for(let p=11;p<=B;p++)if(spf[p]===p)for(let s of [-1,1]){let D=2*X+mod(-s-2*X,p);if(D%2)D+=p;for(;D<7*X;D+=2*p){Skey+=rAt(D);keys++}}
 let arithmetic=null;
 if(X<=16384){let Amin=0,roughPairs=0,roughPairs31=0,triples=0;for(let q=11;q<=B;q++)if(spf[q]===q)for(let s of [-1,1]){let D=2*X+mod(-s-2*X,q);if(D%2)D+=q;for(;D<7*X;D+=2*q){let r=rAt(D);for(let g=0;g<L&&D+q-1+g<7*X;g+=2){let v=rAt(D+q-1+g);if(!v)continue;Amin+=Math.min(r,v);triples++;if(Math.min(r,v)>=Math.ceil(Math.exp(Math.sqrt(Math.log(B)))))roughPairs++;if(Math.min(r,v)>=31)roughPairs31++}}}arithmetic={Amin,roughPairs,roughPairs31,triples}}
 const base=Math.max(2,Math.floor(B/8)),modes=[[base,base,1],[base,2*base,1],[base,4*base,2],[Math.max(2,Math.floor(B/4)),B,2]];
 const results=[];
 for(let [lo,hi,F] of modes){
  const head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N),t=new Int32Array(N),K=new Int32Array(N),prevP=new Int32Array(N),prevD=new Int32Array(N),prevR=new Int32Array(N),prevMass=new Int32Array(N),lowGain=new Int32Array(N),maxLevel=new Int32Array(N);
  const push=(i,C)=>{next[i]=head[C/2];head[C/2]=i};
  for(let i=0;i<N;i++){let M=X+2*i+1;t[i]=M+2;K[i]=Math.floor((7*M-1)/4);push(i,2*M-2)}
  let s={lo,hi,F,R:0,lowR:0,upR:0,transportR:0,events:0,high:0,stopped:0,upperOnly:0,upOnly:0,both:0,sinks:0,twin:0,bad:0,maxPassed:0,maxUp:0,literal:0,transportTags:0,upTags:0,transportMin:0,transportCandidateMin:0,transportCandidateCount:0,largePassed:0,largePassedTags:0,largePassedR:0,stopTransport:0,stopUp:0,levels:[2,4,8,16,32,64,128,256,512,1024,2048].filter(k=>k<=N).map(k=>({k,first:0,rr31:0,rrZ:0,rise:0,transport:0,firstR:0,transportFirstR:0,stopFirst:0}))};
  let Z=Math.ceil(Math.exp(Math.sqrt(Math.log(B)))),prevCandidates=new Set();
  for(let C=2*X;C<7*X;C+=2){
   let i=head[C/2];if(i<0)continue;let groups=new Map(),r=rAt(C);
   while(i>=0){let j=next[i],[n,p]=hit(t[i],C,K[i]);if(X<=1024){let nn=K[i]+1,pp=0;for(let k=t[i]+1;k<=K[i];k++){let g=gcd(k%2?k-2:k,C+(k%2?1:-1));if(g>1&&spf[g]<=B){nn=k;pp=spf[g];break}}ck(n===nn&&p===pp);s.literal++}
    if(!p){if(spf[C-1]===C-1&&spf[C+1]===C+1)s.twin++;else s.bad++}
    else if(p<=7){ck(r>0&&n-t[i]<=2*r);lowGain[i]+=p-1;ck(lowGain[i]<L);s.R+=r;s.lowR+=r;s.events++;t[i]=n;ck(C+p-1<=2*n);push(i,C+p-1)}
    else{if(!groups.has(p))groups.set(p,[]);groups.get(p).push([i,n])}i=j
   }
   for(let [p,a] of groups){
    let up=0;for(let [i,n] of a)if(!prevP[i]||r>F*prevR[i])up++;
    let upper=a.length>=hi,rising=up>=lo,stop=upper||rising;
    for(let [i,n] of a){
     let old=prevP[i],D=prevD[i],r0=prevR[i],g=old?C-D-old+1:0; if(old){ck(g>=0&&g<L&&g%2===0);ck((D-1)%old===0||(D+1)%old===0);ck((C-g)%old===0||(C-g+2)%old===0);ck(r0===rAt(D))}
     let isUp=!old||r>F*r0;
     for(let l of s.levels)if(maxLevel[i]<l.k&&a.length>=l.k){if(old)ck(prevMass[i]<l.k);l.first++;l.firstR+=r;if(isUp)l.rise++;else{l.transport++;l.transportFirstR+=r}if(old&&Math.min(r,r0)>=31)l.rr31++;if(old&&Math.min(r,r0)>=Z)l.rrZ++;if(stop)l.stopFirst++}
     maxLevel[i]=Math.max(maxLevel[i],a.length);
     if(stop){if(isUp)s.stopUp++;else s.stopTransport++;continue}
     ck(r>0&&n-t[i]<=2*r);s.R+=r;s.events++;s.high++;
     if(isUp){s.upR+=r;s.upTags++}else{s.transportR+=r;s.transportTags++;let mn=Math.min(r,r0);ck(r<=F*mn);s.transportMin+=mn;let key=(D*B+old)*L+g;if(!prevCandidates.has(key)){prevCandidates.add(key);s.transportCandidateMin+=mn;s.transportCandidateCount++}}
     lowGain[i]=0;prevP[i]=p;prevD[i]=C;prevR[i]=r;prevMass[i]=a.length;t[i]=n;ck(C+p-1<=2*n);push(i,C+p-1)
    }
    if(stop){s.stopped+=a.length;s.sinks++;if(upper&&rising)s.both+=a.length;else if(upper)s.upperOnly+=a.length;else s.upOnly+=a.length}
    else{s.maxPassed=Math.max(s.maxPassed,a.length);s.maxUp=Math.max(s.maxUp,up);if(a.length>=lo){s.largePassed++;s.largePassedTags+=a.length;s.largePassedR+=r*a.length}}
   }
  }
  ck(s.stopped+s.twin+s.bad===N);ck(s.upperOnly+s.upOnly+s.both===s.stopped&&s.stopTransport+s.stopUp===s.stopped);
  ck(s.maxPassed<hi&&s.maxUp<lo);ck(s.R===s.lowR+s.upR+s.transportR);ck(s.upR<=(lo-1)*Skey);ck(s.transportR<=F*s.transportMin&&s.transportMin<=(hi-1)*s.transportCandidateMin);
  ck(s.lowR<=1.5*L*(N+(hi-1)*keys));if(arithmetic)ck(s.transportCandidateMin<=arithmetic.Amin);
  for(let l of s.levels)ck(l.first===l.rise+l.transport&&l.first<=N);
  results.push(s)
 }
 return {X,B,N,L,base,Skey,keys,arithmetic,results};
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
