// Node.js: exact full budget with low-only gains charged to preceding high event.
function lowForest(X){
 const B=Math.ceil(Math.sqrt(7*X)),spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const check=b=>{if(!b)throw Error("check")},gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return a};
 function hit(t,C,K){let u=K+1,q=0;for(let s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let m=2*p,r=s===-1?0:p+2,h=t+1+((r-t-1)%m+m)%m;if(h<u||(h===u&&p<q)){u=h;q=p}while(v%p===0)v/=p}}return [u,q]}
 const ys=[3,5,7,11,13],Ls=[6,30,210,2310,30030],cuts=[Math.ceil(Math.sqrt(B)),Math.ceil(B/Math.log(B)**(2/3)),Math.ceil(B/Math.log(B)**(1/16))];
 const st=ys.map((y,i)=>({y,L:Ls[i],initial:0,last:0,forest:0,surplus:0,chronological:0,allEdges:0,surplusEdges:0,cyclesAbove:cuts.map(u=>({u,count:0,excess:0})),maxWeight:0,high:0,distinct:0}));
 let R=0,events=0,literal=0;
 for(let M=X+1;M<2*X;M+=2){
  let t=M+2,C=2*M-2,K=Math.floor((7*M-1)/4),w=[];
  for(;;){let [u,p]=hit(t,C,K);if(X<=1024){let v=K+1,q=0;for(let j=t+1;j<=K;j++){let g=gcd(j%2?j-2:j,C+(j%2?1:-1));if(g>1&&spf[g]<=B){v=j;q=spf[g];break}}check(u===v&&p===q);literal++}if(!p)break;let r=Math.min(spf[C-1],spf[C+1]);check(u-t<=2*r);R+=r;events++;w.push([p,r]);C+=p-1;t=u;check(C<=2*t)}
  for(let s of st){
   let init=0,lg=0,high=[],weights=[];
   for(let [p,r] of w){if(p<=s.y){lg+=p-1;if(!high.length)init+=r;else weights[weights.length-1]+=r}else{check(lg<s.L);lg=0;high.push(p);weights.push(r)}}
   check(lg<s.L);s.initial+=init;s.high+=high.length;
   if(!high.length)continue;
   let ps=[...new Set(high)],ids=high.map(p=>ps.indexOf(p)),par=ps.map((_,i)=>i),root=i=>{while(par[i]!==i)i=par[i];return i},edges=[];
   s.last+=weights[weights.length-1];s.distinct+=ps.length;
   for(let j=0;j<weights.length;j++){check(2*weights[j]<=2*B+3*s.L);s.maxWeight=Math.max(s.maxWeight,weights[j]);if(j+1<weights.length){edges.push([ids[j],ids[j+1],weights[j]]);s.allEdges++}}
   for(let [u,v,r] of edges){if(root(u)===root(v))s.chronological+=r;else par[root(v)]=root(u)}
   for(let i=0;i<par.length;i++)par[i]=i;
   edges.sort((a,b)=>b[2]-a[2]);let f=0,c=0;
   for(let [u,v,r] of edges){if(root(u)===root(v)){s.surplus+=r;s.surplusEdges++;c++;for(let z of s.cyclesAbove)if(r>=z.u){z.count++;z.excess+=r-z.u+1}}else{par[root(v)]=root(u);s.forest+=r;f++}}
   check(f===ps.length-1&&c===high.length-ps.length);
  }
 }
 for(let s of st){check(s.initial+s.last+s.forest+s.surplus===R);check(s.surplus<=s.chronological);check(s.surplusEdges===s.high-s.distinct);check(2*(s.last+s.forest)<=(2*B+3*s.L)*s.distinct)}
 return {X,B,R,events,literal,st};
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(lowForest(Number(a))));
