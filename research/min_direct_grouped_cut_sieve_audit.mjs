// Grouped Bonferroni envelopes and all-label pinned-cut endpoint corridors.
function audit(N=60000){
 const lim=1800000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i%2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(v,m)=>{if(!v)throw Error(m)};
 const st={roots:0,events:0,cap:0,pointwise:0,meanExact:0,expansionChecks:0,upperTerms:0,lowerTerms:0,maxSupport:0,dyadicChecks:0,cuts:0,extendedCuts:0,anchors:0,extendedAnchors:0,oldAnchorRemoved:0,launch:0,landing:0,bypass:0,completed:0,pending:0,clean:0,witness:0,cleanLaunch:0,cleanLanding:0,largeLaunch:0,largeLanding:0,fast:0,drop:0,disjoint:0,localizedBudgets:0,anchorBudget:0,examples:[]};
 function choose(n,k){if(k<0||k>n)return 0n;let v=1n;for(let j=1;j<=k;j++)v=v*BigInt(n-j+1)/BigInt(j);return v}
 function U(n,k){let a=0n;for(let i=0;i<=k;i++)a+=(i%2?-1n:1n)*choose(n,i);return a}
 let seed=3229;function rand(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n}
 // Pointwise Bonferroni products, including negative lower factors.
 for(let i=0;i<50000;i++){let m=1+rand(8),ns=Array.from({length:m},()=>rand(15)),ks=Array.from({length:m},()=>2*rand(5)),us=ns.map((n,j)=>U(n,ks[j])),gs=ns.map((n,j)=>choose(n,ks[j]+1)),prod=us.reduce((a,b)=>a*b,1n),lo=prod;
  for(let j=0;j<m;j++){ok(us[j]>=BigInt(ns[j]===0),"upper");lo-=gs[j]*us.reduce((a,b,k)=>k===j?a:a*b,1n)}
  let truth=BigInt(ns.every(n=>!n));ok(lo<=truth&&truth<=prod,"grouped envelope");st.pointwise++}
 // Exact expectation and formal expansion (coefficients integer, weights rational).
 for(let test=0;test<250;test++){
  let m=2+rand(3),groups=[],pos=2+rand(5);for(let j=0;j<m;j++){let n=1+rand(4);groups.push(pr.slice(pos,pos+n));pos+=n}
  let all=groups.flat(),D=all.reduce((a,p)=>a*BigInt(p),1n),trueNum=all.reduce((a,p)=>a*BigInt(p-2),1n),k=2;
  function poly(ps,gap){let out=[];for(let mask=0;mask<2**ps.length;mask++){let n=0,q=1n;for(let j=0;j<ps.length;j++)if(mask>>j&1){n++;q*=BigInt(ps[j])}
    if(gap?n!==k+1:n>k)continue;out.push({q,n,coef:gap?1n:n%2?-1n:1n});}return out}
  function combine(list){let r=[{q:1n,n:0,coef:1n}];for(let a of list)r=r.flatMap(x=>a.map(y=>({q:x.q*y.q,n:x.n+y.n,coef:x.coef*y.coef})));return r}
  let up=groups.map(g=>poly(g,false)),gaps=groups.map(g=>poly(g,true)),terms=combine(up),low=terms.map(x=>({...x}));
  for(let j=0;j<m;j++)low.push(...combine(up.map((a,i)=>i===j?gaps[j]:a)).map(x=>({...x,coef:-x.coef})));
  function num(t){return t.reduce((a,x)=>a+x.coef*(2n**BigInt(x.n))*(D/x.q),0n)}
  ok(num(low)<=trueNum&&trueNum<=num(terms),"exact mean");st.meanExact++;st.upperTerms+=terms.length;st.lowerTerms+=low.length;
  for(let t of [...terms,...low]){ok(D%t.q===0n&&t.n<=m*k+1,"support");st.maxSupport=Math.max(st.maxSupport,t.n);st.expansionChecks++}
 }
 for(let j=2;j<=50;j++){let L=2**j,k=2*Math.ceil(Math.log(j+2));let s=0;for(let i=0;i<j;i++)s+=L/2**i;ok(s<=2*L&&k*s+L<=(2*k+1)*L,"log product");st.dyadicChecks++}
 function factors(x){ok(x>0&&x<lim,"factor range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=((I?p+2:0)-t)%(2*p);w=(w+2*p)%(2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g;z={H,p,w,d,dp,g,Z:H+g}}}return z}
 const configs=[{S:5,R:7,V:14,K:30,Z:97},{S:7,R:11,V:48,K:210,Z:251},{S:11,R:13,V:120,K:2310,Z:503}];
 function cut(J,c,Z){for(let p of pr){if(p>Z)break;if(p<=c.S){if(J%p)return false}else if(p<=c.R){if(J%p%2||J%p>p-3)return false}else if(J%p===1||J%p===p-1)return false}return true}
 function inspect(rows,c){if(!rows.length||rows[0].H+1<c.S*c.S)return;let {S,R,V,K,Z}=c,L=5*S,alpha=L-4*S,prev=-1,gl=0,neg=0,gain=0,plusOut=0,used=new Set,dem=0,launchG=0,anchorG=0,an=0;
  let end=rows.at(-1).Z;
  for(let i=0;i<rows.length;i++){let u=rows[i];for(let J=Math.ceil(u.H/K)*K;J<u.Z;J+=K){if(!cut(J,c,V))continue;st.cuts++;let ext=cut(J,c,Z);if(ext)st.extendedCuts++;
    if(u.H===J){st.anchors++;if(ext){ok(u.p>Z,"anchor exclusion");st.extendedAnchors++;an++;anchorG+=u.g}else if(u.p<=Z)st.oldAnchorRemoved++;continue}
    if(!ext)continue;
    let a=J-u.H,b=u.Z-J,type;if(a<=V){type="launch";st.launch++;if(u.p>V)st.largeLaunch++}else if(b<=V/2){type="landing";st.landing++;if(u.p>V)st.largeLanding++}else{st.bypass++;ok(u.g>1.5*V,"bypass");continue}
    if(J+V>end){st.pending++;continue}
    let start=type==="launch"?i:i+1,j=start;ok(start<rows.length,"start");while(rows[j].Z<J+V)j++;
    ok(start>prev,"disjoint");prev=j;st.disjoint++;st.completed++;
    let G=0,low=0,minus=0,witness=false;
    for(let k=start;k<=j;k++){let v=rows[k],u=Math.abs(v.H-J);ok(u>0&&u<=V,"offset");G+=v.g;if(v.p<=L)low+=v.g;minus+=Math.max(0,v.d-v.dp);
      if(pr.every(f=>f>S||((v.H-1)%f!==0&&(v.H+1)%f!==0))){ok(u>=4&&spf[u-1]===u-1&&spf[u+1]===u+1&&u-1>S,"twin");witness=true}
      else{ok(v.w<=2*S,"clock");st.fast++;if(v.p>L){ok(L*(v.d-v.dp)>=alpha*v.g,"drop");st.drop++}}
    }
    let demand=type==="launch"?Math.max(V,u.g):V/2;ok(G>=demand,"demand");
    if(witness){st.witness++;continue}
    st.clean++;if(type==="launch")st.cleanLaunch++;else st.cleanLanding++;
    for(let k=start;k<=j;k++)used.add(k);dem+=demand;gl+=low;neg+=minus;gain+=G;
    if(type==="launch"&&u.p>V&&st.examples.length<3)st.examples.push({S,V,Z,J,H:u.H,post:u.Z,p:u.p,w:u.w,gain:G,low,minus})
    ok(alpha*(G-low)<=L*minus,"local");
  }}
  for(let i=0;i<rows.length;i++)if(!used.has(i))plusOut+=Math.max(0,rows[i].dp-rows[i].d);
  let net=rows.filter((_,i)=>used.has(i)).reduce((a,v)=>a+v.d-v.dp,0);
  ok(gain>=dem&&alpha*(gain-gl)<=L*neg&&alpha*dem<=(alpha+5*L)*gl+L*(plusOut+rows[0].d),"localized budget");
  ok(net<=plusOut+rows[0].d&&an*Z<=anchorG,"anchor budget");st.localizedBudgets++;st.anchorBudget++;
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
  for(let c of configs)inspect(rows,c)
 }
 ok(st.pointwise&&st.meanExact&&st.extendedCuts&&st.oldAnchorRemoved&&st.clean&&st.bypass&&st.largeLaunch&&st.largeLanding,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
