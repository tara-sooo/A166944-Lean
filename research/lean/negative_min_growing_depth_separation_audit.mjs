// Growing-depth separated actual orbit prefixes: finite CRT, rough-frontier and fast-event checks.
// Run with node. Finite proxy cutoffs do not certify asymptotic sieve estimates.
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 const MAX=1600002,sp=new Int32Array(MAX+2);
 for(let p=2;p<sp.length;p++)if(!sp[p]){sp[p]=p;if(p*p<sp.length)for(let n=p*p;n<sp.length;n+=p)if(!sp[n])sp[n]=p}
 function fac(n){let a=[];while(n>1){let p=sp[n];ok(p>0,"factor range");a.push(p);while(n%p===0)n/=p}return a.sort((a,b)=>a-b)}
 function next(x,n){let w=Infinity,p=0,s=0;for(let e of [-1,1])for(let q of fac(x+e)){let t=mod((e===1?0:q+2)-n,2*q)||2*q;if(t<w||(t===w&&q<p)){w=t;p=q;s=e}}return {w,p,s}}
 function trial(n){let a=[];for(let p=3;p*p<=n;p+=2)if(n%p===0){a.push(p);while(n%p===0)n/=p}if(n>1)a.push(n);return a}
 function literal(x,n,T){const a=trial(x-1),b=trial(x+1);for(let i=1;i<=T;i++){let nn=n+i,qs=nn%2===0?b:a;let hits=qs.filter(p=>mod(nn,2*p)===(nn%2===0?0:p+2));if(hits.length)return {w:i,p:Math.min(...hits),s:nn%2===0?1:-1}}return null}
 function modulus(ps){return [...new Set(ps)].reduce((m,p)=>m*BigInt(p),1n)}
 let first=0,firstTicks=0,suffix=0,suffixTicks=0,rough=0,fast=0,pin=0,det=0,pair=0,allVisited=0,repeats=0,sourceCross=0,primeSources=0,rows=[];
 function pins(v){ok((v.x+v.g)%v.p===0,"first label pin");pin++;for(const e of v.word){ok(mod(v.x+v.g-e.g-(1-e.s),e.p)===0,"suffix incoming pin");pin++}return [v.p,...v.word.map(e=>e.p)]}
 function forms(x,records,end){
  let ps=records.flatMap(pins),M=modulus(ps),forms=[];
  const add=(shift,div)=>{let b=BigInt(x+shift),d=BigInt(div);ok(b%d===0n&&M%d===0n,"integral progression forms");forms.push([M/d,b/d])};
  for(const v of records){ok(v.A===x+v.g+v.p-1,"source identity");add(v.g+v.p,v.p);add(v.g+v.p-2,1)}
  if(end){add(-1,1);add(1,1)}
  for(let i=0;i<forms.length;i++)for(let j=i+1;j<forms.length;j++){ok(forms[i][0]*forms[j][1]!==forms[j][0]*forms[i][1],"nonzero determinant");det++}
 }
 for(const [R,k,Z,K] of [[12000,2,11,7],[48000,3,13,11],[192000,4,17,11],[768000,5,19,13]]){
  let states=new Map(),survivors=[],roots=new Set(),N=0,Brough=0,Bfast=0,C=0,vis=0,highHeight=0;
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   if(Math.min(sp[A-1],sp[A+1])<K||sp[A-1]===A-1&&sp[A+1]===A+1)continue;
   let n=3-A/2,e=next(A,n),p=e.p;if(e.s!==1||p<=k*Z+1||p>4*Math.sqrt(2*R+1)+7)continue;
   let l=literal(A,n,e.w);ok(l&&l.p===p&&l.s===1&&l.w===e.w,"first replay");
   const x0=A-p+1,h0=x0/2+n+e.w;ok(x0%p===0&&(h0===0||h0===p),"first height");
   ok(e.w===(((A+1)/p)%4*p-7)/2,"first formula");first++;firstTicks+=e.w;N++;roots.add(A);if(sp[A-1]===A-1)primeSources++;if(h0===p)highHeight++;
   let x=x0,g=0,u=0,word=[],visited=[],good=true;n+=e.w;
   for(let j=0;j<=k;j++){
    let v={A,p,x,g,word:word.slice()};pins(v);visited.push(v);
    if(Math.min(sp[x-1],sp[x+1])>=K){forms(x,[v],true);rough++;Brough++;good=false;break}
    if(j===k)break;
    let f=next(x,n),ll=literal(x,n,f.w);ok(ll&&ll.w===f.w&&ll.p===f.p&&ll.s===f.s,"suffix replay "+JSON.stringify({A,x,n,f,ll}));suffix++;suffixTicks+=f.w;
    ok(f.w<2*K,"short wait");u+=f.w;ok(u<=2*(j+1)*K,"total short time");
    if(f.p>Z){
      let c=f.s===1?0:3,b=2*h0+2*u-g+1-2*c;ok(f.p!==p&&b>0&&b%f.p===0,"fast large pin");
      ok(f.p<=2*(h0+u)+1,"fast height bound");ok((x+f.s)%f.p===0,"fast spatial pin");fast++;Bfast++;good=false;break;
    }
    if(word.some(q=>q.p===f.p))repeats++;
    g+=f.p-1;x-=f.p-1;n+=f.w;word.push({p:f.p,s:f.s,g});ok(x===x0-g&&x/2+n===h0+u-g/2,"suffix ledger");
   }
   for(let v of visited){if(!states.has(v.x))states.set(v.x,[]);states.get(v.x).push(v);allVisited++;vis++}
   if(good){survivors.push({A,visited});C++;ok(word.length===k,"complete depth")}
  }
  let localPairs=0;
  for(let arr of states.values())for(let i=0;i<arr.length;i++)for(let j=i+1;j<arr.length;j++){
   let a=arr[i],b=arr[j];ok(a.A!==b.A,"strict movement");ok(a.p!==b.p,"same label collision");forms(a.x,[a,b],false);pair++;localPairs++;
  }
  for(let s of survivors)for(let v of s.visited){ok(!roots.has(v.x),"rough initial roots excluded");sourceCross++}
  let kept=survivors.filter(s=>s.visited.every(v=>states.get(v.x).length===1));
  rows.push({R,k,Z,K,N,highHeight,rough:Brough,fast:Bfast,complete:C,visited:vis,pairs:localPairs,isolated:kept.length});
 }
 let wordChecks=0;const ps=[3,5,7,11],Q=1155n;
 for(let m=0;m<=6;m++){
  let sum=0n;function go(a){if(a.length===m){sum+=Q/modulus(a);wordChecks++;return}for(let p of ps)go([...a,p])}go([]);
  let harmonic=ps.reduce((s,p)=>s+Q/BigInt(p),0n);ok(m===0?sum===Q:sum*Q**BigInt(m-1)<=(harmonic+BigInt(m)*Q)**BigInt(m),"weighted word bound");
 }
 return {rows,first,firstTicks,suffix,suffixTicks,rough,fast,pin,det,pair,allVisited,repeats,sourceCross,primeSources,wordChecks}
}
console.log(JSON.stringify(audit(),null,2));
