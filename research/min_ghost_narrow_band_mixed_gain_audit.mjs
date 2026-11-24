// Narrow-band bounded-support mixed-gain resource audit.
function audit(U,N=128){
 const V=4*U,ps=[],sv=new Uint8Array(V+1);for(let p=2;p<=V;p++)if(!sv[p]){if(p>2)ps.push(p);if(p*p<=V)for(let j=p*p;j<=V;j+=p)sv[j]=1}
 const mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x59142be3^U)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}function uni(p){let a=4294967296-4294967296%p,x;do{x=u32()}while(x>=a);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),seen=new Uint8Array(ps.length);
 let out={U,N,V,events:0,windows:0,capWindows:0,resourceChecks:0,maxLength:0,byK:[null,{checks:0,maxLength:0,resourceChecks:0},{checks:0,maxLength:0,resourceChecks:0},{checks:0,maxLength:0,resourceChecks:0}],maxStock:0,clusterChecks:0};
 for(let a=0;a<N;a++){
  let parity=uni(2);seen.fill(0);let g=0,e=0,seq=[];
  for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let x=uni(p);t[i]=x%2===parity?x:x+p;}
  for(;;){let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let z=2*p-mod(t[j]+e-(cc===1?0:p+2),2*p);if(z<w||(z===w&&p<ps[i])){w=z;i=j}}
   if(e+w>U)break;let p=ps[i];seen[i]=1;seq.push({p,g,s:mod(c[i]+g,p)===1?1:-1});g+=p-1;e+=w;out.events++;}
  let stock=ps.filter((p,i)=>seen[i]&&p>=32&&p<=2*U+1);out.maxStock=Math.max(out.maxStock,stock.length);
  for(let P of stock)for(let k=1;k<=3;k++){
   const C=2*5**(k-1)-1,prev=k===1?0:2*5**(k-2)-1,D=Math.floor(P/4),width=Math.floor(P/(4*(prev+1)));
   let band=seq.filter(x=>x.p>=P&&x.p<=P+width),support=new Set(band.map(x=>x.p));
   if(support.size>k)continue;
   let weight=0,off=0;for(let i=0;i<band.length;i++){weight+=band[i].p;if(i)off+=band[i].g-band[i-1].g-band[i-1].p+1;}
   ck(band.length<=C+(C+1)*Math.floor(off/(D+1)),"resource global");out.resourceChecks++;out.byK[k].resourceChecks++;
   for(let i=0;i<band.length;i++){let d=0;for(let j=i;j<band.length;j++){if(j>i)d+=band[j].g-band[j-1].g-band[j-1].p+1;if(d>D)break;let len=j-i+1;ck(len<=C,"length");out.windows++;out.byK[k].checks++;out.maxLength=Math.max(out.maxLength,len);out.byK[k].maxLength=Math.max(out.byK[k].maxLength,len);if(band[j].g<=2*U)out.capWindows++;}}
   // First-discovery anchor for each stock cluster, irrespective of order.
   let members=stock.filter(x=>x>=P&&x<=P+width);if(members.length>1)out.clusterChecks++;
  }
 }
 return out
}
function relaxed(P,labels,budget){
 const k=labels.length,C=2*5**(k-1)-1,prev=k===1?0:2*5**(k-2)-1,mod=(a,b)=>(a%b+b)%b;
 if(P<16||labels.some(p=>p<P||p-P>Math.floor(P/(4*(prev+1))))||budget>Math.floor(P/4))throw Error("parameters");
 let count=0,maxLen=0,witness=null,zeroChecks=0;
 function dfs(g,known,word,remaining){
  count++;if(word.length>C)throw Error("relaxed bound");if(word.length>maxLen){maxLen=word.length;witness=word;}
  for(let p of labels)for(let d=0;d<=remaining;d+=2){
   let x=g+d;if(known.has(p)){let s=mod(known.get(p)+x,p);if(s===1||s===p-1)dfs(x+p-1,known,[...word,{p,g:x,d,s:s===1?1:-1}],remaining-d);}
   else for(let s of [-1,1]){let next=new Map(known);next.set(p,mod(s-x,p));dfs(x+p-1,next,[...word,{p,g:x,d,s}],remaining-d);}
  }
 }
 // first event pre-gain 0, no off-band charge before it.
 for(let p of labels)for(let s of [-1,1])dfs(p-1,new Map([[p,mod(s,p)]]),[{p,g:0,d:0,s}],budget)
 return {P,labels,budget,count,maxLen,witness}
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?64:128)));
for(const x of [[41,[41],10],[41,[41,43],10],[101,[101,103],24],[1009,[1009,1013,1019],4]])console.log(JSON.stringify(relaxed(...x)));
