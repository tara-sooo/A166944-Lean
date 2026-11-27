// Exact finite-alphabet maxima of same-height small descents and arrivals, and coherent sampled extensions.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,pr=[3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127];
 let out={states:0,events:0,repeatChecks:0,localChecks:0,rows:[],samples:[]};
 function add(m,h){let v=(m.get(h)||0)+1;m.set(h,v);return v}
 for(let K of [3,5,7,11]){
  let P=pr.filter(p=>p<=K),Q=P.reduce((a,b)=>a*b,1),L=2*Q,eligible=Array.from({length:Q},(_,x)=>P.flatMap(p=>[-1,1].filter(e=>mod(2*x-e,p)===0).map(e=>[p,e===-1?0:p+2,e])));
  let row={K,Q,states:Q*L,maxD5:0,maxD7:0,maxN5:0,maxN7:0,maxN11:0,maxSame5:0,maxSame7:0,meanMaxD5:0,meanMaxD7:0};
  for(let x0=0;x0<Q;x0++)for(let n0=0;n0<L;n0++){
   let x=x0,n=n0,d5=new Map(),d7=new Map(),n5=new Map(),n7=new Map(),n11=new Map(),prev=new Map(),a5=0,a7=0;
   for(;;){let p=0,w=Infinity,s=0;for(let [q,c,e] of eligible[x]){let v=mod(c-n,2*q)||2*q;if(v<w||v===w&&q<p){p=q;w=v;s=e}}
    if(!p)break;
    let b=n+w-n0+x-x0,k=(p-1)/2,h=b-k;
    if(p>=5&&p<=11){let m=p===5?n5:p===7?n7:n11,v=add(m,h);row["maxN"+p]=Math.max(row["maxN"+p],v);let key=p+":"+s+":"+h;if(prev.has(key)){let a=prev.get(key)-2*x;ck(a>=4*p&&a%(4*p)===0,"same label height spacing");out.repeatChecks++}prev.set(key,2*x)}
    if(p<=5)for(let h=b+1-k;h<b;h++)a5=Math.max(a5,add(d5,h));
    if(p<=7)for(let h=b+1-k;h<b;h++)a7=Math.max(a7,add(d7,h));
    x-=k;n+=w;ck(x>=0,"wall");out.events++;
   }
   row.maxD5=Math.max(row.maxD5,a5);row.maxD7=Math.max(row.maxD7,a7);row.meanMaxD5+=a5;row.meanMaxD7+=a7;out.states++;
  }
  row.meanMaxD5/=row.states;row.meanMaxD7/=row.states;delete row.maxSame5;delete row.maxSame7;out.rows.push(row)
 }
 let seed=0x1234abcd;function u(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0}function rnd(n){let b=Math.floor(4294967296/n)*n,x;do{x=u()}while(x>=b);return x%n}
 for(let K of [13,23,47,97,127]){
  let P=pr.filter(p=>p<=K),N=10000,maxD5=0,maxD7=0,maxN5=0,maxN7=0,meanD5=0,meanD7=0,maxGain=0,truncated=0;
  for(let i=0;i<N;i++){
   let a=P.map(p=>rnd(p)),par=rnd(2),n=P.map(p=>2*rnd(p)+par),G=0,W=0,d5=new Map(),d7=new Map(),n5=new Map(),n7=new Map(),m5=0,m7=0;
   for(;;){let p=0,w=Infinity;for(let j=0;j<P.length;j++){let q=P[j],r=mod(a[j]-G,q);if(r!==1&&r!==q-1)continue;let t=mod((r===q-1?0:q+2)-n[j]-W,2*q)||2*q;if(t<w||t===w&&q<p){p=q;w=t}}if(!p)break;if(G+p-1>64*K){truncated++;break}
    let b=W+w-G/2,k=(p-1)/2,h=b-k;
    if(p===5)maxN5=Math.max(maxN5,add(n5,h));if(p===7)maxN7=Math.max(maxN7,add(n7,h));
    if(p<=5)for(let x=h+1;x<b;x++)m5=Math.max(m5,add(d5,x));
    if(p<=7)for(let x=h+1;x<b;x++)m7=Math.max(m7,add(d7,x));
    G+=p-1;W+=w;
   }maxD5=Math.max(maxD5,m5);maxD7=Math.max(maxD7,m7);meanD5+=m5;meanD7+=m7;maxGain=Math.max(maxGain,G)
  }
  out.samples.push({K,N,maxD5,maxD7,maxN5,maxN7,meanD5:meanD5/N,meanD7:meanD7/N,maxGain,truncated})
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
