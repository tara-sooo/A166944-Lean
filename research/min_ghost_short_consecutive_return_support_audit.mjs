// Short consecutive-return relations and two-large-label alternating runs.
function audit(U,N=128,A=5,k=3){
 const V=4*U,ps=[],sv=new Uint8Array(V+1);for(let p=2;p<=V;p++)if(!sv[p]){if(p>2)ps.push(p);if(p*p<=V)for(let j=p*p;j<=V;j+=p)sv[j]=1}
 const L=2*ps.filter(p=>p<A).reduce((a,b)=>a*b,1),root=Math.ceil(Math.sqrt(2*U)),diagnostic=Math.max(11,Math.floor(root/4)),Q2=Math.ceil(U**(2/3)),Q3=Math.ceil(U**.75),thresholds=[diagnostic,root,Q2,Q3];
 const mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x9e25e751^U^A)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}function uni(p){let a=4294967296-4294967296%p,x;do{x=u32()}while(x>=a);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),first=new Int32Array(ps.length),last=new Int32Array(ps.length);
 const out={U,N,A,L,V,events:0,shortReturnChecks:0,divisorCases:0,residueCases:0,lowOnlyReturns:0,thresholds:thresholds.map(Q=>({Q,short2:0,short3:0,paths2:0,paths3:0,weight2:0,weight3:0})),twoSupportRuns:0,maxTwoSupportLength:0};
 for(let a=0;a<N;a++){
  let parity=uni(2);first.fill(-1);last.fill(-1);
  for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let x=uni(p);t[i]=x%2===parity?x:x+p}
  let e=0,g=0,seq=[],hit=thresholds.map(()=>[false,false]);
  for(;;){
   let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[j]+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i])){w=f;i=j}}
   if(e+w>U)break;let p=ps[i];if(first[i]<0)first[i]=e+w;
   if(p>=A){
    let j=last[i],h=seq.length;
    if(j>=0&&g<=2*U&&h-j<=k+1){
     let old=seq[j],counts=new Map(),sum=0;for(let z=j+1;z<h;z++){let q=seq[z].p;counts.set(q,(counts.get(q)||0)+1);sum+=q-1}
     let d=g-old.g-(p-1)-sum,sgn=mod(c[i]+g,p)===1?1:-1,aa=sgn-old.sgn;
     ck(d>=0&&d<(h-j)*L&&d%2===0&&mod(sum+d-1-aa,p)===0,"return relation");
     if(!counts.size){out.lowOnlyReturns++;ck(p<=L+3,"no consecutive large self return")}
     else{
      let labels=[p,...counts.keys()],m=Math.min(...labels),lastPrime=labels.reduce((x,y)=>first[ps.indexOf(x)]>first[ps.indexOf(y)]?x:y);
      if(lastPrime===p){let C=sum+d-1-aa;ck(C%p===0,"divisor case");if(m>7)ck(C>0,"positive divisor target");out.divisorCases++;}
      else{let n=counts.get(lastPrime),C=sum-n*(lastPrime-1)+d-1-aa;ck(mod(n*(lastPrime-1)+C,p)===0,"residue case");out.residueCases++}
      for(let z=0;z<thresholds.length;z++)if(m>=thresholds[z]){let s=out.thresholds[z];if(labels.length<=2){s.short2++;s.weight2+=p;hit[z][0]=true}if(labels.length<=3){s.short3++;s.weight3+=p;hit[z][1]=true}}
     }out.shortReturnChecks++;
    }
    last[i]=h;seq.push({p,g,sgn:mod(c[i]+g,p)===1?1:-1});
   }
   e+=w;g+=p-1;out.events++;
  }
  for(let i=0;i<seq.length;i++){if(seq[i].p<=4*L+10)continue;let set=new Set();for(let j=i;j<seq.length;j++){if(seq[j].p<=4*L+10)break;set.add(seq[j].p);if(set.size>2)break;let len=j-i+1;ck(len<=7,"two support length");if(set.size===2){out.twoSupportRuns++;out.maxTwoSupportLength=Math.max(out.maxTwoSupportLength,len)}}}
  for(let z=0;z<thresholds.length;z++){out.thresholds[z].paths2+=+hit[z][0];out.thresholds[z].paths3+=+hit[z][1]}
 }
 return out;
}
function twoAudit(L){
 const P=4*L+11,ps=[];for(let p=P|1;p<P+180;p+=2){let ok=true;for(let q=3;q*q<=p;q+=2)if(p%q===0){ok=false;break}if(ok)ps.push(p)}
 const ck=(b,m)=>{if(!b)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 let pairs=0,states=0,maxLength=0,witness=null;
 for(let i=0;i<ps.length;i++)for(let j=i+1;j<ps.length;j++){
  let p=ps[i],q=ps[j];pairs++;
  for(let start of [p,q])for(let sg of [-1,1]){
   function dfs(g,last,cp,cq,seq){
    states++;let len=seq.length;ck(len<=7,"two-label bound");if(len>maxLength){maxLength=len;witness={p,q,seq}}
    let next=last===p?q:p;
    for(let d=0;d<L;d+=2){
     let x=g+last-1+d,c=next===p?cp:cq;
     if(c===null){for(let s of [-1,1]){let v=mod(s-x,next);dfs(x,next,next===p?v:cp,next===q?v:cq,[...seq,{p:next,g:x,d,s}])}}
     else{let v=mod(c+x,next);if(v===1||v===next-1)dfs(x,next,cp,cq,[...seq,{p:next,g:x,d,s:v===1?1:-1}]);}
    }
   }
   dfs(0,start,start===p?mod(sg,p):null,start===q?mod(sg,q):null,[{p:start,g:0,d:0,s:sg}])
  }
 }
 return {L,P,pairs,states,maxLength,witness}
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?64:128)));
for(const L of [6,30])console.log(JSON.stringify(twoAudit(L)));
