// Local coupled-return matrices, sink subwords and exact minor reconstruction.
function audit(U,N=64,A=5,K=12){
 const V=4*U,ps=[],sv=new Uint8Array(V+1);for(let p=2;p<=V;p++)if(!sv[p]){if(p>2)ps.push(p);if(p*p<=V)for(let j=p*p;j<=V;j+=p)sv[j]=1;}
 const L=2*ps.filter(p=>p<A).reduce((a,b)=>a*b,1),root=Math.ceil(Math.sqrt(2*U)),base=Math.max(11,Math.floor(root/32)),mod=(x,p)=>(x%p+p)%p,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x98f2ce71^U)>>>0;function rand(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0;}function uni(p){let a=4294967296-4294967296%p,x;do{x=rand()}while(x>=a);return x%p;}
 function det(a){let n=a.length;if(!n)return 1n;let x=a.map(r=>r.map(BigInt)),sg=1n,d=1n;for(let k=0;k<n-1;k++){let j=k;while(j<n&&x[j][k]===0n)j++;if(j===n)return 0n;if(j!==k){[x[j],x[k]]=[x[k],x[j]];sg=-sg;}let p=x[k][k];for(let i=k+1;i<n;i++){for(let j=k+1;j<n;j++){let v=x[i][j]*p-x[i][k]*x[k][j];ck(v%d===0n,"Bareiss exact");x[i][j]=v/d;}x[i][k]=0n;}d=p;}return sg*x[n-1][n-1];}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),first=new Int32Array(ps.length);
 const out={U,N,V,A,L,K,root,base,events:0,windows:0,allRepeated:0,sinkChecks:0,strongBlocks:0,maxSupport:0,maxLength:0,rootBlocks:0,minorChecks:0,invertible:0,singular:0,analyticGate:0,reconstructions:0,marked:0,markedPositive:0,markedWeight:0,edgeDistinctStrong:0,farFirst:0};
 for(let a=0;a<N;a++){
  let parity=uni(2);first.fill(-1);for(let j=0;j<ps.length;j++){let p=ps[j];c[j]=uni(p);let x=uni(p);t[j]=x%2===parity?x:x+p;}
  let s=0,g=0,seq=[],marks=new Set(),sig=new Set();
  for(;;){let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[j]+s-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i])){w=f;i=j;}}
   if(s+w>U)break;let p=ps[i],J=2*(s+w)-g-p+1-6*((parity+s+w)%2);if(first[i]<0)first[i]=s+w;out.events++;if(g+p-1>2*U)break;
   if(p>=A)seq.push({p,i,g,J,s:s+w,w});s+=w;g+=p-1;
  }
  function checkBlock(l,r,labels,loc){
   const h=labels.length,mi=labels[0],mx=labels[h-1],span=seq[r].g-seq[l].g,ix=new Map(labels.map((p,i)=>[p,i])),M=[],E=[];
   ck(h>=2&&span<=K*mi&&mx<=span+1,"block bounds");
   for(let i=0;i<h;i++){let p=labels[i],[a,b]=loc.get(p),D=seq[b].g-seq[a].g,coef=-1,off=0;
    for(let x of [-2,0,2])if(mod(D-x,p)===0){coef=(D-x)/p;off=x;}
    ck(coef>=2&&coef%2===0,"return stride");let n=new Array(h).fill(0),d=0;for(let j=a;j<b;j++){let v=seq[j];ck(ix.has(v.p),"sink interval");n[ix.get(v.p)]++;let low=seq[j+1].g-v.g-v.p+1;ck(low>=0&&low<L&&low%2===0,"low gain");d+=low;}
    let e=d-(b-a)-off,row=n.map(x=>-x);row[i]+=coef;ck(row.reduce((v,x,j)=>v+x*labels[j],0)===e,"matrix identity");ck(Math.abs(e)<=2*K*(L+1)+2,"error bound");M.push(row);E.push(e);
   }
   const Emax=2*K*(L+1)+2,gate=BigInt(mi)>BigInt(Emax)*BigInt(2*K+1)**BigInt(h);
   out.analyticGate+=+gate;
   let earliest=labels.reduce((i,p,j)=>first[seq[loc.get(p)[0]].i]<first[seq[loc.get(labels[i])[0]].i]?j:i,0);
   for(let k=0;k<h;k++){
    let inds=labels.map((_,i)=>i).filter(i=>i!==k),B=inds.map(i=>inds.map(j=>M[i][j])),D=det(B);out.minorChecks++;out.invertible+=+(D!==0n);out.singular+=+(D===0n);if(gate)ck(D!==0n,"analytic minor");
    if(k===earliest&&D!==0n){let rhs=inds.map(i=>E[i]-M[i][k]*labels[k]);for(let j=0;j<inds.length;j++){let C=B.map((r,i)=>r.map((x,jj)=>jj===j?rhs[i]:x));ck(det(C)===D*BigInt(labels[inds[j]]),"Cramer reconstruction");out.reconstructions++;}}
   }
   let ky=l+","+r;if(sig.has(ky))return;sig.add(ky);out.strongBlocks++;out.rootBlocks+=+(mi>=root);out.maxSupport=Math.max(out.maxSupport,h);out.maxLength=Math.max(out.maxLength,r-l+1);
   let edges=new Set();for(let j=l+1;j<=r;j++){let p=seq[j].p,q=seq[j-1].p;ck(p!==q,"no loop");edges.add(Math.min(p,q)+","+Math.max(p,q));marks.add(j);}out.edgeDistinctStrong+=+(edges.size===r-l);out.farFirst+=+(labels.every(p=>seq[loc.get(p)[0]].s-first[seq[loc.get(p)[0]].i]>K*p));
  }
  for(let l=0;l<seq.length;l++){if(seq[l].p<base)continue;let mi=Infinity,loc=new Map();
   for(let r=l;r<seq.length;r++){let p=seq[r].p;if(p<base)break;mi=Math.min(mi,p);if(seq[r].g-seq[l].g>K*mi)break;
    let v=loc.get(p);if(!v)loc.set(p,[r,r]);else v[1]=r;out.windows++;
    if(loc.size<2||[...loc.values()].some(([a,b])=>a===b))continue;out.allRepeated++;
    let labels=[...loc.keys()].sort((a,b)=>a-b),h=labels.length,ix=new Map(labels.map((p,i)=>[p,i])),reach=labels.map((p,i)=>{let [a,b]=loc.get(p),r=new Array(h).fill(false);for(let j=a;j<=b;j++)r[ix.get(seq[j].p)]=true;return r;});
    for(let k=0;k<h;k++)for(let i=0;i<h;i++)for(let j=0;j<h;j++)reach[i][j]||=reach[i][k]&&reach[k][j];
    let sink=-1;for(let i=0;i<h;i++)if(reach[i].every((v,j)=>!v||reach[j][i])){sink=i;break;}ck(sink>=0,"sink exists");
    let S=labels.filter((_,i)=>reach[sink][i]),sl=Math.min(...S.map(p=>loc.get(p)[0])),sr=Math.max(...S.map(p=>loc.get(p)[1]));
    ck(S.length>=2&&seq.slice(sl,sr+1).every(x=>S.includes(x.p)),"closed sink subword");out.sinkChecks++;checkBlock(sl,sr,S,loc);
   }
  }
  out.marked+=marks.size;for(let j of marks){out.markedWeight+=seq[j].p;out.markedPositive+=Math.max(0,seq[j].J-seq[j-1].J);}
 }
 return out;
}
function synthetic(){
 function determinant(a){let n=a.length;if(!n)return 1n;let v=0n;for(let j=0;j<n;j++){let m=a.slice(1).map(r=>r.filter((_,k)=>k!==j));v+=(j%2?-1n:1n)*BigInt(a[0][j])*determinant(m);}return v;}
 let checks=0;for(let h=2;h<=6;h++)for(let k=1;k<=12;k++){let P=10n**20n,p=Array.from({length:h},(_,i)=>P+BigInt(2*i+1)),M=Array.from({length:h},(_,i)=>Array.from({length:h},(_,j)=>i===j?k+1:j===(i+1)%h?-1:j===(i+h-1)%h&&h>2?-k:0));if(h===2)M=M.map((r,i)=>r.map((v,j)=>i===j?k+1:-(k+1)));let e=M.map(r=>r.reduce((s,x,j)=>s+BigInt(x)*p[j],0n)),E=e.reduce((m,x)=>m>(x<0n?-x:x)?m:(x<0n?-x:x),0n);if(P<=E*BigInt(2*(k+2)+1)**BigInt(h))throw Error("synthetic gate");for(let r=0;r<h;r++){let a=M.filter((_,i)=>i!==r).map(x=>x.filter((_,j)=>j!==r));if(determinant(a)===0n)throw Error("synthetic minor");checks++;}}
 return {checks}
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?64:128)));
console.log(JSON.stringify(synthetic()));
