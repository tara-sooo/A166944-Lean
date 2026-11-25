function audit(P=59){
 const primes=[];for(let n=3;n<=P;n+=2)if(primes.every(p=>p*p>n||n%p))primes.push(n);
 const mod=(a,b)=>(a%b+b)%b;
 function solve(S){
  let Q=S.reduce((a,b)=>a*b,1),D=new Uint16Array(Q+1),max=0,start=0,edges=0;
  for(let j=Q-1;j>=0;j--)for(let p of S){let r=(2*j)%p;if(r!==1&&r!==p-1)continue;let k=j+(p-1)/2;if(k>Q)throw Error("cut");edges++;let v=D[k]+1;if(v>D[j])D[j]=v;if(v>max){max=v;start=j}}
  let C=2*start,word=[],j=start;while(D[j]){let p=S.find(p=>{let r=2*j%p;return (r===1||r===p-1)&&D[j+(p-1)/2]+1===D[j]});word.push({p,s:2*j%p===1?1:-1});j+=(p-1)/2}
  if(word.length!==max)throw Error("length");
  return {S,Q,max,start:C,word,edges}
 }
 // Affine equations indexed by k ordered labels and residues of larger labels mod smaller ones.
 function equations(S,word){
  let k=S.length,dim=k*(k+1)/2+1,idx=new Map(),z=k;for(let i=0;i<k;i++)for(let j=i+1;j<k;j++)idx.set(j+":"+i,z++);
  let vals=[...S];for(let i=0;i<k;i++)for(let j=i+1;j<k;j++)vals.push(S[j]%S[i]);vals.push(1);
  let last=new Map(),rows=[];
  for(let b=0;b<word.length;b++){let i=S.indexOf(word[b].p);if(last.has(i)){let a=last.get(i),row=Array(dim).fill(0),sum=0;for(let h=a;h<b;h++){let j=S.indexOf(word[h].p);sum+=S[j]%S[i]-1;if(j<i)row[j]++;else if(j>i)row[idx.get(j+":"+i)]++;row[dim-1]--}
    let diff=word[b].s-word[a].s,Q=(sum-diff)/S[i];if(!Number.isInteger(Q)||Math.abs(Q)>b-a+1)throw Error("quotient");row[i]-=Q;row[dim-1]-=diff;if(row.reduce((s,v,t)=>s+v*vals[t],0)!==0)throw Error("affine equation");rows.push(row)}
   last.set(i,b)}
  // Exact integer elimination (primitive row reduction preserves Q span).
  const gcd=(a,b)=>{a=a<0n?-a:a;b=b<0n?-b:b;while(b)[a,b]=[b,a%b];return a};
  const norm=v=>{let g=v.reduce((a,b)=>gcd(a,b),0n);return g?v.map(a=>a/g):v};
  let basis=[];for(let r of rows){let v=r.map(BigInt);for(let {j,u} of basis)if(v[j]){let a=u[j],b=v[j];v=norm(v.map((x,i)=>a*x-b*u[i]))}let j=v.findIndex(x=>x!==0n);if(j>=0)basis.push({j,u:norm(v)})}
  if(basis.length>dim-1)throw Error("rank with witness");
  // CRT of first appearances via direct modular search on the finite period;
  // confirms that no additional constraint is needed for relaxed horizon words.
  let E=0,first=new Map();for(let {p,s} of word){if(!first.has(p))first.set(p,mod(s-E,p));E+=p-1}
  let n=0;while(![...first].every(([p,r])=>2*n%p===r)){n++;if(n>=S.reduce((a,b)=>a*b,1))throw Error("CRT")}
  let C=2*n+2*S.reduce((a,b)=>a*b,1);
  for(let {p,s} of word){if(C%p!==mod(s,p))throw Error("reconstructed word");C+=p-1}
  return {rows:rows.length,rank:basis.length,dim}
 }
 let summary={P,sets:{1:0,2:0,3:0},edges:0,affineRows:0,maxRank:{1:0,2:0,3:0},max:{},maxNo3:{},samples4:[],cutoffReplay:0};
 function record(S){let v=solve(S),k=S.length,eq=equations(S,v.word);summary.sets[k]++;summary.edges+=v.edges;summary.affineRows+=eq.rows;summary.maxRank[k]=Math.max(summary.maxRank[k],eq.rank);if(!summary.max[k]||v.max>summary.max[k].max)summary.max[k]={...v,eq};if(!S.includes(3)&&(!summary.maxNo3[k]||v.max>summary.maxNo3[k].max))summary.maxNo3[k]={...v,eq};if(k===1&&v.max>(S[0]===3?2:1))throw Error("one-label bound");if(k===2){let cap=S[0]!==3?3:S[1]===5?6:4;if(v.max>cap)throw Error("two-label bound")}}
 for(let i=0;i<primes.length;i++){record([primes[i]]);for(let j=i+1;j<primes.length;j++){record([primes[i],primes[j]]);for(let k=j+1;k<primes.length;k++)record([primes[i],primes[j],primes[k]])}}
 for(let S of [[3,5,7,11],[3,5,7,17],[3,5,17,19],[3,11,13,17],[5,7,11,13],[7,11,23,47],[11,13,17,19]]){let v=solve(S),eq=equations(S,v.word);summary.samples4.push({S,max:v.max,rank:eq.rank,rows:eq.rows})}
 // The two-label extremizer also respects the square-root cutoff after translation.
 let ext=summary.max[2],C=ext.start+2*ext.Q;for(let {p,s} of ext.word){if(p*p>C+1||C%p!==mod(s,p))throw Error("adaptive relaxed witness");C+=p-1;summary.cutoffReplay++}
 return summary
}

console.log(JSON.stringify(audit(Number(process.argv[2] || 59)),null,2));
