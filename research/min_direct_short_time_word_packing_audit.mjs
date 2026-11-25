// Short-time CRT word packing and fixed-deficit return-word diagnostics.
function audit(N=12000){
 const cap=300000,spf=new Int32Array(cap);for(let i=2;i<cap;i++)if(!spf[i]){spf[i]=i;if(i*i<cap)for(let j=i*i;j<cap;j+=i)if(!spf[j])spf[j]=i}
 const gcd=(a,b)=>{a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a},mod=(a,b)=>(a%b+b)%b;
 function tick(H,t){let n=t+1,I=n%2,e=1-2*I,d=2*t-H,g=gcd(n-2*I,H-e),p=g>1?spf[g]:0;if(p&&p*p>H+1)p=0;if(p&&(d+3-6*I)%p!==0)throw Error("defect");return {p,H,t,d,I0:t%2,e}}
 let st={roots:0,ticks:0,events:0,abstractStarts:0,wordGroups:0,wordOccurrences:0,spacingChecks:0,branchChecks:0,highBlocks:0,distinctChecks:0,returnWords:0,returnRepeatTests:0,adjacentReturnTests:0,cutReturns:0,witnesses:[]};
 function inspect(rows,L,S,D,A,B,groups){
  let Z=D+2*L+3,branch=1+Math.floor(Math.log(Z)/Math.log(3)+1e-12);
  let cnt=0,seen=new Map;
  for(let i=0;i+L<=rows.length;i++){
   let r=rows[i];if(r.d<0||r.d>D||r.H<A||r.H>B)continue;
   let word=rows.slice(i,i+L).map(x=>x.p),hi=word.filter(p=>p>S),set=[...new Set(hi)];
   if(!hi.length)continue;
   let last=new Map;for(let j=0;j<L;j++){let p=word[j];if(p<=S)continue;if(last.has(p)&&j-last.get(p)<p-2)throw Error("repeat lag");last.set(p,j);st.distinctChecks++}
   let maxRep=1+Math.floor((L-1)/(S-1));if(set.length<Math.ceil(hi.length/maxRep))throw Error("distinct");
   if(L<S-1&&hi.length!==set.length)throw Error("short distinct");
   let d=r.d,H=r.H,off=0,P=1n;
   for(let j=0;j<L;j++){let p=word[j],I=(r.I0+j+1)%2,e=1-2*I,F=d+3-6*I;if(p&&F%p!==0)throw Error("word divisor");
    if(p){if(mod(H+off-e,p)!==0)throw Error("word residue");off+=p-1;if(set.includes(p)&&P%BigInt(p)!==0n)P*=BigInt(p)}
    d+=2-(p?p-1:0);
    if(d>D+2*(j+1)||Math.abs(F)>Z)throw Error("branch bound");st.branchChecks++;
   }
   let key=[r.d,r.I0,...word].join(","),group=groups.get(key);if(!group){group={P,hs:new Set,k:hi.length,distinct:set.length};groups.set(key,group)}if(group.P!==P)throw Error("group");group.hs.add(H);cnt++;st.highBlocks++;
  }
  return cnt
 }
 function verify(groups,A,B,D,L,S){
  let counts=new Map;
  for(let [key,g] of groups){let hs=[...g.hs].sort((a,b)=>a-b),m=4n*g.P;
   for(let i=1;i<hs.length;i++){if(BigInt(hs[i]-hs[i-1])%m!==0n)throw Error("spacing");st.spacingChecks++}
   if(BigInt(hs.length)>BigInt(B-A)/m+1n)throw Error("capacity");
   let q=counts.get(g.k)||0;counts.set(g.k,q+hs.length);st.wordGroups++;st.wordOccurrences+=hs.length;
  }
  let branch=1+Math.floor(Math.log(D+2*L+3)/Math.log(3)+1e-12),maxRep=1+Math.floor((L-1)/(S-1));
  for(let [k,num] of counts){let j=Math.ceil(k/maxRep),bound=BigInt(D+2)*BigInt(branch)**BigInt(L)*(BigInt(B-A)/(4n*BigInt(S+1)**BigInt(j))+1n);if(BigInt(num)>bound)throw Error("total")}
 }
 // Exhaustive abstract starting states, not ancestry. Count actual deterministic tick words.
 for(let [L,S,D] of [[4,7,20],[8,11,40],[12,17,60],[12,5,60]]){
  let groups=new Map;for(let H=100;H<=1200;H+=2)for(let d=0;d<=D;d+=2){let t=(H+d)/2,h=H,rows=[];
   for(let i=0;i<L;i++){let a=tick(h,t);rows.push(a);t++;if(a.p)h+=a.p-1}
   st.abstractStarts++;inspect(rows,L,S,D,100,1200,groups)
  }verify(groups,100,1200,D,L,S)
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[],cutMap=new Map,retMap=new Map,evs=[];st.roots++;
  for(let i=0;i<4000;i++){let a=tick(H,t);rows.push(a);st.ticks++;t++;
   if(a.p){let old=H;H+=a.p-1;st.events++;let dp=2*t-H;evs.push({p:a.p,i:i+1,H,t,d:dp,I:t%2});
    if(dp<a.d)for(let b=dp+2;b<=a.d;b+=2){let key=[b,a.p,t%2].join(","),prev=cutMap.get(key);if(prev){if(dp!==prev.d||H-prev.H!==2*(t-prev.t)||mod(H-prev.H,4*a.p)!==0)throw Error("cut return");st.cutReturns++}cutMap.set(key,{d:dp,H,t})}
   }
   // terminal: both neighbors prime; H +/-1 odd, spf equals itself
   if(spf[H-1]===H-1&&spf[H+1]===H+1)break;
   if(H+3>=cap)throw Error("range");
  }
  for(let [L,S] of [[4,7],[8,11],[12,5]]){let groups=new Map;inspect(rows,L,S,200,2*M-2,H,groups);verify(groups,2*M-2,H,200,L,S)}
  for(let j=0;j<evs.length;j++){let a=evs[j],key=a.d+","+a.I,prev=retMap.get(key);if(prev){let word=rows.slice(prev.i,a.i).map(x=>x.p),P=1n;for(let p of new Set(word.filter(Boolean)))P*=BigInt(p);
     if(a.H-prev.H!==2*word.length)throw Error("closed word");st.returnWords++;
     let k=key+":"+word.join(","),last=retMap.get(k);if(last){if(BigInt(prev.H-last.H)%(4n*P)!==0n)throw Error("return word spacing");st.returnRepeatTests++;if(last.end===prev.H){if(BigInt(a.H-prev.H)<4n*P)throw Error("adjacent");st.adjacentReturnTests++}}
     retMap.set(k,{H:prev.H,end:a.H})
    }retMap.set(key,a)
  }
 }
 // The previous 98-digit canonical witness, reconstructed with the original word.
 let p=79,word=[31,7,41,13],G=0,data=word.map((s,i)=>{let j=i+1,I=j%2,e=1-2*I,F=2*p+2*j+1-6*I-G,offset=p-1+G-e;G+=s-1;return{s,F,offset}});
 let H=0n,P=4n,checks=0;
 for(let f=3;f<=3*p+6;f+=2){if(spf[f]!==f)continue;let hit=data.find(a=>a.s===f),r=f===p?1:hit?mod(-hit.offset,f):0,ok=x=>(f===p?x===1:x!==1&&x!==f-1)&&data.every(a=>a.F%f!==0||(a.s===f?mod(x+a.offset,f)===0:mod(x+a.offset,f)!==0));
  if(f===p||hit){if(!ok(r))throw Error("CRT")}else{while(r<f&&!ok(r))r++;if(r===f)throw Error("CRT empty")}
  let a=Number(P%BigInt(f)),b=f,u=1,v=0;while(b){let q=Math.floor(a/b);[a,b]=[b,a-q*b];[u,v]=[v,u-q*v]}H+=P*BigInt(mod(u*mod(r-Number(H%BigInt(f)),f),f));P*=BigInt(f);checks++;
 }
 if(H<BigInt(p*p+8))H+=P;
 let starts=[];
 for(let shift=0;shift<3;shift++){let H0=H+BigInt(shift)*P,h=H0,t=h/2n+3n,labels=[p,...word],waits=[115,1,1,1,1],ticks=0;
  for(let i=0;i<labels.length;i++){let s=labels[i],w=waits[i],n=t+BigInt(w);for(let j=1;j<=w;j++){let z=t+BigInt(j),I=z%2n,e=1n-2n*I,x=z-2n*I,y=h-e;while(y)[x,y]=[y,x%y];if(x!==(j===w?BigInt(s):1n))throw Error("witness gcd");ticks++}
   if(BigInt(s)**2n>h+1n)throw Error("eligibility");h+=BigInt(s-1);t=n;
   if(i===0){if(2n*t-h!==158n)throw Error("A1");starts.push(h)}
  }st.witnesses.push({digits:(H0/2n+1n).toString().length,ticks,checks})
 }
 let product=word.reduce((a,p)=>a*BigInt(p),1n);for(let j=1;j<starts.length;j++)if((starts[j]-starts[j-1])%(4n*product)!==0n)throw Error("witness spacing");
 return st;
}
console.log(JSON.stringify(audit(Number(process.argv[2]||12000)),null,2));
