function audit(P=2000,budget=500000){
 const max=(P+2)*(P+2)+100,spf=new Int32Array(max+1);for(let i=2;i<=max;i++)if(!spf[i]){spf[i]=i;if(i*i<=max)for(let j=i*i;j<=max;j+=i)if(!spf[j])spf[j]=i}
 function fs(z){let a=[];while(z>1){let p=spf[z];if(!p)throw Error("range "+z);a.push(p);while(z%p===0)z/=p}return a}
 function gcd(a,b){while(b)[a,b]=[b,a%b];return Math.abs(a)}
 const mod=(a,b)=>(a%b+b)%b;
 function clocks(C){let b=Math.floor(Math.sqrt(C+1)),a=[];for(let s of [-1,1])for(let p of fs(C+s))if(p<=b)a.push({p,s,r:s===-1?0:p+2});return a}
 function next(t,C){let best=null;for(let {p,s,r} of clocks(C)){let w=mod(r-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,s,w}}return best}
 function inverse(n,Z){let a=[],s=n%2?1:-1;for(let p of fs(gcd(n%2?n-2:n,Z+(s===1?2:0)))){if(p<3)continue;let C=Z-p+1;if(C<8||p*p>C+1)continue;let g=gcd(n%2?n-2:n,C+s);if(g<3||spf[g]!==p)continue;let L=Infinity;for(let {p:q,r} of clocks(C))L=Math.min(L,mod(n-r,2*q)||2*q);let lo=Math.max(C/2,n-L),hi=n-1;if(lo<=hi)a.push({p,C,lo,hi,s})}return a}
 function root(t,C){return C%4===0&&C>=8&&t===C/2+3}
 let stats={P,budget,labels:0,exactInverseChecks:0,oddTargets:0,oddAllowed:0,r3Even:0,r3EvenAllowed:0,r5Even:0,r5EvenAllowed:0,rootsAtTarget:0,reachable:0,unreachable:0,unknown:0,reachableComposite:0,reachableTwin:0,reverseNodes:0,examples:[],r3Examples:[],r5OtherExamples:[],maxNodes:0,ancestryResultants:0,resonances:0,resonanceExample:null,nonresonantBoundChecks:0,reachableLabels:[],unknownLabels:[],smallForwardRoots:0,smallForwardEdges:0,smallForwardMatches:0};
 let reverseSets=new Map();
 for(let p=7;p<=P;p+=2)if(spf[p]===p){stats.labels++;let s=p%4===1?-1:1,x=p+1,C=x*x+(s===1?-2:0),Z=C+p-1,n=(Z+(s===1?6:0))/2,r=spf[p+2],composite=r!==p+2;
 let edge=inverse(n,Z).find(e=>e.p===p);
 if(!edge)throw Error("target missing");
 for(let t=Math.max(C/2,n-2*p);t<n;t++){let f=next(t,C),yes=f?.p===p&&f.w===n-t;if(yes!==(t>=edge.lo&&t<=edge.hi))throw Error("inverse interval");stats.exactInverseChecks++}
 let gate=[];for(let t=edge.lo;t<=edge.hi;t++){if(root(t,C)){gate.push({root:true,t});stats.rootsAtTarget++}for(let e of inverse(t,C))gate.push({t,l:e.p,side:e.s,Cprev:e.C,lo:e.lo,hi:e.hi})}
 if(s===1){stats.oddTargets++;if(gate.length){stats.oddAllowed++;throw Error("odd gate "+p)}}
 if(r===3&&s===-1){stats.r3Even++;if(gate.length)stats.r3EvenAllowed++;if((gate.length>0)!==(p%204===145)||gate.some(e=>e.root||e.l!==17||e.t!==n-1))throw Error("r3 gate");if(gate.length)stats.r3Examples.push({p,C,n,gate})}
 if(r===5&&s===-1){stats.r5Even++;if(gate.length)stats.r5EvenAllowed++;if(gate.some(e=>e.root||!((e.l===3&&e.t===n-2)||(e.l===17&&e.t===n-1&&p%17===9))))throw Error("r5 even");if(gate.some(e=>e.l!==3))stats.r5OtherExamples.push({p,s,r,gate})}
 const key=(t,H)=>t*(max+1)+H, seen=new Map(),stack=[],roots=new Map();let unknown=false;
 function push(t,H,succ){let k=key(t,H);if(!seen.has(k)){seen.set(k,succ);stack.push({t,H,k})}}
 for(let t=edge.lo;t<=edge.hi;t++)push(t,C,{t:n,H:Z,p});
 while(stack.length){if(seen.size>budget){unknown=true;break}let {t,H,k}=stack.pop();if(root(t,H))roots.set(H/2+1,k);
 for(let e of inverse(t,H)){let A=n-t,D=x*x-H,K=2*A-D+(s===-1?(e.s===-1?2:8):(e.s===-1?-2:4)),R=K*K-D+(e.s===1?2:0);stats.ancestryResultants++;if(R%e.p!==0||mod(x-K,e.p)!==0)throw Error("resultant");if(R===0){stats.resonances++;if(!stats.resonanceExample)stats.resonanceExample={p,A,D,K,t,H,l:e.p,side:e.s,Cprev:e.C,lo:e.lo,hi:e.hi};if((x-K)%2||x-K<=0||e.p>(x-K)/2)throw Error("resonance bound");}else{stats.nonresonantBoundChecks++;if(e.p>Math.abs(R))throw Error("resultant bound")}for(let u=e.lo;u<=e.hi;u++)push(u,e.C,{t,H,p:e.p})}
 }
 stats.reverseNodes+=seen.size;stats.maxNodes=Math.max(stats.maxNodes,seen.size);
 if(unknown){stats.unknown++;stats.unknownLabels.push(p)}else if(roots.size){stats.reachable++;stats.reachableLabels.push(p);if(composite)stats.reachableComposite++;else stats.reachableTwin++;
 let all=[...roots.keys()].sort((a,b)=>a-b),pr=all.filter(M=>spf[M]===M),M=pr.at(-1)??all.at(-1);let t=M+2,H=2*M-2,path=[];while(t!==n||H!==Z){let e=seen.get(key(t,H));if(!e)throw Error("missing witness");let f=next(t,H);if(!f||f.p!==e.p||t+f.w!==e.t||H+f.p-1!==e.H)throw Error("replay");t=e.t;H=e.H;path.push([t,H,f.p]);}stats.examples.push({p,composite,rootCount:all.length,primeRootCount:pr.length,roots:all.length<=30?all:all.slice(0,10),primeRoots:pr.length<=30?pr:pr.slice(0,10),M,primeRoot:spf[M]===M,steps:path.length,tail:path.slice(-4),nodes:seen.size});}else stats.unreachable++;
 if(p<=Math.min(P,97)&&!unknown)reverseSets.set(p,new Set(roots.keys()));
 }
 // Independent forward traversal of ALL roots for the smaller complete target range.
 let smallP=Math.min(P,97),Hmax=(smallP+1)**2+smallP+10,forward=new Map([...reverseSets.keys()].map(p=>[p,new Set()]));
 for(let M=5;2*M-2<=Hmax;M+=2){stats.smallForwardRoots++;let t=M+2,C=2*M-2;while(C<=Hmax){let e=next(t,C);if(!e)break;let n=t+e.w,Z=C+e.p-1,p=e.p,s=p%4===1?-1:1;if(forward.has(p)&&e.s===s&&C===(p+1)**2+(s===1?-2:0)&&2*n-Z===(s===1?6:0))forward.get(p).add(M);stats.smallForwardEdges++;t=n;C=Z;}}
 for(let [p,a] of reverseSets){let b=forward.get(p);if(a.size!==b.size||[...a].some(x=>!b.has(x)))throw Error("forward set mismatch "+p);stats.smallForwardMatches++}
 return stats
}

console.log(JSON.stringify(audit(Number(process.argv[2] || 2000),Number(process.argv[3] || 500000)),null,2));
