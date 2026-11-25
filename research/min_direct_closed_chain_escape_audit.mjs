// Closed odd-reset chains: bounded-prime barrier, nested escape, fresh-prime sign, and literal witnesses.
function audit(){
 const max=2500,ps=[];for(let p=3;p<=max;p+=2){let ok=true;for(let d=3;d*d<=p;d+=2)if(p%d===0){ok=false;break}if(ok)ps.push(p)}
 const mod=(a,b)=>(a%b+b)%b;
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a<0n?-a:a};
 const cutoffs=[23,79,331,499,919,2011];
 const data=cutoffs.map(R=>({R,ps:ps.filter(p=>p<=R),P:ps.filter(p=>p<=R).reduce((a,p)=>a*BigInt(p),1n)}));
 let s={roots:0,cutoffChecks:0,steps:0,barrierChecks:0,recordSideChecks:0,recordResidues:0,nestingChecks:0,literalTicks:0,chainChecks:0,cutoffResults:data.map(x=>({R:x.R,escape:0,fail:0,steps:0})),witness:[]};
 function valid(X){return X%4n===2n&&X%3n===2n&&X%7n===3n&&(X%5n===3n||X%5n===4n)}
 function search(X,{ps,R,P},literal=false){
  let initial=X,word=[],J=2n*P*((X+2n*P-1n)/(2n*P));
  for(;;){
   if(!valid(X))return {escape:false,word};
   let r=0,side=0;for(let p of ps){let f=BigInt(p);if((X+3n)%f===0n){r=p;side=-1;break}if((X+5n)%f===0n){r=p;side=1;break}}
   if(!r)return {escape:true,word};
   let Y=X+BigInt(r+5);
   if(r<=23||side!==1||r%4!==3||!valid(Y))return {escape:false,word};
   if(!(X<=J&&Y<=J)||Y-initial>2n*P)throw Error("barrier");
   s.barrierChecks++;s.steps++;word.push(r);
   if(literal){
    // The relaxed map omits initial 11..19 exclusions and r+4 competitor;
    // for the explicit constructed witnesses these are separately true.
    let H=X-2n,M=X/2n,t=M+2n,ev=[];
    for(let j=1;j<=(r+5)/2;j++){let n=++t,e=n%2n?-1n:1n,g=gcd(e===1n?n:n-2n,H-e);if(g!==1n){if(g!==7n&&g!==BigInt(r)||g*g>H+1n)throw Error("witness gcd");ev.push(Number(g));H+=g-1n}s.literalTicks++}
    if(ev.join()!==`7,${r}`||H!==Y-2n||2n*t-H!==6n)throw Error("witness return");
   }
   X=Y;
   // In witness tests only certify prescribed prefix, not unverified later cylinders.
   if(literal&&word.length===literal)return {escape:null,word};
  }
 }
 // Full residue check for any shift: exactly one residue per sign, no overlap.
 for(let p of ps.filter(p=>p<=251))for(let shift=0;shift<p;shift++){
  let a=0,b=0;for(let x=0;x<p;x++){let u=mod(x+shift+3,p)===0,v=mod(x+shift+5,p)===0;if(u&&v)throw Error("overlap");a+=u;b+=v;s.recordResidues++}
  if(a!==1||b!==1)throw Error("sign");s.recordSideChecks++;
 }
 // Direct integer controls; sample all odd M in a consecutive interval.
 for(let M=5000001;M<5060001;M+=2){let X=2n*BigInt(M),prev=true;
  for(let i=0;i<data.length;i++){
   let z=search(X,data[i]);if(z.escape&&!prev)throw Error("cutoff nesting");prev=z.escape;s.nestingChecks++;s.cutoffChecks++;
   let q=s.cutoffResults[i];q[z.escape?"escape":"fail"]++;q.steps+=z.word.length;
  }s.roots++;
 }
 // Reconstruct the actual seven-segment witness from the earlier note.
 let rs=[331,499,751,919,1171,1759,2011],sh=[0];for(let r of rs)sh.push(sh.at(-1)+r+5);
 let M=1n,P=2n;
 for(let l of ps.filter(p=>p<=rs.at(-1)+4)){
  let a=-1;for(let v=0;v<l;v++){
   let ok=true;for(let i=0;i<rs.length;i++){let r=rs[i],x=mod(v+sh[i],l);
    if(l===3&&x!==2||l===7&&x!==3||l===5&&x!==(i%2?4:3)||l===r&&x!==l-5||l<r&&(x===mod(-3,l)||x===mod(-5,l))||l===r+4&&x===mod(-3,l)||l<=21&&![3,5,7].includes(l)&&(x===1||x===3)){ok=false;break}
   }if(ok){a=v;break}
  }if(a<0)throw Error("CRT");let L=BigInt(l),v=BigInt(a)*BigInt((l+1)/2)%L;while(M%L!==v)M+=P;P*=L;
 }
 if(M<5000000n)M+=P;
 for(let lift=0;lift<2;lift++){let X=2n*(M+BigInt(lift)*P);
  for(let d of data){let k=rs.filter(r=>r<=d.R).length,z=search(X,d);
   if(z.word.slice(0,k).join()!==rs.slice(0,k).join()||k<rs.length&&(!z.escape||z.word.length!==k))throw Error("witness cutoff");
   s.chainChecks++;if(lift===0)s.witness.push({R:d.R,prescribedBeforeEscape:k,escape:z.escape,knownSteps:z.word.length})
  }
  let z=search(X,data.at(-1),rs.length);if(z.word.join()!==rs.join())throw Error("witness literal");
 }
 return s;
}
console.log(JSON.stringify(audit(),null,2));
