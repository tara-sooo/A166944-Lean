// Stationary extension sieve inputs and exact actual idle-prefix equivalence.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=2400000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)if(!spf[n])spf[n]=p;
 function fs(n){let a=[];n=Math.abs(n);while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function c(p,e){return e===-1?0:p+2}
 function wait(v,p,e){return mod(c(p,e)-v,2*p)||2*p}
 function ev(a,v){let p=Infinity,w=Infinity,e=0;for(let [d,f] of [[a+1,-1],[a-1,1]])for(let r of fs(d)){let t=wait(v,r,f);if(t<w||t===w&&r<p){p=r;w=t;e=f}}return {p,w,e}}
 function inv(a,p){let b=mod(a,p),x=1;while(mod(x*b,p)!==1)x++;return x}
 let ps=[];for(let p=5;p<=40000;p+=2)if(!spf[p])ps.push(p);
 let s={prefixControls:0,prefixEvents:0,idleChecks:0,primeGateChecks:0,progressionControls:0,progressionRoots:0,sieveEquivalence:0,remainderChecks:0,maxRemainderFraction:0,rows:[],leafControls:0,leafRoots:0,leafIdleChecks:0,leafRows:[]};
 function forbidden(G,t0,K,par){
  let h=3+t0-G/2,z=2*(h+K)+1,sets=new Map(),gate=true;
  ck(h>=0&&z>=3,"height");
  for(let e of [-1,1])if(mod(-G-e,3)===0&&wait(3-3*par+t0,3,e)<=K)gate=false;
  for(let p of ps){if(p>z)break;let a=[];
   for(let e of [-1,1]){let r=mod((G+e)*inv(6,p),p),j=r+p*mod(par-r,2);if(wait(3-3*j+t0,p,e)<=K)a.push(r)}
   if(a.length)sets.set(p,a);
  }
  return {z,gate,sets};
 }
 function prefix(j,t0){let A=6*j,a=A,v=3-3*j,t=0,arr=[];while(t<t0){let x=ev(a,v);if(t+x.w>t0)break;arr.push([x.p,x.e,x.w]);t+=x.w;a-=x.p-1;v+=x.w;s.prefixEvents++}return {G:A-a,arr,t0,h:3+t0-(A-a)/2}}
 function countAP(b,m,lo,hi,t0,G,K,label){
  let l0=Math.ceil((lo-b)/m),l1=Math.floor((hi-b)/m),n=l1-l0+1;ck(n>0&&m%2===0,"progression");
  let f=forbidden(G,t0,K,mod(b,2)),ok=new Uint8Array(n).fill(f.gate?1:0),V=f.gate?1:0;
  let free=[];
  for(let [p,R] of f.sets){if(m%p===0){if(R.includes(mod(b,p))){ok.fill(0);V=0}continue}
   let B=R.map(r=>mod((r-b)*inv(m,p),p));V*=1-B.length/p;free.push([p,B]);for(let r of B)for(let l=l0+mod(r-l0,p);l<=l1;l+=p)ok[l-l0]=0;
  }
  let cnt=0,rough=0;
  for(let i=0;i<n;i++){let j=b+m*(l0+i),A=6*j,pre=prefix(j,t0);ck(pre.G===G,"prefix gain");if(label==="p7")ck(pre.arr.length===1&&pre.arr[0][0]===7&&pre.arr[0][1]===1&&pre.arr[0][2]===3,"specified p7");
   let a=A-G,v=3-3*j+t0,x=ev(a,v),idle=x.w>K;
   ck(idle===Boolean(ok[i]),{b,m,j,K,G,t0,idle,mark:ok[i]});s.sieveEquivalence++;s.progressionRoots++;if(idle)cnt++;
   if(fs(a-1).every(p=>p>f.z)&&fs(a+1).every(p=>p>f.z)){ck(idle,"rough sufficient");rough++}
  }
  // Verify squarefree CRT remainder input on up to 3 coordinates.
  for(let i=0;i<Math.min(12,free.length);i++)for(let j=i;j<Math.min(12,free.length);j++)for(let k=j;k<Math.min(12,free.length);k++){
   let F=[free[i],...(j===i?[]:[free[j]]),...(k===j?[]:[free[k]])],d=F.reduce((a,x)=>a*x[0],1),nu=F.reduce((a,x)=>a*x[1].length,1),c0=0;
   for(let l=l0;l<=l1;l++)if(F.every(([p,B])=>B.includes(mod(l,p))))c0++;
   let err=Math.abs(c0-n*nu/d);ck(err<=nu+1e-8,"sieve remainder");s.remainderChecks++;s.maxRemainderFraction=Math.max(s.maxRemainderFraction,err/nu)
  }
  s.progressionControls++;return {label,b,m,lo,hi,t0,G,K,z:f.z,n,idle:cnt,rough,V,ratio:V?cnt/(n*V):null}
 }
 for(let [lo,hi] of [[20000,70000],[100000,200000],[200001,399990]])for(let K of [10,30,100,1000,5000])s.rows.push(countAP(55,154,lo,hi,3,6,K,"p7"));
 for(let par of [0,1])for(let K of [10,100,1000])s.rows.push(countAP(par,2,100000,150000,0,0,K,"initial"));
 // Actual prefix at variable t0, all residues tested on the stationary
 // future interval; this compares both clean and forced-old-clock cases.
 for(let t0 of [1,3,5,8,12,30,60])for(let j=30001;j<=31000;j+=3){
  let p=prefix(j,t0),x=ev(6*j-p.G,3-3*j+t0);
  for(let K of [4,10,25,80,200]){
   let f=forbidden(p.G,t0,K,j%2),yes=f.gate;
   for(let [q,B] of f.sets){if(B.includes(mod(j,q)))yes=false;s.primeGateChecks++}
   ck(yes===(x.w>K),"conditional idle");s.idleChecks++;
  }s.prefixControls++
 }
 return s
}
console.log(JSON.stringify(audit(),null,2));
