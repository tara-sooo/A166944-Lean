// Exact canonical CRT witness for discovery packing and per-prime clock gain.
function audit(){
 const word=[7687,5233,3541,2389,1621,1093,733,7369],max=Math.max(...word),spf=new Int32Array(3*max+7);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b,pr=[];for(let s=3;s<spf.length;s+=2)if(spf[s]===s)pr.push(s);
 const shift=[0];for(let p of word)shift.push(shift.at(-1)+p-1);
 let H=0n,P=4n,checks=0;
 for(let s of pr){let at=word.indexOf(s),r=at>=0?mod(1-shift[at],s):0;
  let valid=x=>shift.slice(0,-1).every((g,i)=>word[i]===s?mod(x+g,s)===1:![1,s-1].includes(mod(x+g,s)));
  if(at<0){while(r<s&&!valid(r))r++}
  if(r===s||!valid(r))throw Error("CRT");
  let a=Number(P%BigInt(s)),b=s,u=1,v=0;while(b){let q=Math.floor(a/b);[a,b]=[b,a-q*b];[u,v]=[v,u-q*v]}
  if(a!==1)throw Error("inverse");H+=P*BigInt(mod(u*mod(r-Number(H%BigInt(s)),s),s));P*=BigInt(s);checks+=word.length
 }
 if(H<100000000n)H+=P;
 let H0=H,t=H/2n+3n,ticks=0,rows=[],events=[];
 for(let p of word){
  let d=Number(2n*t-H),w=(3*p-d-1)/2;
  if(!Number.isInteger(w)||w<=0)throw Error("wait");
  for(let j=1;j<=w;j++){
   let n=t+1n,I=n%2n,e=1n-2n*I,a=n-2n*I,b=H-e;while(b)[a,b]=[b,a%b];
   let label=j===w?p:0;
   if(a!==BigInt(label||1))throw Error("literal");
   rows.push({H,t,d:Number(2n*t-H),p:label});t=n;ticks++;
   if(label){if(BigInt(p)**2n>H+1n)throw Error("eligibility");H+=BigInt(p-1);if(2n*t-H!==2n*BigInt(p))throw Error("post");events.push({p,w,index:rows.length,H,t,d:Number(2n*t-H)})}
  }
 }
 rows.push({H,t,d:Number(2n*t-H),p:0});
 let mark=events[0],start=mark.index,end=start;while(end<rows.length&&rows[end].d+3>mark.p)end++;
 if(end>=rows.length||mark.p<47||mark.p<5*6+15)throw Error("recovery");
 let L=end-start,gain=Number(rows[end].H-rows[start].H),D=rows[start].d,counts=new Map();
 for(let i=start;i<end;i++)if(rows[i].p)counts.set(rows[i].p,(counts.get(rows[i].p)||0)+1);
 if(gain!==D-rows[end].d+2*L||gain<mark.p+3)throw Error("balance");
 let cap=(p)=> (p-1)*(1+Math.floor((L+1)/p)),R=Math.max(...counts.keys()),out=[];
 for(let [p,c] of counts)if(c*(p-1)>cap(p))throw Error("clock");
 for(let S of [7,47,100,1000]){
  let lowCap=pr.filter(p=>p<=S).reduce((a,p)=>a+cap(p),0),high=[...counts.keys()].filter(p=>p>S),maxCap=R+L;
  if(gain>lowCap+high.length*maxCap)throw Error("forcing");
  let forced=Math.max(0,Math.ceil((gain-lowCap)/maxCap));
  let r=rows[start],known=new Map(pr.filter(p=>p<=S).map(p=>[p,Number(r.H%BigInt(p))])),off=0,d=r.d,discoveries=[],reconstructed=0;
  for(let i=start;i<end;i++){
   let z=rows[i],I=Number((z.t+1n)%2n),e=1-2*I,F=d+3-6*I,selected=0;
   for(let [p,res] of known)if(F%p===0&&mod(res+off-e,p)===0&&(!selected||p<selected))selected=p;
   if(z.p>S&&!known.has(z.p)){
    if(F%z.p!==0||selected&&selected<z.p)throw Error("new");
    known.set(z.p,mod(e-off,z.p));discoveries.push({tick:i-start+1,p:z.p});selected=z.p;
   }
   if(selected!==z.p)throw Error("replay");if(selected)off+=selected-1;d+=2-(selected?selected-1:0);reconstructed++;
  }
  if(d!==rows[end].d||off!==gain||discoveries.length!==high.length||forced>high.length)throw Error("result");
  out.push({S,L,R,gain,lowCap,forced,distinctHigh:high.length,discoveries,reconstructed})
 }
 return {digits:(H0/2n+1n).toString().length,ticks,checks,initialDeficit:D,finalDeficit:rows[end].d,recovery:out}
}
console.log(JSON.stringify(audit(),null,2));
