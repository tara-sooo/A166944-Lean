// Sequential polynomial-scale reset chain: finite CRT and literal orbit controls.
// Run: node research/lean/negative_min_sequential_reset_vector_sieve_audit.mjs
// Finite proxies do not test BV or the asymptotic lower sieve.
function audit(){
const ok=(b,m)=>{if(!b)throw Error(m)},mod=(a,m)=>(a%m+m)%m;
const max=1000000,sp=new Uint8Array(max+1),ps=[];
for(let p=2;p<=max;p++)if(!sp[p]){ps.push(p);if(p*p<=max)for(let j=p*p;j<=max;j+=p)sp[j]=1}
const prime=x=>x>=2&&ps.every(p=>p*p>x||x%p!==0);
function factors(x){let a=[];for(const p of ps){if(p*p>x)break;if(x%p===0){a.push(p);while(x%p===0)x/=p}}if(x>1)a.push(x);return a}
function next(x,n){let w=Infinity,p=0;for(const s of [-1,1])for(const q of factors(x+s)){const c=s===1?0:q+2,t=mod(c-n,2*q)||2*q;if(t<w||(t===w&&q<p)){w=t;p=q}}return {w,p}}
function literal(x,n,T){let a=factors(x-1),b=factors(x+1);for(let i=1;i<=T;i++){let t=n+i,qs=t%2===0?b:a;for(let p of qs)if(mod(t,2*p)===(t%2===0?0:p+2))return {w:i,p}}return null}
function inv(a,p){let r=1;while(mod(a*r,p)!==1)r++;return r}
function crt(a,m,b,p){ok(m%p!==0,"CRT distinct");return [a+m*mod((b-a)*inv(m%p,p),p),m*p]}
function offsets(labels){let d=[0];for(let i=labels.length-1;i>=0;i--)d.unshift(d[0]+labels[i]-1);return d}
function admissible(labels){let d=offsets(labels);
for(let j=0;j<labels.length;j++){let p=labels[j];for(let i=0;i<d.length;i++)for(let s of [-1,1]){const div=mod(d[i]-d[j+1]+s,p)===0;if(div!==(i===j&&s===1))return false}}
return true}
let tupleTests=0,bad=0,good=0,localChecks=0,crtChecks=0,eventChecks=0,tickChecks=0,primeTargets=0,vectorChecks=0,phaseChecks=0;const examples=[],rows=[];
const labels=[13,37,61,73,97,109,157]; // finite proxy: fixed modulus 12, separately check small free primes
for(let k=1;k<=4;k++){
let count=0,tried=0,g=0,b=0;
function visit(arr){
 if(arr.length<k){for(const p of labels)if(!arr.includes(p))visit([...arr,p]);return}
 tupleTests++;tried++;
 if(!admissible(arr)){bad++;b++;return}good++;g++;
 let d=offsets(arr),a=0,m=12;
 for(let j=0;j<k;j++) [a,m]=crt(a,m,mod(-d[j+1],arr[j]),arr[j]);
 for(let j=0;j<k;j++){ok((a+d[j+1])%(4*arr[j])===0,"reset target pin");crtChecks++}
 let small=ps.filter(q=>q>=5&&q<=Math.max(...arr)&&!arr.includes(q));
 for(let q of small){let seen=new Set();for(let i=0;i<d.length;i++)for(const s of [-1,1]){const h=mod(-1-d[i]-s,q);if(h!==0)seen.add(h)}
 ok(seen.size<=2*k+1,"reduced bad-class bound");if(seen.size===q-1)return;localChecks++}
 if(count>=16)return;
 // Find examples with every pre-final center rough up to its own label, and final one prime + rough.
 const H=2*Math.max(...arr)+10,Z=2*H+8;
 for(let j=1;j<=12000;j++){
  let x=a+j*m;
  if(x+d[0]>max*max/2)break;
  if(!ps.filter(p=>p<=Z).every(p=>(x+1)%p!==0&&(x-1)%p!==0))continue;
  let pass=true;for(let i=0;i<k;i++){let v=x+d[i];for(let p of ps){if(p>=arr[i])break;if((v-1)%p===0||(v+1)%p===0){pass=false;break}}if(!pass)break}
  if(!pass||!prime(x-1))continue;
  primeTargets++;let A=x+d[0],v=A,n=3-A/2,t=0,gain=0;
  for(let i=0;i<k;i++){
   let p=arr[i],w=(p-7)/2,expected=x+d[i+1],e=next(v,n),l=literal(v,n,w);
   ok(e.w===w&&e.p===p&&l.w===w&&l.p===p,"exact first firing");
   n+=w;v-=p-1;gain+=p-1;t+=w;eventChecks++;tickChecks+=w;
   ok(v===expected&&literal(v,n,3)===null,"three quiet ticks");
   n+=3;t+=3;tickChecks+=3;
   ok(n===3-v/2&&2*t===gain,"canonical reset invariant");phaseChecks++;
  }
  ok(v===x&&literal(x,n,H)===null,"terminal long wait");
  tickChecks+=H;count++;
  examples.push({k,labels:arr,x,A,H,gain,elapsed:t,finalAge:t+H});break;
 }
}
visit([]);rows.push({k,tuples:tried,good:g,bad:b,examples:count});
}
for(let i=0;i<=1;i++)for(let j=0;j<=1;j++)for(let u=i;u<=4;u++)for(let v=j;v<=4;v++)for(let l=-3;l<=i;l++)for(let m=-3;m<=j;m++){ok(l*v+u*m-u*v<=i*j,"vector sieve pointwise");vectorChecks++}
return {tupleTests,bad,good,localChecks,crtChecks,eventChecks,tickChecks,primeTargets,vectorChecks,phaseChecks,rows,examples:examples.slice(0,3).concat(examples.filter(e=>e.k===4).slice(0,2))}
}
console.log(JSON.stringify(audit(),null,2));
