function audit(){
 const abs=a=>a<0n?-a:a,mod=(a,b)=>(a%b+b)%b;
 function gcd(a,b){a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a}
 function fac(a){let out=[];for(let p=2n;p*p<=a;p+=(p===2n?1n:2n))if(a%p===0n){out.push(p);while(a%p===0n)a/=p}if(a>1n)out.push(a);return out}
 function prime(a){return a>1n&&fac(a)[0]===a}
 function tick(n,H){let s=n%2n?1n:-1n,g=gcd(n%2n?n-2n:n,H+s);if(g===1n)return 1n;let p=fac(g)[0];return p*p<=H+1n?p:1n}
 let records=[];
 for(let l of [19n,173n,1009n,10007n,100003n]){
 if(!prime(l))throw Error("label");
 let p=145n;while(p%l!==3n)p+=204n;
 let tries=0;while(p<=l+2n||p%31n===21n||fac(l-9n).some(r=>r>2n&&mod(p+6n,r)===0n)||!prime(p)){p+=204n*l;if(++tries>100000)throw Error("candidate search")}
 let x=p+1n,n=p*(p+3n)/2n,H=x*x-l-17n,t=n-8n,events=[];
 if(H>2n*t||H%2n)throw Error("start");
 for(let j=t+1n;j<=n;j++){let q=tick(j,H);if(q>1n){H+=q-1n;events.push([j-n,q,H]);}}
 let expected=[[-7n,l,x*x-18n],[-2n,3n,x*x-16n],[-1n,17n,x*x],[0n,p,p*(p+3n)]];
 const str=o=>JSON.stringify(o,(_,v)=>typeof v==="bigint"?String(v):v);
 if(str(events)!==str(expected)||p%204n!==145n||(p+2n)%3n)throw Error("chain");
 records.push({l,p,x,n,start:[t,x*x-l-17n],events,tries});
 }
 return JSON.parse(JSON.stringify(records,(_,v)=>typeof v==="bigint"?String(v):v))
}

console.log(JSON.stringify(audit(),null,2));
