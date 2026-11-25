// Bounded-deficit local realization control; no canonical ancestry claimed.
function auditShort(){
 const mod=(x,m)=>(x%m+m)%m;
 function fac(n){let fs=[];for(let d=3;d*d<=n;d+=2)if(n%d===0){fs.push(d);while(n%d===0)n/=d}if(n>1)fs.push(n);return fs}
 function gcd(a,b){while(b)[a,b]=[b,a%b];return a}
 let s={checks:0,phases:0,minimumRatio:null,large:[],literalTicks:0};
 function check(H,p,e){
 let q=(H-e)/p,I=(1-e)/2,h0=mod(I-(q+1)/2,2),n0=p*((q+1)/2+h0)+2*I,w=Math.ceil((p-1)/4);
 let other=[1,-1].flatMap(fside=>fac(H-fside).filter(f=>f!==p&&f*f<=H+1).map(f=>({f,fside})));
 if(other.length>5||other.some(x=>x.f<p))return;
 let count=0,example=null,maxD=0;
 for(let j=0;j<4*p;j++){let n=n0+2*p*j,t=n-w,h=h0+2*j,D=2*p*h;
 if(t<H/2||D>=16*p*p)throw Error("envelope");
 let ok=other.every(({f,fside})=>{let lag=mod(n-(fside===1?0:f+2),2*f);return lag===0||lag>=w});
 if(ok){count++;maxD=Math.max(maxD,D);if(!example)example={n,t,h,D,w}}
 s.phases++;
 }
 if(2*count<p)throw Error("short phase lower bound");
 if(!s.minimumRatio||count*s.minimumRatio.p<s.minimumRatio.count*p)s.minimumRatio={H,p,e,count};
 s.checks++;
 if(H>1e10){
 let {t}=example;for(let i=1;i<=w;i++){let n=t+i,ef=n%2?-1:1,g=gcd(ef===1?n:n-2,H-ef),f=g===1?0:fac(g)[0],active=f&&f*f<=H+1;if(i<w&&active||i===w&&(!active||f!==p))throw Error("literal");s.literalTicks++}
 s.large.push({H,p,e,w,other,count,total:4*p,example,maxD});
 }
 }
 for(let H=8;H<=2000;H+=2){let cs=[1,-1].flatMap(e=>fac(H-e).filter(p=>p*p<=H+1).map(p=>({p,e}))).sort((a,b)=>a.p-b.p);if(cs.length)check(H,cs[0].p,cs[0].e)}
 for(let p of [5003,5039])check(p**3+1,p,1);
 return s
}
console.log(JSON.stringify(auditShort(),null,2));
