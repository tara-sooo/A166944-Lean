// Positive-height completed-event construction: CRT calendar and finite canonical replay.
// Run with node. Finite examples do not validate the asymptotic sieve lower.
function audit(){
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(a,m)=>(a%m+m)%m;
 const max=1000000,sp=new Int32Array(max+1);
 for(let p=2;p<=max;p++)if(!sp[p]){sp[p]=p;if(p*p<=max)for(let j=p*p;j<=max;j+=p)if(!sp[j])sp[j]=p}
 const primes=[];for(let p=2;p<=max;p++)if(sp[p]===p)primes.push(p);
 function fac(n){let a=[];for(let p of primes){if(p*p>n)break;if(n%p===0){a.push(p);while(n%p===0)n/=p}}if(n>1)a.push(n);return a}
 function inv(a,q){a=mod(a,q);for(let i=1;i<q;i++)if(mod(a*i,q)===1)return i;throw Error("inverse")}
 function plan(q){
  let out=[];
  for(let u=q+2;u<=2*q;u++)if(u%2===0){
   let r=mod(-u-inv(2,q),q),w=3*q+2-u;
   if([0,1,3,q-1].includes(r)||w<q||w>2*q)continue;
   out.push({q,u,w,r,v:mod(1-inv(r,q),q)});
  }
  return out;
 }
 let localPlans=0,clockControls=0,sourceClassControls=0,averageControls=0;
 for(let q of primes.filter(q=>q>=11&&q<=997&&q%3===2)){
  let ps=plan(q);ok(ps.length>=q/2-5,"many choices");
  ok(new Set(ps.map(a=>a.v)).size===ps.length,"injective choices");
  for(let a of ps){
   localPlans++;
   for(let p=1;p<q;p++){
    let source=mod(p*a.v-2,q)!==0;
    let plus=mod(p*(a.v-1)+1,q)===0,minus=mod(p*(a.v-1)-1,q)===0;
    ok(plus===(p===a.r)&&minus===(p===q-a.r),"exact match classes");
    if(plus||minus){
     ok(source,"source compatibility");
     let u=plus?a.u:a.w,b=plus?0:3;
     ok(u>=q&&u<=2*q&&u%2===(plus?0:1)&&mod(2*p+2*u+1-2*b,q)===0,"clock pin");
     let first=0;for(let t=1;t<=2*q;t++)if(t%2===(plus?0:1)&&mod(2*p+2*t+1-2*b,q)===0){first=t;break}
     ok(first===u,"first calendar");clockControls++;
    }else if(source)sourceClassControls++;
   }
  }
  for(let p=1;p<q;p+=Math.max(1,Math.floor(q/17)))for(let g=0;g<q;g+=Math.max(1,Math.floor(q/13))){
   let cnt=ps.filter(a=>mod(p*(a.v-1)-g+1,q)===0).length;ok(cnt<=1,"one matching plan");averageControls++;
  }
 }
 function next(x,n){let w=Infinity,p=0,s=0;for(let e of [-1,1])for(let q of fac(x+e)){let t=mod((e===1?0:q+2)-n,2*q)||2*q;if(t<w||t===w&&q<p){w=t;p=q;s=e}}return{w,p,s}}
 function literal(x,n,T){let f=[fac(x+1),fac(x-1)];for(let t=1;t<=T;t++){let nn=n+t,s=mod(nn,2)?-1:1,qs=f[s===1?0:1].filter(q=>mod(nn,2*q)===(s===1?0:q+2));if(qs.length)return{w:t,p:Math.min(...qs),s}}return null}
 let pairs=0,matched=0,firstControls=0,firstOutside=0,secondPositive=0,thirdTooLarge=0,thirdPositiveNet=0,bothNonTwin=0,netMin=Infinity,examples=[],tickChecks=0;
 // Finite proxies: K=12, a single selected prime 11, fixed progression on v.
 // No claim of asymptotic density from this sample.
 const q=11,B=4620,ps=plan(q);
 for(let a of ps){
  let residues=[];for(let v=7;v<B;v+=12)if(v%5===1&&v%7===1&&v%q===a.v)residues.push(v);
  ok(residues.length===1,"CRT class");
  for(let p of primes.filter(p=>p>=13&&p<=157&&p%3===1)){
   if(p%q!==a.r&&p%q!==q-a.r)continue;
   for(let v=residues[0];v<=max;v+=B){
    if(v<=4*p||sp[v]!==v)continue;
    let A=p*v-1;if(fac(A-1)[0]<4*p)continue;
    pairs++;let x=p*(v-1),n=p-x/2,w=(3*p-7)/2,e=next(A,3-A/2),l=literal(A,3-A/2,w);
    ok(e.p===p&&e.w===w&&l&&l.p===p&&l.w===w,"canonical high source");firstControls++;tickChecks+=w;
    let s=p%q===a.r?1:-1,u=s===1?a.u:a.w;
    ok(mod(x+s,q)===0&&mod(n+u,2*q)===(s===1?0:q+2),"designated arrival");matched++;
    let f=next(x,n),lf=literal(x,n,f.w);ok(lf&&lf.p===f.p&&lf.w===f.w,"second literal");tickChecks+=f.w;
    ok(f.w<=u,"designated event deadline");
    if(f.p!==q){ok(f.p>=12,"outside selected");firstOutside++;continue}
    ok(f.s===s&&f.w===u,"actual planned second");let y=x-q+1,nn=n+u,h=y/2+nn;
    ok(h===p+u-(q-1)/2&&h>=p+q/2,"positive height change");secondPositive++;
    ok(y%3===2&&(y+1)%3===0,"three clock after selected prime");
    let g=next(y,nn),lg=literal(y,nn,g.w);ok(lg&&lg.p===g.p&&lg.w===g.w&&g.w<=6,"third literal");tickChecks+=g.w;
    let b=g.s===1?0:3;ok(mod(2*p+2*(u+g.w)-(q-1)+1-2*b,g.p)===0,"third height pin");
    if(g.p>=q/2){thirdTooLarge++;continue}
    let z=y-g.p+1,hn=z/2+nn+g.w,inc=hn-p;ok(inc>=q/4,"retained net increase");thirdPositiveNet++;netMin=Math.min(netMin,inc);
    let nt=!(fac(z-1).length===1&&fac(z-1)[0]===z-1&&fac(z+1).length===1&&fac(z+1)[0]===z+1);
    if(nt)bothNonTwin++;
    if(examples.length<6)examples.push({A,p,v,second:{q,w:u,s,h},third:{q:g.p,w:g.w,h:hn},net:inc,nonTwin:nt});
   }
  }
 }
 return{localPlans,clockControls,sourceClassControls,averageControls,pairs,matched,firstControls,firstOutside,secondPositive,thirdTooLarge,thirdPositiveNet,bothNonTwin,netMin:netMin===Infinity?null:netMin,tickChecks,examples}
}
console.log(JSON.stringify(audit(),null,2));
