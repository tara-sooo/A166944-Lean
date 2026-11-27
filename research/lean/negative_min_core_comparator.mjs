// Independent event-calendar vs literal tick comparator for NegativeMINCore.
// node research/lean/negative_min_core_comparator.mjs
function audit(){
 const mod=(x,n)=>(x%n+n)%n,ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 const prime=p=>p>=3&&p%2===1&&Array.from({length:Math.max(0,p-2)},(_,i)=>i+2).every(d=>p%d!==0);
 function factors(n){let a=[];for(let p=2;p*p<=n;p++)if(n%p===0){a.push(p);while(n%p===0)n/=p}if(n>1)a.push(n);return a}
 function tick(x,n){
  let t=n+1;
  for(let p=3;p<=x+1;p+=2)if(prime(p)&&(mod(t,2)===0?(x+1)%p===0&&mod(t,2*p)===0:x>=2&&(x-1)%p===0&&mod(t,2*p)===p+2))return [x-p+1,t,p];
  return [x,t,0];
 }
 function event(x,n){
  let p=Infinity,w=Infinity,ties=0;
  if(x<2)return {p,w,ties};
  for(let e of [-1,1])for(let r of factors(x-e)){
   if(r===2)continue;
   let d=mod((e===-1?0:r+2)-n,2*r)||2*r;
   if(d<w){w=d;p=r;ties=1;}else if(d===w){ties++;if(r<p)p=r;}
  }
  return {p,w,ties};
 }
 let checks=0,events=0,ties=0,fixtures=[],sameCenter=null,tieFixture=null,seen=new Map();
 for(let A=6;A<=1200;A+=6){
  let x=A,n=3-A/2,y=x,m=n,ev=event(y,m),fire=m+ev.w;
  for(let k=1;k<=120;k++){
   let r=tick(x,n);x=r[0];n=r[1];
   if(n===fire){
    ck(r[2]===ev.p,"winning prime");if(ev.ties>1){ties++;if(tieFixture===null)tieFixture={A,age:k-1,x:y,n:n-1,p:ev.p};}
    y-=ev.p-1;m=n;ev=event(y,m);fire=m+ev.w;events++;
   }else ck(r[2]===0,"quiet tick");
   ck(x===y&&2*n+x>=0&&x%2===0&&A-x<=2*k+6,{A,k,x,y,n});checks++;
   if(A<=120&&[1,5,10,20].includes(k))fixtures.push({A,k,x,n});
   if(A<=120&&sameCenter===null&&x>2){
    let old=seen.get(x);if(old&&old.n!==n&&tick(x,n)[0]!==tick(old.x,old.n)[0])sameCenter={old,new:{A,k,x,n},nextOld:tick(x,old.n)[0],nextNew:tick(x,n)[0]};
    else if(!old)seen.set(x,{A,k,x,n});
   }
  }
 }
 return {checks,events,ties,tieFixture,sameCenter,fixtures:fixtures.filter((_,i)=>i%7===0)};
}
if(typeof console!=="undefined")console.log(JSON.stringify(audit(),null,2));
