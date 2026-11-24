// Node.js; exact integer arithmetic in the tested range (X <= 2^22).
function audit(X) {
 const B=Math.ceil(Math.sqrt(7*X)), spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return a};
 function next(t,C,K){let u=K+1,q=0;for(const s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let r=s===-1?0:p+2,m=2*p,h=t+1+((r-t-1)%m+m)%m;if(h<u||(h===u&&p<q)){u=h;q=p}while(v%p===0)v/=p}}return [u,q]}
 const assert=(b)=>{if(!b)throw Error("assertion failed")};
 let Qs=[Math.max(11,Math.ceil(Math.sqrt(B))),Math.max(11,Math.ceil(B/Math.log(B)**(2/3))),Math.max(11,Math.ceil(B/Math.log(B)**(1/16)))], Js=[32,210], T=Math.ceil(B*Math.log(B)**(1/16)), mass=new Int32Array(7*X/2+1), mark=new Uint8Array(mass.length);
 let stats=Qs.flatMap(Q=>Js.map(J=>({Q,J,big:0,windows:0,alternating:0,light:0,short:0,long:0,zero:0,nonlow:0,maxmid:0,tagR:0,unionR:0,horizons:0})));
 let R=0,events=0,literal=0;
 for(let M=X+1;M<2*X;M+=2){
  let C=2*M-2,t=M+2,K=Math.floor((7*M-1)/4),a=[];
  for(;;){let [u,p]=next(t,C,K);if(X<=1024){let v=K+1,q=0;for(let j=t+1;j<=K;j++){let g=gcd(j%2?j-2:j,C+(j%2?1:-1));if(g>1&&spf[g]<=B){v=j;q=spf[g];break}}assert(u===v&&p===q);literal++}if(!p)break;let r=Math.min(spf[C-1],spf[C+1]);assert(u-t<=2*r);mass[C/2]++;R+=r;events++;a.push([C,p,u%2?1:-1]);C+=p-1;t=u;assert(C<=2*t)}
  for(let i=0;i<Qs.length;i++){
   let v=[];for(let j=0;j<a.length;j++)if(a[j][1]>=Qs[i])v.push(j);
   for(let k=0;k<2;k++){let s=stats[2*i+k];s.big+=v.length;s.windows+=Math.max(0,v.length-3)}
   for(let j=0;j+3<v.length;j++){
    let [x,y,z,u]=v.slice(j,j+4).map(k=>a[k]),p=x[1],q=y[1];if(p===q||p!==z[1]||q!==u[1])continue;
    let g1=y[0]-x[0]-p+1,g2=z[0]-y[0]-q+1,g3=u[0]-z[0]-p+1,A=z[0]-x[0]+z[2]-x[2],D=u[0]-y[0]+u[2]-y[2],c=g1-g3+z[2]-x[2]-u[2]+y[2];
    assert(g1>=0&&g2>=0&&g3>=0&&A>0&&D>0&&A%p===0&&D%q===0&&A-D===c);if(c===0)assert(A>=p*q);
    let nonlow=false;for(let h=v[j+1]+1;h<v[j+2];h++)if(a[h][1]>7)nonlow=true;
    for(let k=0;k<2;k++){let s=stats[2*i+k];s.alternating++;if(g1>s.J||g3>s.J)continue;s.light++;s.maxmid=Math.max(s.maxmid,g2);s.zero+=+(c===0);s.nonlow+=+nonlow;if(g2<=T){s.short++;for(let e of [x,y,z,u])mark[e[0]/2]|=1<<(2*i+k)}else s.long++;for(let e of [x,y,z,u])s.tagR+=Math.min(spf[e[0]-1],spf[e[0]+1])}
   }
  }
 }
 for(let C=2*X;C<7*X;C+=2)if(mark[C/2])for(let i=0;i<stats.length;i++)if(mark[C/2]&(1<<i)){stats[i].horizons++;stats[i].unionR+=mass[C/2]*Math.min(spf[C-1],spf[C+1])}
 for(const s of stats)assert(s.short+s.long===s.light);
 return {X,B,T,R,events,literal,stats};
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
