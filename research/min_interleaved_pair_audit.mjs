// Node.js: bounded-rank two light pairs, same or reversed; exact integers in tested windows.
function auditPairs(X) {
 const B=Math.ceil(Math.sqrt(7*X)),spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const assert=x=>{if(!x)throw Error("assertion failed")};
 const gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return a};
 function next(t,C,K){let u=K+1,q=0;for(const s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let m=2*p,r=s===-1?0:p+2,h=t+1+((r-t-1)%m+m)%m;if(h<u||(h===u&&p<q)){u=h;q=p}while(v%p===0)v/=p}}return [u,q]}
 const Qs=[Math.max(11,Math.ceil(Math.sqrt(B))),Math.max(11,Math.ceil(B/Math.log(B)**(2/3))),Math.max(11,Math.ceil(B/Math.log(B)**(1/16)))],J=210,T=Math.ceil(B*Math.log(B)**(1/16)),H=8;
 const stats=Qs.map(Q=>({Q,big:0,lightPairs:0,pairs:0,same:0,reverse:0,short:0,long:0,middleNonlow:0,nonadjacent:0,maxmid:0,zero:0,tagR:0,coveredR:0,coveredH:0}));
 const mass=new Int32Array(7*X/2+1),mark=new Uint8Array(mass.length);
 let R=0,events=0,literal=0;
 for(let M=X+1;M<2*X;M+=2){
  let C=2*M-2,t=M+2,K=Math.floor((7*M-1)/4),a=[];
  for(;;){let [u,p]=next(t,C,K);if(X<=1024){let v=K+1,q=0;for(let j=t+1;j<=K;j++){let g=gcd(j%2?j-2:j,C+(j%2?1:-1));if(g>1&&spf[g]<=B){v=j;q=spf[g];break}}assert(u===v&&p===q);literal++}if(!p)break;let r=Math.min(spf[C-1],spf[C+1]);assert(u-t<=2*r);mass[C/2]++;R+=r;events++;a.push([C,p,u%2?1:-1]);C+=p-1;t=u;assert(C<=2*t)}
  for(let i=0;i<Qs.length;i++){
   let v=[];for(let j=0;j<a.length;j++)if(a[j][1]>=Qs[i])v.push(j);let s=stats[i];s.big+=v.length;
   for(let j=0;j+1<v.length;j++){let x=a[v[j]],y=a[v[j+1]],p=x[1],q=y[1],g1=y[0]-x[0]-p+1;if(p===q||g1>J)continue;s.lightPairs++;
    for(let l=j+2;l+1<v.length&&l+1-j<H;l++){let z=a[v[l]],u=a[v[l+1]],same=z[1]===p&&u[1]===q,rev=z[1]===q&&u[1]===p;if(!same&&!rev)continue;let g3=u[0]-z[0]-z[1]+1;if(g3>J)continue;
     let g2=z[0]-y[0]-q+1,A=(same?z[0]:u[0])-x[0]+(same?z[2]:u[2])-x[2],D=(same?u[0]:z[0])-y[0]+(same?u[2]:z[2])-y[2];assert(A>0&&D>0&&A%p===0&&D%q===0);
     let a1=A-(rev?p:0),d1=D+(rev?q:0),c=same?g1-g3+z[2]-x[2]-u[2]+y[2]:g1+g3-2+u[2]-x[2]-z[2]+y[2];assert(a1-d1===c&&a1>0&&d1>0);if(!c)assert(a1>=p*q);s.pairs++;s.same+=+same;s.reverse+=+rev;s.nonadjacent+=+(l>j+2);s.zero+=+(c===0);s.maxmid=Math.max(s.maxmid,g2);
     let nonlow=false;for(let h=v[j+1]+1;h<v[l];h++)if(a[h][1]>7)nonlow=true;s.middleNonlow+=+nonlow;
     if(g2<=T){s.short++;for(let e of [x,y,z,u])mark[e[0]/2]|=1<<i}else s.long++;
     for(let e of [x,y,z,u])s.tagR+=Math.min(spf[e[0]-1],spf[e[0]+1]);
    }
   }
  }
 }
 for(let C=2*X;C<7*X;C+=2)if(mark[C/2])for(let i=0;i<stats.length;i++)if(mark[C/2]&(1<<i)){stats[i].coveredH++;stats[i].coveredR+=mass[C/2]*Math.min(spf[C-1],spf[C+1])}
 for(const s of stats)assert(s.pairs===s.same+s.reverse&&s.pairs===s.short+s.long);
 return {X,B,J,T,H,R,events,literal,stats};
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(auditPairs(Number(a))));
