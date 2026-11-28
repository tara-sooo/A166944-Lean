// Exact congruence word and independent height-local replay. Two huge physical CRT representatives; not a finite-slab density test.
function audit(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 const mod=(a,b)=>((a%b)+b)%b;
 const prime=n=>{if(n<2)return false;if(n%2===0)return n===2;for(let d=3;d*d<=n;d+=2)if(n%d===0)return false;return true;};
 const gcd=(a,b)=>b?gcd(b,a%b):a;
 const nextAP=(lo,hi,Q,ok)=>{let p=1+Math.ceil((lo-1)/Q)*Q;for(;p<hi;p+=Q)if(prime(p)&&ok(p))return p;return 0;};
 function choose(k,minP,maxP){
   let Q=4;for(let p=3;p<=Math.max(5,2*(k+1));p+=2)if(prime(p))Q*=p;
   const forbidden=(p,ps)=>{
     let S=0;for(let i=ps.length-1;i>=0;i--){S+=ps[i]-1;if(S%p===0||mod(S-2,p)===0)return false;}return true;
   };
   for(let p1=1+Math.ceil((minP-1)/Q)*Q;p1<maxP;p1+=Q){
     if(!prime(p1))continue;
     const ps=[p1],aa=[1],hs=[p1];let fail=false;
     for(let i=1;i<k;i++){
       const prev=ps.at(-1),a=aa.at(-1);
       let lo,hi,b;
       if(i===1){lo=.54;hi=.55;b=3;}
       else if(i===2){lo=.394;hi=.396;b=9;}
       else{
         for(let t=1;t<10000000;t+=2){
           const l=Math.max(.39,a/(t-1.35)),u=Math.min(.46,a/(t-1.45));
           if(t>1.45&&u-l>1e-5){lo=l+.15*(u-l);hi=u-.15*(u-l);b=t;break;}
           if(t>a/.39+3)break;
         }
       }
       if(!(hi>lo)){fail=true;break;}
       const p=nextAP(lo*prev,hi*prev,Q,q=>forbidden(q,ps));
       if(!p){fail=true;break;}
       ps.push(p);aa.push(b);hs.push(b*p);
     }
     if(fail)continue;
     const p=ps.at(-1),a=aa.at(-1);
     const q=nextAP(p*(1+1/(8*a)),p*(1+1/(4*a)),Q,r=>forbidden(r,ps)&&!ps.includes(r));
     if(!q)continue;
     const low=hs.at(-1)+(p+1)/2,high=((2*a+1)*q-1)/2-1;
     if(high<low)continue;
     return {k,Q,ps,aa,hs,q,H:Math.floor((low+high)/2)};
   }
   throw Error("no tuple k="+k);
 }
 function spf(n){const f=new Int32Array(n+1);for(let p=2;p<=n;p++)if(!f[p]){f[p]=p;if(p*p<=n)for(let x=p*p;x<=n;x+=p)if(!f[x])f[x]=p;}return f;}
 function inv(a,p){let t=0,nt=1,r=p,nr=mod(a,p);while(nr){const q=Math.floor(r/nr);[t,nt]=[nt,t-q*nt];[r,nr]=[nr,r-q*nr];}assert(r===1,"inv");return mod(t,p);}
 const rows=[];let primeChecks=0,sourceChecks=0,clockChecks=0,ticks=0,crtChecks=0,crtDigits=0,reverseChecks=0,boxChecks=0;
 for(const [k,min,max] of [[1,1000,20000],[2,6000,100000],[3,100000,2000000],[4,300000,5000000]]){
   const v=choose(k,min,max),{ps,aa,hs,q,H,Q}=v,Z=2*H+3,f=spf(Z),G=[0];
   for(const p of ps)G.push(G.at(-1)+p-1);
   const res=new Int32Array(Z+1);res.fill(-1);
   for(let p=3;p<=Z;p+=2)if(f[p]===p){
     primeChecks++;
     let r;
     const i=ps.indexOf(p);
     if(i>=0)r=mod(G[i]-1,p);
     else if(p===q)r=mod(G.at(-1)-1,p);
     else if(Q%p===0)r=0;
     else{
       r=0;while(G.some(g=>mod(r-g-1,p)===0||mod(r-g+1,p)===0))r++;
       assert(r<p,"free residue exists");
     }
     res[p]=r;
     for(let j=0;j<G.length;j++){
       const eligible=mod(r-G[j]+1,p)===0||mod(r-G[j]-1,p)===0;
       assert(eligible===(i===j||(p===q&&j===k)),"exact spatial word eligibility");
       sourceChecks++;
     }
   }
   let prev=3;
   for(let i=0;i<k;i++){
     const p=ps[i],h=hs[i],w=h-prev+(p-1)/2;
     assert(w>0&&w<=2*p&&w%2===0,"wait range and parity");
     if(i>0){assert(h-prev>(ps[i-1]-1)/2,"next arrival surpasses previous prefire");assert(G.at(-1)-G[i]<ps[i-1]-1,"later gains bound");}
     assert(h+(p-1)/2-1<H,"no earlier first height");
     const source=mod(res[p]-G[i],p);
     const nmod=mod(h-mod(source-p+1,p)*inv(2,p),p);
     assert(nmod===0,"arrival clock mod p");
     assert(gcd(p,Q)===1&&p%Q===1,"AP");
     prev=h;clockChecks++;
     if(i>=1){assert(ps[i]/ps[i-1]>.38&&ps[i]/ps[i-1]<.56,"ratio");boxChecks++;}
   }
   assert(H-hs.at(-1)>= (ps.at(-1)+1)/2 && H<((2*aa.at(-1)+1)*q-1)/2,"terminal idle");
   assert(H>=ps[0]&&G.at(-1)+6<=4*H,"gain budget");
   let h=3,gain=0,events=[],elapsed=0;
   while(h<H){
     const s=mod(h+1-(4-gain/2),2)===0?1:-1;
     let n=Math.abs(s===1?2*h+3:2*h-3),winner=0;
     while(n>1){const p=f[n];assert(p>0,"factor");if(mod(res[p]+6-gain+s,p)===0){winner=p;break;}while(n%p===0)n/=p;}
     if(winner){gain+=winner-1;h+=1-(winner-1)/2;events.push({p:winner,h,elapsed:elapsed+1});}else h++;
     elapsed++;ticks++;
     assert(h>=0&&elapsed<=3*H+10,"height and time bound");
   }
   assert(JSON.stringify(events.map(x=>x.p))===JSON.stringify([5,3,...ps]),"exact prescribed sequence");
   assert(events[0].h===3&&events[1].h===3,"canonical prefix");
   for(let i=0;i<k;i++){assert(events[i+2].h===hs[i],"expected heights");const prevElapsed=events[i+1].elapsed;assert(events[i+2].elapsed-prevElapsed===hs[i]-(i?hs[i-1]:3)+(ps[i]-1)/2,"exact wait");}
   assert(gain===G.at(-1)+6&&elapsed===H-3+gain/2,"final ledger");
   assert(mod(res[q]-G.at(-1)+1,q)===0,"terminal least prime");
   let d=G.at(-1);
   for(let i=k-1;i>=0;i--){const p=ps[i];assert(mod(res[p]-d,p)===0,"reverse p divides arrival");d-=p-1;reverseChecks++;}
   assert(d===0,"reverse root");
   if(k<=2){
     let a=2n,M=4n;
     for(let p=3;p<=Z;p+=2)if(f[p]===p){
       const P=BigInt(p),r=BigInt(res[p]),t=BigInt(mod(Number(r-a%P)*inv(Number(M%P),p),p));
       a+=M*t;M*=P;
     }
     if(a<100n)a+=M;
     for(let p=3;p<=Z;p+=2)if(f[p]===p){assert(a%BigInt(p)===BigInt(res[p]),"materialized CRT residue");crtChecks++;}
     assert(a%4n===2n&&(a+6n)%6n===0n,"actual canonical CRT");
     let x=a+6n,hh=3,tt=0,lab=[];
     while(hh<H){
       const nn=BigInt(hh+1)-x/2n,s=nn%2n===0n?1:-1;
       let F=Math.abs(s===1?2*hh+3:2*hh-3),p=0;
       while(F>1){const r=f[F];if((x+BigInt(s))%BigInt(r)===0n){p=r;break;}while(F%r===0)F/=r;}
       if(p){x-=BigInt(p-1);hh+=1-(p-1)/2;lab.push(p);}else hh++;
       tt++;assert(tt<=3*H+10,"CRT physical time");
     }
     assert(x===a-BigInt(G.at(-1))&&tt===elapsed&&JSON.stringify(lab)===JSON.stringify([5,3,...ps]),"CRT actual replay");
     crtDigits+=a.toString().length;
   }
   rows.push({...v,Z,gain,elapsed,terminalRatio:q/H,events});
 }
 return {primeChecks,sourceChecks,clockChecks,ticks,crtChecks,crtDigits,reverseChecks,boxChecks,rows};
}
console.log(JSON.stringify(audit(),null,2));
