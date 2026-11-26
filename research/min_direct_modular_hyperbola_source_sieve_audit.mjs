// Near-square modular hyperbola: actual product constraints, local sieve densities and elementary exponential-sum controls.
function audit(N=40000){
 const lim=1600000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i>2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)spf[j]=spf[j]||i}
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function inv(a,b){let c=b,x=1,y=0;a=mod(a,b);while(c){let q=Math.floor(a/c);[a,c]=[c,a-q*c];[x,y]=[y,x-q*y]}ok(a===1,"inverse");return mod(x,b)}
 function factors(x){ok(x>0&&x<lim,"range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p)z={H,p,w,I,e:1-2*I,g:p-1,q:(H-1+2*I)/p}}return z}
 let st={roots:0,events:0,cap:0,controls:0,pairs:0,product:0,rough:0,generic:0,exception:0,box:0,largeWait:0,fast:0,sourcePrime:0,targetComposite:0,disjoint:0,localDensities:0,crtDensity:0,hyperbolaBoxes:0,hyperbolaPoints:0,expSums:0,secondMoment:0,fourier:0,maxRatio:0,longBoxes:0,longFourier:0,longPoints:0,examples:[]};
 for(let n=5;n<=N;n+=2){let H=2*n-2,t=n+2,v=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;v.push(z);H+=z.g;t+=z.w}st.events+=v.length;if(v.length===180)st.cap++;
 for(let T of [11,17,31,61]){let B=Math.min(T-4,Math.ceil(Math.log(T)**2)),hi=v.map((z,i)=>({...z,i})).filter(z=>z.p>=T),last=-1,used=0,Glo=v.filter(z=>z.p<T).reduce((s,z)=>s+z.g,0);
 for(let j=1;j<hi.length;j++){let u=hi[j-1],z=hi[j],p=u.p,r=z.p;if(p>6*T||r>6*T||2*u.w<=u.g)continue;let E=v.slice(u.i+1,z.i).reduce((s,z)=>s+z.g,0);if(E>B)continue;
 let a=E+u.e-1-z.e,q=u.q,s=z.q;ok(p!==r&&a%2!==0&&Math.abs(a)<p&&r*s===p*(q+1)+a&&mod(r*s-a,p)===0,"product");st.product++;st.pairs++;
 if(q===spf[q])st.sourcePrime++;if(s!==spf[s])st.targetComposite++;
 if(z.w>=Math.sqrt(T))st.largeWait++;else st.fast++;
 if(u.H<=100*p*p&&z.H<=100*p*p){ok(r<=6*p&&s<=600*p+6,"box");st.box++}
 for(let l of pr){if(l>=T||4*l>=u.g)break;if(l<=3)continue;let A=mod(p+a,l),D=mod(p+a-2*u.e,l);ok(A!==D&&r%l!==0&&q%l!==0&&(p*q+2*u.e)%l!==0&&mod(r*s,l)!==A&&mod(r*s,l)!==D,"rough");st.rough++;if(A&&D)st.generic++;else st.exception++}
 if(u.i>last){last=z.i;used+=E;ok(used<=Glo,"disjoint");st.disjoint++}
 if(st.examples.length<3&&s!==spf[s])st.examples.push({T,p,r,q,s,E,a,H:u.H,H2:z.H,wait:z.w})
 }st.controls++}}
 for(let l of [5,7,11,13,17,19,23,29])for(let A=0;A<l;A++)for(let D=0;D<l;D++){if(A===D)continue;let count=0;for(let r=0;r<l;r++)for(let s=0;s<l;s++)if(!r||mod(r*s,l)===A||mod(r*s,l)===D)count++;ok(count===3*l-2,"density");st.localDensities++}
 for(let d of [35,55,77]){let fs=factors(d),count=0;for(let r=0;r<d;r++)for(let s=0;s<d;s++)if(fs.every(l=>!mod(r,l)||mod(r*s,l)===1||mod(r*s,l)===2))count++;ok(count===fs.reduce((v,l)=>v*(3*l-2),1),"density CRT");st.crtDensity++}
 for(let p of [11,17,31,61,101])for(let a of [-3,-1,1,3])for(let d of [1,5,7,35])for(let i=0;i<20;i++){
 let l=-p+3*i,R=l+2*p+7,L=2*i-17,S=L+p+11,b=mod(7*i,d),c=mod(11*i+1,d),brute=0,via=0;
 let rs=[],ss=[];for(let r=l;r<R;r++)if(mod(r,d)===b)rs.push(r);for(let s=L;s<S;s++)if(mod(s,d)===c)ss.push(s);
 for(let r of rs)for(let s of ss)if(mod(r*s-a,p)===0)brute++;
 for(let r of rs)if(mod(r,p)!==0){let residue=mod(a*inv(r,p),p);via+=ss.filter(s=>mod(s,p)===residue).length}
 ok(brute===via,"hyperbola box");st.hyperbolaBoxes++;st.hyperbolaPoints+=brute;
 }
 for(let p of [11,17,31,61,101,127]){let C=Array.from({length:p},(_,i)=>Math.cos(2*Math.PI*i/p)),S=Array.from({length:p},(_,i)=>Math.sin(2*Math.PI*i/p)),iv=Array(p).fill(0);for(let x=1;x<p;x++)iv[x]=inv(x,p);
 for(let b=1;b<Math.min(p,9);b++){let sum=0;for(let h=1;h<p;h++){let re=0,im=0;for(let z=2;z<p;z++){let k=mod(-b*iv[h]*iv[mod(z*(z-1),p)],p);re+=C[k];im+=S[k]}sum+=re*re+im*im}
 let count=0;for(let z=2;z<p;z++)for(let t=2;t<p;t++)if(mod(z*(z-1)-t*(t-1),p)===0)count++;
 ok(Math.abs(sum-(p*count-(p-2)**2))<1e-6*p*p&&sum<=2*p*p,"second moment");st.secondMoment++;
 for(let a=0;a<Math.min(p,17);a++){let re=0,im=0;for(let x=1;x<p;x++){let k=mod(a*x+b*iv[x],p);re+=C[k];im+=S[k]}let v=re*re+im*im;ok(v<=p-1+Math.sqrt((p-1)*sum)+1e-6*p*p,"Kloosterman");st.expSums++;st.maxRatio=Math.max(st.maxRatio,Math.sqrt(v)/p**.75)}
 }
 let xs=[],ys=[];for(let x=-p;x<2*p+3;x++)if(mod(x,5)===1)xs.push(x);for(let y=-3;y<p+4;y++)if(mod(y,7)===2)ys.push(y);
 let main=0,imag=0,brute=0;for(let x of xs)for(let y of ys)if(mod(x*y-3,p)===0)brute++;
 function ft(arr,k){let re=0,im=0;for(let x of arr){let a=mod(-k*x,p);re+=C[a];im+=S[a]}return [re,im]}
 let Fx=Array.from({length:p},(_,k)=>ft(xs,k)),Fy=Array.from({length:p},(_,k)=>ft(ys,k));
 for(let a=0;a<p;a++)for(let b=0;b<p;b++){let re=0,im=0;for(let x=1;x<p;x++){let k=mod(a*x+3*b*iv[x],p);re+=C[k];im+=S[k]}let [u,v]=Fx[a],[w,z]=Fy[b],rr=u*w-v*z,ii=u*z+v*w;main+=rr*re-ii*im;imag+=rr*im+ii*re}
 ok(Math.abs(main/(p*p)-brute)<1e-6&&Math.abs(imag/(p*p))<1e-6,"Fourier identity");st.fourier++;
 }
 for(let p of [11,31,61,101])for(let d of [5,7,13])for(let m of [1,10,100]){
 let a=3,xs=[],ys=[];for(let x=p;x<6*p+1;x++)if(mod(x,d)===1)xs.push(x);for(let y=1;y<=m*p+17;y++)if(mod(y,d)===2)ys.push(y);
 let xc=Array(p).fill(0),yc=Array(p).fill(0);for(let x of xs)xc[mod(x,p)]++;for(let y of ys)yc[mod(y,p)]++;
 let count=0,brute=0;for(let x=1;x<p;x++)count+=xc[x]*yc[mod(a*inv(x,p),p)];
 for(let x of xs)if(mod(x,p))brute+=ys.filter(y=>mod(y,p)===mod(a*inv(x,p),p)).length;
 ok(count===brute,"long rectangle");
 for(let k=1;k<p;k++){let re=0,im=0;for(let x=0;x<p;x++){re+=yc[x]*Math.cos(2*Math.PI*k*x/p);im+=yc[x]*Math.sin(2*Math.PI*k*x/p)}let bound=1/Math.abs(Math.sin(Math.PI*mod(k*d,p)/p));ok(Math.hypot(re,im)<=bound+1e-6*ys.length,"nonzero Fourier independent of AP length");st.longFourier++}
 st.longBoxes++;st.longPoints+=count;
 }
 ok(st.pairs&&st.rough&&st.targetComposite&&st.fast&&st.largeWait&&st.hyperbolaBoxes,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||40000)),null,2));
