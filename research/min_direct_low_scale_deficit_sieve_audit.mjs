// Low-scale deficit-coordinate band sieve: exact arithmetic and gain budgets.
function audit(N=60000){
 const lim=1800000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i>2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function inv(a,b){if(b===1)return 0;let c=b,x=1,y=0;a=mod(a,b);while(c){let q=Math.floor(a/c);[a,c]=[c,a-q*c];[x,y]=[y,x-q*y]}ok(a===1,"inverse");return mod(x,b)}
 function factors(x){ok(x>0&&x<lim,"range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g;z={H,p,w,I,e:1-2*I,d,dp,x:(dp-6*I)/2,g}}}return z}
 const st={roots:0,events:0,cap:0,blocks:0,selected:0,pairs:0,close:0,cap1:0,cap2:0,unique:0,crt:0,parameter:0,residues:0,range:0,budget:0,localBand:0,localGroups:0,localEdges:0,localBoundaries:0,localMulti:0,localRangeBudget:0,syntheticLocal:0,smallTvsH:0,synthetic:0,syntheticResidues:0,weighted:0,examples:[]};
 function inspect(rows,T,nu){let cap=Math.floor(T**(nu===2?1.4:1.85)),l=rows.filter(z=>z.p>=T&&z.p<2*T&&z.x>0&&z.x<=cap);if(!l.length)return;st.blocks++;st[nu===2?"cap2":"cap1"]++;st.selected+=l.length;
 let G=rows.reduce((s,z)=>s+z.g,0),F=l.reduce((s,z)=>s+z.g,0),V=rows.reduce((s,z)=>s+Math.abs(z.dp-z.d),0),L=Math.min(...l.map(z=>z.x)),R=Math.max(...l.map(z=>z.x))-L,W=Math.max(T,R+1),A=Math.floor(T/2),B=Math.floor(T/2),Etotal=0,Dtotal=0,close=0,bad=0;
 ok(R<=V/2+3,"range");st.range++;let M=new Map;
 for(let i=1;i<l.length;i++){let u=l[i-1],v=l[i],E=v.H-u.H-u.g,d=v.dp-u.dp,c=v.x-u.x;Etotal+=E;Dtotal+=Math.abs(d);st.pairs++;
 if(E>B||Math.abs(d)>A){bad+=v.g;continue}
 ok(u.p!==v.p&&c!==0&&factors(u.x).filter(p=>p>=T).length===1&&factors(v.x).filter(p=>p>=T).length===1,"unique");st.unique+=2;
 let h=u.x/u.p,k=v.x/v.p,g=gcd(h,k),a=h/g,b=k/g,m=c/g;ok(c%g===0,"gcd");
 let x0=h*mod(-m*inv(a,b),b),P=h*b,z=(u.x-x0)/P;ok(Number.isInteger(z)&&u.p===x0/h+b*z&&v.p===(x0+c)/k+a*z,"forms");st.parameter++;
 for(let f of pr){if(f>=Math.min(u.p,v.p,31))break;if(a%f&&b%f){let r1=mod(-x0/h*inv(b,f),f),r2=mod(-(x0+c)/k*inv(a,f),f);ok((r1===r2)===(m%f===0)&&mod(z,f)!==r1&&mod(z,f)!==r2,"roots");st.residues++}}
 let H0=u.e+u.p*mod((v.e-u.g-E-u.e)*inv(u.p,v.p),v.p);ok(mod(u.H-H0,u.p*v.p)===0,"horizon CRT");st.crt++;
 let key=[u.x,c,E,u.I,v.I].join(","),o=M.get(key)||{n:0,min:u.H,max:u.H,P:u.p*v.p,w:0};ok(o.P===u.p*v.p,"tuple");o.n++;o.min=Math.min(o.min,u.H);o.max=Math.max(o.max,u.H);o.w+=v.g;M.set(key,o);
 close+=v.g;st.close++;if(T*T*100<u.H)st.smallTvsH++;if(st.examples.length<3)st.examples.push({T,nu,H:u.H,H2:v.H,p:u.p,r:v.p,x:u.x,x2:v.x,E,d});
 }
 for(let o of M.values()){ok(o.n<=1+Math.floor((o.max-o.min)/o.P)&&o.w<=2*T*(1+Math.floor((o.max-o.min)/o.P)),"tuple bound");st.weighted++}
 let groups=[];for(let z of l){let id=Math.floor(z.H/(T*T));if(!groups.length||groups.at(-1).id!==id)groups.push({id,vis:[]});groups.at(-1).vis.push(z)}
 let sumR=0,sumW=0,nedge=0,inter=0,firstGain=0;for(let {vis} of groups){let lo=Math.min(...vis.map(z=>z.x)),hi=Math.max(...vis.map(z=>z.x));sumR+=hi-lo;sumW+=Math.max(T,hi-lo+1);firstGain+=vis[0].g;nedge+=vis.length-1;for(let j=1;j<vis.length;j++)inter+=Math.abs(vis[j].dp-vis[j-1].dp)}
 let span=Math.floor(rows.at(-1).H/(T*T))-Math.floor(rows[0].H/(T*T))+1;ok(groups.length<=span&&firstGain<=2*T*groups.length&&nedge+groups.length===l.length,"bin endpoints");ok(2*sumR<=inter+6*groups.length&&inter<=V&&2*sumW<=2*(T+4)*groups.length+V,"local range budget");st.localBand++;st.localGroups+=groups.length;st.localEdges+=nedge;st.localBoundaries+=groups.length-1;if(groups.length>1)st.localMulti++;st.localRangeBudget++;
 ok(Etotal<=G-F&&Dtotal<=V&&F===l[0].g+close+bad,"partition");ok((F-l[0].g-close)*(A+1)*(B+1)<=2*T*((A+1)*(G-F)+(B+1)*V),"band budget");st.budget++;
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
 for(let T of [7,11,17,31,61])for(let nu of [1,2])inspect(rows,T,nu)
 }
 for(let T of [11,31,101,1009])for(let h=1;h<=20;h++)for(let k=1;k<=20;k++)for(let c of [-9,-1,1,9]){let g=gcd(h,k);if(c%g)continue;let a=h/g,b=k/g,m=c/g,x0=h*mod(-m*inv(a,b),b),P=h*b,L=T*17+3,W=T;let first=Math.ceil((L-x0)/P),last=Math.floor((L+W-1-x0)/P);let count=0;for(let x=L;x<L+W;x++)if(x%h===0&&(x+c)%k===0){ok(mod(x-x0,P)===0,"translated");count++}ok(count===Math.max(0,last-first+1),"length");st.synthetic++;
 for(let f of [23,29,31]){let r1=mod(-x0/h*inv(b,f),f),r2=mod(-(x0+c)/k*inv(a,f),f);ok((r1===r2)===(m%f===0),"synthetic root");st.syntheticResidues++}}
 for(let T of [7,11,31,101])for(let i=0;i<200;i++){let H=0,x=2*T,I=0,arr=[];for(let j=0;j<100;j++){H+=2*(1+(j*19+i)%T);x=Math.max(T,x+((i+j*17)%13)-6);I=(i+j)%2;arr.push({H,x,d:2*x+6*I})}let V=arr.slice(1).reduce((s,z,j)=>s+Math.abs(z.d-arr[j].d),0),groups=new Map;for(let z of arr){let k=Math.floor(z.H/(T*T));if(!groups.has(k))groups.set(k,[]);groups.get(k).push(z)}let W=0;for(let v of groups.values())W+=Math.max(T,Math.max(...v.map(z=>z.x))-Math.min(...v.map(z=>z.x))+1);ok(2*W<=2*(T+4)*groups.size+V,"synthetic local range");st.syntheticLocal++}
 ok(st.localMulti&&st.close&&st.smallTvsH&&st.cap1&&st.cap2&&st.synthetic,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
