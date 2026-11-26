// Odd multiplier obstruction and whole-tag baseline cost, no support assumption.
function audit(Xs=[4096,16384,65536]){
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 let lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1);
 for(let p=2;p<=lim;p++)if(!spf[p])for(let j=p;j<=lim;j+=p)spf[j]=p;
 let out=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,tags=[],events=0;
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let C0=2*M-2,C=C0,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity;for(let I=0;I<2;I++){let v=C-1+2*I;while(v>1){let f=spf[v];while(v%f===0)v/=f;if(f*f>C+1)continue;let r=mod((I?f+2:0)-t,2*f)||2*f;if(r<w||r===w&&f<p){p=f;w=r}}}if(!p)break;
    let J=C+p-1,n=t+w,I=n%2,d=2*t-C,dp=2*n-J;path.push({C,t,J,n,I,e:1-2*I,p,w,g:p-1,d,dp,j:path.length});events++;C=J;t=n;
   }tags.push({M,C0,F:C,path})
  }
  for(let Y of [11,17,31,61])for(let mode of [0,1]){
   let L=mode?Math.max(1,Math.floor(H/2)):H,K=6;
   let st={X,focus,N:tags.length,events,Y,L,K,tagsWithPairs:0,pairs:0,M:0,G:0,adjusted3:0,unadjusted3:0,oddChecks:0,parityChecks:0,ratioChecks:0,baselineChecks:0,shallowPairs:0,shallowMass:0,lambda:0,inverse:0,weightedInverse:0,tagQuadraticChecks:0,prefixChecks:0,prefixGain:0,interiorGain:0,lateSlack:0,downSlack:0,nonconsecutivePairs:0,maxK:0,maxPost:0,lowerNormalized:0};
   for(let tag of tags){
    let G=tag.path.reduce((s,e)=>s+e.g,0),bins=new Map(),pairs=[],used=new Set();
    for(let e of tag.path){let id=Math.floor((e.C-tag.C0)/L);if(!bins.has(id))bins.set(id,[]);bins.get(id).push(e)}
    for(let es of bins.values()){
     let high=es.filter(e=>e.p>=Y);
     for(let j=1;j<high.length;j++){
      let s=high[j-1],t=high[j];if(s.p>K*Y||t.p>K*Y||s.dp<=s.d||t.dp>=t.d)continue;
      let relay=tag.path.slice(s.j+1,t.j),E=relay.reduce((v,e)=>v+e.g,0),V=relay.reduce((v,e)=>v+e.w,0);
      let upper=Math.min(s.dp,t.d,...relay.map(e=>e.dp)),lower=Math.max(6,s.d,t.dp),m=Math.max(0,upper-lower);
      if(!m)continue;
      ok(!used.has(s)&&!used.has(t)&&E===t.C-s.J&&V===t.t-s.n,"actual nonoverlapping pair");used.add(s);used.add(t);
      pairs.push({s,t,E,V,m,u:s.dp-s.d,v:t.d-t.dp});
     }
    }
    let M=pairs.reduce((v,z)=>v+z.m,0),Gu=pairs.reduce((v,z)=>v+z.s.g,0),Gd=pairs.reduce((v,z)=>v+z.t.g,0),Go=G-Gu-Gd,n=pairs.length,A=3*Gu+4*n-M,D=Gd-M,del3=A+3*D+3*Go,raw3=3*G-4*M;
    ok(A>=0&&D>=2*n&&Go>=0&&del3===raw3+4*n&&3*raw3>=del3&&M<=G,"unadjusted saturation slack");
    let lambda=0,inv=0,weighted=0,mis=0,ratio=0,late=0,down=0,base=6,last=-1,og=0,shallow=0,shallowM=0;
    for(let z of pairs){
     let {s,t,E,V,m,u,v}=z,p=s.p,r=t.p,h=(s.dp-6*s.I)/(2*p),k=(t.dp-6*t.I)/(2*r),c=E-1-2*(V+t.w)+6*(t.I-s.I),a=2*p-s.w;
     ok(Number.isInteger(h)&&h>=1&&Number.isInteger(k)&&k>=0&&2*h*p-(2*k+1)*r===c&&Math.abs(c)%2===1,"exact odd multiplier");
     ok(s.j>last&&s.j<t.j&&V<=3*E&&Math.abs(c)<=5*E+2*t.w+7,"interior clock budget");
     let R=Math.abs(r-3*p),ell=R+5*E+2*t.w+7;
     ok(Math.abs(2*h-6*k-3)>=1&&p<=(2*k+1)*R+Math.abs(c)&&p<=(2*k+1)*ell,"odd parity obstruction");
     ok(r-3*p===v-u+2-2*a+2*t.w&&m<=Math.min(u,v),"endpoint ratio");
     let other=tag.path.slice(last+1,s.j).reduce((v,e)=>v+e.g,0);
     base+=5*other;og+=other;ok(s.d<=base,"prefix and interpair baseline envelope");
     base+=Math.abs(u-v)+5*E;og+=E;ok(t.dp<=base&&base<=6+5*del3/3+1e-7,"target baseline envelope");
     last=t.j;
     lambda+=ell;inv+=p/(2*k+1);weighted+=m*Y/(Y+t.dp);mis+=Math.abs(u-v);ratio+=R;late+=2*a;down+=2*t.w;
     if(k<=2){shallow++;shallowM+=m}
     st.maxK=Math.max(st.maxK,k);st.maxPost=Math.max(st.maxPost,t.dp);st.oddChecks++;st.parityChecks++;st.ratioChecks++;st.baselineChecks+=2;st.interiorGain+=E;if(t.j>s.j+1)st.nonconsecutivePairs++;
    }
    ok(og<=Go&&mis<=A+D&&late<=A&&down<=D&&ratio<=2*(A+D)+2*n,"whole-tag complementary budget");
    ok(lambda<=2*A+3*D+5*Go+9*n&&lambda<=2*del3+9*n&&2*n<=del3/3&&inv<=lambda+1e-7&&weighted<=4*inv+1e-7,"inverse multiplier sum");
    ok(shallowM<=20*lambda+1e-7,"bounded multiplier mass");
    let delta=del3/3,raw=raw3/3;
    ok(M<=42*delta*(1+(6+5*delta)/Y)+1e-6,"tag quadratic bound");
    ok(raw+1e-7>=M*Math.sqrt(Y/H)/1512,"unadjusted all-support gap");
    if(n){st.tagsWithPairs++;let s=pairs[0].s,pre=s.C-tag.C0;ok(pre>=Math.max(0,(s.d-6)/5)-1e-7,"canonical prefix");st.prefixGain+=pre;st.prefixChecks++}
    st.tagQuadraticChecks++;st.pairs+=n;st.M+=M;st.G+=G;st.adjusted3+=del3;st.unadjusted3+=raw3;st.lambda+=lambda;st.inverse+=inv;st.weightedInverse+=weighted;st.shallowPairs+=shallow;st.shallowMass+=shallowM;st.lateSlack+=late;st.downSlack+=down;st.lowerNormalized+=M*Math.sqrt(Y/H)/1512;
   }
   ok(3*st.unadjusted3>=st.adjusted3&&st.unadjusted3/3+1e-6>=st.lowerNormalized&&st.inverse<=st.lambda+1e-6,"aggregate unconditional budget");
   out.push(st)
  }
 }
 return out
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
