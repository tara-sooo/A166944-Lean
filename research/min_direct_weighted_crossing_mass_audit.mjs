// Exact inner/outer smoothed mass, pinned-lattice capacity, and weighted A1 tail transfer.
function audit(N=30000){
 const lim=300000,spf=new Int32Array(lim),ps=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i%2)ps.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b,prod=a=>a.reduce((v,p)=>v*p,1),ok=(x,m)=>{if(!x)throw Error(m)};
 let seed=8431;const rand=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n};
 const st={periodControls:0,periodPositions:0,unionChecks:0,intervalChecks:0,shortIntervals:0,innerStarts:0,directChecks:0,mixedChecks:0,roots:0,events:0,unresolved:0,rayControls:0,tailMarks:0,pending:0,resetCorridors:0,nonresetCorridors:0,crossingCorridors:0,colorChecks:0,tailTransferChecks:0,resetWeightChecks:0,witnessTicks:0,witnessResidues:0,examples:[]};
 function setup(S,R,V,L0){
  let small=ps.filter(f=>f<=R),extra=ps.filter(f=>f>R&&f<=V),PS=prod(small.filter(f=>f<=S)),P=prod(small),period=P*prod(extra),A=prod(small.map(f=>f<=S?1:(f-1)/2))*prod(extra.map(f=>f-2)),L=L0||Math.ceil(P**(4/11));
  ok(period<=300000,"period");
  let pref=new Int32Array(period+1);for(let j=0;j<period;j++){let hit=small.every(f=>{let v=mod(2*j,f);return f<=S?v===0:v%2===0&&v<=f-3})&&extra.every(f=>![1,f-1].includes(mod(2*j,f)));pref[j+1]=pref[j]+Number(hit)}
  ok(pref[period]===A,"density");
  const pre=j=>{let q=Math.floor(j/period);return q*A+pref[j-q*period]},mass=(a,b)=>pre(b)-pre(a);
  const unit=BigInt(A)*BigInt(L),p=BigInt(period),roll=j=>p*BigInt(mass(j,j+L));
  // Cache exact lower/upper error prefixes for constant-time ray queries.
  let ep=[0n],en=[0n];for(let j=0;j<period;j++){let v=roll(j)-unit;ep.push(ep.at(-1)+(v>0n?v:0n));en.push(en.at(-1)+(v<0n?-v:0n))}
  const epre=(a,j)=>{let q=Math.floor(j/period);return BigInt(q)*a[period]+a[j-q*period]},err=(a,b,neg)=>{let v=neg?en:ep;return epre(v,b)-epre(v,a)};
  return {S,R,V,PS,P,period,A,L,unit,p,mass,roll,err};
 }
 const specs=[[3,5,7],[5,7,17],[7,7,13],[7,11,17],[11,13,17],[3,7,17]],cs=specs.map(v=>setup(...v));
 for(let c of cs){let {period:P,L,unit,p,PS,mass,roll,err}=c;st.periodControls++;st.periodPositions+=P;
  for(let k=0;k<150;k++){
   let a=rand(4*P)-2*P,b=a+20+rand(1000),j=a,parts=[],N=0,G=0,m=0n,cap=0n,inner=0n;
   while(j<b){j+=rand(8);if(j>=b)break;let z=Math.min(b,j+1+rand(70));parts.push([j,z]);j=z+rand(7)}
   for(let [u,v] of parts){let n=v-u,q=p*BigInt(L)*BigInt(mass(u,v)),d=p*BigInt(L)*BigInt(Math.ceil(n/PS)),s=unit*BigInt(n+L-1);ok(q<=d,"direct");m+=q;cap+=d<s?d:s;N++;G+=n;st.directChecks++;st.intervalChecks++;if(n<L)st.shortIntervals++;
    let i=0n;for(let j=u;j+L<=v;j++){i+=roll(j);st.innerStarts++}ok(i<=q,"inner");inner+=i
   }
   ok(inner<=m&&m>=unit*BigInt(G-(L-1)*N)-err(a,b,true),"lower");
   ok(m<=unit*BigInt(G+(L-1)*N)+err(a-L+1,b,false),"upper");
   ok(m<=cap+err(a-L+1,b,false),"mixed");st.mixedChecks++;st.unionChecks++;
  }
 }
 const A1=z=>z.p>=47&&z.p>=5*(z.d+3)&&z.dp-6*z.I===2*z.p,reset=z=>z.p>=5&&z.dp===6*z.I;
 function inspect(rows,c,T0,kind){
  let {period:P,L,unit,p,mass,err,PS}=c,x=[...rows.map(z=>z.d+3),rows.at(-1).dp+3],C=Math.max(...rows.map(z=>z.p)),h0=rows[0].H/2n,base=Number(h0%p),last=rows.at(-1),len=Number((last.H+BigInt(last.p-1))/2n-h0);
  let cuts=rows.map(z=>{let a=Number((z.H/2n)%p),q=mass(a,a+(z.p-1)/2);ok(q<=Math.ceil((z.p-1)/(2*PS)),"cut cap");if(q)ok(z.p>c.R,"ordinary barrier");st.directChecks++;return q});
  let MB=2n*p*BigInt(L)*BigInt(rows.reduce((v,z,i)=>v+(!A1(z)&&!reset(z)?cuts[i]:0),0)),colors=[[],[],[]],rw=new Map,nReset=0,nTail=0,Gtail=0;
  for(let T=T0,j=0;T<=C;T*=2,j++){let prev=-1,pending=0;for(let i=0;i<rows.length;i++)if(A1(rows[i])&&rows[i].p>=T&&rows[i].p<2*T){st.tailMarks++;
   let b=i+1;while(b<x.length&&5*x[b]>2*T)b++;if(b===x.length){pending++;st.pending++;continue}
   ok(i>=prev,"cores");prev=b;let a=b-1;while(10*x[a]<19*T)a--;
   let rs=-1,G=0,B=0;for(let h=a;h<b;h++){let z=rows[h];ok(!A1(z)&&5*x[h]>2*T&&10*x[h+1]<19*T,"corridor");if(reset(z)){ok(h===b-1,"reset last");rs=h}else ok(20*x[h]<57*T,"localization");G+=z.p-1;B+=cuts[h]}
   ok(2*G>=3*T&&G>=4*L,"tail gain");
   if(rs>=0){ok(5*(rows[rs].p+6)>2*T,"reset");rw.set(rs,(rw.get(rs)||0)+rows[i].p);nReset++;st.resetCorridors++;continue}
   colors[j%3].push({a,b,G,B});nTail++;Gtail+=G;st.nonresetCorridors++;
   if(B){st.crossingCorridors++;if(st.examples.length<3)st.examples.push({kind,S:c.S,R:c.R,V:c.V,L,T,mark:rows[i].p,labels:rows.slice(a,b).map(z=>z.p),B,G})}
  }ok(pending<=1,"pending")}
  let E=2n*err(base,base+len,true),sum=0n,counts=new Int32Array(rows.length);
  for(let a of colors){a.sort((u,v)=>u.a-v.a);let G=0,B=0;for(let i=0;i<a.length;i++){let z=a[i];if(i)ok(a[i-1].b<=z.a,"color");for(let h=z.a;h<z.b;h++)counts[h]++;G+=z.G;B+=z.B;let h=Number((rows[z.a].H/2n)%p);ok(mass(h,h+z.G/2)===z.B,"mass")}
   let m=2n*p*BigInt(L)*BigInt(B);ok(m>=unit*BigInt(G-2*(L-1)*a.length)-E,"color lower");sum+=m;st.colorChecks++;
  }
  for(let q of counts)ok(q<=3,"overlap");ok(sum<=3n*MB,"B mass");
  ok(unit*BigInt(2*L*nTail)<=3n*MB+3n*E,"tail count");ok(unit*BigInt(Gtail)<=6n*MB+6n*E,"tail gain");st.tailTransferChecks++;
  let W=0;for(let [i,v] of rw){ok(v<10*(rows[i].p+6),"reset weight");W+=rows[i].p+6;st.resetWeightChecks++}ok(4*L*nReset<=15*W,"reset tail count");st.rayControls++;
 }
 function factors(x){let a=[];ok(x>0&&x<lim,"sieve");while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;for(let i=0;i<180;i++){let z=null;for(let I=0;I<=1;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p)z={H:BigInt(H),p,w,I,d:2*t-H,dp:2*t-H+2*w-p+1}}if(!z)break;rows.push(z);H+=z.p-1;t+=z.w}st.events+=rows.length;if(rows.length===180)st.unresolved++;if(rows.some(A1))for(let c of cs.slice(0,3))inspect(rows,c,Math.max(47,Math.ceil(8*c.L/3)),"canonical")}
 const word=[7687,5233,3541,2389,1621,1093,733,7369],g=[0];for(let p of word)g.push(g.at(-1)+p-1);
 let H=0n,P=4n;for(let s of ps.filter(p=>p<=3*7687+6)){let at=word.indexOf(s),r=at>=0?mod(1-g[at],s):0,valid=x=>g.slice(0,-1).every((v,i)=>word[i]===s?mod(x+v,s)===1:![1,s-1].includes(mod(x+v,s)));while(at<0&&r<s&&!valid(r))r++;ok(r<s&&valid(r),"CRT");let a=Number(P%BigInt(s)),b=s,u=1,v=0;while(b){let q=Math.floor(a/b);[a,b]=[b,a-q*b];[u,v]=[v,u-q*v]}ok(a===1,"inv");H+=P*BigInt(mod(u*mod(r-Number(H%BigInt(s)),s),s));P*=BigInt(s);st.witnessResidues+=word.length}
 if(H<100000000n)H+=P;let t=H/2n+3n,rows=[];const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a};
 for(let p of word){let d=Number(2n*t-H),w=(3*p-d-1)/2;for(let j=1;j<=w;j++){let n=t+BigInt(j),I=n%2n;ok(gcd(n-2n*I,H-1n+2n*I)===BigInt(j===w?p:1),"literal tick");st.witnessTicks++}rows.push({H,p,d,dp:2*p,w,I:0});H+=BigInt(p-1);t+=BigInt(w)}
 for(let c of cs)inspect(rows,c,3500,"witness");
 for(let L of [100,1000])inspect(rows,setup(3,5,7,L),3500,"witness");
 ok(st.mixedChecks&&st.shortIntervals&&st.nonresetCorridors&&st.crossingCorridors&&st.resetCorridors,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||30000)),null,2));
