// Small-prime absorption potential and reverse active-time identity.
function audit(){
const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))}, mod=(a,p)=>(a%p+p)%p, N=300000,spf=new Uint32Array(N+3);
for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let x=p*p;x<=N+2;x+=p)if(!spf[x])spf[x]=p;
function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
let C=Array.from({length:8193},(_,k)=>k?fs(k%2?k+2:k):[]);
function step(a,k){let e=k%2?1:-1,p=C[k].find(p=>mod(a-e,p)===0);return p===undefined?a:a-p+1}
let rows=[];
for(let z of [3,5,7,11]){
 let A=fs(1);for(let p=3;p<=z;p+=2)if(!spf[p])A.push(p);
 let Q=2*A.reduce((a,p)=>a*p,1),R=new Uint16Array(Q*Q/2),rough=new Uint8Array(Q/2),get=(b,k)=>R[mod(b,Q)/2*Q+mod(k,Q)],rr=b=>rough[mod(b,Q)/2]===1;
 let s={z,Q,states:R.length,rough:0,maxR:0,meanR:0,stepChecks:0,targets:0,edges:0,high:0,neutral:0,disruptive:0,positive:0,roughToNonrough:0,firstDisruption:0,extinct:0,roots:0,events:0,telescopes:0,active:0,elapsed:0,net:0,pos:0,profile:[]};
 for(let b=0;b<Q;b+=2){
  let E=[];for(let p of A){if(mod(b+1,p)===0)E.push([p,0]);else if(mod(b-1,p)===0)E.push([p,p+2])}
  if(!E.length){rough[b/2]=1;s.rough++;continue}
  for(let k=0;k<Q;k++){let p=Infinity,w=Infinity;for(let [r,t] of E){let h=mod(t+k,2*r)||2*r;if(h<w||h===w&&r<p){p=r;w=h}}ck(b>=p-1,"wall");let h=w+get(b-p+1,k-w);ck(h<=3*Q,"cap");R[b/2*Q+k]=h;s.maxR=Math.max(s.maxR,h);s.meanR+=h}
 }
 s.meanR/=R.length;
 for(let b=0;b<Q;b+=2)for(let k=0;k<Q;k++){let p=A.find(p=>mod(k%2?k+2:k,p)===0&&mod(b-(k%2?1:-1),p)===0),a=p===undefined?b:b-p+1;ck(get(b,k+1)-get(a,k)===(rr(b)?0:1),"step");s.stepChecks++}
 for(let P=1009;P<=N;P+=2)if(!spf[P]&&spf[P-2]&&(P<=30000||P%101===1)){
  let b0=P-1,S=new Map([[b0,false]]),K=Math.min(8192,b0/2-4);s.targets++;
  for(let k=1;k<=K;k++){let V=new Map();
   function add(a,b,p,flag){
    let high=p>z,delta=high?get(b,k)-get(a,k):0,lhs=get(a,k+1)-get(b,k)+delta;
    ck(lhs===(rr(a)?0:1),{z,P,k,a,b,p,high,delta,lhs,rough:rr(a),R:[get(a,k+1),get(b,k),get(a,k)],C:C[k],A});
    s.edges++;if(high){s.high++;if((p-1)%Q===0){s.neutral++;ck(delta===0,"neutral")}else{s.disruptive++;flag=true}if(delta>0)s.positive++;if(rr(a)&&!rr(b))s.roughToNonrough++}
    if(!rr(b0)&&!flag){ck(!rr(a)&&k<=s.maxR-get(b0,1),"no disruption survival");s.firstDisruption++}
    if(V.has(a))ck(V.get(a)===flag,"uniqueness");V.set(a,flag)
   }
   for(let [b,flag] of S){if(step(b,k)===b)add(b,b,0,flag);for(let p of C[k])if(step(b+p-1,k)===b)add(b+p-1,b,p,flag)}
   S=V;if(!S.size){s.extinct++;break}
  }
 }
 for(let X=12;X<=N;X+=198){let a=X,v=-X/2+3,initial=get(a,-v),act=0,net=0,pos=0,time=0;
  while(v< -1&&a){let p=Infinity,w=Infinity;for(let [d,e] of [[a+1,1],[a-1,-1]])for(let r of fs(d)){let h=mod((e===1?0:r+2)-v,2*r)||2*r;if(h<w||h===w&&r<p){p=r;w=h}}
   let W=Math.min(w,-1-v),b=W===w?a-p+1:a,k=-v-W,high=W===w&&p>z,delta=high?get(b,k)-get(a,k):0;
   ck(W*(rr(a)?0:1)===get(a,-v)-get(b,k)+delta,"event telescope");act+=W*(rr(a)?0:1);net+=delta;pos+=Math.max(0,delta);time+=W;s.events++;a=b;v+=W
  }
  ck(act===initial-get(a,-v)+net,"path telescope");s.roots++;s.telescopes++;s.active+=act;s.net+=net;s.pos+=pos;s.elapsed+=time
 }
 rows.push(s)
}
return rows
}
console.log(JSON.stringify(audit(),null,2));
