// Independent difference-array audit of hybrid canonical target correction.
function check(X,stress=false){
const B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),a=Math.max(13,Math.ceil(B/(stress?8:2))),Q=Math.max(5,Math.ceil(B/10)),lim=7*X+B+20,S=new Int32Array(lim);
const ok=(x,msg)=>{if(!x)throw Error(msg)},eq=(x,y)=>Math.abs(x-y)<=1e-7*Math.max(1,Math.abs(x),Math.abs(y)),mod=(x,y)=>(x%y+y)%y;
for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
function fac(n){let f=[];while(n>1){let p=S[n];if(p>2&&p<=B)f.push(p);while(n%p===0)n/=p}return f}
let N=0,events=0,targets=0,reached=0,reset=0,even=0,old=0,hybrid=0,oldRem=0,hybridRem=0,oldReached=0,hybridReached=0,checks=0,peak=0;
for(let M=X;M<2*X;M++)if(S[M]===M){
 N++;let C0=2*M-2,C=C0,t0=M+2,t=t0,cut=Math.floor((7*M-1)/4),es=[],can=[{g:0,t}];
 while(C-C0<T){
 let p=0,v=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
 if(!p||v>cut)break;
 let G=C+p-1,w=v-t,k=(2*v-G-6*(v%2))/(2*p),c=C/2+3,r=Math.min(...fac(C-1),...fac(C+1));
 if(C%4===0&&t<=c&&c<v&&c>can.at(-1).t)can.push({g:C-C0,t:c});
 ok(w<=2*r&&w<=3*(p-1)&&Number.isInteger(k),"clock");
 es.push({g:C-C0,G:G-C0,t,v,k,mark:w<=.2*(p-1)||(p>=Q&&r>3&&2*r>p&&k===0&&v-can.at(-1).t>2*p)});
 events++;C=G;t=v;if(C%4===0&&2*t-C===6&&t>can.at(-1).t)can.push({g:C-C0,t});
 }
 const n=t-t0,prev=new Float64Array(n+1),load=new Float64Array(n+1),gaps=can.filter(c=>c.g<T);
 const add=(arr,l,h,w)=>{arr[l-t0]+=w;arr[h-t0]-=w};
 let j=0,V=0,U=0,D=0,F=0,H=0,J=0;
 for(let i=0;i<gaps.length;i++){let c=gaps[i],L=(gaps[i+1]?.g??T)-c.g;if(L<a)continue;
 for(let x=c.g+Math.floor(L/2)+1;x<=c.g+L;x++){
 while(j<es.length&&es[j].G<x)j++;
 let e=es[j],R=x-c.g,W=(e?.v??t)-c.t,w=1/R,Wh=W,d=2*t-C,missing=x-(C-C0);
 targets++;J++;H+=w;add(prev,c.t,e?.v??t,w);
 if(e){reached++;let ts=Math.max(e.t,c.t),f=(x-e.g)/(e.G-e.g),dp=2*ts-(C0+e.g),dq=2*e.v-(C0+e.G),I=W-(1-f)*(e.v-ts),A=W-(e.G-x)/2;
 ok(dp>=0&&dq>=0&&f>0&&f<=1&&eq(2*I,R-6+(1-f)*dp+f*dq)&&eq(2*A,R-6+dq),"deficit identities");
 Wh=Math.min(I,A);d=Math.min(dq,(1-f)*dp+f*dq);missing=0;
 ok(Wh>0&&Wh<=W+1e-9&&2*Wh>=R-6-1e-8,"reached bound");
 if(e.k===0){reset++;if(e.v%2===0){even++;ok(eq(2*Wh,R-6),"even reset");}}
 if(A<I){add(load,c.t,e.v,w*A/W)}else{add(load,c.t,ts,w);add(load,ts,e.v,w*f)}
 oldReached+=W*w;hybridReached+=Wh*w;
 }else add(load,c.t,t,w);
 ok(eq(2*Wh,R-6+d-missing),"target identity");D+=d*w;F+=missing*w;V+=W*w;U+=Wh*w;
 }}
 let l=0,o=0,ss=0,oo=0,pr=0,hr=0;
 for(let e of es)for(let tick=e.t;tick<e.v;tick++){let k=tick-t0;l+=load[k];o+=prev[k];ok(l>=-1e-7&&l<=o+1e-7&&o<=1+1e-7,"tick domination");peak=Math.max(peak,l);ss+=l;oo+=o;if(!e.mark){hr+=l;pr+=o}checks++}
 ok(eq(V,oo)&&eq(U,ss)&&eq(2*U,J-6*H+D-F)&&hr<=pr+1e-7,"transpose");
 old+=V;hybrid+=U;oldRem+=pr;hybridRem+=hr;
}
const rnd=x=>+x.toFixed(6);return {X,stress,N,events,targets,reached,reset,even,old:rnd(old),hybrid:rnd(hybrid),oldRem:rnd(oldRem),hybridRem:rnd(hybridRem),oldReached:rnd(oldReached),hybridReached:rnd(hybridReached),checks,peak:rnd(peak)};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536])) console.log(JSON.stringify(check(X)));console.log(JSON.stringify(check(65536,true)));
