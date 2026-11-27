// Exact arbitrary-phase finite-alphabet small-descent capacity (all states).
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(m)},mod=(a,p)=>(a%p+p)%p,pr=[3,5,7,11];
 let z={states:0,transitions:0,directChecks:0,rows:[]};
 for(let K of [3,5,7,11]){
  let P=pr.filter(p=>p<=K),Q=P.reduce((a,b)=>a*b,1),L=2*Q,len=Q*L,g=new Int32Array(len),c5=new Int32Array(len),c7=new Int32Array(len),maxG=0,max5=0,max7=0,s5=0,s7=0;
  for(let x=0;x<Q;x++){
   let E=[];for(let p of P)for(let s of [-1,1])if(mod(2*x-s,p)===0)E.push([p,s===-1?0:p+2]);
   for(let n=0;n<L;n++){
    let p0=0,w=Infinity;for(let [p,c] of E){let t=mod(c-n,2*p)||2*p;if(t<w||t===w&&p<p0){p0=p;w=t}}
    let i=x*L+n;
    if(p0){let y=x-(p0-1)/2;ck(y>=0,"wall");let j=y*L+mod(n+w,L);g[i]=p0-1+g[j];c5[i]=(p0<=5?(p0-3)/2:0)+c5[j];c7[i]=(p0<=7?(p0-3)/2:0)+c7[j];z.transitions++}
    maxG=Math.max(maxG,g[i]);max5=Math.max(max5,c5[i]);max7=Math.max(max7,c7[i]);s5+=c5[i];s7+=c7[i];z.states++;
   }
  }
  for(let x=0;x<Q;x+=Math.max(1,Math.floor(Q/29)))for(let n0=0;n0<L;n0+=Math.max(1,Math.floor(L/31))){
   let a=2*x,n=n0,G=0,C5=0,C7=0;
   for(;;){let p0=0,w=Infinity;for(let p of P)for(let s of [-1,1])if(mod(a-s,p)===0){let t=mod((s===-1?0:p+2)-n,2*p)||2*p;if(t<w||t===w&&p<p0){p0=p;w=t}}if(!p0)break;G+=p0-1;if(p0<=5)C5+=(p0-3)/2;if(p0<=7)C7+=(p0-3)/2;a-=p0-1;n+=w}
   let i=x*L+n0;ck(G===g[i]&&C5===c5[i]&&C7===c7[i],"direct");z.directChecks++;
  }
  z.rows.push({K,Q,states:len,maxG,max5,max7,mean5:s5/len,mean7:s7/len,max5Ratio:max5/K,max7Ratio:max7/K});
 }return z
}
console.log(JSON.stringify(audit(),null,2));
