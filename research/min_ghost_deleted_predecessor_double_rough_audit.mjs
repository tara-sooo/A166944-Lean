// Delete the fresh predecessor and count insertion phases; equal-slope double rough sieve.
function audit(U,N=64){
 const V=4*U,ps=[],sv=new Uint8Array(V+1);
 for(let p=2;p<=V;p++)if(!sv[p]){if(p>2)ps.push(p);if(p*p<=V)for(let j=p*p;j<=V;j+=p)sv[j]=1;}
 const mod=(x,p)=>(x%p+p)%p,ck=(x,m)=>{if(!x)throw Error(m)};
 let rng=(0x921bf2d7^U)>>>0;function rand(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}function uni(p){let a=4294967296-4294967296%p,x;do{x=rand()}while(x>=a);return x%p;}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),H=3,A=5,L=6,base=Math.max(11,Math.floor(Math.sqrt(2*U)/8));
 let out={U,N,V,H,A,L,base,events:0,upwardPairs:0,longTargetPairs:0,shortPredecessor:0,longPredecessor:0,shortWeight:0,longWeight:0,phaseChecks:0,deletedPrefixChecks:0,roughChecks:0,localChecks:0,nondegenerate:0,collisions:0,degenerate:0,exhaustive:[]};
 function run(del=-1,lim=U){let g=0,s=0,a=[];for(;;){let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){if(j===del)continue;let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[j]+s-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i])){w=f;i=j;}}
 if(s+w>lim)break;a.push({i,p:ps[i],g,s:s+w,w});s+=w;g+=ps[i]-1;}return a;}
 function exposure(del,q,G,parity){let x=0,g=0,end=U+1;for(let e of del){if(g===G){end=e.s;break;}x=e.s;g=e.g+e.p-1;}
 if(g!==G)return null;let all=new Set(),short=new Set();
 for(let w=1;w<=Math.min(2*q,U-x,end-x);w++){let s=x+w,chi=(parity+s)%2,key=mod(1-2*chi-G,q)*q+mod(2*chi-s,q);all.add(key);if(w<=q/H)short.add(key);}
 ck(all.size<=2*q&&short.size<=Math.floor(q/H),"exposure size");return {all,short,x};}
 function rough(g,cut,omit=-1){for(let j=0;j<ps.length&&ps[j]<=cut;j++)if(j!==omit){let x=mod(c[j]+g,ps[j]);if(x===1||x===ps[j]-1)return false;}return true;}
 for(let n=0;n<N;n++){
 let parity=uni(2);for(let j=0;j<ps.length;j++){let p=ps[j];c[j]=uni(p);let x=uni(p);t[j]=x%2===parity?x:x+p;}
 let seq=run(),first=new Map(),prev=null;out.events+=seq.length;
 for(let k=0;k<seq.length;k++){let x=seq[k],fresh=!first.has(x.i);
 if(x.p>=A){if(!fresh&&prev?.fresh&&x.p>prev.p&&x.p>=base&&prev.p>=7&&x.g+x.p-1<=2*U){out.upwardPairs++;
 if(4*x.w>x.p){out.longTargetPairs++;let q=prev.p,p=x.p,u=first.get(x.i),d=x.g-prev.g-q+1;
 ck(u.s<prev.s&&d>=0&&d<L&&d%2===0,"pair order and low gain");let a=[-2,0,2].find(a=>mod(x.g-u.g-a,p)===0),m=(x.g-u.g-a)/p;ck(Number.isInteger(m)&&m>=1,"return stride");
 let del=run(prev.i),before=seq.filter(e=>e.s<prev.s),db=del.filter(e=>e.s<prev.s);ck(JSON.stringify(before)===JSON.stringify(db),"deleted prefix");out.deletedPrefixChecks++;
 let z=exposure(del,q,prev.g,parity);ck(z&&z.all.has(c[prev.i]*q+mod(t[prev.i],q)),"insertion phase");out.phaseChecks++;
 ck(rough(x.g,Math.floor(p/8),prev.i),"target rough");out.roughChecks++;
 if(prev.w<=q/H){ck(z.short.has(c[prev.i]*q+mod(t[prev.i],q)),"short phase");out.shortPredecessor++;out.shortWeight+=p;}
 else{ck(rough(prev.g,Math.floor(q/(2*H)),prev.i),"predecessor rough");out.roughChecks++;out.longPredecessor++;out.longWeight+=p;}
 }}prev={...x,fresh};}if(fresh)first.set(x.i,x);}
 // Local sieve roots for two positions of equal slope.
 for(let h=0;h<16;h++){let m=1+uni(2*U),v=uni(2*U+1),q=ps[1+uni(Math.min(20,ps.length-1))],d=2*uni(L/2),a=q-1+d;
 for(let j=0;j<ps.length&&ps[j]<=47;j++){let ell=ps[j],roots=new Set([0]);for(let x=0;x<ell;x++){let z=mod(c[j]+v+m*x,ell),y=mod(z-a,ell);if(z===1||z===ell-1||y===1||y===ell-1)roots.add(x);}
 out.localChecks++;if(m%ell===0||[a,a-2,a+2].some(x=>x%ell===0)){out.degenerate++;continue;}
 let collision=[1,-1,a+1,a-1].some(x=>mod(c[j]+v-x,ell)===0);ck(roots.size===(collision?4:5),"equal-slope five roots");if(collision)out.collisions++;else out.nondegenerate++;}}
 // Enumerate actual insertion pairs with other coordinates fixed.
 if(n<2){let qi=n+1,q=ps[qi],oc=c[qi],ot=t[qi],del=run(qi),counts=new Map(),shorts=new Map(),hits=0;
 for(let a=0;a<q;a++)for(let b=0;b<q;b++){c[qi]=a;t[qi]=b%2===parity?b:b+q;let f=run().find(x=>x.i===qi);if(!f)continue;hits++;let z=exposure(del,q,f.g,parity);ck(z&&z.all.has(a*q+b),"enumerated phase coverage");counts.set(f.g,(counts.get(f.g)||0)+1);if(f.w<=q/H){ck(z.short.has(a*q+b),"enumerated short coverage");shorts.set(f.g,(shorts.get(f.g)||0)+1);}}
 c[qi]=oc;t[qi]=ot;let max=Math.max(0,...counts.values()),maxShort=Math.max(0,...shorts.values());ck(max<=2*q&&maxShort<=Math.floor(q/H),"enumeration bound");out.exhaustive.push({q,pairs:q*q,hits,locations:counts.size,max,maxShort});}
 }
 return out;
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?64:128)));
