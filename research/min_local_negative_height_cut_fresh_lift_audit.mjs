// Exact first-preheight one-step pushforward and fresh-prime lift energy.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,pr=[3,5,7,11,13,17,19];
 function cut(a,H){let A=a,n=3-a/2,h=3;for(;;){let p=0,w=Infinity;for(let q of pr)if(q<=2*H-1)for(let e of [-1,1])if(mod(a-e,q)===0){let t=mod((e===-1?0:q+2)-n,2*q)||2*q;if(t<w||t===w&&q<p){p=q;w=t}}
 if(h+w>=H)return a;h+=w-(p-1)/2;n+=w;a-=p-1;ck(h>=0,"height");}}
 let out={periodRoots:0,transitionChecks:0,freshLiftChecks:0,energyChecks:0,rows:[]};
 for(let H=4;H<=8;H++){
 let M=2*pr.filter(p=>p>=5&&p<=2*H-1).reduce((a,b)=>a*b,1),M2=2*pr.filter(p=>p>=5&&p<=2*H+1).reduce((a,b)=>a*b,1),period=6*M2,old=new Map(),now=new Map(),map=new Map();
 for(let j=0;j<M2;j++){let A=6*j,a=mod(cut(A,H),period),b=mod(cut(A,H+1),period);old.set(a,(old.get(a)||0)+1);now.set(b,(now.get(b)||0)+1);if(map.has(a))ck(map.get(a)===b,"map");map.set(a,b);out.periodRoots++}
 let stay=new Map(),incoming=new Map(),E=0,E2=0,moving=0,fresh=0,parityEligible=0,moveEnergy=0;
 for(let [a,m] of old){let b=map.get(a),n=H-a/2,q=0;
   for(let p of pr){if(p>2*H+1)break;let e=n%2===0?-1:1,c=e===-1?0:p+2;if(mod(a-e,p)===0&&mod(n-c,2*p)===0){q=p;break}}
   ck((b===a)===(q===0),"moving iff first tick fires");out.transitionChecks++;
   if(b===a)stay.set(b,m);else{incoming.set(b,(incoming.get(b)||0)+m);moving+=m;moveEnergy+=m*m;}
   E+=m*m;
   if(n%2===0){parityEligible+=m*m;if(q===2*H+1)fresh+=m*m}
 }
 let cross=0,V=0;for(let [b,m] of now){E2+=m*m;let i=incoming.get(b)||0,s=stay.get(b)||0;ck(m===i+s,"pushforward");cross+=2*i*s;V+=i*i;out.energyChecks++}
 ck(E2-E===cross+V-moveEnergy,"energy balance");ck(E2>=E,"nested energy");
 if(pr.includes(2*H+1)){ck(fresh*(2*H+1)===parityEligible,"fresh prime exact energy");out.freshLiftChecks++}
 out.rows.push({H,M,M2,oldEnergy:E/M2,nextEnergy:E2/M2,movingMass:moving/M2,movingEnergy:moveEnergy/M2,freshEnergy:fresh/M2,parityEligible:parityEligible/M2,delta:(E2-E)/M2})
 }
 return out;
}
console.log(JSON.stringify(audit(),null,2));
