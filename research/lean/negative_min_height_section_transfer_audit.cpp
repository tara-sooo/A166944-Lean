#include <cstdint>
#include <algorithm>
#include <cmath>
#include <iostream>
#include <iomanip>
#include <vector>
#include <cassert>
using namespace std;
int mod(long long a,int b){int r=a%b;return r<0?r+b:r;}
struct Hit{int x=0,g=0,age=0,events=0,minh=0,idle=0;};
struct Engine{vector<int> sp;Engine(int R):sp(2*R+2){for(int p=2;p<(int)sp.size();p++)if(!sp[p]){sp[p]=p;if((long long)p*p<(int)sp.size())for(int j=p*p;j<(int)sp.size();j+=p)if(!sp[j])sp[j]=p;}}
 pair<int,int> next(int x,int n){int w=INT32_MAX,p=0;for(int s:{-1,1})for(int v=x+s;v>1;){int q=sp[v];while(v%q==0)v/=q;int t=mod((s==1?0:q+2)-n,2*q);if(!t)t=2*q;if(t<w||(t==w&&q<p)){w=t;p=q;}}return{w,p};}
 int literal(int x,int n){int v=x+(mod(n,2)?-1:1);for(int q=3;(long long)q*q<=v;q+=2){if(v%q)continue;if(mod(n,2*q)==(mod(n,2)?q+2:0))return q;while(v%q==0)v/=q;}return v>1&&mod(n,2*v)==(mod(n,2)?v+2:0)?v:0;}
 Hit go(int A,int x,int h,int H,int B){int n=h-x/2,ev=0,mh=h;while(h<H){auto[w,p]=next(x,n);if(w>H-h){int g=A-x;assert(g<=B);return{x,g,H-3+g/2,ev,mh,H-h};}if(A-x+p-1>B)return{};n+=w;x-=p-1;h=x/2+n;assert(h>=0&&h<H);mh=min(mh,h);ev++;}return{x,A-x,H-3+(A-x)/2,ev,mh,0};}
};
int main(){cout<<setprecision(10);cout<<"R,H,roots,sinks,rough_lt_H16,active_lt_H16,min_gain_lt_H4,root_gain_ge_H,transfer_in,transfer_out,budget_fail,merge_loss,descended_below_half\n";for(int R:{12000,48000,192000,768000,3072000}){Engine e(R);int H=(int)pow(R,.4),h0=(int)pow(R,.2854);vector<int> heights={h0};while(heights.back()<H)heights.push_back(min(H,2*heights.back()));heights.erase(unique(heights.begin(),heights.end()),heights.end());int B=4*H;for(int A=(R+5)/6*6;A<=2*R;A+=6000){int x=A,n=3-A/2,h=3;while(h<H&&A-x<=B){int q=e.literal(x,n+1);if(q)x-=q-1;n++;h=x/2+n;}auto f=e.go(A,A,3,H,B);assert((h==H&&A-x<=B)?f.x==x:!f.x);}vector<int> prev(e.sp.size()),practical(e.sp.size());for(int h:heights){vector<int> exact(e.sp.size()),fixed(e.sp.size()),transfer(e.sp.size()),fromPractical(e.sp.size());long long roots=0,sinks=0,active=0,smallrough=0,gsmall=0,bigGain=0,loose=0,same=0,fail=0,merged=0,down=0,pop=0,pcnt=0,ploss=0;for(int A=(R+5)/6*6;A<=2*R;A+=6){auto s=e.go(A,A,3,h,4*h);if(s.x){roots++;if(!exact[s.x]||A<exact[s.x])exact[s.x]=A;if(s.g>=h)bigGain++;}auto f=e.go(A,A,3,h,B);if(f.x&&(!fixed[f.x]||A<fixed[f.x]))fixed[f.x]=A;}
 for(int x=R-B;x<=2*R;x+=2)if(exact[x]){sinks++;int q=min(e.sp[x-1],e.sp[x+1]),g=exact[x]-x;if(q*16<h){smallrough++;if(g>=h/2)active++;}if(g<h/4)gsmall++;}
 // previous height via sequence index
 int idx=find(heights.begin(),heights.end(),h)-heights.begin();if(idx){int a=heights[idx-1];for(int x=R-B;x<=2*R;x+=2){if(prev[x]){auto t=e.go(prev[x],x,a,h,B);if(t.x&&(!transfer[t.x]||prev[x]<transfer[t.x]))transfer[t.x]=prev[x];}if(practical[x]){pop++;auto t=e.go(practical[x],x,a,h,4*h);if(!t.x){fail++;continue;}if(t.minh<a/2)down++;if(fromPractical[t.x])merged++;if(!fromPractical[t.x]||practical[x]<fromPractical[t.x])fromPractical[t.x]=practical[x];}}assert(transfer==fixed);for(int x=R-B;x<=2*R;x+=2)if(fromPractical[x]){pcnt++;assert(exact[x]&&exact[x]<=fromPractical[x]);}assert(pop==fail+merged+pcnt);}
 cout<<R<<","<<h<<","<<roots<<","<<sinks<<","<<smallrough<<","<<active<<","<<gsmall<<","<<bigGain<<","<<pop<<","<<pcnt<<","<<fail<<","<<merged<<","<<down<<endl;prev.swap(fixed);if(!idx)practical=exact;else practical.swap(fromPractical);
 }}}
