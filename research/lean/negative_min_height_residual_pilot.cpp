#include <algorithm>
#include <cmath>
#include <iostream>
#include <iomanip>
#include <vector>
#include <numeric>
#include <cassert>
using namespace std;
int mod(long long a,int b){int r=a%b;return r<0?r+b:r;}
struct Result{double sinks=0,trial=0,common=0,defect=0,weighted=0;long long trueSites=0,trialSites=0,commonSites=0,changed=0,changedOccupied=0;};
int main(){cout<<setprecision(10);cout<<"R,H,z,true_mass,trial_mass,common_mass,raw_defect,all_weighted_defect,true_sites,trial_sites,common_sites,changed_states,changed_occupied,weighted_lower,last_defect,clamped_lower\n"; for(int R:{12000,48000,192000,768000}){
 int H=(int)pow(R,.4),lo=R-4*H,hi=2*R,rows=(hi-lo)/2+1,S=H+1,ring=H+3;
 vector<int> sp(hi+2);for(int p=2;p<=hi+1;p++)if(!sp[p]){sp[p]=p;if((long long)p*p<=hi+1)for(int j=p*p;j<=hi+1;j+=p)if(!sp[j])sp[j]=p;}
 vector<int> zs={7,(int)sqrt(H), (int)pow(H,.75),H/2,H,2*H+3};sort(zs.begin(),zs.end());zs.erase(unique(zs.begin(),zs.end()),zs.end());
 vector<double> weights(H+2);for(int j=0;j<=H+1;j++)weights[j]=exp(-log(log((double)R))*2*j/H);
 auto fillWinner=[&](int x,vector<int>& win){fill(win.begin(),win.end(),0);for(int s:{-1,1})for(int v=x+s;v>1;){int p=sp[v];while(v%p==0)v/=p;if(p>2*H+3)continue;int h0=mod((s==1?0:p+2)+x/2-1,2*p);for(int h=h0;h<H;h+=2*p)if(!win[h]||p<win[h])win[h]=p;}};
 for(int z:zs){Result a;vector<double>C(ring*S),F(ring*S),G(ring*S);vector<float> changedMass((size_t)rows*S);vector<int>win(S);vector<double> fs(rows),gs(rows),debt(rows);
  for(int i=rows-1;i>=0;i--){int x=lo+2*i;fillWinner(x,win);int row=i%ring*S;for(int h=0;h<=H;h++){
    int k=row+h;double c=min(1.,C[k]+(x>=R&&x%6==0&&h==3)),f=min(1.,F[k]+(x>=R&&x%6==0&&h==3)),g=min(1.,G[k]+(x>=R&&x%6==0&&h==3));C[k]=F[k]=G[k]=0;
    if(h==H){a.sinks+=c;a.trial+=f;a.common+=g;a.trueSites+=c>0;a.trialSites+=f>0;a.commonSites+=g>0;fs[i]=f;gs[i]=g;assert(g<=c+1e-9&&g<=f+1e-9);continue;}
    int p=win[h],d=p?(p-1)/2:0,hn=h+1-d;assert(hn>=0&&d<ring);int dt=p&&p<=z?d:0,ht=h+1-dt;bool diff=d!=dt;
    if(diff){a.changed++;if(f>0){a.changedOccupied++;a.defect+=f;changedMass[(size_t)i*S+h]=nextafterf((float)f,INFINITY);}}
    if(i>=d&&hn>=0){int j=(i-d)%ring*S+hn;C[j]+=weights[d]*c;if(!diff)G[j]+=weights[d]*g;}
    if(i>=dt&&ht>=0)F[(i-dt)%ring*S+ht]+=weights[dt]*f;
  }}
  vector<double>D(ring*S);vector<int>sink(ring*S,-1);vector<unsigned char>clean(ring*S);double last=0,clamped=0;
  for(int i=0;i<rows;i++){int x=lo+2*i;fillWinner(x,win);int row=i%ring*S;for(int h=H;h>=0;h--){int k=row+h;if(h==H){D[k]=1;sink[k]=i;clean[k]=1;continue;}int p=win[h],d=p&&p<=z?(p-1)/2:0,hn=h+1-d;bool diff=p>z;
   if(i>=d&&hn>=0){int j=(i-d)%ring*S+hn;D[k]=weights[d]*D[j];sink[k]=sink[j];if(diff&&clean[j]&&sink[k]>=0){double v=changedMass[(size_t)i*S+h]*D[k];last+=v;debt[sink[k]]+=v;}clean[k]=!diff&&clean[j];}
   else{D[k]=0;sink[k]=-1;clean[k]=0;}a.weighted+=changedMass[(size_t)i*S+h]*D[k];}}
  for(int i=0;i<rows;i++){assert(fs[i]-gs[i]<=debt[i]+1e-8);clamped+=max(0.,fs[i]-debt[i]);}assert(clamped<=a.common+1e-6);
  cout<<R<<","<<H<<","<<z<<","<<a.sinks<<","<<a.trial<<","<<a.common<<","<<a.defect<<","<<a.weighted<<","<<a.trueSites<<","<<a.trialSites<<","<<a.commonSites<<","<<a.changed<<","<<a.changedOccupied<<","<<a.trial-a.weighted<<","<<last<<","<<clamped<<endl;
 }
}}
