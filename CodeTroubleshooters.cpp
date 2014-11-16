#include<algorithm>
#include<cctype>
#include<cmath>
#include<cstdio>
#include<cstdlib>
#include<cstring>
#include<string>
#include<fstream>
#include<iomanip>
#include<iostream>
#include<map>
#include<stack>
#include<vector>
#include<deque>
#include<queue>
#include<bitset>
#include<set>
#define MAXN 100000
#define LOGMAXN 17
#define PI 3.1415926535
#define ERROR -1
#define EPS 1e-8
#define MatDimension 6
#define INF 100000
using namespace std;

int prime[3405];
bitset<31629> composite;

/***********************************************Miscellaneous*************************************************/

void MakePrimeList(){
    int k,len=0;
    composite[1]=1;
    for(int i=2;i<15813;i++)
        if(composite[i]==0){
            prime[len]=2*i-1;
            len++;
            for(int j=((2*i-1)*(2*i-1))/2+1;j<31624;j+=2*i-1)
                composite[j]=1;
        }
}

void MatrixMultiplication(int a[MatDimension][MatDimension],
                          int b[MatDimension][MatDimension],
                          int c[MatDimension][MatDimension]){
    int i,j,k;
    for(i=0;i<MatDimension;i++)
        for(j=0;j<MatDimension;j++){
            c[i][j]=0;
            for(k=0;k<MatDimension;k++)
                c[i][j]+=a[i][k]*b[k][j];
        }
}

/************************************************Data Structure***********************************************/

void PreProcessRMQ(int M[MAXN][LOGMAXN],int A[MAXN],int N){ //O(NlogN)
    int i,j;
    for(i=0;i<N;i++)
        M[i][0]=i;
    for(j=1;1<<j<=N;j++)
        for(i=0;i+(1<<j)-1<N;i++){
            if(A[M[i][j-1]]<A[M[i+(1<<(j-1))][j-1]])
                M[i][j]=M[i][j-1];
            else
                M[i][j]=M[i+(1<<(j-1))][j-1];
        }
}

int IndexOfRMQ(int M[MAXN][LOGMAXN],int A[MAXN],int i,int j){ //O(1)
    int k=log2(j-i+1);
    return A[M[i][k]]<A[M[j-1<<k+1][k]]?M[i][k]:M[j-1<<k+1][k];
}

int BuildSegmentTree(int node,int M[MAXN*2],A[MAXN]){ //RMQ
    if(node>=MAXN)
        M[node]=A[node-MAXN];
    else{
        BuildSegmentTree(2*node,int M[MAXN*2],A[MAXN])
        BuildSegmentTree(2*node+1,int M[MAXN*2],A[MAXN])
        M[node]=A[M[2*node]]<=A[M[2*node+1]]&&A[M[2*node]]!=ERROR?M[2*node]:M[2*node+1];
      }
}

int SearchSegmentTree(int node,int b,int e,int M[MAXN*2],int A[MAXN],int i,int j){ //RMQ
    int p1, p2;
    if(i>e||j<b)
        return ERROR;
    if(b>=i&&e<=j)
        return M[node];
    p1=SearchSegmentTree(2*node,b,(b+e)/2,M,A,i,j);
    p2=SearchSegmentTree(2*node+1,(b+e)/2+1,e,M,A,i,j);
    if(p1==ERROR)
        return M[node]=p2;
    if(p2==ERROR)
        return M[node]=p1;
    if(A[p1]<=A[p2])
        return M[node]=p1;
    return M[node]=p2;
}

void PreProcessLCA(int N,int T[MAXN],int P[MAXN][LOGMAXN]){ //O(NlogN)
    int i, j;
    for(i=0;i<N;i++)
        for(j=0;1<<j<N;j++)
            P[i][j]=ERROR;
    for(i=0;i<N;i++)
        P[i][0]=T[i];
    for(j=1;1<<j<N;j++)
        for(i=0;i<N;i++)
            if(P[i][j-1]!=ERROR)
                P[i][j]=P[P[i][j-1]][j-1];
}

int SearchLCA(int N,int P[MAXN][LOGMAXN],int T[MAXN],int L[MAXN],int p,int q){ //O(logN)
    int tmp,log,i;
    if(L[p]<L[q]){
        tmp=p;
        p=q;
        q=tmp;
    }
    log=log2(L[p]);
    for(i=log;i>=0;i--)
        if(L[p]-(1<<i)>=L[q])
            p=P[p][i];
    if(p==q)
        return p;
    for(i=log;i>=0;i--)
        if(P[p][i]!=ERROR&&P[p][i]!=P[q][i]){
            p=P[p][i];
            q=P[q][i];
        }
    return T[p];
}

/***************************************************Geometry**************************************************/

class Point{
public:
    double x,y;
    Point(double i=0,double j=0){x=i;y=j;}
    double Magnitude(){return sqrt(x*x+y*y);}
    double DistanceFrom(Point a){Point temp(this->x-a.x,this->y-a.y); return temp.Magnitude();}
    double DistanceFrom(Point a,Point b){
        Point temp1(b.x-a.x,b.y-a.y),temp2(this->x-a.x,this->y-a.y);
        if(a.x==b.x&&a.y==b.y) return temp2.Magnitude();
        return abs(temp1.x*temp2.y-temp1.y*temp2.x)/temp1.Magnitude();
    }
    Point Reflection(Point a,Point b){
        Point ans;
        double A1,B1,C1,A2,B2,C2,det;
        B1=b.y-a.y;A1=b.x-a.x;C1=A1*this->x+B1*this->y;
        A2=b.y-a.y;B2=a.x-b.x;C2=A2*a.x+B2*a.y;
        det=A1*B2-A2*B1;
        if(abs(det)<EPS)
            ans.x=ans.y=ERROR;
        else{
            ans.x=(B2*C1-B1*C2)/det;
            ans.y=(A1*C2-A2*C1)/det;
            ans.x=2*ans.x-this->x;
            ans.y=2*ans.y-this->y;
        }
        return ans;
    }
};

bool XYasscending(Point a,Point b){
    if(a.x==b.x) return a.y<b.y;
    return a.x<b.x;
}

double PAngle(Point a,Point b,Point c){
    Point temp1(a.x-b.x,a.y-b.y),temp2(c.x-b.x,c.y-b.y);
    double ans=asin((temp1.x*temp2.y-temp1.y*temp2.x)/(temp1.Magnitude()*temp2.Magnitude()));
    if((ans<0&&(temp1.x*temp2.x+temp1.y*temp2.y)<0)||(ans>=0&&(temp1.x*temp2.x+temp1.y*temp2.y)<0))
        ans=PI-ans;
    ans=ans<0?2*PI+ans:ans;
    return ans;
}

double SignedArea(Point a,Point b,Point c){
    Point temp1(b.x-a.x,b.y-a.y),temp2(c.x-a.x,c.y-a.y);
    return 0.5*(temp1.x*temp2.y-temp1.y*temp2.x);
}

void RectangleIntersect(Point a1,Point a2,Point b1,Point b2,Point &c1,Point &c2){
    c1.x=max(a1.x,b1.x); c1.y=max(a1.y,b1.y);
    c2.x=min(a2.x,b2.x); c2.y=min(a2.y,b2.y);
    if(c1.x>c2.x||c1.y>c2.y)
        c1.x=c1.y=c2.x=c2.y=ERROR;
}

Point LineIntersect(Point a,Point b,Point c,Point d){
    Point ans;
    double A1,B1,C1,A2,B2,C2,det;
    A1=b.y-a.y;B1=a.x-b.x;C1=A1*a.x+B1*a.y;
    A2=d.y-c.y;B2=c.x-d.x;C2=A2*c.x+B2*c.y;
    det=A1*B2-A2*B1;
    if(abs(det)<EPS)
        ans.x=ans.y=ERROR;
    else{
        ans.x=(B2*C1-B1*C2)/det;
        ans.y=(A1*C2-A2*C1)/det;
    }
    return ans;
}

Point Circumcenter(Point a,Point b,Point c){
    Point ans;
    double A1,B1,C1,A2,B2,C2,det;
    B1=b.y-a.y;A1=b.x-a.x;C1=A1*(a.x+b.x)/2+B1*(a.y+b.y)/2;
    B2=b.y-c.y;A2=b.x-c.x;C2=A2*(c.x+b.x)/2+B2*(c.y+b.y)/2;
    det=A1*B2-A2*B1;
    if(abs(det)<EPS)
        ans.x=ans.y=ERROR;
    else{
        ans.x=(B2*C1-B1*C2)/det;
        ans.y=(A1*C2-A2*C1)/det;
    }
    return ans;
}

void MakeConvexHull(vector<Point>given,vector<Point>&ans){
    int i,n=given.size(),j=0,k=0;
    vector<Point>U,L;
    ans.clear();
    sort(given.begin(),given.end(),XYasscending);
    for(i=0;i<n;i++){
        while(1){
            if(j<2) break;
            if(SignedArea(L[j-2],L[j-1],given[i])<=0) j--;
            else break;
        }
        if(j==L.size()){
            L.push_back(given[i]);
            j++;
        }
        else{
            L[j]=given[i];
            j++;
        }
    }
    for(i=n-1;i>=0;i--){
        while(1){
            if(k<2) break;
            if(SignedArea(U[k-2],U[k-1],given[i])<=0) k--;
            else break;
        }
        if(k==U.size()){
            U.push_back(given[i]);
            k++;
        }
        else{
            U[k]=given[i];
            k++;
        }
    }
    for(i=0;i<j-1;i++) ans.push_back(L[i]);
    for(i=0;i<k-1;i++) ans.push_back(U[i]);
}

/***************************************************Graph*****************************************************/

class PQNode{
public:
    int id,cost,parent;
    PQNode(int a,int b,int c){id=a;cost=b;parent=c;}
    bool operator<(const PQNode &a)const { //Defined in reversed order for priority queue
        return this->cost>a.cost;
    }
};

void Dijkstra(int cost[MatDimension][MatDimension],vector<int>adjacent[MAXN],int source,int ans[MatDimension],int parent[MatDimension]){
    int i,top,len;
    bool dequed[MatDimension];
    priority_queue<PQNode> pq;
    for(i=0;i<MatDimension;i++){
        ans[i]=INF;
        dequed[i]=false;
    }
    ans[source]=0;
    parent[source]=-1;
    pq.push(PQNode(source,0,-1));
    while(!pq.empty()){
        top=pq.top().id;
        len=adjacent[top].size();
        for(i=0;i<len;i++)
            if(ans[adjacent[top][i]]>cost[top][adjacent[top][i]]+ans[top]&&!dequed[adjacent[top][i]]){
                ans[adjacent[top][i]]=cost[top][adjacent[top][i]]+ans[top];
                parent[adjacent[top][i]]=top;
                pq.push(PQNode(i,ans[i],parent[i]));
            }
        pq.pop();
        dequed[top]=true;
    }
}

int main(){
    return 0;
}
