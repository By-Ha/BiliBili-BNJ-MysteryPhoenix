/* ---- 
# MysteryPhoenix
# By: By_Ha
---- */

#include <cstdio>
#include <iostream>
#include <cmath>
#include <queue>
#include <map>
#include <ctime>

using namespace std;

const int N = 4;
typedef unsigned long long ull;
#define Rint register int
struct Graph{
    short dat[N+1][N+1];
    Graph(){};
    Graph(bool ans){
        for(int i=1;i<=N;++i)
            for(int j=1;j<=N;++j)
                dat[i][j] = ~-i*N+j;

        dat[N][N] = 0;
    }
    inline bool operator < (Graph b)const{
        for(Rint i = 1;i<=N;++i)
            for(Rint j = 1;j<=N;++j){
                if(dat[i][j] == b.dat[i][j]) continue;
                return dat[i][j] < b.dat[i][j];
            }

        return false;
    }
}beginGraph;
Graph ans(true),ans2;
struct Position{
    int a,b,step;
    short db[100][2];
    Graph data;
    inline bool operator < (Position b)const{
        return step<b.step;
    }
}beginPosition;

typedef pair<int,Position> pip;
priority_queue < pair<int,Position> > q;
// map <Graph,bool> vis;
map <Graph,int> vis;
map <Graph,int> vis2;
int h(Graph a){
    int ret=0;
    for(Rint i=1;i<=N;++i)
        for(Rint j=1;j<=N;++j){
            if(a.dat[i][j]==0) {
                continue;
            }
            int t = a.dat[i][j];
            ret += abs(i-1-(~-t)/N) + abs(j-1-(~-t)%N);
        }

    return ret;
}
int plca[N*N+1],plcb[N*N+1];
int h2(Graph a){
    int ret=0;
    for(Rint i=1;i<=N;++i)
        for(Rint j=1;j<=N;++j){
            if(a.dat[i][j]==0) continue;
            int t = a.dat[i][j];
            ret += abs(plca[a.dat[i][j]]-i) + abs(plcb[a.dat[i][j]]-j);
        }

    return ret;
}


int nxt[4][2] = {0,1,0,-1,1,0,-1,0};

bool safe(int gx,int gy){
    return (gx<=4 && gy<=4 && gx>=1 && gy >= 1);
}
int M = 0;
int A(){
    while(!q.empty()){
        cout << (M = max(M,q.top().second.step)) << ' ' << q.size() << endl;
        Position tmp2 = q.top().second;
        Position tmp = tmp2;
        if(!(tmp.data < ans) && !(ans < tmp.data)){
            for(int i = 0;i<=tmp.step;++i)
                cout << tmp.db[i][0] << ' ' << tmp.db[i][1] << '\n';
            return tmp.step;
        }
        q.pop();
        for(Rint i = 0;i<4;++i){
            tmp = tmp2;
            int nxtx = tmp.a+nxt[i][0];
            int nxty = tmp.b+nxt[i][1];
            if(!safe(nxtx,nxty)) continue;
            swap(tmp.data.dat[tmp.a][tmp.b],tmp.data.dat[nxtx][nxty]);
            if(vis[tmp.data]) continue;
            vis[tmp.data] = 1;
            tmp.step++;tmp.a=nxtx;tmp.b=nxty;
            tmp.db[tmp.step][0] = tmp.a;
            tmp.db[tmp.step][1] = tmp.b;
            q.push(pip(-tmp.step-h(tmp.data),tmp));
        }
    }
}

Position idaPosition,idaPosition2;
int limit;

int IDA(){
    if(idaPosition.step>limit) return -1;
    if(h(idaPosition.data) == 0){
        for(int i = 0;i<=idaPosition.step;++i)
            cout << idaPosition.db[i][0] << ' ' << idaPosition.db[i][1] << endl;
        return idaPosition.step;
    }
    int nowx = idaPosition.a;
    int nowy = idaPosition.b;
    for(Rint i = 0;i<4;++i){
        int nxtx = idaPosition.a+nxt[i][0];
        int nxty = idaPosition.b+nxt[i][1];
        if(!safe(nxtx,nxty)) continue;
        swap(idaPosition.data.dat[nowx][nowy],idaPosition.data.dat[nxtx][nxty]);
        auto it = &vis[idaPosition.data];
        if(*it == 0) *it = 0x3f3f3f3f;
        if(*it<idaPosition.step+1){
            swap(idaPosition.data.dat[nowx][nowy],idaPosition.data.dat[nxtx][nxty]);
            continue;
        }
        *it = idaPosition.step+1;
        //if(vis2[idaPosition.data]!=0){
        //    cout << vis[idaPosition.data] + idaPosition.step + 1;
        //    exit(0); return 0;
        //}
        //if(vis[idaPosition.data] == 0) vis[idaPosition.data] = 0x3f3f3f3f;
        //if(vis[idaPosition.data]<=idaPosition.step+1) continue;
        //vis[idaPosition.data] = idaPosition.step+1;
        idaPosition.step++;idaPosition.a=nxtx;idaPosition.b=nxty;
        idaPosition.db[idaPosition.step][0] = idaPosition.a;
        idaPosition.db[idaPosition.step][1] = idaPosition.b;
        if(h(idaPosition.data) + idaPosition.step <= limit){
            int t = IDA();
            if(t!=-1) return t;
        }
        idaPosition.step--;idaPosition.a=nowx;idaPosition.b=nowy;
        swap(idaPosition.data.dat[nowx][nowy],idaPosition.data.dat[nxtx][nxty]);
    }
    return -1;
}

int IDA2(){
    if(idaPosition2.step>limit) return -1;
    if(h2(idaPosition2.data) == 0)
        return idaPosition2.step;
    int nowx = idaPosition2.a;
    int nowy = idaPosition2.b;
    for(Rint i = 0;i<4;++i){
        int nxtx = idaPosition2.a+nxt[i][0];
        int nxty = idaPosition2.b+nxt[i][1];
        if(!safe(nxtx,nxty)) continue;
        swap(idaPosition2.data.dat[nowx][nowy],idaPosition2.data.dat[nxtx][nxty]);
        auto it = &vis2[idaPosition2.data];
        if(*it == 0) *it = 0x3f3f3f3f;
        if(*it<idaPosition2.step+1){
            swap(idaPosition2.data.dat[nowx][nowy],idaPosition2.data.dat[nxtx][nxty]);
            continue;
        }
        *it = idaPosition2.step+1;
        if(vis[idaPosition2.data]!=0){
            cout << vis[idaPosition2.data] + idaPosition2.step + 1;
            exit(0);
        }
        //if(vis[idaPosition.data] == 0) vis[idaPosition.data] = 0x3f3f3f3f;
        //if(vis[idaPosition.data]<=idaPosition.step+1) continue;
        //vis[idaPosition.data] = idaPosition.step+1;
        idaPosition2.step++;idaPosition2.a=nxtx;idaPosition2.b=nxty;
        idaPosition2.db[idaPosition2.step][0] = idaPosition2.a;
        idaPosition2.db[idaPosition2.step][1] = idaPosition2.b;
        if(h2(idaPosition2.data) + idaPosition2.step <= limit){
            int t = IDA2();
            if(t!=-1) return t;
        }
        idaPosition2.step--;idaPosition2.a=nowx;idaPosition2.b=nowy;
        swap(idaPosition2.data.dat[nowx][nowy],idaPosition2.data.dat[nxtx][nxty]);
    }
    return -1;
}

int main(){
    // freopen("input.txt","r",stdin);
    // freopen("output.txt","w",stdout);
    //input
    for(Rint i=1;i<=N;++i)
        for(Rint j=1;j<=N;++j)
            cin >> beginGraph.dat[i][j];

    //find empty place
    for(Rint i=1;i<=N;++i)
        for(Rint j=1;j<=N;++j)
            plca[beginGraph.dat[i][j]] = i,plcb[beginGraph.dat[i][j]] = j;


    beginPosition.a=plca[0],beginPosition.b=plcb[0];


    //begin algo a

    // beginPosition.step = 0;
    // beginPosition.data = beginGraph;
    // beginPosition.db[beginPosition.step][0] = beginPosition.a;
    // beginPosition.db[beginPosition.step][1] = beginPosition.b;
    // q.push(pip(-h(beginGraph),beginPosition));
    // vis[beginGraph] = 1;
    // cout << "Steps:" << A() << '\n';
    // cout << "Time:" << clock();

    //end algo a


    // begin algo ida

    beginPosition.step = 0;
    beginPosition.data = beginGraph;
    beginPosition.db[beginPosition.step][0] = beginPosition.a;
    beginPosition.db[beginPosition.step][1] = beginPosition.b;
    idaPosition = beginPosition;
    idaPosition2.data = ans;
    idaPosition2.a = N;
    idaPosition2.b = N;
    ans2 = beginGraph;
    while(true){
        if((IDA()!=-1)){
            cout << limit;
            break;
        }
        // IDA2();
        limit++;
        cout << limit << ' ' << clock() << endl;
    }

    //end algo ida
    return 0;
}
