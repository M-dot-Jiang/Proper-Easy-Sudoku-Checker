#include <bits/stdc++.h>
using namespace std;
using Mask = unsigned;

struct Unit { char type; int key; vector<int> cells; };
struct PatternData {
    vector<int> pos; // flattened row*9+col, sorted
};

static vector<vector<int>> rowSetRepresentatives(int r) {
    switch (r) {
      case 2: return {{0,1},{0,3}};
      case 3: return {{0,1,2},{0,1,3},{0,3,6}};
      case 4: return {{0,1,2,3},{0,1,3,4},{0,1,3,6}};
      case 5: return {{0,1,2,3,4},{0,1,2,3,6},{0,1,3,4,6}};
    }
    return {};
}

static void generatePatternsForTypes(int n, const vector<int>& rows, const vector<int>& cols,
                                     set<vector<int>>& output) {
    int nr=rows.size(), nc=cols.size();
    vector<int> colCount(nc,0), chosenMasks(nr,0);
    function<void(int,int)> rec = [&](int ri, int remain) {
        if (ri==nr) {
            if (remain!=0) return;
            for (int v:colCount) if (v<2) return;
            vector<int> pos;
            for (int i=0;i<nr;i++) for (int j=0;j<nc;j++) if (chosenMasks[i]>>j&1)
                pos.push_back(rows[i]*9+cols[j]);
            sort(pos.begin(),pos.end());
            int boxCount[9]={0};
            for (int p:pos) boxCount[(p/9/3)*3+(p%9)/3]++;
            for (int v:boxCount) if (v==1) return;
            output.insert(pos);
            return;
        }
        int future=nr-ri-1;
        for (int m=0;m<(1<<nc);m++) {
            int pc=__builtin_popcount((unsigned)m);
            if (pc<2 || pc>remain-2*future) continue;
            if (pc>remain) continue;
            bool possible=true;
            for (int j=0;j<nc;j++) {
                int v=colCount[j]+((m>>j)&1);
                // Every remaining row contributes at most one cell to this column.
                if (v + future < 2) { possible=false; break; }
            }
            if (!possible) continue;
            chosenMasks[ri]=m;
            for (int j=0;j<nc;j++) colCount[j]+=(m>>j)&1;
            rec(ri+1,remain-pc);
            for (int j=0;j<nc;j++) colCount[j]-=(m>>j)&1;
        }
    };
    rec(0,n);
}

struct Search {
    int n;
    vector<int> pos;
    vector<Unit> units;
    vector<array<int,3>> cellUnits;
    vector<vector<int>> conflicts;
    vector<int> order;
    vector<vector<int>> earlierConflicts;
    vector<int> colorByOrder, colorByCell;
    long long proper=0, stalled=0;
    bool uniqueFound=false;

    void build(const vector<int>& p) {
        pos=p; n=p.size(); units.clear();
        cellUnits.assign(n,{}); conflicts.assign(n,{});
        map<pair<char,int>,vector<int>> um;
        for (int i=0;i<n;i++) {
            int r=pos[i]/9,c=pos[i]%9;
            um[{'r',r}].push_back(i);
            um[{'c',c}].push_back(i);
            um[{'b',(r/3)*3+c/3}].push_back(i);
        }
        map<pair<char,int>,int> uid;
        for (auto &it:um) {
            uid[it.first]=units.size();
            units.push_back({it.first.first,it.first.second,it.second});
        }
        for (int i=0;i<n;i++) {
            int r=pos[i]/9,c=pos[i]%9;
            cellUnits[i]={(int)uid[{'r',r}],(int)uid[{'c',c}],(int)uid[{'b',(r/3)*3+c/3}]};
        }
        for (int i=0;i<n;i++) for (int j=0;j<n;j++) if (i!=j) {
            int r=pos[i]/9,c=pos[i]%9, rr=pos[j]/9,cc=pos[j]%9;
            if (r==rr || c==cc || (r/3==rr/3 && c/3==cc/3)) conflicts[i].push_back(j);
        }
        order.resize(n); iota(order.begin(),order.end(),0);
        sort(order.begin(),order.end(),[&](int a,int b){
            if (conflicts[a].size()!=conflicts[b].size()) return conflicts[a].size()>conflicts[b].size();
            return a<b;
        });
        earlierConflicts.assign(n,{});
        for (int k=0;k<n;k++) for (int j=0;j<k;j++) {
            int a=order[k], b=order[j];
            if (find(conflicts[a].begin(),conflicts[a].end(),b)!=conflicts[a].end()) earlierConflicts[k].push_back(j);
        }
        colorByOrder.assign(n,-1); colorByCell.assign(n,-1);
    }

    int countSolutions(const vector<int>& domains) {
        vector<int> ass(n,-1), used(units.size(),0);
        int solutions=0;
        function<void(int)> dfs = [&](int filled) {
            if (solutions>=2) return;
            if (filled==n) { solutions++; return; }
            int best=-1, bestMask=0, bestSize=99;
            for (int i=0;i<n;i++) if (ass[i]<0) {
                int mask=domains[i];
                for (int u:cellUnits[i]) mask &= ~used[u];
                int sz=__builtin_popcount((unsigned)mask);
                if (sz==0) return;
                if (sz<bestSize) { best=i;bestMask=mask;bestSize=sz; if (sz==1) break; }
            }
            for (int d=0;d<9;d++) if (bestMask>>d&1) {
                ass[best]=d;
                for (int u:cellUnits[best]) used[u]|=1<<d;
                dfs(filled+1);
                for (int u:cellUnits[best]) used[u]&=~(1<<d);
                ass[best]=-1;
                if (solutions>=2) return;
            }
        };
        dfs(0);
        return solutions;
    }

    bool checkCompletePartition() {
        proper++;
        fill(colorByCell.begin(),colorByCell.end(),-1);
        for (int k=0;k<n;k++) colorByCell[order[k]]=colorByOrder[k];
        vector<int> unitMask(units.size(),0);
        for (int u=0;u<(int)units.size();u++) for (int i:units[u].cells) unitMask[u]|=1<<colorByCell[i];
        vector<int> domains(n);
        for (int i=0;i<n;i++) {
            int d=unitMask[cellUnits[i][0]] & unitMask[cellUnits[i][1]] & unitMask[cellUnits[i][2]];
            if (__builtin_popcount((unsigned)d)<2) return false;
            domains[i]=d;
        }
        stalled++;
        if (countSolutions(domains)==1) {
            uniqueFound=true;
            cout << "Unique stalled local configuration found with "<<n<<" blanks.\nPattern (row,col zero-based): ";
            for(int p:pos) cout<<"("<<p/9<<","<<p%9<<") ";
            cout<<"\nDigit-equivalence labels by pattern order: ";
            for(int x:colorByCell) cout<<x<<" ";
            cout<<"\n";
            return true;
        }
        return false;
    }

    bool colorDfs(int idx, int maxLabel) {
        if (idx==n) return checkCompletePartition();
        int forbidden=0;
        for (int j:earlierConflicts[idx]) forbidden |= 1<<colorByOrder[j];
        int maxTry=min(maxLabel+1,8); // at most 9 distinct Sudoku digits
        for (int lab=0;lab<=maxTry;lab++) {
            if (forbidden>>lab&1) continue;
            if (lab==maxLabel+1 && maxLabel>=8) continue;
            colorByOrder[idx]=lab;
            if (colorDfs(idx+1,max(maxLabel,lab))) return true;
            colorByOrder[idx]=-1;
        }
        return false;
    }

    bool run(const vector<int>& p) { build(p); return colorDfs(0,-1); }
};

int main(int argc,char**argv) {
    int maxN=10;
    if (argc>1) maxN=atoi(argv[1]);
    for (int n=4;n<=maxN;n++) {
        set<vector<int>> patterns;
        int maxAffected=min(5,n/2);
        for (int nr=2;nr<=maxAffected;nr++) for (int nc=2;nc<=maxAffected;nc++) {
            for (auto rows:rowSetRepresentatives(nr)) for (auto cols:rowSetRepresentatives(nc))
                generatePatternsForTypes(n,rows,cols,patterns);
        }
        long long proper=0,stalled=0; bool found=false;
        for (const auto &p:patterns) {
            Search s;
            if (s.run(p)) { found=true; break; }
            proper+=s.proper; stalled+=s.stalled;
        }
        cout << "n="<<n<<" patterns="<<patterns.size()<<" proper_partitions="<<proper<<" stalled_partitions="<<stalled<<" unique_stalled="<<(found?1:0)<<"\n";
    }
}
