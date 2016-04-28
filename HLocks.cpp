#include<iostream>
#include<vector>
#include<utility>
#include<fstream>
#include<set>
#include<algorithm>
#include<queue>
#include<map>
using namespace std;

vector<int> *graph, *invGraph;
pair<int,int> *interval;
// int* dominatorTree;
bool *active, *explored, *parentUpdated;
int ncount;
int lockCost = 3;
int* levels;
int maxLevel = 0;
vector<pair<int, int> > *levelWiseIntervals;
map< pair<int, int> , vector<pair<int, int> > > intervalTree;
map< pair<int, int> , pair<int, int> > inverseIntervalTree;
pair<int, int>* correspondingInterval;
map< pair<int, int> , int> levelMap;

void updateParent(int parent, int node) {
    if(parent == -1)
       return;
    if((interval[parent].first == -1) and (interval[parent].second == -1)) {
        interval[parent].first = interval[node].first;
        interval[parent].second = interval[node].second;
    }
    else {
        if(interval[parent].first > interval[node].first)
            interval[parent].first = interval[parent].first;
        if(interval[parent].second < interval[node].second)
            interval[parent].second = interval[node].second;
    }
    if(parentUpdated[parent] == true) {
        for(vector<int>::iterator it = invGraph[parent].begin(); it != invGraph[parent].end(); ++it)
            updateParent(*it, parent);
    }
}

void constructIntervals(int root) {
    if(!explored[root]) {
        if((graph[root].size() == 0) or active[root]) {
            ncount++;
            interval[root].first = ncount;
            interval[root].second = ncount;
        }
        else {
            active[root] = true;
            for(vector<int>::iterator it = graph[root].begin(); it != graph[root].end(); ++it)
                constructIntervals(*it);
        }
        explored[root] = true;
        active[root] = false;
    }
    for(vector<int>::iterator it = invGraph[root].begin(); it != invGraph[root].end(); ++it)
        updateParent(*it, root);
    parentUpdated[root] = true;
}

bool intersecting(pair<int,int> a, pair<int,int> b) {
    if((a.second < b.first) or (b.second < a.first))
        return false;
    return true;
}

bool compare(const pair<int, int>&i, const pair<int, int>&j)
{
    return i.first < j.first;
}

int mergeCompare(pair<int, int> i, pair<int, int> j)
{
    if (i.first < j.first) {
        if (i.second < j.first)
            return -1;
    }
    else if(i.first > j.first) {
        if (j.second < i.first)
            return 1;
    }
    return 0;
}

vector<pair<int,int> > vectorMerge(vector<pair<int,int> > list) {
    vector<pair<int,int> > mergedList;
    mergedList.push_back(list[0]);
    for(int i = 1; i < list.size(); i++) {
        if (intersecting(mergedList.back(), list[i])) {
            pair<int,int> p = mergedList.back();
            mergedList.pop_back();
            mergedList.push_back(make_pair(p.first, list[i].second));
        }
        else {
            mergedList.push_back(list[i]);
        }
    }
    return mergedList;
}

int mergeCost(pair<int, int> start, pair<int, int> end) {
    return (end.first - start.second) - 3;
}

pair<int, int> mergePair(pair<int, int> start, pair<int, int> end) {
    return make_pair(start.first, end.second);
}

vector<pair<int, int> > generateIntervals(vector<pair<int,int> > list) {
    vector<pair<int,int> > mergedList;
    mergedList.push_back(list[0]);
    for(int i = 1; i < list.size()-1; i++) {
        if(mergeCost(mergedList.back(), list[i]) < mergeCost(list[i], list[i+1]) and mergeCost(mergedList.back(), list[i]) < 0) {
            pair<int,int> p = mergedList.back();
            mergedList.pop_back();
            mergedList.push_back(mergePair(p, list[i]));
        }
        else {
            if(mergeCost(mergedList.back(), list[i]) > mergeCost(list[i], list[i+1]) and mergeCost(list[i], list[i+1]) < 0) {
                mergedList.push_back(mergePair(list[i], list[i+1]));
                i++;
            }
            else {
                mergedList.push_back(list[i]);
            }
        } 
    }
    if(mergeCost(mergedList.back(), list[list.size() - 1]) < 0) {
        pair<int,int> p = mergedList.back();
        mergedList.pop_back();
        mergedList.push_back(mergePair(p, list[list.size()-1]));
    }
    else {
        mergedList.push_back(list[list.size()-1]);
    }
    return mergedList;
}

vector<pair<int,int> > lockRange(vector<pair<int,int> > list, vector<pair<int,int> > range) {
    vector<pair<int, int> > mergedList;
    int count1=0,count2=0;
    while(count1 < list.size() or count2 < range.size()) {
        if(count1 == list.size()) {
            mergedList.push_back(range[count2++]);
            continue;
        }
        if(count2 == range.size()) {
            mergedList.push_back(list[count1++]);
            continue;
        }
        if(mergeCompare(list[count1], range[count2]) == 1) {
            mergedList.push_back(range[count2++]);
            continue;
        }
        else if(mergeCompare(list[count1], range[count2]) == -1) {
            mergedList.push_back(list[count1++]);
            continue;
        }
        return range;
    }
    return mergedList;
}

vector<pair<int,int> > lockRemove(vector<pair<int,int> > list, vector<pair<int,int> > range) {
    vector<pair<int, int> > mergedList;
    int count1 = 0, count2 = 0;
    while( count1 < list.size() and count2 < range.size()) {
        if(list[count1].first == range[count2].first and list[count1].second == range[count2].second) {
            count1++;
            count2++;
        }
        else {
            mergedList.push_back(range[count2]);
            count2++;
        }
    }
    if(count1 == list.size()) {
        return mergedList;
    }
    return range;
}

void constructLevels(queue<int> q) {
    if(q.size() == 0) {
        return;
    }
    else {
        int t = q.front();
        for(int i = 0; i < graph[t].size(); i++) {
            if(levels[graph[t][i]] == -1) {
                levels[graph[t][i]] = levels[t]+1;
                q.push(graph[t][i]);
                if(maxLevel < levels[t]+1) {
                    maxLevel = levels[t]+1;
                }
            }
        }
        q.pop();
        constructLevels(q);
    }
}

bool subsume(pair<int, int> itvl1, pair<int, int> itvl2) {
    return itvl1.first >= itvl2.first and itvl1.second <= itvl2.second;
}

pair<int, int> getBestMatch(pair<int, int> itvl, pair<int, int> itvl2) {
    for(int i = 0; i < intervalTree[itvl2].size(); i++) {
        if(subsume(itvl, intervalTree[itvl2][i]))
            return getBestMatch(itvl, intervalTree[itvl2][i]);
    }
    return itvl2;
}

double getCost(vector<pair<int, int> > intervals) {
    double cost = 0;
    for(vector<pair<int, int> >::iterator it = intervals.begin(); it != intervals.end(); ++it) {
        cout << "(" <<(*it).first <<","<<(*it).second<<")";
    }
    cout << endl;
    for(vector<pair<int, int> >::iterator it = intervals.begin(); it != intervals.end(); ++it) {
        cost += 0.3*((*it).second - (*it).first + 1);
    }
    cost += 0.7*intervals.size();
    return cost;
}

int main(int argc, char* argv[]) {
    ifstream fp;
    fp.open(argv[1]);
    int nodes, edges;
    fp >> nodes >> edges;
    int edgeSrc, edgesDst;
    graph = new vector<int>[nodes];
    invGraph = new vector<int>[nodes];
    interval = new pair<int,int>[nodes];
    active = new bool[nodes];
    explored = new bool[nodes];
    parentUpdated = new bool[nodes];
    levels = new int[nodes];
    vector<pair<int,int> > lockList;
    
    for(int i = 0; i < edges; i++) {
        fp >> edgeSrc >> edgesDst;
        graph[edgeSrc].push_back(edgesDst);
        invGraph[edgesDst].push_back(edgeSrc);
    }
    fp.close();
    for(int i = 0; i < nodes; i++) {
        interval[i] = make_pair(-1,-1);
        levels[i] = -1;
    }
    constructIntervals(0);
    queue<int> q;
    q.push(0);
    levels[0] = 0;
    constructLevels(q);
    levelWiseIntervals = new vector<pair<int, int> >[maxLevel+1];
    for(int i = 0; i < nodes; i++) {
        levelWiseIntervals[levels[i]].push_back(interval[i]);
    }
    for(int i = 0; i <= maxLevel; i++) {
        sort(levelWiseIntervals[i].begin(), levelWiseIntervals[i].end(), compare);
        levelWiseIntervals[i] = vectorMerge(levelWiseIntervals[i]);
        for(int it = 0; it < levelWiseIntervals[i].size(); it++) {
            levelMap[levelWiseIntervals[i][it]] = i;
        }
    }
    for(int i = 0; i < maxLevel; i++) {
        int kprev = -1;
        for(int j = 0; j < levelWiseIntervals[i].size(); j++) {
            for(int k = kprev+1; k < levelWiseIntervals[i+1].size(); k++) {
                if(intersecting(levelWiseIntervals[i][j], levelWiseIntervals[i+1][k])) {
                    if(!(levelWiseIntervals[i][j].first == levelWiseIntervals[i+1][k].first and levelWiseIntervals[i][j].second == levelWiseIntervals[i+1][k].second)) {
                    intervalTree[levelWiseIntervals[i][j]].push_back(levelWiseIntervals[i+1][k]);
                    inverseIntervalTree[levelWiseIntervals[i+1][k]] = levelWiseIntervals[i][j];
                    }
                    kprev = k;
                }
                else
                    break;
            }
        }
    }
    correspondingInterval = new pair<int, int> [nodes];
    for(int i = 0; i < nodes; i++) {
        correspondingInterval[i] = getBestMatch(interval[i], interval[0]);
    }
//     inverseIntervalTree[interval[0]] = NULL;
    while (true) {
        string s;
        int node,numnodes;
        cin >> s ;
        if(s == "halt")
            break;
        else cin >> numnodes;
        if ( s == "lock" ) {
            int temp;
            set<pair<int, int> > list;
            vector<pair<int, int> > lockIntervals;
            for(int i = 0; i < numnodes; i++) {
                cin >> temp;
                list.insert(correspondingInterval[temp]);
            }
            vector<vector<pair<int, int> > > pathList;
            vector< pair<int, int> >* IntervalLevels = new vector< pair<int, int> > [maxLevel+1];
            for(set<pair<int, int> >::iterator it = list.begin(); it != list.end(); ++it) {
                vector<pair<int, int> > v;
                pair<int, int> itvl = *it;
                lockIntervals.push_back(*it);
                while(!(itvl.first == interval[0].first and itvl.second == interval[0].second)) {
                    v.push_back(itvl);
                    itvl = inverseIntervalTree[itvl];
                    IntervalLevels[levelMap[itvl]].push_back(itvl);
                }
                v.push_back(interval[0]);
                pathList.push_back(v);
            }
            double currentCost = getCost(lockIntervals);
            for(int i = maxLevel; i >= 0; i--) {
                for(vector< pair<int, int> >::iterator it = IntervalLevels[i].begin(); it != IntervalLevels[i].end(); ++it) {
                    vector<pair<int, int> > tempList;
                    tempList.push_back(*it);
                    for(int l = 0; l <= lockIntervals.size(); l++) {
                        if(!subsume(lockIntervals[i], *it)) {
                            tempList.push_back(lockIntervals[i]);
                        }
                    }
                    if(getCost(tempList) < currentCost) {
                        currentCost = getCost(tempList);
                        lockIntervals = tempList;
                    }
                }
            }
            for(vector<pair<int, int> >::iterator it = lockIntervals.begin(); it != lockIntervals.end(); ++it) {
                cout << "("<<(*it).first<<","<<(*it).second<<"),";
            }
            cout << endl;
        }
        if ( s == "unlock" ) {
            int temp;
            vector<pair<int, int> > list;
            for(int i = 0; i < numnodes; i++) {
                cin >> temp;
                list.push_back(interval[temp]);
            }
            sort(list.begin(), list.end(), compare);
            list = vectorMerge(list);
            list = generateIntervals(list);
            int prevSize = lockList.size();
            lockList = lockRemove(list, lockList);
            if(prevSize > lockList.size())
                cout << "Unlock was successful" << endl;
            else
                cout << "Unlock was unsuccessful" << endl;
        }
    }
    return 0;
}
