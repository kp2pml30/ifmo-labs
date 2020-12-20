#include <vector>
#include <map>
#include <iostream>
#include <set>
#include <sstream>
#include <fstream>
#include <string>
#include <algorithm>
#include <list>
using uint = unsigned int;
using ull = unsigned long long;
 
#ifndef MBUF
auto cin = std::fstream("nextsetpartition.in", std::ios_base::in);
auto cout = std::fstream("nextsetpartition.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(5 2
1 2 3
4 5
 
5 2
1 3 5
2 4
 
5 1
1 2 3 4 5
 
5 5
1
2
3
4
5
 
0 0
 
)delim");
using std::cout;
#endif
 
using ull = unsigned long long;
 
#include <ctime>
 
int getind(int cur, const std::vector<int> &used)
{
  int resi = -1, best = 5000000;
  for (int pex = 0; pex < used.size(); pex++)
    if (used[pex] > cur && used[pex] < best)
      resi = pex, best = used[pex];
  return resi;
}
 
void next(std::vector<std::vector<int>> &v, int n)
{
  std::vector<int> used;
  for (int i = v.size() - 1; i >= 0; i--)
  {
    if (int tmp = getind(v[i].back(), used); tmp != -1)
    {
      v[i].push_back(used[tmp]);
      std::swap(used.back(), used[tmp]);
      used.pop_back();
      break;
    }
    for (int j = v[i].size() - 1; j > 0; j--)
    {
      if (int resi = getind(v[i][j], used); resi != -1)
      {
        std::swap(v[i][j], used[resi]);
        goto CYCLE_END;
      }
      used.push_back(v[i][j]);
      v[i].erase(v[i].begin() + j);
    }
    if (v[i].size())
    {
      used.push_back(v[i][0]);
      v[i].erase(v[i].begin() + 0);
    }
  }
  CYCLE_END:
  for (int i = 0; i < v.size();)
    if (v[i].size() == 0)
      v.erase(v.begin() + i);
    else
      i++;
  cout << n << ' ' << v.size() + used.size() << '\n';
  for (auto &s : v)
  {
    for (auto &e : s)
      cout << e << ' ';
    cout << '\n';
  }
  std::sort(used.begin(), used.end());
  for (auto &a : used)
    cout << a << '\n';
  cout << '\n';
}
 
int main(void)
{
  std::vector<std::vector<int>> v(0);
  while (!cin.eof())
  {
    int n, k;
    cin >> n >> k;
    if (n == 0 && k == 0)
      break;
    v.clear();
    char trash[10];
    cin.getline(trash, 10);
    for (int i = 0; i < k; i++)
    {
      char buf[1000000];
      cin.getline(buf, 1000000);
      std::stringstream k(buf);
      v.push_back(std::vector<int>());
      while (!k.eof())
      {
        int p;
        k >> p;
        v.back().push_back(p);
      }
    }
    /*
      if (k == 1)
      {
        cout << n << ' ' << n << '\n';
        for (int i = 1; i <= n; i++)
          cout << i << '\n';
        cout << '\n';
      }
      else
    */
      next(v, n);
  }
  return 0;
}