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
auto cin = std::fstream("part2sets.in", std::ios_base::in);
auto cout = std::fstream("part2sets.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(
10 2
)delim");
using std::cout;
#endif
 
using ull = unsigned long long;
 
bool operator<(const std::vector<int> &l, const std::vector<int> &r)
{
  if (l.size() < r.size())
    return true;
  if (l.size() > r.size())
    return false;
  for (int i = 0; i < l.size(); i++)
    if (l[i] > r[i])
      return false;
  return true;
}
 
bool operator<(const std::vector<std::vector<int>> &l, const std::vector<std::vector<int>> &r)
{
  if (l.size() < r.size())
    return true;
  if (l.size() > r.size())
    return false;
  for (int i = 0; i < l.size(); i++)
    if (l[i] > r[i])
      return false;
  return true;
}
 
std::set<std::vector<std::vector<int>>> ohmy;
 
std::vector<std::vector<int>> finalize(const std::vector<std::vector<int>> &i)
{
  std::vector<std::vector<int>> ret = i;
  for (auto &a : ret)
    std::reverse(a.begin(), a.end());
  std::sort(ret.begin(), ret.end());
  return ret;
}
 
void gen(std::vector<std::vector<int>> &sub, int n, int k)
{
  int cnt = 0;
  for (auto &a : sub)
    cnt += a.size() == 0;
  if (cnt > n)
    return;
  if (n == 0)
  {
    ohmy.insert(finalize(sub));
    return;
  }
  bool wasempty = false;
  for (int i = 0; i < k; i++)
  {
    auto &s = sub[i];
    if (s.empty())
    {
      if (wasempty)
        continue;
      wasempty = true;
    }
    s.push_back(n);
    gen(sub, n - 1, k);
    s.pop_back();
  }
}
 
#include <ctime>
 
int main(void)
{
  int n, k;
  cin >> n >> k;
  if (k == 1)
  {
    for (int i = 1; i <= n; i++)
      cout << i << ' ';
    cout << std::endl;
    return 0;
  }
  std::vector<std::vector<int>> subsets(k);
  time_t st = clock();
  gen(subsets, n, k);
  time_t et = clock();
  // cout << et - st << std::endl;
  for (auto &s : ohmy)
  {
    for (auto &a : s)
    {
      for (auto &b : a)
        cout << b << ' ';
      cout << '\n';
    }
    cout << '\n';
  }
  return 0;
}