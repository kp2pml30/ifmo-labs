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
auto cin = std::fstream("permutations.in", std::ios_base::in);
auto cout = std::fstream("permutations.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(3)delim");
using std::cout;
#endif
 
void printbin(int i, int n)
{
  for (int j = n - 1; j >= 0; j--)
    cout << ((i >> j) & 1);
  cout << std::endl;
}
 
int main(void)
{
  int n;
  cin >> n;
  std::list<std::vector<int>> re;
  re.push_back(std::vector<int>(1, 1));
  for (int i = 2; i <= n; i++)
  {
    auto iter = re.begin();
    while (iter != re.end())
    {
      auto next = std::next(iter);
      for (int j = 1; j < i; j++)
      {
        auto i2 = re.insert(next, *iter);
        i2->insert(std::next(i2->begin(), j), i);
      }
      iter->insert(iter->begin(), i);
      iter = next;
      if (iter == re.end())
        break;
      next = std::next(iter);
      for (int j = 1; j < i; j++)
      {
        auto i2 = re.insert(next, *iter);
        i2->insert(std::prev(i2->end(), j), i);
      }
      iter->insert(iter->end(), i);
      iter = next;
    }
  }
 
  re.sort([](const auto &a, const auto &b)
  {
    for (int i = 0; i < a.size(); i++)
      if (a[i] < b[i])
        return true;
      else if (a[i] > b[i])
        return false;
    return false;
  });
  for (auto &b : re)
  {
    for (auto &a : b)
      cout << a << " ";
    cout << std::endl;
  }
  return 0;
}