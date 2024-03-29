#include <vector>
#include <map>
#include <iostream>
#include <set>
#include <sstream>
#include <fstream>
#include <string>
#include <algorithm>
using uint = unsigned int;
using ull = unsigned long long;
 
#ifndef MBUF
auto cin = std::fstream("vectors.in", std::ios_base::in);
auto cout = std::fstream("vectors.out", std::ios_base::app);
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
  std::vector<int> re;
  for (uint i = 0; i < (1 << n); i++)
  {
    bool ok = true;
    for (int j = 0; j < n; j++)
      if (((i >> j) & 1) && ((i >> (j + 1)) & 1))
      {
        ok = false;
        break;
      }
    if (ok)
      re.push_back(i);
  }
  cout << re.size() << std::endl;
  for (auto &a : re)
    printbin(a, n);
  return 0;
}