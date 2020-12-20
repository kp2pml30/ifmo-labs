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
 
// #undef MBUF
 
int main(void)
{
#ifndef MBUF
  auto cin = std::fstream("allvectors.in", std::ios_base::in);
  auto cout = std::fstream("allvectors.out", std::ios_base::app);
#else
  auto cin = std::stringstream(R"delim(3)delim");
  using std::cout;
#endif
  int n;
  cin >> n;
  for (uint i = 0; i < (1 << n); i++)
  {
    for (int j = n - 1; j >= 0; j--)
      cout << ((i >> j) & 1);
    cout << std::endl;
  }
  return 0;
}