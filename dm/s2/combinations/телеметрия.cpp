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
using longlong = long long;
 
#ifndef MBUF
auto cin = std::fstream("telemetry.in", std::ios_base::in);
auto cout = std::fstream("telemetry.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(3 3)delim");
using std::cout;
#endif
 
void printbin(int i, int n)
{
  for (int j = n - 1; j >= 0; j--)
    cout << ((i >> j) & 1);
  cout << std::endl;
}
 
longlong fact[20];
 
 
void print(const std::vector<int> &v)
{
  for (auto &a : v)
    cout << a;
  cout << std::endl;
}
 
void gen(std::vector<int> &v, int dim, int n, int k)
{
  if (dim < 0)
    return;
  if (v[dim] == 0)
  {
    for (int i = 0; i < k; i++)
    {
      v[dim] = i;
      if (dim == 0)
        print(v);
      gen(v, dim - 1, n, k);
    }
  }
  else
  {
    for (int i = k - 1; i >= 0; i--)
    {
      v[dim] = i;
      if (dim == 0)
        print(v);
      gen(v, dim - 1, n, k);
    }
  }
}
 
void main(void)
{
  fact[0] = 1;
  for (int i = 1; i < sizeof(fact) / sizeof(fact[0]); i++)
    fact[i] = fact[i - 1] * i;
  int n, k;
  cin >> n >> k;
  std::vector<int> dig(n);
  gen(dig, n - 1, n, k);
   
}