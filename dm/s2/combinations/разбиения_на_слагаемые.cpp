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
auto cin = std::fstream("partition.in", std::ios_base::in);
auto cout = std::fstream("partition.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(4)delim");
using std::cout;
#endif
 
void printbin(int i, int n)
{
  for (int j = n - 1; j >= 0; j--)
    cout << ((i >> j) & 1);
  cout << std::endl;
}
 
longlong fact[20];
 
 
void print(const std::vector<int> &v, int to = -1)
{
  if (to == -1)
    to = v.size();
  cout << v[0];
  for (int i = 1; i < to; i++)
    cout << "+" << v[i];
  cout << std::endl;
}
 
void gen(std::vector<int> &v, int sum, int p, int n)
{
  if (sum == 0)
  {
    print(v, p);
    return;
  }
  for (int c = p == 0 ? 1 : v[p - 1]; c <= sum; c++)
  {
    v[p] = c;
    gen(v, sum - c, p + 1, n);
  }
}
 
void main(void)
{
  fact[0] = 1;
  for (int i = 1; i < sizeof(fact) / sizeof(fact[0]); i++)
    fact[i] = fact[i - 1] * i;
  int n;
  cin >> n ;
  std::vector<int> dig(n);
  gen(dig, n, 0, n);
 
}