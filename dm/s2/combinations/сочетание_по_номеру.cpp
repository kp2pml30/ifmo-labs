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
auto cin = std::fstream("num2choose.in", std::ios_base::in);
auto cout = std::fstream("num2choose.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(4 2 3)delim");
using std::cout;
#endif
 
void printbin(int i, int n)
{
  for (int j = n - 1; j >= 0; j--)
    cout << ((i >> j) & 1);
  cout << std::endl;
}
 
long long fact[40];
constexpr long long  CN = 40, CK = 40;
long long C[CN][CK];
 
void gen(int v[40], int ind, int from, int n, int k, long long &m)
{
  if (ind == k)
  {
    for (int i = 0; i < ind; i++)
      cout << v[i] << " ";
    cout << std::endl;
    exit(0);
    // return;
  }
 
  for (int i = from; i <= n; i++)
  {
    long long  cnt = C[n - i][k - ind - 1];
    if (cnt <= m)
      m -= cnt;
    else
    {
      v[ind] = i;
      gen(v, ind + 1, i + 1, n, k, m);
    }
  }
}
 
void main(void)
{
  // fact
  fact[0] = 1;
  for (int i = 1; i < sizeof(fact) / sizeof(fact[0]); i++)
    fact[i] = fact[i - 1] * i;
  // C
  C[0][0] = 1;
  for (int n = 1; n < CN; n++)
  {
    C[n][0] = 1;
    for (int k = 1; k < CK; k++)
      C[n][k] = C[n - 1][k] + C[n - 1][k - 1];
  }
  long long n, k, m;
  cin >> n >> k >> m;
  int v[40] = {};
  gen(v, 0, 1, n, k, m);
}