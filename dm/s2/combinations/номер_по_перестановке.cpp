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
auto cin = std::fstream("perm2num.in", std::ios_base::in);
auto cout = std::fstream("perm2num.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(
3
1 3 2
)delim");
using std::cout;
#endif
 
void printbin(int i, int n)
{
  for (int j = n - 1; j >= 0; j--)
    cout << ((i >> j) & 1);
  cout << std::endl;
}
 
long long fact[20];
 
void gen(bool w[20], int v[20], int ind, long long &k, int n)
{
  if (ind == n)
  {
    cout << k << std::endl;
    exit(0);
    // return;
  }
 
  for (int i = 0; i < n; i++)
    if (!w[i])
    {
      long long  cnt = fact[n - ind - 1];
      if (i + 1 != v[ind])
        k += cnt;
      else
      {
        w[i] = true;
        v[ind] = i;
        gen(w, v, ind + 1, k, n);
        w[i] = false;
      }
    }
}
 
void main(void)
{
  fact[0] = 1;
  for (int i = 1; i < sizeof(fact) / sizeof(fact[0]); i++)
    fact[i] = fact[i - 1] * i;
  int n;
  cin >> n;
  bool w[20] = {};
  int v[20] = {};
  for (int i = 0; i < n; i++)
    cin >> v[i];
  long long  k = 0;
  gen(w, v, 0, k, n);
}