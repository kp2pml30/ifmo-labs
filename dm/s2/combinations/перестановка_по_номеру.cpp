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
 
#define int long long
 
#ifndef MBUF
auto cin = std::fstream("num2perm.in", std::ios_base::in);
auto cout = std::fstream("num2perm.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(8 0)delim");
using std::cout;
#endif
 
void printbin(int i, int n)
{
  for (int j = n - 1; j >= 0; j--)
    cout << ((i >> j) & 1);
  cout << std::endl;
}
 
int fact[20];
 
void gen(bool w[20], int v[20], int ind, int &k, int n)
{
  if (ind == n)
  {
    if (k != 0)
      exit(30);
    for (int i = 0; i < n; i++)
      cout << v[i] + 1 << " ";
    cout << std::endl;
    exit(0);
    // return;
  }
 
  for (int i = 0; i < n; i++)
    if (!w[i])
    {
      int cnt = fact[n - ind - 1];
      if (cnt <= k)
        k -= cnt;
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
  int n, k;
  cin >> n >> k;
  bool w[20] = {};
  int v[20] = {};
  gen(w, v, 0, k, n);
}