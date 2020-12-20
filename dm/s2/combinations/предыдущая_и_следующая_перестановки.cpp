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
auto cin = std::fstream("nextperm.in", std::ios_base::in);
auto cout = std::fstream("nextperm.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(4
1 3 2 4)delim");
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
 
static int __factprecalcer = [](void) -> int {
  fact[0] = 1;
  for (int i = 1; i < sizeof(fact) / sizeof(fact[0]); i++)
    fact[i] = fact[i - 1] * i;
  return 0;
}();
 
static int __Cprecalcer = [](void) -> int {
  C[0][0] = 1;
  for (int n = 1; n < CN; n++)
  {
    C[n][0] = 1;
    for (int k = 1; k < CK; k++)
      C[n][k] = C[n - 1][k] + C[n - 1][k - 1];
  }
  return 0;
}();
 
void main(void)
{
  long long n;
  cin >> n;
  std::vector<int> dig(n);
  for (int i = 0; i < n; i++)
    cin >> dig[i];
  auto dig1 = dig;
 
  // prev
  {
    int max = dig[n - 1];
    int resi = -1, maxi = n - 1;
    for (int i = n - 2; i >= 0; i--)
      if (dig[i] < max)
      {
        max = dig[i];
        maxi = i;
      }
      else
      {
        resi = i;
        break;
      }
    if (resi == -1)
      for (int i = 0; i < n; i++)
        cout << "0 ";
    else
    {
      for (int i = resi + 1; i < n; i++)
        if (dig[i] < dig[resi] && dig[i] > dig[maxi])
          maxi = i;
      std::swap(dig[resi], dig[maxi]);
      std::sort(dig.begin() + resi + 1, dig.end());
      std::reverse(dig.begin() + resi + 1, dig.end());
      for (int i = 0; i < n; i++)
        cout << dig[i] << " ";
    }
  }
 
  cout << std::endl;
  dig1.swap(dig);
 
  // next
  {
    int max = dig[n - 1];
    int resi = -1, maxi = n - 1;
    for (int i = n - 2; i >= 0; i--)
      if (dig[i] > max)
      {
        max = dig[i];
        maxi = i;
      }
      else
      {
        resi = i;
        break;
      }
    if (resi == -1)
      for (int i = 0; i < n; i++)
        cout << "0 ";
    else
    {
      for (int i = resi + 1; i < n; i++)
        if (dig[i] > dig[resi] && dig[i] < dig[maxi])
          maxi = i;
      std::swap(dig[resi], dig[maxi]);
      std::sort(dig.begin() + resi + 1, dig.end());
      for (int i = 0; i < n; i++)
        cout << dig[i] << " ";
    }
  }
  cout << std::endl;
}