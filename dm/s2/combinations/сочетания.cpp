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
auto cin = std::fstream("choose.in", std::ios_base::in);
auto cout = std::fstream("choose.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(16 8)delim");
using std::cout;
#endif
 
void printbin(int i, int n)
{
  for (int j = n - 1; j >= 0; j--)
    cout << ((i >> j) & 1);
  cout << std::endl;
}
 
void gen(bool w[20], int i, int c, int k, int n)
{
  if (n - i < k - c)
    return;
  if (c == k)
  {
    for (int j = 0; j <= i; j++)
      if (w[j])
        cout << j + 1 << " ";
    cout << std::endl;
    return;
  }
  w[i] = true;
  gen(w, i + 1, c + 1, k, n);
  w[i] = false;
  gen(w, i + 1, c, k, n);
}
 
int main(void)
{
  int n, k;
  cin >> n >> k;
  bool w[20] = {};
 
  gen(w, 0, 0, k, n);
  return 0;
}