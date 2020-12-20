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
auto cin = std::fstream("subsets.in", std::ios_base::in);
auto cout = std::fstream("subsets.out", std::ios_base::app);
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
 
void gen(bool w[20], int i, int n)
{
  if (i > n)
    return;
 
  if (w[i - 1])
  {
    bool was = false;
    for (int j = 0; j <= i; j++)
      if (w[j])
      {
        cout << j + 1 << " ";
        was = true;
      }
    if (was)
      cout << std::endl;
  }
 
  w[i] = true;
  gen(w, i + 1, n);
  w[i] = false;
  gen(w, i + 1, n);
}
 
int main(void)
{
  int n;
  cin >> n;
  bool w[20] = {};
 
  cout << std::endl;
  gen(w, 0, n);
  return 0;
}