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
auto cin = std::fstream("antigray.in", std::ios_base::in);
auto cout = std::fstream("antigray.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(2)delim");
using std::cout;
#endif
 
void print3anti(int i, int n)
{
  for (int j = n - 1; j >= 0; j--)
    cout << ((i / (int)pow(3, j)) % 3);
  cout << std::endl;
  for (int j = n - 1; j >= 0; j--)
    cout << (((i / (int)pow(3, j)) + 1) % 3);
  cout << std::endl;
  for (int j = n - 1; j >= 0; j--)
    cout << (((i / (int)pow(3, j)) + 2) % 3);
  cout << std::endl;
}
 
int main(void)
{
  int n;
  cin >> n;
  for (uint i = 0; i < pow(3, n - 1); i++)
  {
    print3anti(i, n);
  }
  return 0;
}