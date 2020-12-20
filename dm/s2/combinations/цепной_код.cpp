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
auto cin = std::fstream("chaincode.in", std::ios_base::in);
auto cout = std::fstream("chaincode.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(4)delim");
using std::cout;
#endif
 
int topow2(int i)
{
  i--;
  i |= i >> 1;
  i |= i >> 2;
  i |= i >> 4;
  i |= i >> 8;
  i |= i >> 16;
  return i + 1;
}
 
void printbin(int i, int n)
{
  for (int j = n - 1; j >= 0; j--)
    cout << ((i >> j) & 1);
  cout << std::endl;
}
 
int main(void)
{
  int n;
  cin >> n;
  int mask = (1 << (n - 1)) - 1;
 
  std::set<int> was;
 
  was.insert(0);
  printbin(0, n);
  int last = 0;
  while (true)
  {
    const int
      n2 = ((last & mask) << 1),
      n1 = n2 | 1;
    if (was.find(n1) == was.end())
    {
      was.insert(was.end(), n1);
      printbin(n1, n);
      last = n1;
    }
    else if (was.find(n2) == was.end())
    {
      was.insert(was.end(), n2);
      printbin(n2, n);
      last = n2;
    }
    else
      break;
  }
 
  return 0;
}