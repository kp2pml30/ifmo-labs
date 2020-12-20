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
auto cin = std::fstream("nextvector.in", std::ios_base::in);
auto cout = std::fstream("nextvector.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(10000)delim");
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
  for (int i = 0; i < v.size(); i++)
    cout << v[i];
  cout << std::endl;
}
 
void main(void)
{
  fact[0] = 1;
  for (int i = 1; i < sizeof(fact) / sizeof(fact[0]); i++)
    fact[i] = fact[i - 1] * i;
  std::vector<bool> dig;
 
  while (!cin.eof())
  {
    char c;
    cin >> c;
    switch (c)
    {
    case '1':
    case '0':
      dig.push_back(c - '0');
      break;
    default:
      break;
    }
  }
  dig.pop_back(); // ???
 
  std::reverse(dig.begin(), dig.end());
  int rightmost1 = -1;
  for (int i = 0; i < dig.size(); i++)
    if (dig[i] == 1)
    {
      rightmost1 = i;
      break;
    }
  if (rightmost1 == -1)
    cout << '-';
  else
  {
    for (int i = dig.size() - 1; i > rightmost1; i--)
      cout << dig[i];
    cout << 0;
    for (int i = rightmost1 - 1; i >= 0; i--)
      cout << 1;
  }
  cout << std::endl;
  rightmost1 = -1;
  for (int i = 0; i < dig.size(); i++)
    if (dig[i] == 0)
    {
      rightmost1 = i;
      break;
    }
  if (rightmost1 == -1)
    cout << '-';
  else
  {
    for (int i = dig.size() - 1; i > rightmost1; i--)
      cout << dig[i];
    cout << 1;
    for (int i = rightmost1 - 1; i >= 0; i--)
      cout << 0;
  }
  cout << std::endl;
}