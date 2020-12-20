#define _CRT_SECURE_NO_WARNINGS
 
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
auto cin = std::fstream("part2num.in", std::ios_base::in);
auto cout = std::fstream("part2num.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(2+2
)delim");
using std::cout;
#endif
 
class endler
{
public:
  ~endler(void)
  {
    cout << std::endl;
  }
};
 
int main(void)
{
  std::string str;
  cin >> str;
  int pos = 0, n = 0;
  std::list<int> lst;
  while (pos < str.size())
  {
    int cur, off;
    sscanf(str.c_str() + pos, "%i%n", &cur, &off);
    pos += off;
    n += cur;
    lst.push_back(cur);
    if (pos < str.size() && str[pos] == '+')
      pos++;
    else
      break;
  }
  endler e;
  
  long long d[300][300] = {};
  for (int i = 0; i < 110; i++)
    d[i][i] = 1;
  for (int iter = 1; iter < 110; iter++)
    for (int j = 0; j < 110; j++)
    {
      int i = j + iter;
      d[i][j] = d[i][j + 1] + d[i - j][j];
    }
  long long k = 0;
  int prev = 1, sum = 0;
  auto iter = lst.begin();
  for (auto &el : lst)
  {
    for (int j = prev; j < el; j++)
      k += d[n - sum - j][j];
    sum += el;
    prev = el;
  }
  cout << k;
  return 0;
}