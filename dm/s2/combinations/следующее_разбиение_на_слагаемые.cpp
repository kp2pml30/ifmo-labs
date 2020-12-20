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
auto cin = std::fstream("nextpartition.in", std::ios_base::in);
auto cout = std::fstream("nextpartition.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(5=1+1+3
)delim");
using std::cout;
#endif
 
int main(void)
{
  std::string str;
  cin >> str;
  int n, pos;
  sscanf(str.c_str(), "%i=%n", &n, &pos);
  std::list<int> lst;
  while (pos < str.size())
  {
    int cur, off;
    sscanf(str.c_str() + pos, "%i%n", &cur, &off);
    pos += off;
    lst.push_back(cur);
    if (pos < str.size() && str[pos] == '+')
      pos++;
    else
      break;
  }
  if (lst.size() == 1)
  {
    cout << "No solution" << std::endl;
    return 0;
  }
  auto
    last = std::prev(lst.end()),
    prev = std::prev(last);
  (*last)--;
  (*prev)++;
  if (*prev > *last)
  {
    *prev += *last;
    lst.pop_back();
  }
  else
    while ((*std::prev(lst.end(), 2) << 1) <= lst.back())
    {
      lst.push_back(lst.back() - *std::prev(lst.end(), 2));
      *std::prev(lst.end(), 2) = *std::prev(lst.end(), 3);
    }
  cout << n << '=';
  last = lst.begin();
  cout << *last;
  last++;
  while (last != lst.end())
    cout << '+' << *last++;
  cout << std::endl;
  return 0;
}