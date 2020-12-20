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
auto cin = std::fstream("brackets.in", std::ios_base::in);
auto cout = std::fstream("brackets.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(4)delim");
using std::cout;
#endif
 
void gen(std::string &res, int i, int su)
{
  if (su > (int)res.size() - i)
    return;
  if (i == res.size())
  {
    cout << res << std::endl;
    return;
  }
  else if (su == res.size() - i)
  {
    res[i] = ')';
    gen(res, i + 1, su - 1);
    return;
  }
 
  res[i] = '(';
  gen(res, i + 1, su + 1);
  if (su > 0)
  {
    res[i] = ')';
    gen(res, i + 1, su - 1);
  }
}
 
int main(void)
{
  int n;
  cin >> n;
  std::string r;
  r.resize(2 * n);
 
  gen(r, 0, 0);
  return 0;
}