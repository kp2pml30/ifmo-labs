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
auto cin = std::fstream("nextbrackets.in", std::ios_base::in);
auto cout = std::fstream("nextbrackets.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim((())()())delim");
using std::cout;
#endif
 
long long dyke[90][90];
 
void gendyke(int xx, int yy)
{
  memset(dyke, 0, sizeof(dyke));
 
  dyke[xx][yy] = 1;
 
  for (int x = xx + 1; x <= 80; x++)
    for (int y = 0; y <= 80; y++)
      dyke[x][y] = (y == 0 ? 0 : dyke[x - 1][y - 1]) + dyke[x - 1][y + 1];
}
 
 
int main(void)
{
  std::string r;
  while (!cin.eof())
  {
    char c;
    cin >> c;
    r.push_back(c);
  }
  r.pop_back();
  int cc = 0, co = 0;
  for (int i = r.size() - 1; i >= 0; i--)
  {
    if (r[i] == '(')
    {
      co++;
      if (cc > co)
        break;
    }
    else
      cc++;
  }
  int offset = co + cc;
  if (offset == r.size())
  {
    cout << '-' << std::endl;
    return 0;
  }
  offset = r.size() - offset;
  r[offset] = ')';
 
  while (co > 0)
  {
    r[++offset] = '(';
    co--;
  }
  while (cc > 0)
  {
    r[++offset] = ')';
    cc--;
  }
  cout << r << std::endl;
  return 0;
}