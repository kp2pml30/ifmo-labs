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
auto cin = std::fstream("brackets2num.in", std::ios_base::in);
auto cout = std::fstream("brackets2num.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(((()(())))())delim");
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
  std::vector<int> pref(r.size());
  pref[0] = 1;
  for (int i = 1; i < pref.size(); i++)
    pref[i] = pref[i - 1] + (r[i] == '(' ? 1 : -1);
  gendyke(0, 0);
  long long
    num = 0,
    sum = 0;
  for (int i = 0; i < r.size(); i++)
    if (r[i] == '(')
      sum++;
    else
    {
      num += dyke[r.size() - i - 1][sum + 1];
      sum--;
    }
  cout << num;
  return 0;
}