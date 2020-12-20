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
auto cin = std::fstream("brackets2num2.in", std::ios_base::in);
auto cout = std::fstream("brackets2num2.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(([])()[] )delim");
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
  gendyke(0, 0);
  long long
    num = 0,
    sum = 0;
  const char br[4] = {'(', ')', '[', ']'};
  std::vector<std::pair<char, int>> stack;
  for (int i = 0; i < r.size(); i++)
  {
    int pos = 0;
    while (pos < 3 && br[pos] != r[i])
      pos++;
 
    const int d = (pos & 1) * -2 + 1;
 
    if (pos > 0)
      num += dyke[r.size() - i - 1][sum + 1] * (1 << ((r.size() - i - 1 - sum) >> 1));
    if (pos > 1 && stack.size() && stack.back().first == 1)
      num += dyke[r.size() - i - 1][sum - 1] * (1 << ((r.size() - i - 1 - sum + 1) >> 1));
    if (pos > 2)
      num += dyke[r.size() - i - 1][sum + 1] * (1 << ((r.size() - i - 1 - sum) >> 1));
 
    if (d == 1)
      if (!stack.empty() && stack.back().first == (pos ^ 1))
        stack.back().second++;
      else
        stack.push_back({pos ^ 1, 1});
    else
      if (--stack.back().second == 0)
        stack.pop_back();
 
    sum += d;
  }
  cout << num;
  return 0;
}