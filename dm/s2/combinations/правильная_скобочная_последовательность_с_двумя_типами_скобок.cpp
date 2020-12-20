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
auto cin = std::fstream("num2brackets2.in", std::ios_base::in);
auto cout = std::fstream("num2brackets2.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(
4 100
)delim");
using std::cout;
#endif
 
using ull = unsigned long long;
 
long long dyke[90][90];
 
void gendyke(int xx, int yy)
{
  memset(dyke, 0, sizeof(dyke));
 
  dyke[xx][yy] = 1;
 
  for (int x = xx + 1; x <= 80; x++)
    for (int y = 0; y <= 80; y++)
      dyke[x][y] = (y == 0 ? 0 : dyke[x - 1][y - 1]) + dyke[x - 1][y + 1];
}
 
ull getcnt(const std::vector<std::pair<char, int>> &br, int putwhat, int n, int sum, int i)
{
  ull num = 0;
  if (putwhat == 0)
    num += dyke[n - i - 1][sum + 1] * ((ull)1 << ((n - i - 1 - sum) >> 1));
  if (putwhat == 1 && br.size() && br.back().first == 1)
    num += dyke[n - i - 1][sum - 1] * ((ull)1 << ((n - i - 1 - sum + 1) >> 1));
  if (putwhat == 2)
    num += dyke[n - i - 1][sum + 1] * ((ull)1 << ((n - i - 1 - sum) >> 1));
  if (putwhat == 3 && br.size() && br.back().first == 3)
    num += dyke[n - i - 1][sum - 1] * ((ull)1 << ((n - i - 1 - sum + 1) >> 1));
  return num;
}
 
void updstack(std::vector<std::pair<char, int>> &br, char putwhat)
{
  if (putwhat % 2 == 0)
    if (!br.empty() && br.back().first == (putwhat ^ 1))
      br.back().second++;
    else
      br.push_back({putwhat ^ 1, 1});
  else
    if (--br.back().second == 0)
      br.pop_back();
}
 
int main(void)
{
  int n;
  ull k;
  cin >> n >> k;
  n *= 2;
  gendyke(0, 0);
  int sum = 0;
  const char br[4] = {'(', ')', '[', ']'};
  std::vector<std::pair<char, int>> stack;
  for (int i = 0; i < n; i++)
  {
    for (int j = 0; j < 4; j++)
    {
      const ull cnt = getcnt(stack, j, n, sum, i);
      if (cnt > k)
      {
        cout << br[j];
        updstack(stack, j);
        sum += (j & 1) * -2 + 1;
        break;
      }
      else
      {
        k -= cnt;
      }
    }
  }
  return 0;
}