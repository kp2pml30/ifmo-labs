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
auto cin = std::fstream("num2brackets.in", std::ios_base::in);
auto cout = std::fstream("num2brackets.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(6 99)delim");
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
  long long n, k;
  cin >> n >> k;
  n <<= 1;
  gendyke(0, 0);
  long long
    num = 0,
    sum = 0;
  for (int i = 0; i < n; i++)
    if (long long cnt = dyke[n - i - 1][sum + 1]; cnt > k)
    {
      cout << '(';
      sum++;
    }
    else
    {
      k -= cnt;
      cout << ')';
      sum--;
    }
  cout << std::endl;
  return 0;
}