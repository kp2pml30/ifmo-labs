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
auto cin = std::fstream("num2part.in", std::ios_base::in);
auto cout = std::fstream("num2part.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(4 3)delim");
using std::cout;
#endif
 
void printbin(int i, int n)
{
  for (int j = n - 1; j >= 0; j--)
    cout << ((i >> j) & 1);
  cout << std::endl;
}
 
long long d[300][300] = {};
 
void print(const std::vector<int> &v, int to = -1)
{
  if (to == -1)
    to = v.size();
  cout << v[0];
  for (int i = 1; i < to; i++)
    cout << "+" << v[i];
  cout << std::endl;
}
 
void gen(std::vector<int> &v, int left, int min, long long k)
{
  if (left == 0)
  {
    print(v);
    return;
  }
  long long miss = 0;
  for (int c = left; c >= min; c--)
  {
    long long cnt = d[left][c];
    if (k <= cnt)
    {
      v.push_back(c);
      gen(v, left - c, c, k - miss);
      return;
    }
    miss = cnt;
  }
}
 
void main(void)
{
  for (int i = 0; i < 110; i++)
    d[i][i] = 1;
  for (int iter = 1; iter < 110; iter++)
    for (int j = 0; j < 110; j++)
    {
      int i = j + iter;
      d[i][j] = d[i][j + 1] + d[i - j][j];
    }
 
  int n;
  long long k;
  cin >> n >> k;
  std::vector<int> dig;
  gen(dig, n, 1, d[n][1] - k);
 
}