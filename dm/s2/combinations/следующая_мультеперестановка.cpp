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
auto cin = std::fstream("nextmultiperm.in", std::ios_base::in);
auto cout = std::fstream("nextmultiperm.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(6
1 3 2 1 3 2
)delim");
using std::cout;
#endif
 
int main(void)
{
  int n;
  cin >> n;
  std::vector<int> perm(n);
  for (int i = 0; i < n; i++)
    cin >> perm[i];
 
  int i;
  for (i = n - 2; i >= 0 && perm[i] >= perm[i + 1]; i--)
    ;
  if (i < 0)
  {
    for (int i = 0; i < n; i++)
      cout << 0 << ' ';
    cout << std::endl;
    return 0;
  }
  int j;
  for (j = i + 1; j < n - 1 && perm[j + 1] > perm[i]; j++)
    ;
  std::swap(perm[i], perm[j]);
  for (int ii = 0; ii < i + 1; ii++)
    cout << perm[ii] << ' ';
  for (int ii = n - 1; ii >= i + 1; ii--)
    cout << perm[ii] << ' ';
  cout << std::endl;
  return 0;
}