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
auto cin = std::fstream("nextchoose.in", std::ios_base::in);
auto cout = std::fstream("nextchoose.out", std::ios_base::app);
#else
auto cin = std::stringstream(R"delim(4 2
1 4)delim");
using std::cout;
#endif
 
int main(void)
{
  long long n, k;
  cin >> n >> k;
  std::vector<int> nums(k);
  for (int i = 0; i < k; i++)
    cin >> nums[i];
  // 1 2 4 -> 1 2 5 if 5 exists // find min from end which can be upped and replace others with min possible
  int res = -1;
  if (n - nums.back() > 0)
    res = k - 1;
  else
    for (int i = k - 2; i >= 0; i--)
      if (nums[i] + 1 < nums[i + 1])
      {
        res = i;
        break;
      }
  if (res == -1)
  {
    cout << -1 << std::endl;
    return 0;
  }
  int cur = ++nums[res];
  for (int i = res + 1; i < k; i++)
    nums[i] = ++cur;
  for (int i = 0; i < k; i++)
    cout << nums[i] << " ";
  cout << std::endl;
  return 0;
}