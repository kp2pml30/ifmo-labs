#include <iostream>
#include <cstdio>
#include <vector>

using type = int;

int main(void)
{
  type
    n, x, y, a0,
    m, z, t, b0;
  std::cin >> n >> x >> y >> a0;
  std::cin >> m >> z >> t >> b0;
  std::vector<long long> asum(n);
  asum[0] = a0;
  type aprev = a0;
  for (type i = 1; i < n; i++)
  {
    const type
      anext = (aprev * x + y) % (1 << 16);
    asum[i] = asum[i - 1] + anext;
    aprev = anext;
  }
  long long sum = 0;
  type bprev = b0;
  for (type i = 0; i < m; i++)
  {
    type
      bnext = ((long long)bprev  * z + t) % (1 << 30);
    type
      c2i  = bprev % n,
      c2i1 = bnext % n;
    if (c2i > c2i1)
      std::swap(c2i, c2i1);
    sum += (long long)asum[c2i1] - (c2i == 0 ? 0 : asum[c2i - 1]);
    bprev = bnext;
    bnext = ((long long)bprev  * z + t) % (1 << 30);
    bprev = bnext;
  }
  std::cout << sum << std::endl;
  return 0;
}

