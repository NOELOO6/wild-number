#include <algorithm>
#include <cstdint>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

// Probabilities are enclosed by integers in units of 10^-8.
// The replay enables the signed-overflow sanitizer and stops on any violation.
using I = std::int64_t;
constexpr I scale = 100000000;
struct Range {
  I lo = 1, hi = 0;
  bool feasible() const { return lo <= hi; }
};
I C2(I n) { return n * (n - 1) / 2; }
I C3(I n) { return n * (n - 1) * (n - 2) / 6; }
I ceil_div(I a, I b) { return a / b + (a % b > 0); }
I floor_div(I a, I b) { return a / b - (a % b < 0); }
I cap(I q, I k) { return std::min(C3(q), k * C2(q) / 3); }
// Extremal sums of squares of integers with fixed sum and common bounds.
I min_squares(I count, I sum) {
  I d = sum / count, extra = sum % count;
  return count * d * d + extra * (2 * d + 1);
}
I max_squares(I count, I sum, I d, I D) {
  if (d == D)
    return count * d * d;
  I extras = sum - count * d, high = extras / (D - d), r = extras % (D - d);
  return count * d * d + high * (D * D - d * d) + r * (2 * d + r);
}
// Labeled rooted triples contained in an arbitrary q-subset of the free
// vertices.
Range labeled(I n, I roots, I q) {
  I k = n - q, baseline = C2(n) - 3 * ((n - 1) / 2) * k;
  I lo = std::max(
      {I(0), baseline + 2 * C2(k), q * std::max(I(0), q - (n + 1) / 2)});
  I hi = std::min(C2(q), baseline + 3 * C2(k));
  return {roots * lo, roots * hi};
}
// Enclose the truncated inclusion-exclusion remainder, indexed by the number
// of distinct forbidden triples. An empty interval denotes an impossible count.
std::vector<Range> layer(I n, I roots, I q, I j,
                         const std::vector<Range> &child) {
  I k = 3 * roots, D = std::min(C2(q - 1), k * (q - 1) / 2);
  I d = ceil_div(std::max(I(0), roots * (3 * ((n - 1) / 2) - 3 * (n - q))), 3);
  auto labels = labeled(n, roots, q);
  std::vector<Range> result(cap(q, k) + 1);
  for (I a = 0; a < I(result.size()); ++a) {
    if (a < ceil_div(labels.lo, 3) || a > labels.hi || 3 * a < q * d ||
        3 * a > q * D)
      continue;
    if (!a) {
      result[a] = {scale, scale};
      continue;
    }
    I low = std::max(I(0), a - 3 * D + 2);
    I high =
        std::min(I(child.size()) - 1, a - std::max(I(1), 3 * d - 3 * k + 1));
    // The expected number after removing a uniform member, multiplied by a, is
    // the number of ordered disjoint pairs of triples.
    I meanlo = std::max(a * low, a * (a - 1) - max_squares(q, 3 * a, d, D) +
                                     min_squares(C2(q), 3 * a));
    I meanhi = std::min(a * high, a * (a - 1) - min_squares(q, 3 * a) +
                                      max_squares(C2(q), 3 * a, 0, k));
    if (meanlo > meanhi)
      continue;
    while (low <= high && !child[low].feasible())
      ++low;
    while (low <= high && !child[high].feasible())
      --high;
    if (low > high)
      continue;
    meanlo = std::max(meanlo, a * low);
    meanhi = std::min(meanhi, a * high);
    if (meanlo > meanhi)
      continue;
    // Use the two endpoints only to select a slope. Check the intercept
    // at every feasible integer before applying the disjoint-pair mean.
    I slope = high > low ? ((child[high].lo + child[high].hi) -
                            (child[low].lo + child[low].hi)) /
                               (2 * (high - low))
                         : 0;
    I l = std::numeric_limits<I>::max(), h = std::numeric_limits<I>::min();
    for (I v = low; v <= high; ++v)
      if (child[v].feasible()) {
        l = std::min(l, child[v].lo - slope * v);
        h = std::max(h, child[v].hi - slope * v);
      }
    I den = (j + 1) * C2(q - 1);
    result[a] = {
        scale - ceil_div(a * h + slope * (slope < 0 ? meanlo : meanhi), den),
        scale - floor_div(a * l + slope * (slope < 0 ? meanhi : meanlo), den)};
  }
  return result;
}
std::vector<Range> avoidance(I n, I roots, I q) {
  std::vector<Range> best(cap(q, 3 * roots) + 1, {0, scale});
  // Each truncation starts at one. Odd and even depths supply independent
  // lower and upper bounds on the same avoidance probability.
  for (I depth = 1; depth <= std::min(I(10), q / 3); ++depth) {
    std::vector<Range> arr(cap(q - 3 * depth, 3 * roots) + 1, {scale, scale});
    for (I j = depth - 1; j >= 0; --j)
      arr = layer(n, roots, q - 3 * j, j, arr);
    for (std::size_t i = 0; i < best.size(); ++i) {
      if (!arr[i].feasible())
        best[i] = {scale + 1, -1};
      else if (depth % 2)
        best[i].lo = std::max(best[i].lo, arr[i].lo);
      else
        best[i].hi = std::min(best[i].hi, arr[i].hi);
    }
  }
  return best;
}
int main(int argc, char **argv) {
  if (argc != 4)
    return 2;
  I n = std::stoll(argv[1]), r = std::stoll(argv[2]), q = std::stoll(argv[3]);
  if (n < 9 || n > 75 || n % 2 != 1 || r < 1 || r > 2 || q < 0 || q > n ||
      q % 3 != 0)
    return 2;
  auto a = avoidance(n, r, q);
  for (std::size_t i = 0; i < a.size(); ++i)
    std::cout << i << ' ' << a[i].lo << ' ' << a[i].hi << '\n';
}
