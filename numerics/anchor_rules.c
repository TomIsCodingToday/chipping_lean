/* Compare the chip gain and loss of the linear anchored moment for two anchor
   rules in the frame of the largest pile:
     level 1: anchors are offsets with at least two particles;
     level 2: also the first of two adjacent singles.
   For each sampled state in the majority region and each occupied site, apply
   the chip, recompute the moment, and accumulate the positive and negative
   parts of the change (times w, the chip rate).
   Build: gcc -O2 -o anchor_rules anchor_rules.c
   usage: anchor_rules L N w burn samp every seed
   Starts from a uniform spread; samples every `every` time units. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static uint64_t s[2];
static inline uint64_t rng(void) {
  uint64_t s1 = s[0]; const uint64_t s0 = s[1];
  s[0] = s0; s1 ^= s1 << 23; s[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26);
  return s[1] + s0;
}
static inline double unif(void) { return (rng() >> 11) * (1.0 / 9007199254740992.0); }

static int L;
/* moment of a frame sequence a[0..L-1] (a[0] = peak) under a rule */
static double moment(const long *a, int level) {
  double m = 0; int A = 0;
  for (int u = 0; u < L; u++) {
    int pile = a[u] >= 2 || (level == 2 && a[u] == 1 && u + 1 < L && a[u + 1] == 1);
    if (pile) A = u;
    m += (double)A * a[u];
  }
  return m;
}

int main(int argc, char **argv) {
  L = atoi(argv[1]); long N = atol(argv[2]); double w = atof(argv[3]);
  double burn = atof(argv[4]), samp = atof(argv[5]); int every = atoi(argv[6]);
  s[0] = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atol(argv[7]); s[1] = 0xD1B54A32D192ED03ULL;
  for (int k = 0; k < 20; k++) rng();
  long *eta = calloc(L, sizeof(long)), *a = calloc(L, sizeof(long)), *b = calloc(L, sizeof(long));
  for (long k = 0; k < N; k++) eta[k % L]++;
  double R = 1.0 + w; long spu = (long)(R * L);
  double gain[3] = {0}, loss[3] = {0}, nmaj = 0;
  for (long u = 0; u < (long)(burn + samp); u++) {
    for (long k = 0; k < spu; k++) {
      int i = (int)(rng() % (uint64_t)L); long x = eta[i];
      if (x == 0) continue;
      double r = unif() * R; int j = (i + 1 == L) ? 0 : i + 1;
      if (r < w) { eta[i]--; eta[j]++; } else if (x >= 2) { eta[j] += x; eta[i] = 0; }
    }
    if (u < (long)burn || u % every) continue;
    int p = 0; for (int i = 1; i < L; i++) if (eta[i] > eta[p]) p = i;
    if (2 * eta[p] <= N + 2) continue;
    nmaj++;
    for (int off = 0; off < L; off++) a[off] = eta[(p + off) % L];
    for (int level = 1; level <= 2; level++) {
      double m0 = moment(a, level);
      for (int off = 0; off < L; off++) {
        if (a[off] < 1) continue;
        memcpy(b, a, L * sizeof(long));
        b[off]--;
        if (off + 1 < L) b[off + 1]++; else b[0]++;   /* last offset chips into the peak */
        double d = moment(b, level) - m0;
        if (d > 0) gain[level] += w * d; else loss[level] -= w * d;
      }
    }
  }
  printf("L=%d w=%.2f  level1: gain=%.4f loss=%.4f net=%.4f | level2: gain=%.4f loss=%.4f net=%.4f\n",
         L, w, gain[1] / nmaj, loss[1] / nmaj, (gain[1] - loss[1]) / nmaj,
         gain[2] / nmaj, loss[2] / nmaj, (gain[2] - loss[2]) / nmaj);
  return 0;
}
