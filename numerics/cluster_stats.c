/* Cluster statistics in the frame of the largest pile.
   A cluster is a background pile (mass >= 2) together with the singles ahead
   of it up to the next pile. Singles ahead of the largest pile up to the first
   background pile form the peak's own domain.
   Build: gcc -O2 -o cluster_stats cluster_stats.c
   usage: cluster_stats L N w burn samp seed
   Starts from a uniform spread and averages over states where one pile
   holds a majority with margin, N + 2 < 2M. */
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

#define MMAX 64
int main(int argc, char **argv) {
  int L = atoi(argv[1]); long N = atol(argv[2]); double w = atof(argv[3]);
  double burn = atof(argv[4]), samp = atof(argv[5]);
  s[0] = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atol(argv[6]); s[1] = 0xD1B54A32D192ED03ULL;
  for (int k = 0; k < 20; k++) rng();
  long *eta = calloc(L, sizeof(long));
  for (long k = 0; k < N; k++) eta[k % L]++;
  double R = 1.0 + w;
  long steps_per_unit = (long)(R * L);
  double cnt[MMAX + 1]; memset(cnt, 0, sizeof cnt);     /* clusters by total mass */
  double pcnt[MMAX + 1]; memset(pcnt, 0, sizeof pcnt);  /* clusters by pile mass */
  double domainSingles = 0, clusterMass = 0, offsetMass = 0, nmaj = 0, nsamp = 0;
  double farMass = 0; /* cluster mass with anchor offset > sqrt(L) */
  for (long u = 0; u < (long)(burn + samp); u++) {
    for (long k = 0; k < steps_per_unit; k++) {
      int i = (int)(rng() % (uint64_t)L);
      long a = eta[i];
      if (a == 0) continue;
      double x = unif() * R;
      int j = (i + 1 == L) ? 0 : i + 1;
      if (x < w) { eta[i]--; eta[j]++; }
      else if (a >= 2) { eta[j] += a; eta[i] = 0; }
    }
    if (u < (long)burn) continue;
    nsamp++;
    int p = 0; for (int i = 1; i < L; i++) if (eta[i] > eta[p]) p = i;
    if (2 * eta[p] <= N + 2) continue;
    nmaj++;
    long cm = -1, pm = 0; int anchor = 0;
    for (int off = 1; off < L; off++) {
      long a = eta[(p + off) % L];
      if (a >= 2) {
        if (cm >= 0) { cnt[cm < MMAX ? cm : MMAX]++; pcnt[pm < MMAX ? pm : MMAX]++;
                       clusterMass += cm; offsetMass += (double)cm * anchor;
                       if (anchor * anchor > L) farMass += cm; }
        cm = a; pm = a; anchor = off;
      } else if (a == 1) {
        if (cm >= 0) cm++; else domainSingles++;
      }
    }
    if (cm >= 0) { cnt[cm < MMAX ? cm : MMAX]++; pcnt[pm < MMAX ? pm : MMAX]++;
                   clusterMass += cm; offsetMass += (double)cm * anchor;
                   if (anchor * anchor > L) farMass += cm; }
  }
  printf("L=%d w=%.2f P(maj)=%.4f domainSingles=%.4f clusterMass=%.4f mass*offset=%.4f farMass=%.5f\n",
         L, w, nmaj / nsamp, domainSingles / nmaj, clusterMass / nmaj, offsetMass / nmaj, farMass / nmaj);
  printf("  expected number of clusters by total mass m:");
  for (int m = 2; m <= 12; m++) printf(" %d:%.2e", m, cnt[m] / nmaj);
  printf("\n  expected number of clusters by pile mass k:");
  for (int m = 2; m <= 12; m++) printf(" %d:%.2e", m, pcnt[m] / nmaj);
  printf("\n");
  return 0;
}
