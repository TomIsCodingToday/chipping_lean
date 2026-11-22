/* Tail counts of background piles, the quantity in ClusterCountDecay.
   T_m = number of sites other than one largest pile holding at least m
   particles. The program prints the time average of T_m for m = 2..MMAX and
   the mean background mass in piles of three or more, and the mean fraction
   of all particles on one largest pile.
   Event-driven: only occupied sites carry events, so the cost does not grow
   with the number of empty sites.
   Build: gcc -O2 -o tail_counts tail_counts.c -lm
   (add -DMMAX=400 to record tail counts up to mass 400)
   usage: tail_counts L N w burn samp seed [start]
   burn and samp are in units of time; samples are taken once per unit.
   start = 0 puts all particles on one site (default), 1 spreads them evenly. */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t s[2];
static inline uint64_t rng(void) {
  uint64_t s1 = s[0]; const uint64_t s0 = s[1];
  s[0] = s0; s1 ^= s1 << 23; s[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26);
  return s[1] + s0;
}
static inline double unif(void) { return ((rng() >> 11) + 0.5) * (1.0 / 9007199254740992.0); }

#ifndef MMAX
#define MMAX 40
#endif
static long *eta;
static int *occList, *occPos, nOcc, *mulList, *mulPos, nMul;

static void setMember(int *list, int *pos, int *n, int i, int in) {
  if (in && pos[i] < 0) { pos[i] = *n; list[(*n)++] = i; }
  else if (!in && pos[i] >= 0) {
    int k = pos[i], last = list[--(*n)];
    list[k] = last; pos[last] = k; pos[i] = -1;
  }
}
static void refresh(int i) {
  setMember(occList, occPos, &nOcc, i, eta[i] >= 1);
  setMember(mulList, mulPos, &nMul, i, eta[i] >= 2);
}

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: tail_counts L N w burn samp seed [start]\n"); return 1; }
  int L = atoi(argv[1]); long N = atol(argv[2]); double w = atof(argv[3]);
  double burn = atof(argv[4]), samp = atof(argv[5]);
  int start = argc > 7 ? atoi(argv[7]) : 0;
  s[0] = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atol(argv[6]); s[1] = 0xD1B54A32D192ED03ULL;
  for (int k = 0; k < 20; k++) rng();
  eta = calloc(L, sizeof(long));
  occList = malloc(L * sizeof(int)); occPos = malloc(L * sizeof(int));
  mulList = malloc(L * sizeof(int)); mulPos = malloc(L * sizeof(int));
  for (int i = 0; i < L; i++) occPos[i] = mulPos[i] = -1;
  nOcc = nMul = 0;
  if (start == 0) eta[0] = N; else for (long k = 0; k < N; k++) eta[k % L]++;
  for (int i = 0; i < L; i++) refresh(i);

  double T[MMAX + 1]; memset(T, 0, sizeof T);
  double big = 0, nsamp = 0, nmaj = 0, maxBg = 0, frac = 0, occSum = 0;
  double t = 0, next = burn;
  while (next <= burn + samp) {
    double rate = w * nOcc + nMul;
    t += -log(unif()) / rate;
    while (t > next && next <= burn + samp) {
      /* sample the state at time `next` */
      int p = occList[0];
      for (int k = 1; k < nOcc; k++) if (eta[occList[k]] > eta[p]) p = occList[k];
      if (2 * eta[p] > N) nmaj++;
      frac += (double)eta[p] / (double)N;
      occSum += nOcc;
      for (int k = 0; k < nOcc; k++) {
        int i = occList[k];
        if (i == p) continue;
        long a = eta[i];
        for (int m = 2; m <= MMAX && m <= a; m++) T[m]++;
        if (a >= 3) big += a;
        if (a > maxBg) maxBg = a;
      }
      nsamp++;
      next += 1.0;
    }
    if (next > burn + samp) break;
    int i, j;
    if (unif() * rate < w * nOcc) {
      i = occList[rng() % (uint64_t)nOcc];
      j = (i + 1 == L) ? 0 : i + 1;
      eta[i]--; eta[j]++;
    } else {
      i = mulList[rng() % (uint64_t)nMul];
      j = (i + 1 == L) ? 0 : i + 1;
      eta[j] += eta[i]; eta[i] = 0;
    }
    refresh(i); refresh(j);
  }
  printf("L=%d N=%ld w=%.3f samples=%.0f P(majority)=%.4f bigMass=%.4f maxBackgroundPile=%.0f largestFraction=%.4f occupied=%.4f\n",
         L, N, w, nsamp, nmaj / nsamp, big / nsamp, maxBg, frac / nsamp, occSum / nsamp);
  printf("T_m:");
  for (int m = 2; m <= MMAX; m++) printf(" %.4e", T[m] / nsamp);
  printf("\n");
  return 0;
}
