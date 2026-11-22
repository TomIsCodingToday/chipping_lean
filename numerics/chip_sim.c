/* Totally asymmetric chipping model on a ring, uniformized dynamics.
   Build: gcc -O2 -o chip_sim chip_sim.c
   Each unit of time performs L * (1 + w) site updates, so time is measured in
   the same units as the rates below.
   Site i: chip one particle to i+1 at rate w if eta_i >= 1;
           move the whole pile to i+1 at rate 1 if eta_i >= 2.
   usage: chip_sim L N w burn_time sample_time init(0=concentrated,1=uniform) seed
   Prints time averages of B/N, second largest/N, number of piles (>=2) other
   than one largest, number of singles, mass in non-largest piles of size >= 2. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static uint64_t s[2];
static inline uint64_t rng(void) {
  uint64_t s1 = s[0]; const uint64_t s0 = s[1];
  s[0] = s0; s1 ^= s1 << 23; s[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26);
  return s[1] + s0;
}
static inline double unif(void) { return (rng() >> 11) * (1.0 / 9007199254740992.0); }

int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage\n"); return 1; }
  int L = atoi(argv[1]); long N = atol(argv[2]); double w = atof(argv[3]);
  double burn = atof(argv[4]), samp = atof(argv[5]); int init = atoi(argv[6]);
  s[0] = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atol(argv[7]); s[1] = 0xD1B54A32D192ED03ULL;
  for (int k = 0; k < 20; k++) rng();
  long *eta = calloc(L, sizeof(long));
  if (init == 0) eta[0] = N; else for (long k = 0; k < N; k++) eta[k % L]++;
  double R = 1.0 + w;            /* max rate per site */
  long steps_per_unit = (long)(R * L);
  double sumB = 0, sumB2 = 0, sumSecond = 0, sumPiles = 0, sumSingles = 0, sumMultBg = 0, sumOcc = 0;
  long nsamp = 0;
  double total = burn + samp;
  long units = (long)total;
  for (long u = 0; u < units; u++) {
    for (long k = 0; k < steps_per_unit; k++) {
      int i = (int)(rng() % (uint64_t)L);
      long a = eta[i];
      if (a == 0) continue;
      double x = unif() * R;
      int j = (i + 1 == L) ? 0 : i + 1;
      if (x < w) { eta[i]--; eta[j]++; }
      else if (a >= 2) { eta[j] += a; eta[i] = 0; }
    }
    if (u >= (long)burn) {
      long m1 = 0, m2 = 0, piles = 0, singles = 0, multmass = 0, occ = 0;
      for (int i = 0; i < L; i++) {
        long a = eta[i];
        if (a > m1) { m2 = m1; m1 = a; } else if (a > m2) m2 = a;
        if (a >= 2) { piles++; multmass += a; }
        if (a == 1) singles++;
        if (a >= 1) occ++;
      }
      double B = (double)(N - m1) / N;
      sumB += B; sumB2 += B * B; sumSecond += (double)m2 / N;
      sumPiles += piles - 1; sumSingles += singles; sumMultBg += multmass - m1; sumOcc += occ;
      nsamp++;
    }
  }
  printf("L=%d N=%ld w=%.3f init=%d  E[B/N]=%.5f  sd=%.5f  E[M2/N]=%.5f  E[piles-1]=%.3f  E[singles]=%.3f  E[multBgMass]=%.3f  E[B]=%.3f  E[occ]=%.3f\n",
         L, N, w, init, sumB / nsamp, __builtin_sqrt(sumB2 / nsamp - (sumB / nsamp) * (sumB / nsamp)),
         sumSecond / nsamp, sumPiles / nsamp, sumSingles / nsamp, sumMultBg / nsamp,
         sumB / nsamp * N, sumOcc / nsamp);
  return 0;
}
