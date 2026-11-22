/* The generator of the window potential in stationary states.

   Phi = F1 + Psi, where F1 is the first moment in the frame of the largest
   pile and Psi sums the window weights of window_weights.py over background
   groups. A group is a maximal chain of background sites with consecutive
   offsets at most R apart. Groups within R of the peak, in front or behind,
   are attached to the peak and weigh 0. Groups of four or more particles
   weigh 0 too.

   At each sampled state, Q Phi is computed exactly by enumerating every move.
   For an isolated group g of at most three particles, every move of g is
   credited to g with the change of value it has for g alone, as in the linear
   program, which guarantees  d(g) + sum <= -c [g is a pile of 3]. What the
   move really changes beyond that is an interaction, put into one class:
     merge     the moved mass joins another isolated group (never positive);
     peak      the group is or becomes attached to the peak;
     big       a group of four or more particles is involved.
   Moves of the peak, of groups attached to it, and of big groups go wholly
   into the classes peak and big.
   Since E[Q Phi] = 0 in the stationary law,
     c E[#isolated piles of three] + E[slack] = E[peak] + E[big] + E[merge].

   Build: gcc -O2 -o window_terms window_terms.c -lm
   usage: window_terms L N table burn samp seed [every] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static uint64_t s[2];
static inline uint64_t rng(void) {
  uint64_t s1 = s[0]; const uint64_t s0 = s[1];
  s[0] = s0; s1 ^= s1 << 23; s[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26);
  return s[1] + s0;
}
static inline double unif(void) { return (rng() >> 11) * (1.0 / 9007199254740992.0); }

static int L, R; static long N; static double w, cfac;
static double V2P, V3T, *V3A, *V3B, *V3C;

static double depRate(long n) { return (n >= 1 ? w : 0) + (n >= 2 ? (double)n : 0); }

typedef struct { int k0, k1; long mass; int peakAtt; int nsites, nsingles; double V; int isT; } Chain;
typedef struct {
  int m; int *off; long *cnt; int *chainOf; int nch; Chain *ch; int *xch; int p;
} Groups;

static int argmax(const long *eta) { int p = 0; for (int i = 1; i < L; i++) if (eta[i] > eta[p]) p = i; return p; }

static double listValue(const int *off, const long *cnt, int k0, int k1, long mass);
static double chainValue(const Groups *G, int k0, int k1, long mass) {
  return listValue(G->off, G->cnt, k0, k1, mass);
}
/* The value of the sites of one group after moving amt from its site kk,
   counting only the group itself, with the same component rule. */
static double isolatedAfter(const Groups *G, int k0, int k1, int kk, long amt) {
  int off[8]; long cnt[8]; int n = 0;
  for (int k = k0; k <= k1; k++) {
    long c = G->cnt[k] - (k == kk ? amt : 0);
    if (c > 0) { off[n] = G->off[k]; cnt[n] = c; n++; }
    if (k == kk) {
      int o = G->off[k] + 1;
      if (k + 1 <= k1 && G->off[k + 1] == o) { off[n] = o; cnt[n] = G->cnt[k + 1] + amt; n++; k++; }
      else { off[n] = o; cnt[n] = amt; n++; }
    }
  }
  double v = 0; int a = 0;
  for (int k = 0; k < n; k++) {
    if (k == n - 1 || off[k + 1] - off[k] > R) {
      long m = 0; for (int j = a; j <= k; j++) m += cnt[j];
      v += listValue(off, cnt, a, k, m); a = k + 1;
    }
  }
  return v;
}
static double listValue(const int *off, const long *cnt, int k0, int k1, long mass) {
  int ns = k1 - k0 + 1;
  if (mass == 2) return ns == 1 ? V2P : 0.0;
  if (mass != 3) return 0.0;
  if (ns == 1) return V3T;
  if (ns == 2) {
    int d = off[k1] - off[k0];
    return cnt[k0] == 2 ? V3A[d] : V3B[d];
  }
  int a = off[k0 + 1] - off[k0], b = off[k1] - off[k0 + 1];
  return V3C[a * (R + 1) + b];
}

static void groups(const long *eta, Groups *G) {
  int p = argmax(eta); G->p = p; G->m = 0;
  for (int o = 1; o < L; o++) {
    int i = (p + o) % L; G->xch[o] = -1;
    if (eta[i] > 0) { G->off[G->m] = o; G->cnt[G->m] = eta[i]; G->m++; }
  }
  G->nch = 0;
  for (int k = 0; k < G->m; k++) {
    if (k == 0 || G->off[k] - G->off[k - 1] > R) {
      Chain c = {k, k, 0, 0, 0, 0, 0, 0}; G->ch[G->nch++] = c;
    }
    Chain *c = &G->ch[G->nch - 1];
    c->k1 = k; c->mass += G->cnt[k]; c->nsites++; if (G->cnt[k] == 1) c->nsingles++;
    G->chainOf[k] = G->nch - 1; G->xch[G->off[k]] = G->nch - 1;
  }
  for (int j = 0; j < G->nch; j++) {
    Chain *c = &G->ch[j];
    c->peakAtt = (j == 0 && G->off[c->k0] <= R) || (j == G->nch - 1 && L - G->off[c->k1] <= R);
    c->V = c->peakAtt ? 0.0 : chainValue(G, c->k0, c->k1, c->mass);
    c->isT = !c->peakAtt && c->mass == 3 && c->nsites == 1;
  }
}

static double psi(const Groups *G, double *psi3) {
  double t = 0, t3 = 0;
  for (int j = 0; j < G->nch; j++) { t += G->ch[j].V; if (G->ch[j].mass == 3) t3 += G->ch[j].V; }
  if (psi3) *psi3 = t3;
  return t;
}

static Groups newGroups(void) {
  Groups G; G.off = malloc(sizeof(int) * L); G.cnt = malloc(sizeof(long) * L);
  G.chainOf = malloc(sizeof(int) * L); G.ch = malloc(sizeof(Chain) * L); G.xch = malloc(sizeof(int) * L);
  return G;
}

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: window_terms L N table burn samp seed\n"); return 1; }
  L = atoi(argv[1]); N = atol(argv[2]);
  FILE *f = fopen(argv[3], "r"); if (!f) { perror(argv[3]); return 1; }
  if (fscanf(f, "%lf %d %lf", &w, &R, &cfac) != 3) return 1;
  V3A = calloc(R + 2, sizeof(double)); V3B = calloc(R + 2, sizeof(double));
  V3C = calloc((R + 2) * (R + 2), sizeof(double));
  char line[512];
  while (fgets(line, sizeof line, f)) {
    int v[8], n = 0; char *q = line; double val;
    char *colon = strchr(line, ':'); if (!colon) continue;
    *colon = 0; val = atof(colon + 1);
    while (n < 8 && sscanf(q, "%d", &v[n]) == 1) { n++; while (*q == ' ') q++; while (*q && *q != ' ') q++; }
    if (n == 2 && v[1] == 2) V2P = val;
    else if (n == 2 && v[1] == 3) V3T = val;
    else if (n == 4 && v[1] == 2) V3A[v[2]] = val;
    else if (n == 4 && v[1] == 1 && v[3] == 2) V3B[v[2]] = val;
    else if (n == 6) V3C[v[2] * (R + 1) + (v[4] - v[2])] = val;
  }
  fclose(f);
  double burn = atof(argv[4]), samp = atof(argv[5]);
  s[0] = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atol(argv[6]); s[1] = 0xD1B54A32D192ED03ULL;
  for (int k = 0; k < 20; k++) rng();
  long every = argc > 7 ? atol(argv[7]) : 1;
  long *eta = calloc(L, sizeof(long)), *eta2 = calloc(L, sizeof(long));
  for (long k = 0; k < N; k++) eta[k % L]++;
  double Rt = 1.0 + w; long steps = (long)(Rt * L);
  Groups G = newGroups(), H = newGroups();
  double *intl = malloc(sizeof(double) * L);
  double nsamp = 0, nmaj = 0, sumT = 0, sumIntl = 0, sumSlack = 0, sumMerge = 0;
  double sumPeakF1 = 0, sumPeakUp = 0, sumPeakDown = 0, sumPeak3Up = 0, sumPeak3Down = 0;
  double sumBigF1 = 0, sumBigUp = 0, sumBigDown = 0, sumBig3Up = 0, sumBig3Down = 0;
  double sumQ = 0, sumQ2 = 0, sumPsi = 0, viol = 0, mism = 0, worstViol = 0, sumBigGroups = 0, sumGroups3 = 0;
  for (long u = 0; u < (long)(burn + samp); u++) {
    for (long k = 0; k < steps; k++) {
      int i = (int)(rng() % (uint64_t)L); long a = eta[i];
      if (a == 0) continue;
      double x = unif() * Rt; int j = (i + 1 == L) ? 0 : i + 1;
      if (x < w) { eta[i]--; eta[j]++; } else if (a >= 2) { eta[j] += a; eta[i] = 0; }
    }
    if (u < (long)burn || u % every) continue;
    nsamp++;
    groups(eta, &G);
    if (2 * eta[G.p] <= N + 2) continue;
    nmaj++;
    double ps3; double ps = psi(&G, &ps3); sumPsi += ps;
    double peakF1 = w - L * depRate(eta[(G.p + L - 1) % L]), bigF1 = 0, merge = 0;
    double pUp = 0, pDown = 0, p3Up = 0, p3Down = 0, bUp = 0, bDown = 0, b3Up = 0, b3Down = 0;
    for (int j = 0; j < G.nch; j++) {
      Chain *c = &G.ch[j]; double d = w * c->nsites - c->nsingles;
      if (c->peakAtt) peakF1 += d; else if (c->mass >= 4) { bigF1 += d; sumBigGroups++; }
      else { intl[j] = d; if (c->mass == 3) sumGroups3++; }
    }
    /* moves: the peak, then every background site */
    for (int k = -1; k < G.m; k++) {
      int o = k < 0 ? 0 : G.off[k]; int i = (G.p + o) % L; long a = eta[i];
      for (int mv = 0; mv < 2; mv++) {
        long amt = mv == 0 ? 1 : a; double rate = mv == 0 ? w : 1.0;
        if (mv == 1 && a < 2) continue;
        memcpy(eta2, eta, sizeof(long) * L);
        eta2[i] -= amt; eta2[(i + 1) % L] += amt;
        groups(eta2, &H);
        double qs3; double dpsi = psi(&H, &qs3) - ps, dpsi3 = qs3 - ps3;
        int cls; /* 0 internal 1 merge 2 peak 3 big */
        int g = k < 0 ? -1 : G.chainOf[k];
        if (k < 0 || G.ch[g].peakAtt || o == L - 1) cls = 2;
        else {
          if (H.p != G.p) { fprintf(stderr, "peak moved on a background move\n"); return 1; }
          int g2 = H.xch[o + 1];
          if (H.ch[g2].peakAtt) cls = 2;
          else if (G.ch[g].mass >= 4 || H.ch[g2].mass >= 4) cls = 3;
          else {
            cls = 0;
            for (int kk = H.ch[g2].k0; kk <= H.ch[g2].k1; kk++) {
              int oo = H.off[kk];
              if (G.xch[oo] >= 0 && G.xch[oo] != g) { cls = 1; break; }
            }
          }
        }
        double r = rate * dpsi, r3 = rate * dpsi3;
        if (k >= 0 && !G.ch[g].peakAtt && G.ch[g].mass <= 3) {
          double dlp = isolatedAfter(&G, G.ch[g].k0, G.ch[g].k1, k, amt) - G.ch[g].V;
          intl[g] += rate * dlp;
          if (cls == 0) { if (fabs(dpsi - dlp) > 1e-9) mism++; continue; }
          r -= rate * dlp;
          if (G.ch[g].mass == 3) r3 -= rate * dlp;
        }
        if (cls == 0) intl[g] += r;
        else if (cls == 1) merge += r;
        else if (cls == 2) { if (r > 0) pUp += r; else pDown += r; if (r3 > 0) p3Up += r3; else p3Down += r3; }
        else { if (r > 0) bUp += r; else bDown += r; if (r3 > 0) b3Up += r3; else b3Down += r3; }
      }
    }
    double intlTot = 0, slack = 0, nT = 0;
    for (int j = 0; j < G.nch; j++) {
      Chain *c = &G.ch[j];
      if (c->peakAtt || c->mass >= 4) continue;
      double e = intl[j] + (c->isT ? cfac : 0);
      if (e > 1e-7) { viol++; if (e > worstViol) worstViol = e; }
      intlTot += intl[j]; slack -= e; nT += c->isT;
    }
    double Q = intlTot + merge + peakF1 + pUp + pDown + bigF1 + bUp + bDown;
    sumT += nT; sumIntl += intlTot; sumSlack += slack; sumMerge += merge;
    sumPeakF1 += peakF1; sumPeakUp += pUp; sumPeakDown += pDown; sumPeak3Up += p3Up; sumPeak3Down += p3Down;
    sumBigF1 += bigF1; sumBigUp += bUp; sumBigDown += bDown; sumBig3Up += b3Up; sumBig3Down += b3Down;
    sumQ += Q; sumQ2 += Q * Q;
  }
  double n = nmaj;
  double meanQ = sumQ / n, seQ = sqrt((sumQ2 / n - meanQ * meanQ) / n);
  printf("w=%g R=%d c=%.4f L=%d N=%ld  majority %.0f/%.0f samples\n", w, R, cfac, L, N, nmaj, nsamp);
  printf("  E[#isolated piles of three] %.5f   c times it %.5f   E[#isolated groups of three] %.5f\n",
         sumT / n, cfac * sumT / n, sumGroups3 / n);
  printf("  E[#groups of four or more] %.5f   E[Psi] %.3f\n", sumBigGroups / n, sumPsi / n);
  printf("  internal %.5f  (slack %.5f)   merge %.5f   drift-check violations %.0f (worst %.2e),"
         " bookkeeping mismatches %.0f\n", sumIntl / n, sumSlack / n, sumMerge / n, viol, worstViol, mism);
  printf("  peak: F1 %.5f  jumps up %.5f  down %.5f  [weights of three: up %.5f down %.5f]\n",
         sumPeakF1 / n, sumPeakUp / n, sumPeakDown / n, sumPeak3Up / n, sumPeak3Down / n);
  printf("  big:  F1 %.5f  jumps up %.5f  down %.5f  [weights of three: up %.5f down %.5f]\n",
         sumBigF1 / n, sumBigUp / n, sumBigDown / n, sumBig3Up / n, sumBig3Down / n);
  printf("  E[Q Phi] %.5f +- %.5f (should vanish)\n", meanQ, seQ);
  return 0;
}
