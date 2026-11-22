# Chipping model in Lean

This project extends the Lean baseline extracted from
[ChippingProofStarter.md](ChippingProofStarter.md). Lean and mathlib are pinned
to v4.19.0, matching the starter. Git has been initialized locally.

## Windows setup

From this directory, run in PowerShell with network access:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\Setup-Lean.ps1
```

The script installs Elan and Lean under `.tools/elan` in this project without
changing the system PATH. Lake fetches mathlib and its transitive repositories
under `.lake/packages`, downloads precompiled mathlib files, and builds the
baseline. No separate Lean source checkout is needed. Keep `lake-manifest.json`
in Git once Lake generates it; it locks the dependency commits.

For subsequent sessions:

```powershell
. .\scripts\Enter-Lean.ps1
lake build
lake env lean ChippingSupercondensation\PileBirths.lean
```

`lake build` rechecks only the modules that changed and the modules that
import them. `lake env lean` checks one module against the compiled modules it
imports, so run `lake build` first after editing an earlier module.

The numerical checks in `numerics/` need a C compiler and Python 3:

```powershell
gcc -O2 -o chip_sim numerics\chip_sim.c
.\chip_sim 400 400 0.2 320000 1280000 1 7
python numerics\exact_small_rings.py
```

The simulator arguments are the ring size, the particle number, `w`, the
burn-in time, the averaging time, the initial state (0 for one pile, 1 for a
uniform spread) and a seed.

`numerics/cluster_stats.c` takes the same arguments without the initial-state
flag and reports the cluster statistics described in the assessment below.
`numerics/anchor_rules.c` takes the ring size, the particle number, `w`, the
burn-in and averaging times, a sampling interval and a seed, and compares the
two anchor rules discussed there.

`numerics/window_weights.py` needs scipy. `python numerics\window_weights.py
0.2 8 --maxc2 --verify --dump V.txt` solves for the window weights described
in the assessment, checks them in exact rational arithmetic and writes them to
`V.txt`. `numerics/window_terms.c` takes the ring size, the particle number,
that file, the burn-in and averaging times, a seed and a sampling interval, and
measures the terms of the stationary identity for those weights.

## Module layout

The development is split into twelve modules under `ChippingSupercondensation/`.
The root `ChippingSupercondensation.lean` imports all of them, so
`import ChippingSupercondensation` still provides every declaration. Add any
new module to that import list so that `lake build` checks it.

| Module | Imports | Contents |
|---|---|---|
| `Model` | mathlib | The starter baseline with its declarations unchanged: states, moves, the generator, `StationaryLaw`, `backgroundFraction`, `tails_vanish_iff_mean_vanishes`, `SupercondensesAt`, `SmallWSupercondensation` |
| `Basic` | `Model` | Helper lemmas shared by later modules: `right_ne_self`, `right_eq_add_one`, occupancies after a move, the chip and whole-pile transitions, eventual positivity of the total mass |
| `Stationary` | `Basic` | Particle separation `H` and `B/N ≤ H ≤ 2B/N`; existence, uniqueness and rotation invariance of stationary laws; reduction of `SupercondensesAt` to `E[H] → 0` |
| `Identities` | `Stationary` | Occupied-site balance, squared mass balance, window identities, directional balance |
| `LargestPile` | `Identities` | Drift of the largest pile, majority pile tracking, cutoff flows and level crossings |
| `Background` | `LargestPile` | Occupied pairs, occupied density, multiple background mass, capped mass, threshold pairs |
| `Coalescence` | `Identities` | Large-pile masks, coalescence drift at a selected cutoff, the empty-window potential, two large piles bounded by birth damage |
| `PileBirths` | `Background`, `Coalescence` | Competing birth damage, the gap product, nearby chip births, and `stationary_twoLargePilesProbability_le_wholeAndDistantChipBirthDamage` |
| `PeakFrame` | `LargestPile` | Exact drift of any offset-weighted background moment in the frame of a majority pile; the stationary balance of singles against the chip rate and the inflow into the peak from behind |
| `Clusters` | `PeakFrame` | Piles together with the singles they will sweep, as clusters in the frame of a majority pile; the exact drift of anchor-weighted moments, to which only exceptional chips contribute |
| `PileCount` | `PeakFrame` | The exact balance of the number of piles; piles of two are at most `w` times the occupied sites, and the background reduces to piles of three or more |
| `MassThree` | `Clusters`, `PileCount` | Cluster masses under whole moves and trivial chips; the exact drift of state-dependent weights for clusters of mass three |

`Coalescence` does not depend on `LargestPile` or `Background`, and
`PeakFrame` depends only on `LargestPile`, so Lake can build these in parallel.
The split moved declarations without changing any statement or proof. Eighteen
helpers used across modules, such as `right_eq_add_one` and `chipOrStay`, are no
longer `private`. Lean reports the same 336 declarations, with the same
statements and axioms, as the single file did before the split. `PeakFrame`,
`Clusters`, `PileCount` and `MassThree` later added 176 declarations, and 18
existing helpers, among them `occ_move_delta`, became public. No earlier
statement changed.

## Review and proof status

Each item names the module that contains it.

- (`Model`) `SmallWSupercondensation` is a proposition definition, not a proved
  theorem. The required statement has one positive rate threshold valid for
  every positive density, with the rate held fixed as ring size grows.
- (`Model`) The code represents configurations with exactly N particles. Its
  generator implements rightward chips at rate w and whole-pile moves at rate
  one only from sites of mass at least two, consistent with the rate table.
- (`Model`) The baseline includes mass conservation and the tail/mean
  equivalence. Those estimates use positivity and normalization of the weights;
  the thermodynamic estimate still needs a substantive use of stationarity.
- (`Stationary`) `stationaryLaw_exists` proves that every nonempty ring has a
  stationary law at every nonnegative rate. It builds a discrete transition from
  the original jump clocks and takes a limit of averaged probability vectors.
  `supercondensesAt_iff_meanParticleSeparation_tendsto_zero` then reduces
  `SupercondensesAt` at positive density to the limit of the stationary mean of
  `H` along the same sequences of rings.
- (`Stationary`) At positive rates, `stationaryLaw_eq` proves uniqueness by
  showing that every nonempty set closed under chipping contains the
  configuration with all mass at site zero. The law is rotation invariant by
  `stationaryWeight_rotateState`, so a stationary correlation summed around the
  ring equals the number of sites times the correlation measured from any one
  site. The limiting claim can be stated using only `equilibrium`, the unique
  stationary law on each ring.
- (`Identities`) Section 3 is now proved: `occupied_site_balance` establishes
  `QK = wD - wA - C`, and `stationary_occupied_site_balance` establishes
  `w E[D] = w E[A] + E[C]`. Both use the existing moves and generator on rings
  with at least three sites, including the wraparound bond. No `sorry` or
  additional axioms were introduced.
- (`Stationary`) Section 4's comparison is proved in
  `backgroundFraction_le_particleSeparation_le_twice`. For positive total mass,
  `particleSeparation` is the probability `H` that two particles sampled with
  replacement lie at different sites, and Lean verifies `B/N ≤ H ≤ 2B/N`.
  `tails_vanish_iff_meanParticleSeparation_vanishes` makes convergence of the
  stationary mean of `H` to zero equivalent to vanishing background tails along
  sequences with eventually positive total mass.
- (`Identities`) `squaredMass_move` proves the exact change in the sum of
  squared masses from any transfer. `stationary_squared_mass_balance` balances
  the chip and whole pile contributions. This gives the bound
  `meanAdjacentMassProduct_le`, which controls the sum of neighbouring mass
  products by `(w + 1) * N` in expectation. The expected sum divided by `N^2`
  tends to zero when the total mass grows at fixed rate.
- (`Identities`) For any nonzero clockwise offset `r`, the squared masses of
  windows of length `r` give an exact stationary identity in
  `stationary_massProductAt_eq`. For `0 ≤ w ≤ 1`,
  `normalized_stationary_massProductAt_bounds` bounds the probability of that
  offset by `(r + 1) / N`. The combined probability of offsets from one through
  `R < L` is at most `R * (R + 1) / N`.
  `particleSeparation_eq_nonzeroOffsetProbability` expresses `H` as the sum over
  every nonzero offset. The bound controls offsets up to `R = o(sqrt(N))`
  together.
- (`Identities`) Summing the stationary window identities over every nonzero
  offset gives `stationary_particleSeparation_directional_balance`. Write `J`
  for the expected signed rate correction from mass ahead of and behind
  departures, divided by `(L - 1) * N`. The exact balance is
  `w - J = w * E[K]/N + N/(L - 1) * E[H]`. Since an occupied site outside a
  largest pile contains at least one background particle,
  `directional_deficit_bounds` controls the right side above and below by
  multiples of `E[H]` up to an error `w/N`. At fixed positive density the limit
  `E[H] → 0` is therefore equivalent to `J → w`. Proving this convergence at
  sufficiently small fixed rates is open.
- (`LargestPile`) The largest pile itself gives a separate drift estimate. Whole
  pile moves cannot reduce it, and at most one site can chip in a way that
  reduces it. `stationary_mass_ahead_of_largest_above_le` bounds the stationary
  mean mass immediately ahead of a largest pile by `w`, even conditional on the
  largest mass exceeding any cutoff of at least one. The conditional tail at a
  positive threshold `a` is at most `w/a`. This controls one neighbouring site
  in the frame of a largest pile.
- (`LargestPile`) For a pile with a majority that survives any single chip, Lean
  tracks its position through each jump and computes the drift of a block ahead
  of it. Write `a_r` for the mass at offset `r` from the peak, and `q(a)` for
  the expected mass sent clockwise per unit time by a site of mass `a`.
  `stationary_majority_successive_flow_le` shows that the stationary mean of
  `q(a_r) - a_(r+1) - q(a_(-1))`, restricted to `M > t > N/2`, has absolute
  value at most `w * (N - t) * P(M = t + 1)`. The bound applies to all
  successive offsets ahead of the peak before wraparound. The recurrence leaves
  open how to control the total background mass and how much stationary
  probability lies outside the majority region.
- (`LargestPile`) `stationary_majority_cutoff_flow_eq` identifies the stationary
  entry rate into `M > t > N/2` exactly as `w * P(M = t + 1)`. Entry comes from
  chips into mass `t` or whole pile merges that cross the cutoff. For any band
  of majority cutoffs `a ≤ t ≤ b`, `exists_majority_cutoff_with_small_error`
  gives one cutoff with boundary weight bounded by
  `P(a < M ≤ b + 1) / (b + 1 - a)`. This controls the entry rate and the error
  for every offset at that cutoff. A further level-crossing bound valid at any
  cutoff shows `P(M = m, a_1 ≥ d) ≤ w * P(M = m + d)` for `m ≥ 2` and `d ≥ 1`.
- (`Background`) A chip can bring two occupied sites closer. Stationarity bounds
  the expected number of occupied pairs at each fixed offset by a constant times
  the expected number of multiple sites. Window packing then proves
  `occupiedDensity_tendsto_zero_of_multipleDensity_tendsto_zero`, with no
  assumption that a majority pile exists. At positive limiting density,
  `tails_vanish_iff_multipleBackgroundMass_tendsto_zero` reduces the original
  tail limit to showing that the expected mass on background sites of size at
  least two, divided by total mass, tends to zero.
- (`Background`) Capping each site's mass at `k` gives the exact
  `stationary_cappedMass_balance`. The stationary rate of mergers that create a
  pile above `k` from two piles at or below `k` is at most
  `w * E[number of sites above k]`. For adjacent pairs both at least `k ≥ 2`,
  the expected count is bounded by that same quantity divided by `k + w`. Whole
  pile moves propagate the latter bound to larger offsets with a geometric
  factor. The pair mass estimate also rules out any pair of macroscopic piles
  within `o(sqrt(N))` sites with high probability for `0 ≤ w ≤ 1`. Farther pairs
  and the aggregate mass of smaller background piles remain uncontrolled.
- (`Coalescence`) The set of sites above a mass cutoff follows the rate-one
  clockwise coalescing update, except for chips that cross the cutoff and
  mergers of two smaller piles that create a large one. Summing the expected
  exception rate over cutoffs from `a` through `b` costs at most
  `4 * w * N / a`. If `a ≥ αN` and the band contains at least `βN` cutoffs, one
  cutoff has mean coalescence drift at most `4 * w * C / (α * β * N)` in
  absolute value for every test with oscillation at most `C`. The same cutoff
  works for all tests, including along sequences with `C = o(N)`. This
  establishes small mean drift for the large-pile locations. It leaves open
  their behavior over the times needed for distant piles to meet.
- (`Coalescence` and `PileBirths`) Under pure coalescence, the drift of the
  empty-window count is the discrete second difference in the window length.
  Summing over all proper window lengths gives drift at least two whenever there
  are at least two large piles.
  `stationary_twoLargePilesProbability_le_competingBirthDamage` bounds twice the
  stationary probability of this event, at any separation, by the rate of births
  above the cutoff weighted by the empty windows they erase. The first large
  pile and downward cutoff crossings require no error budget. A birth
  immediately clockwise of an existing large pile erases at most `L - 1`
  windows.
- (`PileBirths`) For a birth between consecutive marks,
  `competingBirthDamage_eq_gap_product` gives the exact weight `p * q`, where
  `p` and `q` are the distances to the nearest marks on either side. The formula
  includes wraparound and the case where both distances lead to the same pile.
- (`PileBirths`) For `0 ≤ w ≤ 1`, choose a band of cutoffs with lower edge at
  least `αN` and width at least `βN`, for fixed positive `α` and `β`. At some
  cutoff in the band, the stationary weighted rate of chip births within `R < L`
  sites of an existing mark is at most `(w / (α³ β)) (L/N) R²(R+1)/N`. Each
  receiving pile has exactly the cutoff mass for at most one cutoff in the band.
  A nearby birth also requires two piles already at or above the lower edge.
  `exists_threshold_nearbyChipBirthDamage_tendsto_zero` therefore removes this
  contribution at positive limiting density for `R = o(N^(1/3))`.
  `stationary_twoLargePilesProbability_le_wholeAndDistantChipBirthDamage` bounds
  the probability of two piles above the prescribed upper edge using that error
  and the weighted rate of whole-pile births and distant chip births at the
  selected cutoff. Those rates and the total mass in smaller background piles
  remain open.
- (`PeakFrame`) Offsets are measured clockwise from the selected peak. While
  the peak holds `N + 2 < 2M`, no jump moves it except its own whole move.
  `generator_peakFrameMoment_eq` gives the exact drift of
  `∑ j, h (offset j) * η j` for every profile `h` with `h 0 = 0`.
  `stationary_peakFrameDrift_majority_le` states the stationary version on
  `M > t > N/2`, with error `w * max h * (N - t) * P(M = t + 1)`. The profile
  `h s = s` has drift `w K - S - L q`, where `S` counts singles and `q` is the
  mass rate into the peak from the site behind it
  (`peakFrameDrift_firstMoment`). Hence `E[S] + L E[q] ≤ w E[K]` on the
  majority region up to that error (`stationary_peak_singles_rear_flux_le`).
  The site behind the peak is then occupied with probability at most
  `(E[K] + error / w) / L` (`stationary_peak_rear_occupied_le`).
  `exists_majority_cutoff_singles_rear_flux_le` selects a cutoff whose error is
  `w (L - 1) E[N - M + 1]` divided by the band width, of order
  `w E[B + 1] / ρ` for a band of width proportional to `N`.
- (`Clusters`) The anchor of an offset is the nearest offset at or behind it
  holding at least two particles, so a background pile and the singles ahead of
  it form a cluster. For any profile `h` with `h 0 = 0`, `clusterMoment h`
  weights each particle by `h` at its anchor's offset.
  `generator_clusterMoment_eq` gives its exact drift in the majority frame: each
  background cluster contributes its mass times the second difference of `h` at
  its pile, plus `w` times the change from chips. Chips into an empty site from
  a site not holding exactly two particles change no cluster
  (`clusterChipChange_eq_zero`). Only chips that land on an occupied site,
  dissolve a pile of two, or enter the peak from behind contribute
  (`sum_clusterChipChange_eq_exceptional`). The chip-and-reabsorb cycle, which
  makes uncoarsened moments cost order `w L` per occupied site, therefore costs
  nothing. `stationary_clusterDrift_majority_le` is the stationary version. For
  the linear profile, piles enter the peak from behind only as fast as
  exceptional chips push anchored mass forward
  (`stationary_cluster_linear_balance`).
- (`Clusters`) `seqMoment_chip` and `seqMoment_entry_chip` compute every chip
  exactly, and `clusterChipChange_eq` identifies the ring version. Each change
  is a forward gain minus a loss. The gain (`seqChipGain`) comes from chips onto
  occupied sites. It moves the chipped particle from the source's anchor `A` to
  the target and, when the target becomes a pile, also the forward mass `F` of
  the source's cluster. For a nondecreasing profile the loss (`seqChipLoss`) is
  nonnegative. It comes from piles of two that dissolve, returning their
  cluster to the previous anchor, and from mass entering the peak.
  `stationary_cluster_balance_le` bounds curvature plus loss by the gain, up to
  the cutoff error. Write `G` for the stationary mean on the majority region of
  `∑ (s + 1 - A) (1 + F)` over chips onto occupied sites. With the linear
  profile, `stationary_dissolution_le` bounds `L` times the mass of piles
  entering the peak from behind, plus `w` times the sum over piles of two with
  an empty site ahead of their cluster mass times their distance to the
  previous anchor, by `w G`. With a capped concave profile,
  `stationary_nearClusterMass_le` bounds the mass of clusters anchored within
  `R` of the peak by `w R G`. Both hold up to the cutoff error.
  `stationary_clusterChipGain_le` splits `G`: the peak's chips contribute at
  most `w (P(M > t) + E[K])`, by the background mass identity and the singles
  balance, and only the gain of chips from background sites remains.
- (`PileCount`) A chip onto a single creates a pile of two, a chip from a pile
  of two destroys one, and a whole move onto a pile merges two piles.
  `stationary_pile_count_balance` is the exact identity
  `w E[#piles of two] + E[#pile-pile bonds] = w E[#occupied-single bonds]`.
  Every single has at most one occupied site behind it, so with the singles
  balance `stationary_twoCount_majority_le` bounds the piles of two by
  `w E[K]` on the majority region, up to the cutoff errors. The occupied sites
  split into singles, piles of two and piles of three or more.
  `stationary_backgroundMass_le_big` therefore shows for `w < 1/2` that the
  background mass on the majority region is at most `(1 - w)/(1 - 2w)` times
  the background mass in piles of three or more, plus `3w/(1 - 2w)` times the
  probability of the region, up to the cutoff errors.
- (`PileCount`) `generator_firstMoment_add_twoCount` adds `1/w` per pile of two
  to the fine first moment of `PeakFrame`. Every term of its exact drift is a
  count, with no factor of `L` except the inflow from behind. Singles drift
  towards the peak at rate one, which pays for the debris left by a dissolving
  pile. `stationary_pricedPiles_le` turns this into a bound on piles of two
  next to other mass: the bonds from a pile of two to an occupied site and from
  a pile to a pile of two, including a pile of two just ahead of the peak,
  number at most `w` times the piles of three plus `w²` times the singles and
  the piles of three or more, up to the cutoff errors.
- (`MassThree`) A cluster mass is the cluster moment of the indicator of its
  anchor (`seqClusterMass_eq_seqMoment`), so the lemmas of `Clusters` track
  cluster masses. A whole move carries a cluster one step or merges it with
  the cluster ahead (`seqClusterMass_pile_move`). A whole move of the peak
  lowers every cluster by one offset (`seqClusterMass_shift`). A trivial chip
  changes no cluster mass (`seqClusterMass_trivial_chip`). The class weight is
  `B₁` for a bare pile of three and `B₂` for a pile of two with one single in
  its cluster. `generator_massThreePotential_eq` gives the exact drift of the
  total class weight on the majority region. Whole moves enter explicitly, and
  chips through `massThreeChipChange`, which `massThreeChipChange_trivial`
  computes for trivial chips. `generator_massThreeLyapunov_eq` adds the first
  moment and the price `1/w` of piles of two.
- (`MassThree`) `seqClusterMass_chip` gives the cluster masses after any chip.
  Six lemmas evaluate the class-weight change of every chip that is not
  trivial: a pile of two dissolving (`seqMassThreePotential_dissolve`), a
  pile of two shedding onto its single (`seqMassThreePotential_shed`), a pile
  of three or more chipping onto a pile or a single, and a single chipping onto
  a pile or a single. `massThreeChipChange_eq_seq` transfers them to the ring.
  A dissolving pile of two never adds class weight
  (`seqMassThreePotential_dissolve_le`).

## Assessment of the remaining problem

This section records numerical evidence and an assessment of the open routes.
It is not part of the checked development.

**Numerics.** `numerics/chip_sim.c` simulates the exact dynamics.
`numerics/exact_small_rings.py` solves for the stationary law on rings with at
most six sites. The table gives time averages at density one, after a burn-in of
`2L²` time units and averaging over `8L²` more.

| `w` | `E[B]` at `L` = 100 / 200 / 400 / 800 |
|---|---|
| 0.1 | 0.23 / 0.20 / 0.24 / 0.23 |
| 0.2 | 0.66 / 0.77 / 1.21 / 1.09 |
| 0.3 | 1.8 / 4.0 / 3.7 / 3.3 |
| 0.4 | 5.6 / 7.9 / 12.4 / 12.9 |
| 0.5 | 10.5 / 28.7 / 42.8 / 122.6 |
| 1.0 | 73 / 162 / 348 / – |

For `w ≤ 0.4` the mean background stays bounded as `L` grows, so `B/N` decays
like `1/L`. This is stronger than the conjecture requires. At `w = 0.5` the
background grows roughly in proportion to `L`, and at `w = 1` most mass is in
the background. At density one the threshold `w₀` therefore lies between `0.4`
and `0.5`. The runs at `w = 0.5` fluctuate strongly, so that row is less
reliable. In every condensed run `E[S]` agrees with `w E[K]` to within a few
percent, as the first-moment identity predicts when little mass reaches the
peak from behind.

**The two-large-piles route.** The open terms in
`stationary_twoLargePilesProbability_le_wholeAndDistantChipBirthDamage` include
distant chip births. Such a birth is a chip into a macroscopic pile holding
exactly the cutoff mass, while another macroscopic pile lies far away. Its
gap-product weight can reach `L²/4`. Averaging over a band of `βN` cutoffs
divides the crossing rate only by `βN`. The bound
`w L² / (4 βN)` grows like `N` at fixed density. Making the term small along
this route needs, roughly, that the site behind such a pile is occupied with
probability `O(1/L)`. That is a statement about mass travelling around the
ring to reach a pile from behind.
`stationary_peak_rear_occupied_le` proves a statement of this kind for the
largest pile in the majority region. It does not yet reach a second pile.

**Clusters.** `numerics/cluster_stats.c` measures clusters, as defined in
`Clusters`, in states where one pile holds a majority. In every run listed below
one pile held a majority with margin at every sampled time. The expected number
of background clusters of total mass `m` is:

| `w` | `L` | `m` = 2 | 3 | 4 | 5 | 6 | total cluster mass |
|---|---|---|---|---|---|---|---|
| 0.1 | 800 | 0.027 | 0.009 | 0.006 | 0.002 | 0.002 | 0.14 |
| 0.2 | 200 | 0.065 | 0.038 | 0.018 | 0.011 | 0.006 | 0.51 |
| 0.2 | 800 | 0.070 | 0.039 | 0.024 | 0.016 | 0.011 | 0.72 |
| 0.3 | 800 | 0.130 | 0.088 | 0.061 | 0.042 | 0.032 | 2.76 |

The counts fall roughly geometrically in `m`, by a factor near `0.6` per unit
at `w = 0.2` and near `0.7` at `w = 0.3`. That is much slower than the factor
`w` expected if clusters grew only through repeated chips, so clusters also
grow by sweeping singles and by merging. At `w = 0.2` the counts at `L = 200`
and `L = 800` are close for `m ≤ 3` and somewhat larger at `L = 800` beyond,
while the total cluster mass stays below one. These runs have no error bars,
so longer runs are needed to decide whether the counts converge as `L` grows.
The mean offset of cluster mass grows with `L`, so a small number of
long-lived clusters travel far from the condensate.

**The forward gain.** The simulator also measures `G` and the dissolution
sum `D₂` appearing in `stationary_dissolution_le`, at `L = 800`:

| `w` | `G` | from the peak | from singles | from piles | `D₂` |
|---|---|---|---|---|---|
| 0.1 | 0.30 | 0.18 | 0.12 | 0.004 | 0.29 |
| 0.2 | 0.85 | 0.35 | 0.46 | 0.036 | 0.78 |
| 0.3 | 2.45 | 0.51 | 1.75 | 0.19 | 2.23 |

`G` stays of order one, and `D₂` nearly exhausts it, so the dissolution bound
is close to tight. At `L = 400`, at least 95 percent of the singles' part
comes from chips of one single onto another. A pile of two that chips into an
empty site leaves two adjacent singles. A chip between them rebuilds the pile
one site further on. This cycle adds almost equally to the gain and to the
loss, so bounding `G` on its own is the wrong target.

**Anchoring at pairs of singles.** Anchoring clusters also at the first of
two adjacent singles was meant to remove the dissolution cycle.
`numerics/anchor_rules.c` compares, under both rules, the rates of gain and
of loss of the linear cluster moment from chips, that is `w` times the gain
and loss of `stationary_dissolution_le`, at `L = 200`:

| `w` | gain, piles only | loss, piles only | gain, with pairs | loss, with pairs |
|---|---|---|---|---|
| 0.1 | 0.029 | 0.030 | 0.024 | 0.011 |
| 0.2 | 0.197 | 0.216 | 0.153 | 0.103 |
| 0.3 | 0.581 | 0.701 | 0.487 | 0.318 |

The gain falls by only about a fifth. The two singles left by a dissolving
pile each hop at rate `w`, so their gap performs a recurrent walk and they
keep becoming adjacent and separating again, each time creating or removing an
anchor. Debris is better paid for by the fine first moment, in which every
single drifts towards the peak at rate one.

**Window weights.** A group is a maximal chain of background sites in which
consecutive occupied sites are at most `R` apart. Groups within `R` of the
peak are attached to it. `numerics/window_weights.py` keeps the proven weights
for groups of two, `1/w` for a pile of two and nothing for two singles, and
solves a linear program for weights on all configurations of three particles
in a window. Every group of three then has drift at most `-c` if it is a bare
pile of three and at most `0` otherwise, counting the first-moment drift
`w K - S` of the group. No merge of two groups raises the potential, and all
weights are nonnegative, so absorption by the peak never raises it either.
The weights below were rounded and every constraint was checked in exact
rational arithmetic, with slack `10⁻⁴`.

| `w` | `R` | largest `c` | weight of a bare pile of three |
|---|---|---|---|
| 0.1 | 16 | 0.63 | 73.5 |
| 0.2 | 8 | 0.98 | 33.5 |
| 0.3 | 8 | 2.00 | 35.6 |

The largest `c` grows with `R`, because the debris of a group lingers inside a
larger window and its singles pay `1 - w` each per unit time. The obstruction
found for the class weights of `MassThree` is therefore gone. The weights are
sparse. Nonzero weights sit only on:

- the bare pile of three;
- a pile of two with a single at distance `d` ahead, decreasing in `d` to `1/w`
  at `d = R`;
- a single just behind a pile of two;
- two adjacent singles with a third single ahead, the debris that re-forms a
  pile and sweeps the third single.

Three singles with no two adjacent weigh nothing. With `c = 1/2` fixed and the
smallest weights, `w²` times the weight of the bare pile of three is `0.55`,
`0.58`, `0.68` and `0.86` at `w = 0.05`, `0.1`, `0.2`, `0.3`. The weight of a
pile of two with a single at distance `d` ahead falls by a factor close to
`1/(1 + w)` per site, the chance that the pile reaches the single before it
chips. The weight of the adjacent pair with a single ahead is about half of it.
This suggests closed forms in `w`, which a proof valid for every small `w`
needs.

`numerics/window_terms.c` computes the generator of the potential
`F₁ + Ψ` exactly at sampled stationary states, where `Ψ` sums these weights
over the groups that are not attached to the peak, and groups of four or more
particles weigh nothing. It credits each move of an isolated group of at most
three particles with the change it makes for that group alone, and books the
rest under the peak, under groups of four or more, or under merges. In every
sampled state, every isolated group satisfied the drift inequality of the
linear program, and merges were never positive. Since `E[Q(F₁ + Ψ)] = 0`, the
stationary identity reads

    c E[#isolated piles of three] + E[slack] = E[peak] + E[groups of four or more] + E[merges].

At `L = 800`, density one, after a burn-in of `2L²` and averaging over `16L²`:

| `w` | `c E[#piles of three]` | slack | peak | four or more | groups of three | groups of four or more |
|---|---|---|---|---|---|---|
| 0.1 | 0.0016 | 0.0015 | 0.0031 | -0.0004 | 0.0031 | 0.0115 |
| 0.2 | 0.0097 | 0.0165 | 0.0237 | 0.0010 | 0.0141 | 0.0605 |
| 0.3 | 0.0300 | 0.0423 | 0.0675 | 0.0091 | 0.0278 | 0.2218 |

The first column agrees at `L = 200`, `400` and `800` to within the noise.
The noise in `E[Q(F₁ + Ψ)]` is about `0.002` to `0.004`, so the row at
`w = 0.1` is only indicative. The peak term dominates the right-hand side. It
contains the first-moment drift of the peak's own group and the weight of
groups that form near the peak and detach from it. Groups of four or more are
several times more frequent than groups of three, yet their net contribution
is small.

**Mechanism and missing estimate.** For small `w` a single condensate sweeps
the slow singles ahead of it. It spawns a two-particle pile at rate of order
`w²`, and that pile dissolves into singles at rate of order `w`. A pile of two
with no singles in its cluster dissolves at its first chip into an empty site,
while a larger cluster must first chip its pile down to two particles. Applying
`generator_peakFrameMoment_eq` to the profile
`h s = s (L - s)` shows that twice the mass in background piles equals
`L (w K - S)` plus terms of first-moment size. That identity is not yet stated
as a theorem, and its cutoff error is not small. The first moment in turn ties
`w E[K] - E[S]` to `L` times the inflow from behind. The missing input is a
quantitative bound showing that the stationary number of clusters of mass `m`
decays geometrically in `m`, uniformly in `L`. A proof along these lines needs
the following steps.

1. Control clusters by the rate of exceptional chips. This is done:
   `clusterChipChange_eq` gives every chip explicitly, and the dissolution and
   near-peak bounds reduce to the single forward gain `G`.
2. Reduce to piles of three or more. This is done: `PileCount` bounds the
   piles of two by a pile-count identity, without treating their dissolution
   cycle, and `stationary_backgroundMass_le_big` reduces the background mass
   to the mass in piles of three or more. The second coarse-graining planned
   earlier for piles of two is not needed for this.
3. Price piles by weights that depend on their internal state, on top of the
   fine first moment, which pays for debris. For piles of two this is done in
   `generator_firstMoment_add_twoCount`. A pile chips into an empty site at
   rate `w` and reabsorbs the single at rate one, so its pile mass changes
   constantly while its cluster mass does not. Counts of piles of three cannot
   do this. Adding `α` per pile of two and `β` per pile of three to the first
   moment, the cycle between a bare pile of three and a pile of two with a
   single just ahead requires both `β ≥ α + 1 + c/w` and
   `β ≤ α + 1 - 2w - c` for a drift of at most `-c`. A count does not tell a
   single ahead of its pile from one shed behind it. Cluster weights can.
   Consider `massThreeLyapunov`, with `B₁` per bare pile of three and `B₂` per
   pile of two with one single. A heuristic calculation, not yet checked,
   treats an isolated cluster of mass three in its states: a bare pile, a pile
   of two with its single adjacent or further ahead, the dissolved debris, and
   a pile of two that has shed its single. For a drift of at most `-c` it
   requires `B₁ - B₂ ≥ (1 + w + c)/w` and `2 + c/w + c/w² ≤ B₂ ≤ (2 - 3w - c)/w`.
   With `c = w/2` this range is nonempty for `w ≤ 1/4`. `MassThree` formalizes
   the exact drift of this potential, including every chip. The exact chip
   formulas expose a state the calculation above missed. Three adjacent
   singles in one cluster have two bonds along which a chip rebuilds a pile,
   and the first creates a cluster of mass three, so their drift is
   `-1 + 3w + w B₂`. This requires `B₂ ≤ (1 - 3w - c)/w`, which with the lower
   bound above forces `c` to be at most of order `w`. Every occupied site
   costs `w` in the first moment, so a drift of order `w` per cluster bounds
   the clusters of mass three only by the other occupied sites, which is no
   progress. Window weights, which also weigh the debris of a dissolved
   cluster, remove this obstruction. The weights of order `1/w²` described
   above give a drift of order one per bare pile of three. They keep the
   weights of groups of two, and make merges free. The next steps are closed
   forms in `w` for these weights, and a formal definition. One candidate
   replaces the window by the nearest occupied site ahead of each pile and of
   each adjacent pair of singles, with weights decaying like `(1 + w)^(-d)`.
   The earlier plan of anchoring at pairs of singles does not help; see the
   table above.
4. Bound the rate at which clusters of each mass are created. Each creation
   needs two unlikely events at once, such as the peak chipping onto a pile of
   two just ahead of it. `stationary_pricedPiles_le` bounds that particular
   coincidence by `w` times the piles of three, so this channel reduces to the
   next level. The other coincidences have to be controlled in the same way,
   by induction on the mass. This is the main open point.
5. Treat clusters that live longer than order `L²` with gap-product
   potentials. A cluster of mass `m` must chip its pile down to two before it
   dissolves, which happens at rate of order `w^(m-1)`, so only masses of order
   `log L` live that long. Their creation rate must be shown to vanish fast
   enough.
6. Show that the majority region `N + 2 < 2M` has probability tending to one.
   The simulations never left it, but no checked estimate addresses it yet.

Step 3 is formalized for piles of two. For clusters of mass three the exact
drift is formalized, but the class weights it uses are too weak. Window
weights that work are known numerically, for fixed `w`, but are not yet
formalized. With them, step 4 at mass three amounts to bounding the peak term
of the identity above. Steps 4 to 6 are not formalized.

Lean 4.19.0 and mathlib are installed. `lake-manifest.json` locks mathlib to
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0) and records the transitive
dependencies. `lake build` passes for all twelve modules and the root.

Setup follows the [Lean community project instructions](https://leanprover-community.github.io/install/project.html)
and the [official Elan Windows installer](https://github.com/leanprover/elan/blob/master/elan-init.ps1).
