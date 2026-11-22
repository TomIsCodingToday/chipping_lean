# Chipping model in Lean

This project extends the Lean baseline extracted from
[ChippingProofStarter.md](ChippingProofStarter.md). Lean and mathlib are pinned
to v4.19.0, matching the starter. Git has been initialized locally.

## Target

The project now targets a **finite background**, not a vanishing one. The
background is the set of particles outside one largest pile. `FiniteBackground w`
asks for one bound `ρc` on the expected background mass per site that holds at
every positive density. The excess mass then condenses: at density `ρ` the
largest pile carries at least a fraction `1 - ρc / ρ` of the mass in mean
(`meanBackground_le_of_backgroundDensityAtMost`), and a background fraction of
at least `δ` has asymptotic probability at most `ρc / (ρ δ)`
(`backgroundTail_le_of_backgroundDensityAtMost`). The open propositions are:

- `FiniteBackground w` at a fixed rate, or its finite-volume form
  `UniformFiniteBackground w`;
- `SmallWFiniteBackground`, the analogue of the original conjecture.

The original target `SmallWSupercondensation` is the case `ρc = 0`, and
`smallWFiniteBackground_of_smallWSupercondensation` proves that it implies the
new one. Every supercondensation result below remains valid. The background
mass is exactly the sum over `m` of the tail counts `T_m`. Lean proves with no
hypothesis that `E[T_m] / L` tends to zero as `m → ∞`, uniformly in the ring,
the density and the stationary law. What remains open is that these counts are
summable. Lean also proves `E[B] ≤ (L - 1) E[K]`, where `K` is the number of
occupied sites, so a bounded number of occupied sites gives a finite
background. Simulations show
a finite background where supercondensation fails: at `w = 0.5` the background
holds about `0.15` particles per site at every density from one to eight (see
the assessment).

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
`python numerics\window_weights_mass.py 0.1 20 4 --fixed` solves the same
linear program for groups of up to `M = 4` particles. `--fixed` keeps the
closed-form `VariableWindow` prices on groups of two and three particles. The
script maximizes the credit of the bare pile of `M` particles.
`numerics/tail_counts.c` takes the ring size, the particle number, `w`, the
burn-in and averaging times, a seed and the initial-state flag. It reports the
time averages of the tail counts `T_m` that enter `ClusterCountDecay`.
`python numerics\peak_frame_prices.py 0.1 40 3 --profile` solves exactly the
background chain seen from the peak, with background mass capped at `M`, and
prints the optimal pile prices. `python numerics\peak_frame_lp.py 0.1 40 3 3
--killed 0.3,0.5,0.7,0.8,0.9,0.95,0.98,0.995` solves for group-additive prices
of a prescribed closed form; both are described in the assessment.

## Module layout

The development is split into twenty modules under `ChippingSupercondensation/`.
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
| `BigBackground` | `PileBirths`, `PileCount`, mathlib | Unconditional reduction to background piles of size at least three, short windows around the peak, and a global bound by distant mass and births |
| `WindowEight` | `PeakFrame` | Exact radius-eight certificate and stationary block bound for `1/6 ≤ w ≤ 1/5` |
| `VariableWindow` | `Basic`, mathlib | Closed-form prices for groups of up to three particles at every `0 < w ≤ 1/32`, with uniform bare-triple drift credit |
| `WindowMotion` | `VariableWindow`, `WindowEight`, mathlib | Embedding of gap transitions in the ring generator, the full drift at a bare triple, and the two exit events that can create positive price from a heavy block |
| `WindowSum` | `WindowMotion`, `PeakFrame` | The block bound at every base of the ring, summed and combined with the linear moment; a stationary bound for isolated bare triples |
| `ContentWindow` | `WindowSum` | The same summation for any certified price of block contents of at most `M` particles; `VariableWindow` as the instance `M = 3` |
| `LargeClusters` | `BigBackground`, mathlib | Threshold densities propagate downward; for every fixed `m₀` the target reduces to background piles of at least `m₀` particles; the hypothesis `ClusterCountDecay` and the conditional theorems |
| `FiniteBackground` | `LargeClusters` | The finite-background target, its consequences for the largest pile, an exact characterization by the directional imbalance, the reduction to large piles, and the conditional theorem from `PerSiteClusterDecay` |

`Coalescence` does not depend on `LargestPile` or `Background`, and
`PeakFrame` depends only on `LargestPile`, so Lake can build these in parallel.
The split moved declarations without changing any statement or proof. Eighteen
helpers used across modules, such as `right_eq_add_one` and `chipOrStay`, are no
longer `private`. Lean reports the same 336 declarations, with the same
statements and axioms, as the single file did before the split. `PeakFrame`,
`Clusters`, `PileCount` and `MassThree` later added 176 declarations, and 18
existing helpers, among them `occ_move_delta`, became public. No earlier
statement changed. `WindowSum` adds 46 declarations. Ten helpers of
`WindowMotion`, among them `slice_facts` and `block_move_after`, became public
with their statements unchanged. `ContentWindow` adds 29 declarations. It made
four more helpers public: `count_after` in `WindowMotion`, and
`natCast_fin_inj`, `block_site_ne_rear` and `slice_sites` in `WindowSum`.
`LargeClusters` adds 27 declarations. It made three helpers of `Background`
public with their statements unchanged: `stationary_threshold_window_packing`,
`density_tendsto_zero_of_window_bounds` and `meanAboveCapCount_nonneg`.
`FiniteBackground` adds 38 declarations and changes no existing one.

## Review and proof status

Each item names the module that contains it.

- (`FiniteBackground`) **The finite-background target.** `meanBackgroundMass`
  is the expected number of particles outside one largest pile.
  `BackgroundDensityAtMost w ρ ρc` says that along every thermodynamic sequence
  at density `ρ` it is eventually at most `(ρc + ε) L`. `FiniteBackground w`
  asks for one `ρc` at every density. `finiteBackground_of_uniform` derives it
  from the finite-volume bound `UniformFiniteBackground w`.
  `backgroundDensityAtMost_zero_of_supercondensesAt` and
  `smallWFiniteBackground_of_smallWSupercondensation` place supercondensation
  inside the new target as `ρc = 0`.
- (`FiniteBackground`) **Exact characterization.** For `1 < L`, `0 < N` and
  `w ≥ 0`, with `D̄ = normalizedDirectionalRateImbalance`,

      E[B] ≤ (L - 1)(w - D̄)   and   (L - 1)(w - D̄) ≤ w(L - 1)/N + 2(w(L - 1)/N + 1) E[B]

  (`meanBackgroundMass_le_directionalDeficit`,
  `directionalDeficit_le_meanBackgroundMass`). A finite background is therefore
  the same as a directional imbalance that stays a bounded distance below the
  chip rate, while supercondensation is `D̄ → w`.
  `finiteBackground_of_directionalImbalanceAbove` turns the lower bound
  `D̄ ≥ w - C` along every sequence into `FiniteBackground w` with `ρc = C`.
  This is the single estimate the new target needs.
- (`FiniteBackground`) **Large piles.** Piles of fewer than `m₀` particles hold
  at most `m₀` particles per site, so `E[B] ≤ m₀ L + E[mass in background piles
  of at least m₀]` (`meanBackgroundMass_le_massFrom`). Only large piles need
  control, now by a trivial count rather than by the downward propagation of
  `LargeClusters`.
- (`FiniteBackground`) **Conditional theorem.** `PerSiteClusterDecay w` asks for
  `E[T_m] ≤ A L q^m` beyond some mass `m₀`, with `q < 1`, on every ring. Unlike
  `ClusterCountDecay` the scale `A L` is linear in the ring size, so a
  background fluid of positive density with geometric tails satisfies it.
  `uniformFiniteBackground_of_perSiteClusterDecay` gives
  `E[B] ≤ (m₁ + (m₁ + 1/(1-q)) A) L` with `m₁ = max m₀ 1`, and
  `perSiteClusterDecay_of_clusterCountDecay` shows that the supercondensation
  hypothesis implies this one. For this target the hypothesis does little
  dynamical work: summing tail counts over all masses gives the background
  mass itself, so it is close to a restatement. The directional
  characterization is the substantive reformulation.
- (`FiniteBackground`) **Unconditional sparsity of large piles.**
  `meanBackgroundMass_eq_sum_tailCounts` writes the background mass exactly as
  `Σ_{m=1}^{N} E[T_m]`, so a finite background means `Σ_m E[T_m] = O(L)`. The
  pair bound at cutoff `k` carries the factor `w/(k+w)`
  (`stationary_adjacentThresholdPair_le`). Feeding it back through window
  packing gives `stationary_thresholdCount_le_two_div`, with no hypothesis: if
  `R ≤ L` and `2 w R (2w+3)^R ≤ k + w`, at most `2L/R` sites hold `k` or more
  particles in mean, under every stationary law. Hence
  `exists_thresholdCount_le_uniform` and
  `exists_backgroundTailCount_le_uniform`: for every `ε > 0` there are `k₀` and
  `R₀`, depending only on `w` and `ε`, with `E[T_k] ≤ ε L` for all `k ≥ k₀`,
  every ring of at least `R₀` sites and every `N`. The tail counts per site
  vanish uniformly, at a rate of order `log(2w+3) / log(k/w)`.
- (`FiniteBackground`) **The limit of packing.** A finite background needs
  `Σ_m E[T_m] / L` to be bounded, and the proved rate `1/log m` is not
  summable. The factor `(2w+3)^(r-1)` in the pair bound is crude, but even a
  pair bound linear in the offset would give only a rate of order
  `(w/k)^(1/2)` by packing, which is still not summable. Tail counts and
  packing alone therefore cannot reach a finite background. The simulations
  show `E[T_m]/L` decaying geometrically, far below the proved bound.
- (`FiniteBackground`) **Count to mass.** The exact window identity
  `stationary_massProductAt_eq` writes the mass product at offset `r` as a sum
  over occupied sites of a rate correction times window masses. A window of at
  most `L` sites holds at most `N` particles (`windowMass_le_mass`), so every
  occupied site contributes at most `N` (`neg_windowRateCorrection_le_occupied`)
  and `E[P_r] ≤ N E[K]` at every nonzero offset
  (`stationary_massProductAt_le_occupied`). Summing over the `L - 1` offsets
  bounds the particle separation, and with it

      E[B] ≤ (L - 1) E[K]                      (meanBackgroundMass_le_occupied)

  for every `0 ≤ w ≤ 1`, every ring and every particle number. The hypothesis
  is a count and the conclusion a mass. For example, two macroscopic piles
  and nothing else carry a background of at most `2 (L - 1)` in mean.
  - `uniformFiniteBackground_of_occupied_le`: a uniform bound `E[K] ≤ C` gives
    `UniformFiniteBackground w` with `ρc = max C 0`.
  - `smallWFiniteBackground_of_occupied_bounded`: such a bound at every small
    rate gives `SmallWFiniteBackground`.
  - `meanBackground_le_ring_sq` and `tails_vanish_of_superextensive`: since
    `K ≤ L`, the background fraction is at most `L² / N` in mean, so the
    largest pile takes almost all the mass along any sequence with
    `L² / N → 0`. That is supercondensation at superextensive density, with
    no hypothesis.

  The bound loses a factor `L` against the target in a background fluid,
  where `K` is proportional to `L`. There it gives only `E[B] = O(L²)`. It
  needs the occupied sites to be few, which the simulations show at small
  rates (see the assessment).
- The nineteen theorems above use only `propext`, `Classical.choice` and
  `Quot.sound`.

- (`BigBackground`) For any fixed positive chip rate and limiting density,
  `tails_vanish_iff_bigBackgroundMass_tendsto_zero` makes the target equivalent
  to vanishing mean mass fraction on sites of size at least three outside one
  largest pile. The proof covers the entire stationary law. Window packing at
  threshold two bounds the density of multiple sites by `1/R` plus
  `R (2w+3)^R` times the density of sites with at least three particles.
- (`BigBackground`) For `0 ≤ w ≤ 1`, the expected fraction on the first
  `R < L` sites on either side of a chosen peak is at most
  `sqrt(R²(R+1)/N)` **on each side**. The mass at an offset is at most the
  peak mass, so its square is bounded by the mass product at that offset.
  `stationary_bigBackgroundFraction_le_distantBand_and_births` then leaves
  two terms to estimate at fixed positive density and `R = o(N^(1/3))`:
  the fraction on distant background piles of sizes three through the upper
  cutoff, and the weighted rate of whole-pile and distant-chip births at
  the selected cutoff.
- (`WindowEight`) One table of half-integer prices gives internal drift at
  most `-1/2` for a bare triple and at most zero for the other groups of up
  to three particles whenever `1/6 ≤ w ≤ 1/5`. Lean checks the two endpoints
  by integer arithmetic, verifies the merging moves, and interpolates the
  drift. A pile of two with an adjacent singleton ahead has drift `3 - 18w`,
  which explains the lower endpoint for this table.
- (`VariableWindow`, `WindowMotion`) A separate analytic family works at
  every `0 < w ≤ 1/32`. Set `R = ceil(1/(8w²))`, `K = 1/w` and write
  `u₊ = max(u,0)`. A pile of two costs 3. With a singleton at distance `d`,
  the price is `3 + (R-d)₊` when the singleton is ahead and
  `3 + (R-Kd)₊/2` when it is behind. Three singletons with gaps `a,b`
  cost `(R-b-Ka)₊`. A bare triple costs the adjacent-ahead price plus
  `1 + 1/(64w)`. The prices add across a gap at the cutoff.
  `smallRate_ring_drift_le` proves that the internal ring clocks plus the
  group's first-moment share have drift at most `-1/64` for a bare triple
  and at most zero for every other shape. Sites outside the block may carry
  arbitrary mass.
- (`WindowMotion`) For the test on one fixed block, `generator_bareThree_le`
  bounds the **full** generator by `-(w+1/64)` when the block contains
  exactly three particles at its first site. On a block of mass at least
  four, positive price can arise only when a chip exits a block of mass four
  or a whole pile exits leaving two or three particles.
  `stationary_bareThree_le_lightDrift_and_exits` charges the bare-triple
  event to those exits and the drift on other blocks of mass at most three.
  This is a finite-volume identity-based bound. The frequencies of the
  creation events and the mass in larger distant groups still require estimates.
- (`WindowSum`) The fixed-block bound is summed over all `L` bases for a block
  width `2 ≤ W < L`, and the peak-frame linear moment is added.
  `ring_drift_eq_shift` applies the certificate to a group at any offset
  in its block. `generator_blockPrice_add_share_le` bounds one block's
  generator plus its share of `w K - S` in every state:
  - by `-1/64` if the block holds exactly a bare triple before its last site;
  - plus at most `6 priceBound w` if the site behind the block is occupied, and
    the same again if the block's last site is occupied;
  - plus `w` per occupied site of the block if it holds four or more particles.

  Summing, every occupied site is behind one block and last in one block, so
  arrivals and exits cost at most `12 priceBound w E[K]` in total, whatever
  `W` is. `stationary_bareBlocks_le` holds for every stationary law, without
  a majority assumption:

      (1/64) E[Σ bare blocks] + W E[w K - S] ≤ 12 priceBound w E[K] + w E[Σ heavy occupancy].

  A bare triple whose `W - 1` neighbours on each side are empty fills `W - 1`
  blocks (`isolatedTripleCount_le`). Bounding `E[w K - S]` below on the
  majority region (`exists_majority_cutoff_singles_rear_flux_le`) gives
  `stationary_isolatedTriples_le`:

      ((W-1)/64) E[isolated triples] ≤ 12 priceBound w E[K] + w E[Σ heavy occupancy]
                                       + W (cutoff error + E[S outside the majority region]).

  The heavy occupancy is at most `W E[K]` (`sum_heavyOccupancy_le`). The
  blocks containing the peak alone contribute about `W`, so the inequality
  can show at best that isolated bare triples number `O(w)` times the
  occupied sites within `W` of a heavy group, plus `O(1/W)` times `E[K]`.
  The boundary constant is crude. At `w = 1/32`, `priceBound w ≈ 132`, so the
  boundary term falls below the credit only for `W` of order `10⁵`.
- (`ContentWindow`) The summation does not depend on `VariableWindow`. Let a
  price `V` of block contents satisfy:
  - `0 ≤ V ≤ B`;
  - `V` vanishes on contents of more than `M` particles;
  - `contentDrift w V P ≤ -c * credit P` for every content `P` of one to `M`
    particles.

  Here `contentDrift` is the generator of `V` under the moves of the particles
  of `P` alone, plus their share of `w K - S`. `stationary_contentBlocks_le`
  then gives

      c E[Σ credited blocks] + W E[w K - S] ≤ ((M + 1)(w + 1) B + M w) E[K] + w E[Σ occupancy of blocks above M].

  The ring embedding (`sum_atSite_share_eq_contentDrift`) and the exits from
  heavy blocks (`generator_heavy_le`) are proved once. A future certificate for
  `M ≥ 4` has to prove only the drift inequality on contents.
  `variableWindow_content_certificate` checks the hypotheses for the prices of
  `VariableWindow` with `M = 3`. `stationary_variableWindow_contentBlocks_le`
  recovers the bound of `WindowSum` from the generic theorem.
- (`ContentWindow`) Moves inside a block never change its number of
  particles (`card_shiftAt`). The content drift of `m` particles therefore
  depends only on the price of `m`-particle contents (`contentDrift_congr`).
  `stationary_levelBlocks_le` takes one price and one credit for each mass
  from `1` to `M`. Each needs only the drift inequality on contents of its
  own mass. A mass-four certificate is thus a statement about four-particle
  contents alone. It needs no consistency with the mass-three prices, and its
  window need not be the radius of `VariableWindow`.
- (`LargeClusters`) The threshold-pair bound holds at every cutoff `k ≥ 2`.
  With window packing it bounds the density of sites holding at least `k`
  particles by `1/R` plus `R (2w+3)^R` times the density of sites holding at
  least `k + 1` (`stationary_thresholdDensity_le`). A vanishing density at any
  fixed mass therefore propagates down to mass two
  (`thresholdDensity_tendsto_zero_of_le`). For every fixed `m₀ ≥ 3`,
  `supercondensesAt_iff_equilibrium_backgroundMassFrom_tendsto_zero` makes the
  target equivalent to the background mass in piles of at least `m₀`
  particles being `o(N)`. Piles of fewer than `m₀` particles never need
  separate control. `BigBackground` is the case `m₀ = 3`.
- (`LargeClusters`) **Conditional theorem.** Let `T_m` count the sites other
  than one largest pile that hold at least `m` particles. `ClusterCountDecay w`
  asserts that there are a mass `m₀`, a ratio `0 ≤ q < 1` and a scale `g ≥ 0`
  with `g L / L → 0` such that every stationary law on every ring satisfies

      E[T_m] ≤ g(L) q^m   for all m ≥ m₀.

  The layer-cake identity `backgroundMassFrom_eq_tailCounts` turns this into
  the mass bound `(m₀ + 1/(1-q)) g(L)` (`stationary_backgroundMassFrom_le_of_geometric`),
  which is `o(N)` at positive density.
  - `supercondensesAt_of_clusterCountDecay` proves `SupercondensesAt w ρ` for
    every `ρ > 0` from `ClusterCountDecay w` at a fixed `w > 0`.
  - `smallWSupercondensation_of_clusterCountDecay` proves
    `SmallWSupercondensation` if the hypothesis holds at every rate below some
    `w₀ ∈ (0, 1]`.
  - `clusterCountDecay_of_rpow` accepts the power law `g(L) = C L^θ` with
    `θ < 1`, so a polylogarithmic number of large clusters is covered.
  - `tails_vanish_of_tailCount_le` is the version along one sequence. It needs
    the bound only eventually along that sequence, so only near the given
    density and for large rings.

  The hypothesis is not proved. It still excludes the two scenarios that make
  the problem hard: a positive density of large clusters, and a second
  macroscopic pile (the decay in `m` rules out both). The theorem removes
  everything else. Nothing is assumed about singles, piles of two, or any pile
  of fewer than `m₀` particles, and a bound on counts suffices. All five
  theorems use only `propext`, `Classical.choice` and `Quot.sound`.
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

For `w ≤ 0.4` the mean background grows far more slowly than `L` in these
runs, so `B/N` decays. Longer runs with `numerics/tail_counts.c`, reported
below, show it bounded at `w = 0.2` but still growing slowly at `w = 0.3` and
`w = 0.4`. At `w = 0.5` the
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

**Certificates for four and five particles.**
`numerics/window_weights_mass.py` solves the window linear program for groups
of up to `M` particles and maximizes the drift credit `c` of the bare pile of
`M`.

Keeping the proven `VariableWindow` prices on groups of two and three, prices
for groups of four exist with positive credit:

| `w` | `R` | `R w²` | largest `c` | `V(bare 4)` |
|---|---|---|---|---|
| 0.1 | 10 | 0.10 | 0.035 | — |
| 0.0707 | 20 | 0.10 | 0.034 | — |
| 0.05 | 40 | 0.10 | 0.031 | 90 |
| 0.1 | 20 | 0.20 | 0.087 | 50 |
| 0.1 | 25 | 0.25 | 0.114 | 63 |
| 0.0707 | 50 | 0.25 | 0.099 | — |

The credit depends mainly on `R w²`. At fixed `R w²` it falls slowly as `w`
decreases, so these runs do not decide whether it stays bounded below. The
prices for groups of four are not sparse. Two piles of two at gap `d` decay
roughly geometrically in `d`. That fits two piles of two performing a
symmetric random walk while each dissolves at rate `w`. A closed form will
need such profiles rather than the piecewise-linear ramps of `VariableWindow`.

With all prices free, the credit of the bare pile of `M` falls by a factor of
order `w` per unit of `M`:

| `w` | `R` | `M = 3` | `M = 4` | `M = 5` |
|---|---|---|---|---|
| 0.2 | 8 | 3.98 | 0.54 | 0.081 |
| 0.1 | 12 | — | 0.157 | 0.013 |

The ratio of credit to price falls the same way. A pile of `m ≥ 4` particles
splits only after two quick chips, and its parts mostly reunite, so it lives
for a time of order `w^-(m-2)`. A certificate with credit of order one at mass
`m` then needs prices of that order, and the summed bound needs `W` much
larger than those prices. Window certificates can therefore control each
fixed mass. Reaching masses up to order `log L` needs a family that is uniform
in `m`, with windows that grow like `w^-(m-2)`.

Two further runs support this. First, credit can be given to every state that
holds a pile of three or more, in proportion to the mass in such piles
(`--pile-credit`), at little cost:

| `w` | `R` | `M = 4`, bare pile only | `M = 4`, all piles of three or more |
|---|---|---|---|
| 0.2 | 8 | 0.54 | 0.43 |
| 0.1 | 12 | 0.157 | 0.143 |
| 0.1 | 16 | 0.27 | 0.245 |

Second, the mass levels decouple, as `stationary_levelBlocks_le` shows. With
the `VariableWindow` prices fixed at radius `20` and `w = 0.1`, the credit of
the bare pile of four grows with the window `R₄` used for groups of four:
`0.087`, `0.119` and `0.150` at `R₄ = 20`, `30` and `40` (`--r3 20`). The
heuristic lifetime `w^-2.5` of a pile of four suggests that a window of that
order gives a credit of order one. A closed form for these prices remains to
be found. Two piles of two at gap `d` perform a symmetric random walk and
dissolve at rate `w`. A dissolved front pile is swept back by the rear one,
while a dissolved rear pile is lost. The prices of that family are therefore
convex near `d = 0` and level off beyond `d` of order `w^-1/2`.

**Finite background.** `numerics/tail_counts.c` now also reports the mean
fraction on one largest pile. The table gives the background per site,
`ρ (1 - E[M/N])`, after a burn-in of `2L²` and averaging over `8L²`, started
from a uniform spread. Runs started from one pile agree.

| `w` | `ρ` = 0.5 | 1 | 2 | 4 | 8 |
|---|---|---|---|---|---|
| 0.2 | 0.004 / 0.001 | 0.004 / 0.001 | 0.004 / 0.001 | 0.004 / 0.001 | 0.004 / 0.001 |
| 0.3 | 0.010 / 0.004 | 0.010 / 0.004 | 0.010 / 0.004 | 0.010 / 0.004 | 0.010 / 0.004 |
| 0.5 | 0.136 / 0.143 | 0.146 / 0.148 | 0.145 / 0.150 | 0.148 / 0.150 | 0.147 / 0.154 |
| 0.7 | 0.37 / 0.44 | 0.62 / 0.78 | 0.71 / 0.96 | 0.68 / 0.98 | 0.73 / 0.93 |
| 1.0 | 0.44 / 0.48 | 0.81 / 0.92 | 1.05 / 1.38 | 1.10 / 1.43 | 1.16 / 1.44 |

Each entry is `L = 200 / L = 800`. At `w ≤ 0.3` the background holds a few
particles in total, bounded at `w = 0.2` and growing slowly with `L` at
`w = 0.3`, so its density falls nearly like `1/L`: supercondensation. At
`w = 0.5` it holds about `0.15` particles per site at every density and both
sizes: a finite background with `ρc ≈ 0.15`, and no supercondensation. At
`w = 0.7` and `w = 1` the background density levels off in `ρ` at about `0.95`
and `1.4`, but it still grows from `L = 200` to `L = 800`. Earlier runs at
`w = 1, ρ = 4` give `0.96`, `1.16`, `1.26` and `1.48` at `L = 100` to `800`.
These runs therefore support `FiniteBackground` at `w ≤ 0.5` and leave it open
at larger rates. Where the background exceeds the density, at small `ρ` and
large `w`, there is no condensate.

For the new target only bounds of order `L` are needed, not limits. That
changes which existing tools help.

- A second macroscopic pile is no longer excluded at each density. A pile of
  mass `N/2` with probability `p` adds `p ρ L / 2` to the background, so
  `FiniteBackground` requires only `p ≤ 2 ρc / ρ`.
- The downward propagation of `LargeClusters` proves limits and gives nothing
  for positive densities. The peak-frame identities need a majority pile,
  which a finite background provides only for `ρ > 2 ρc`, so using them would
  be circular.
- The window certificates give bounds of order `L` at each fixed mass, but
  with constants that grow like `w^-(m-2)`. A finite background needs these
  bounds to be summable over the masses.
- The counts of large piles are now controlled unconditionally
  (`exists_thresholdCount_le_uniform`), but only at a logarithmic rate. The open
  part of the target is the mass carried by large background piles.
- `meanBackgroundMass_le_occupied` converts the number of occupied sites into
  background mass. A uniform bound on `E[K]` therefore suffices for a finite
  background. The table below measures `E[K]` at density one, from runs of
  `5·10⁷` time units started from one pile, four seeds each.

  | `w` | `E[K]` at `L` = 100 / 400 / 1600 / 6400 |
  |---|---|
  | 0.1 | 1.159 / 1.163 / 1.165 / 1.165 |
  | 0.2 | 1.446 / 1.469 / 1.475 / 1.476 |
  | 0.3 | 1.978 / 2.118 / 2.184 / 2.190 |

  The count levels off at every rate shown, even at `w = 0.3`, where the
  background mass still grows slowly. A bounded `E[K]` is thus a plausible
  hypothesis at small rates. It fails in a background fluid, as at `w = 0.5`,
  where only the directional route below remains.
- The exact identity `meanBackgroundMass_le_directionalDeficit` reduces the
  target to the lower bound `D̄ ≥ w - C` on one stationary quantity. Proving it
  needs control of where singles sit relative to the mass around them. Singles
  just ahead of a pile lower the deficit, and singles just behind a pile raise
  it. This is the main open estimate.

**Pile counts and a certificate in the frame of the peak.** These runs test
the small-rate route, in which a bounded number of occupied sites gives a
finite background (`smallWFiniteBackground_of_occupied_bounded`).

*Scaling of pile counts.* `tail_counts.c` at `L = 1000`, density one, three
runs of `5·10⁸` to `10⁹` time units per rate, gives the expected number `n_m`
of background sites holding exactly `m` particles. Fitted exponents of
`n_m ∝ w^α` over `0.05 ≤ w ≤ 0.2`:

| `m` | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|
| `α` | 1.47 | 1.94 | 2.13 | 2.53 | 2.66 | 3.18 |

An earlier guess, `α = m/2 + 1`, is refuted. It assumed a lifetime `w^-(m-2)`,
which is wrong already for a pile of two, which dissolves at its first chip.
Creation at rate `w^m` times the square root of the lifetime gives `w^1.5` for
`m = 2` (lifetime `1/w`) and `w^2` for `m = 3` (lifetime `w^-2`, since a pile of
three is lost only after two quick chips). Both match. Heavier piles are more
common than this estimate predicts. At fixed `w` the counts decay
geometrically in `m`, with ratio about `0.6` at `w = 0.1` and `0.7` at
`w = 0.2`. Summed over `m` they stay bounded, consistent with the bounded
occupied count measured above.

*Exact chain seen from the peak.* `peak_frame_prices.py` treats the peak as a
reservoir at offset `0`. Its moves shift every offset down, its chips land at
offset `1`, and mass reaching offset `L` from behind merges into it. With the
background mass capped at `M` the chain is finite. Write `F₁` for the linear
moment, the sum of the offsets of all background particles; its drift is
`w K − S − L × (inflow from behind)` (`PeakFrame`). Then `F₁ / (1 − w)` pays
exactly one per single and costs `w / (1 − w)` per pile. What remains is a pile
price `E` with `G E ≤ −P / (1 − w) + C'`, where `P` counts background piles,
and the sum `F₁ / (1 − w) + E` bounds the mean number of occupied background
sites by `C = w / (1 − w) + C'`. The smallest `C'` is the stationary mean of
`P / (1 − w)`. At `w = 0.1`:

| `M` | `C` at `L` = 20 / 30 / 40 / 50 / 80 |
|---|---|
| 3 | 0.146 / 0.149 / 0.150 / 0.151 / 0.151 |
| 4 | 0.148 / 0.151 / 0.153 / 0.154 (`L = 45`) |

`C` converges in `L` and changes little from `M = 3` to `M = 4`. The
simulation with all masses gives `0.164`. The term `w / (1 − w)` is most of `C`.
The optimal pile prices are concave and increasing in the offset `d`. The
price of a pile of three at `w = 0.1` rises with slope about `12` near the peak
and levels off near `170`.

*Group-additive prices.* `peak_frame_lp.py` restricts `E` to a sum over
groups, maximal sets of particles with consecutive gaps at most `R`, of a
price `Φ(shape, d)` depending on the shape of the group and the offset of its
first particle. Values of `C'` at `w = 0.1`:

| prices | `M = 3`, `L = 40` | `M = 4`, `L = 24` |
|---|---|---|
| exact optimum | 0.0390 | 0.0385 |
| free table, `R = 3` | 0.0437 | 0.0502 |
| one ramp `α + β min(d, D)` per shape | 0.38 – 1.04 | — |
| piecewise linear, 8 breakpoints | 0.0815 | 0.70 |
| `α + Σ_k β_k (1 − λ_k^d)`, 8 fixed `λ_k` | 0.0454 | 0.0516 |

Piecewise-linear profiles fail for piles of four. The last family consists of
the profiles of a random walk absorbed at the peak and killed at rate `κ`,
with `λ + 1/λ = 2 + κ`. With the same eight values of `λ` it stays close to
the free table at every rate tried: `C' = 0.0131` (exact `0.0124`) and
`0.0149` (`0.0117`) at `w = 0.05`, and `0.158` (`0.124`) and `0.185` (`0.138`)
at `w = 0.2`. A single such profile fits the exact price of a pile of three to
`1%` at `w = 0.1`, with `λ = 0.923`. Its amplitude, `177`, matches the predicted
`1 / ((1 − w) κ) = 174`. The price of a pile of two needs an extra term linear
in `d`, because the two singles it leaves can form a pile again.

*What a Lean proof still needs.* A closed form with killed-walk profiles in
the offset and killing rates depending on the mass, valid for every mass,
together with a proof of the drift inequality for every configuration. It
also needs the cutoff errors of the frame of a majority pile to be `O(1)`. The
computations above cap the mass at four and do not address either point.

**Related literature.** No rigorous proof of condensation is known to us for
a related aggregation–chipping model, so there is no technique to import.

- Rajesh and Majumdar, *Exact phase diagram of a model with aggregation and
  chipping*, Phys. Rev. E 63, 036114 (2001), arXiv:cond-mat/0009110. Masses
  diffuse, coalesce and shed single units at rate `w`. They obtain the critical
  density `ρc(w) = √(w + 1) − 1`. Their model lets single units move as fast as
  whole masses, so its critical line does not transfer to ours.
- Whitehouse, Costa, Blythe and Evans, *Maintenance of order in a moving strong
  condensate*, J. Stat. Mech. P11029 (2014), arXiv:1407.1668. In a totally
  asymmetric model where a site of `n > 1` particles sends `n − 1` forward and
  leaves one behind, they find a moving condensate holding a fraction of the
  mass tending to one. Their mechanism is that "the condensate [is] unable to
  escape from the tail of mass trailing behind". The results come from
  simulation and from an approximate theory that assumes uncorrelated sites and
  a geometric profile, and the authors state that an exact solution is
  "unlikely to be easily attainable".
- A 2009 review, arXiv:0904.4097, is reported to state that the condensed phase
  of the one-directional chipping model of Majumdar, Krishnamurthy and Barma,
  in which singles hop at the full rate, disappears in the thermodynamic limit.
  This was not checked against the text. If it holds, it is consistent with the
  slow singles of this model being essential.

**Tail counts and the conditional theorem.** `ClusterCountDecay` asks for
`E[T_m] ≤ g(L) q^m` beyond some mass, with `q < 1` and `g` sublinear. The
smallest admissible scale for a given `q` is `g(L) = max_m E[T_m] / q^m`.
`numerics/tail_counts.c`, built with `-DMMAX=400`, measured `E[T_m]` for
`m ≤ 400` at density one. Each entry averages six runs of `2·10⁸` time units,
started from a single pile after a burn-in of `10⁶`. The layer-cake identity
`backgroundMassFrom_eq_tailCounts` reproduces the measured mass to every
printed digit.

| `w` | `E[mass in background piles ≥ 3]` at `L` = 100 / 400 / 1600 / 6400 | largest background pile | `q` | `max_m E[T_m]/q^m` at `L` = 100 / 400 / 1600 / 6400 |
|---|---|---|---|---|
| 0.2 | 0.37 / 0.52 / 0.63 / 0.65 | 34 | 0.8 | 0.16 / 0.20 / 0.21 / 0.21 |
| 0.3 | 1.31 / 2.19 / 3.13 / 4.14 | 65 | 0.95 | 0.28 / 0.37 / 0.42 / 0.46 |
| 0.4 | 3.94 / 9.16 / 17.1 / 27.2 | 271 | 0.98 | 0.63 / 0.97 / 1.25 / 1.44 |

At `w = 0.2` the scale is bounded for every `q` from `0.8` to `0.98`, as the
hypothesis allows with room to spare. At `w = 0.3` it grows like `L^0.1` with
`q = 0.95`. A smaller `q` fails there: at `q = 0.9` the scale jumps to `1.5`
at `L = 6400`. At `w = 0.4` only `q = 0.98` gives slow growth, and the profile
is still widening with `L`, so these runs do not decide whether a fixed `q`
works there. The conjecture needs the hypothesis only at small rates, where
the data support it most clearly. Runs started from one pile follow the same
trajectory on every ring until background structure travels a distance of
order `L` from the peak. At `w = 0.2` the runs for `L ≥ 3200` coincide in an
earlier sweep, so no excursion reached that far.

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
decays geometrically in `m`, uniformly in `L`. `LargeClusters` checks that such
a bound suffices, even with a sublinear factor in `L` and only beyond a fixed
mass: `smallWSupercondensation_of_clusterCountDecay`. A proof of the bound
along these lines needs the following steps.

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
   weights of groups of two, and make merges free. The analytic family in
   `VariableWindow` instead uses a price of three for a pile of two and
   piecewise-linear functions of the gaps. Its radius grows with decreasing
   chip rate, and its bare-triple drift credit is independent of the rate.
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

Step 3 now has a checked small-rate certificate for groups of mass at most
three. For step 4, the fixed-block stationary theorem identifies the exit
events that create price from larger blocks. `WindowSum` combines the block
bounds across the ring. Exits and arrivals then cost at most
`12 priceBound w E[K]` in total, which is small against the credit for a
fixed, large `W`. Two terms are not small:

- `w` times the occupied sites of blocks with four or more particles;
- `W` times the linear-moment error, which includes the singles outside the
  majority region.

The result bounds isolated bare triples by heavier structures. It does not
bound the mass of larger piles. That needs the same scheme for groups of every
mass up to a cutoff: certificates for mass `m` whose heavy terms are charged
to mass `m + 1` and to the peak. `ContentWindow` reduces each level to a drift
inequality for block contents of at most `m` particles. Numerically such
certificates exist for `m = 4` on top of the `VariableWindow` prices, and for
`m = 5`. Their credit relative to their price falls like a power of `w` that
grows with `m`, matching lifetimes of order `w^-(m-2)`. Since
`stationary_levelBlocks_le` decouples the masses, the next step is a closed
form for four-particle contents alone, with its own window. The global
reduction in
`BigBackground` also requires control of distant intermediate mass and
competing births. Along that route a separate majority estimate is
unnecessary, but the linear moment used here still needs one.

Lean 4.19.0 and mathlib are installed. `lake-manifest.json` locks mathlib to
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0) and records the transitive
dependencies. `lake build` checks all twenty modules and the root.

Setup follows the [Lean community project instructions](https://leanprover-community.github.io/install/project.html)
and the [official Elan Windows installer](https://github.com/leanprover/elan/blob/master/elan-init.ps1).
