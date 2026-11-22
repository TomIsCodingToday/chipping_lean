import ChippingSupercondensation.LargeClusters

/-!
# Finite background: condensation with a bounded background density

Supercondensation asks the background, the particles outside one largest pile,
to be a vanishing fraction of the mass. This module states the weaker target in
which the background holds a bounded number of particles per site, uniformly in
the density. The excess mass then condenses: at density `ρ` the largest pile
carries at least a fraction `1 - ρc / ρ` of the mass in mean.

* `FiniteBackground w`: one bound `ρc` on the background density along every
  thermodynamic sequence at every positive density. `UniformFiniteBackground w`
  is the finite-volume form, `meanBackgroundMass ≤ ρc L` on every ring, and
  implies it. `SmallWFiniteBackground` is the small-rate target, implied by
  `SmallWSupercondensation`.
* `meanBackground_le_of_backgroundDensityAtMost` and
  `backgroundTail_le_of_backgroundDensityAtMost`: the consequences for the
  largest pile.
* `meanBackgroundMass_le_directionalDeficit` and
  `directionalDeficit_le_meanBackgroundMass`: the background mass equals, up to
  constant factors, `L - 1` times the deficit of the normalized directional
  imbalance below the chip rate. `finiteBackground_of_directionalImbalanceAbove`
  turns a lower bound on that one stationary quantity into a finite background.
* `meanBackgroundMass_le_massFrom`: piles of fewer than `m₀` particles hold at
  most `m₀` particles per site, so only large piles need control.
* `PerSiteClusterDecay w`: tail counts of background piles decay geometrically
  in mass at a scale proportional to the ring size. It gives a uniform finite
  background (`uniformFiniteBackground_of_perSiteClusterDecay`) and is implied
  by the supercondensation hypothesis `ClusterCountDecay`.
* `meanBackgroundMass_eq_sum_tailCounts`: the background mass is the sum of the
  tail counts. `stationary_thresholdCount_le_two_div` and
  `exists_thresholdCount_le_uniform`: with no hypothesis, the density of sites
  holding at least `k` particles tends to zero as `k → ∞`, uniformly in the
  ring, the density and the stationary law, at rate `1 / log k`. A finite
  background needs these counts to be summable.
* `meanBackgroundMass_le_occupied`: `E[B] ≤ (L - 1) E[K]` with `K` the number of
  occupied sites, from the window identity. Consequences: a bounded number of
  occupied sites gives a finite background
  (`uniformFiniteBackground_of_occupied_le`,
  `smallWFiniteBackground_of_occupied_bounded`), and supercondensation holds
  unconditionally along sequences with `L² / N → 0`
  (`tails_vanish_of_superextensive`).
-/

namespace Chipping
open Filter
open scoped BigOperators Topology
noncomputable section

/-! ## The target -/

/-- The expected number of particles outside one largest pile. -/
def meanBackgroundMass {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) : ℝ :=
  ∑ x, μ.weight x * ((N - largest x : ℕ) : ℝ)

theorem meanBackgroundMass_nonneg {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) :
    0 ≤ meanBackgroundMass μ :=
  Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) (Nat.cast_nonneg _)

theorem meanBackgroundMass_eq {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) :
    meanBackgroundMass μ = (N : ℝ) * meanBackground μ := by
  unfold meanBackgroundMass meanBackground backgroundFraction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp

/-- Along every thermodynamic sequence at density `ρ`, the background eventually
holds at most `ρc + ε` particles per site, for every `ε > 0`. -/
def BackgroundDensityAtMost (w ρ ρc : ℝ) : Prop :=
  ∀ (L N : ℕ → ℕ), (∀ n, 3 ≤ L n) → Tendsto L atTop atTop →
    Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ) →
    ∀ (μ : (n : ℕ) → StationaryLaw (L n) (N n) w),
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, meanBackgroundMass (μ n) / (L n : ℝ) ≤ ρc + ε

/-- **Finite background.** One bound `ρc` on the background density holds at
every positive density. -/
def FiniteBackground (w : ℝ) : Prop :=
  ∃ ρc : ℝ, ∀ ρ : ℝ, 0 < ρ → BackgroundDensityAtMost w ρ ρc

/-- The finite-volume form: the bound holds on every ring, for every number of
particles and every stationary law. -/
def UniformFiniteBackground (w : ℝ) : Prop :=
  ∃ ρc : ℝ, ∀ (L N : ℕ), 3 ≤ L → ∀ μ : StationaryLaw L N w,
    meanBackgroundMass μ ≤ ρc * (L : ℝ)

/-- The small-rate target. It is weaker than `SmallWSupercondensation`, which
asks for `ρc = 0`. -/
def SmallWFiniteBackground : Prop :=
  ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ ≤ 1 ∧ ∀ w : ℝ, 0 < w → w < w₀ → FiniteBackground w

theorem finiteBackground_of_uniform {w : ℝ} (h : UniformFiniteBackground w) :
    FiniteBackground w := by
  obtain ⟨ρc, hρc⟩ := h
  refine ⟨ρc, fun ρ _ L N hL _ _ μ ε hε => Eventually.of_forall fun n => ?_⟩
  have hLpos : (0 : ℝ) < L n := by exact_mod_cast (by have := hL n; omega : 0 < L n)
  rw [div_le_iff₀ hLpos, add_mul]
  have := hρc (L n) (N n) (hL n) (μ n)
  nlinarith [mul_pos hε hLpos]

/-! ## Relation to supercondensation -/

/-- Supercondensation at density `ρ` is a background of density zero there. -/
theorem backgroundDensityAtMost_zero_of_supercondensesAt {w ρ : ℝ}
    (h : SupercondensesAt w ρ) : BackgroundDensityAtMost w ρ 0 := by
  intro L N hL hLlim hd μ ε hε
  have hmean := (tails_vanish_iff_mean_vanishes μ).mp (h.2 L N hL hLlim hd μ)
  have hlim := hmean.mul hd
  rw [zero_mul] at hlim
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn
  rw [zero_add, meanBackgroundMass_eq, mul_comm, mul_div_assoc]
  exact hn.le

theorem smallWFiniteBackground_of_smallWSupercondensation (h : SmallWSupercondensation) :
    SmallWFiniteBackground := by
  obtain ⟨w₀, h0, h1, hw⟩ := h
  exact ⟨w₀, h0, h1, fun w hw0 hww => ⟨0, fun ρ hρ =>
    backgroundDensityAtMost_zero_of_supercondensesAt (hw w hw0 hww ρ hρ)⟩⟩

/-! ## Consequences for the largest pile -/

/-- **Condensation from a finite background.** At density `ρ`, a background of
at most `ρc` particles per site leaves at most a fraction `ρc / ρ` of the mass
outside one largest pile, in mean. -/
theorem meanBackground_le_of_backgroundDensityAtMost {w ρ ρc : ℝ} (hρ : 0 < ρ)
    (h : BackgroundDensityAtMost w ρ ρc) {L N : ℕ → ℕ} (hL : ∀ n, 3 ≤ L n)
    (hLlim : Tendsto L atTop atTop)
    (hd : Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ))
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, meanBackground (μ n) ≤ ρc / ρ + ε := by
  intro ε hε
  have hε' : 0 < ε * ρ / 2 := by positivity
  have hinv : Tendsto (fun n => (L n : ℝ) / (N n : ℝ)) atTop (𝓝 ρ⁻¹) := by
    simpa only [inv_div] using hd.inv₀ hρ.ne'
  have hc := hinv.const_mul (ρc + ε * ρ / 2)
  have heq : (ρc + ε * ρ / 2) * ρ⁻¹ = ρc / ρ + ε / 2 := by
    rw [add_mul, div_eq_mul_inv ρc, mul_comm ε ρ, mul_div_assoc,
      ← div_eq_mul_inv (ρ * (ε / 2)), mul_div_cancel_left₀ _ hρ.ne']
  rw [heq] at hc
  filter_upwards [h L N hL hLlim hd μ _ hε', (tendsto_order.1 hc).2 (ρc / ρ + ε) (by linarith),
    eventually_pos_mass_of_tendsto_density hρ hd] with n hn hc' hN
  have hLpos : (0 : ℝ) < L n := by exact_mod_cast (by have := hL n; omega : 0 < L n)
  have hNpos : (0 : ℝ) < N n := by exact_mod_cast hN
  have hmb : meanBackground (μ n) =
      meanBackgroundMass (μ n) / (L n : ℝ) * ((L n : ℝ) / (N n : ℝ)) := by
    rw [meanBackgroundMass_eq, div_mul_div_comm, mul_comm (L n : ℝ) (N n : ℝ),
      mul_div_mul_right _ _ hLpos.ne', mul_div_cancel_left₀ _ hNpos.ne']
  rw [hmb]
  calc _ ≤ (ρc + ε * ρ / 2) * ((L n : ℝ) / (N n : ℝ)) :=
        mul_le_mul_of_nonneg_right hn (div_nonneg hLpos.le hNpos.le)
    _ ≤ _ := hc'.le

/-- The same in probability: the chance that a fraction at least `δ` of the
mass lies outside one largest pile is at most `ρc / (ρ δ)`, asymptotically. -/
theorem backgroundTail_le_of_backgroundDensityAtMost {w ρ ρc : ℝ} (hρ : 0 < ρ)
    (h : BackgroundDensityAtMost w ρ ρc) {L N : ℕ → ℕ} (hL : ∀ n, 3 ≤ L n)
    (hLlim : Tendsto L atTop atTop)
    (hd : Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ))
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) {δ : ℝ} (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, backgroundTail (μ n) δ ≤ ρc / (ρ * δ) + ε := by
  intro ε hε
  filter_upwards [meanBackground_le_of_backgroundDensityAtMost hρ h hL hLlim hd μ (ε * δ)
    (mul_pos hε hδ)] with n hn
  have hm := threshold_mul_tail_le_mean (μ n) δ
  have hle : backgroundTail (μ n) δ ≤ (ρc / ρ + ε * δ) / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  refine hle.trans_eq ?_
  have := hρ.ne'
  have := hδ.ne'
  field_simp
  ring

/-! ## An exact characterization by the directional imbalance -/

/-- **Exact bound.** The expected background mass is at most `L - 1` times the
deficit of the normalized directional imbalance below the chip rate. -/
theorem meanBackgroundMass_le_directionalDeficit {L N : ℕ} [NeZero L] {w : ℝ}
    (hL : 1 < L) (hN : 0 < N) (hw : 0 ≤ w) (μ : StationaryLaw L N w) :
    meanBackgroundMass μ ≤
      ((L - 1 : ℕ) : ℝ) * (w - normalizedDirectionalRateImbalance μ) := by
  have hb := (directional_deficit_bounds hL hN hw μ).1
  have hsep := (meanBackground_le_meanParticleSeparation_le_twice μ hN).1
  have hA : (0 : ℝ) < ((L - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < L - 1)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [meanBackgroundMass_eq]
  calc (N : ℝ) * meanBackground μ ≤ (N : ℝ) * meanParticleSeparation μ :=
        mul_le_mul_of_nonneg_left hsep hNr.le
    _ = ((L - 1 : ℕ) : ℝ) * (((N : ℝ) / ((L - 1 : ℕ) : ℝ)) * meanParticleSeparation μ) := by
        rw [← mul_assoc, mul_div_cancel₀ _ hA.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hA.le

/-- **Converse.** The deficit is in turn bounded by the background mass. Together
the two bounds make a finite background equivalent to a directional imbalance
that stays a bounded distance below the chip rate. -/
theorem directionalDeficit_le_meanBackgroundMass {L N : ℕ} [NeZero L] {w : ℝ}
    (hL : 1 < L) (hN : 0 < N) (hw : 0 ≤ w) (μ : StationaryLaw L N w) :
    ((L - 1 : ℕ) : ℝ) * (w - normalizedDirectionalRateImbalance μ) ≤
      w * ((L - 1 : ℕ) : ℝ) / N +
        2 * (w * ((L - 1 : ℕ) : ℝ) / N + 1) * meanBackgroundMass μ := by
  have hb := (directional_deficit_bounds hL hN hw μ).2
  have hsep := (meanBackground_le_meanParticleSeparation_le_twice μ hN).2
  have hA : (0 : ℝ) < ((L - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < L - 1)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcoef : 0 ≤ w + (N : ℝ) / ((L - 1 : ℕ) : ℝ) := add_nonneg hw (div_nonneg hNr.le hA.le)
  have h2 : w - normalizedDirectionalRateImbalance μ ≤
      w / N + (w + (N : ℝ) / ((L - 1 : ℕ) : ℝ)) * (2 * meanBackground μ) :=
    hb.trans (add_le_add_left (mul_le_mul_of_nonneg_left hsep hcoef) _)
  calc _ ≤ ((L - 1 : ℕ) : ℝ) *
        (w / N + (w + (N : ℝ) / ((L - 1 : ℕ) : ℝ)) * (2 * meanBackground μ)) :=
        mul_le_mul_of_nonneg_left h2 hA.le
    _ = _ := by
        rw [meanBackgroundMass_eq]
        have hA' := hA.ne'
        have hN' := hNr.ne'
        generalize ((L - 1 : ℕ) : ℝ) = a at hA' ⊢
        field_simp
        ring

/-- Along every sequence at every positive density, the normalized directional
imbalance eventually stays at least `w - C`. -/
def DirectionalImbalanceAbove (w C : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ (L N : ℕ → ℕ) (_ : ∀ n, 3 ≤ L n) [∀ n, NeZero (L n)],
    Tendsto L atTop atTop →
    Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ) →
    ∀ (μ : (n : ℕ) → StationaryLaw (L n) (N n) w),
    ∀ᶠ n in atTop, w - C ≤ normalizedDirectionalRateImbalance (μ n)

/-- A lower bound on one stationary quantity, the directional imbalance, gives a
finite background with `ρc = C`. -/
theorem finiteBackground_of_directionalImbalanceAbove {w C : ℝ} (hw : 0 ≤ w)
    (h : DirectionalImbalanceAbove w C) : FiniteBackground w := by
  refine ⟨C, fun ρ hρ L N hL hLlim hd μ ε hε => ?_⟩
  letI (n : ℕ) : NeZero (L n) := ⟨by have := hL n; omega⟩
  filter_upwards [h ρ hρ L N hL hLlim hd μ, eventually_pos_mass_of_tendsto_density hρ hd]
    with n hn hN
  have hLn : 1 < L n := by have := hL n; omega
  have hb := meanBackgroundMass_le_directionalDeficit hLn hN hw (μ n)
  have hLpos : (0 : ℝ) < L n := by exact_mod_cast (by omega : 0 < L n)
  have hApos : (0 : ℝ) < ((L n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < L n - 1)
  have hA : ((L n - 1 : ℕ) : ℝ) ≤ L n := by exact_mod_cast Nat.sub_le _ _
  have h0 := meanBackgroundMass_nonneg (μ n)
  have hd0 : 0 ≤ w - normalizedDirectionalRateImbalance (μ n) := by nlinarith
  have hC : w - normalizedDirectionalRateImbalance (μ n) ≤ C := by linarith
  rw [div_le_iff₀ hLpos]
  calc meanBackgroundMass (μ n) ≤ ((L n - 1 : ℕ) : ℝ) * (w - normalizedDirectionalRateImbalance (μ n)) := hb
    _ ≤ (L n : ℝ) * (w - normalizedDirectionalRateImbalance (μ n)) :=
        mul_le_mul_of_nonneg_right hA hd0
    _ ≤ (L n : ℝ) * C := mul_le_mul_of_nonneg_left hC hLpos.le
    _ ≤ (C + ε) * L n := by nlinarith [mul_pos hε hLpos]

/-! ## Only large piles need control -/

private theorem backgroundCast_eq {L N : ℕ} [NeZero L] (x : State L N) :
    ((N - largest x : ℕ) : ℝ) = ∑ i, if i ≠ peakSite x then (occ x i : ℝ) else 0 := by
  have hmass : (∑ i, (occ x i : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  have hsplit : (∑ i, (occ x i : ℝ)) = (∑ i, if i = peakSite x then (occ x i : ℝ) else 0) +
      ∑ i, if i ≠ peakSite x then (occ x i : ℝ) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i = peakSite x <;> simp [h]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), occ_peakSite, hmass] at hsplit
  rw [Nat.cast_sub (largest_le_mass x)]
  linarith

/-- Piles of fewer than `m₀` particles hold at most `m₀` particles per site. -/
theorem meanBackgroundMass_le_massFrom {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (m₀ : ℕ) :
    meanBackgroundMass μ ≤ (m₀ : ℝ) * L + meanBackgroundMassFrom μ m₀ := by
  have hpoint (x : State L N) :
      ((N - largest x : ℕ) : ℝ) ≤ (m₀ : ℝ) * L + backgroundMassFrom m₀ x := by
    rw [backgroundCast_eq]
    unfold backgroundMassFrom
    have hL : (∑ _i : Fin L, (m₀ : ℝ)) = (m₀ : ℝ) * L := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    rw [← hL, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases hp : i ≠ peakSite x
    · rw [if_pos hp]
      by_cases hm : m₀ ≤ occ x i
      · rw [if_pos ⟨hp, hm⟩]
        have : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg m₀
        linarith
      · rw [if_neg (fun h => hm h.2), add_zero]
        exact_mod_cast (Nat.lt_of_not_le hm).le
    · rw [if_neg hp, if_neg (fun h => hp h.1), add_zero]
      exact Nat.cast_nonneg m₀
  calc meanBackgroundMass μ ≤ ∑ x, μ.weight x * ((m₀ : ℝ) * L + backgroundMassFrom m₀ x) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (μ.nonneg x)
    _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, μ.normalized, one_mul,
          meanBackgroundMassFrom]

/-! ## Conditional finite background from cluster counts -/

/-- **Decay of cluster counts per site.** Beyond some fixed mass `m₀`, on every
ring and for every stationary law, the expected number of background sites
holding at least `m` particles is at most `A L q ^ m`, with `q < 1`. Unlike
`ClusterCountDecay`, the scale may grow linearly in the ring size, so a
background fluid of positive density with geometric tails is allowed. -/
def PerSiteClusterDecay (w : ℝ) : Prop :=
  ∃ (m₀ : ℕ) (A q : ℝ), 0 ≤ A ∧ 0 ≤ q ∧ q < 1 ∧
    ∀ (L N : ℕ) [NeZero L], 3 ≤ L → ∀ μ : StationaryLaw L N w, ∀ m, m₀ ≤ m →
      meanBackgroundTailCount μ m ≤ A * L * q ^ m

theorem uniformFiniteBackground_of_perSiteClusterDecay {w : ℝ}
    (h : PerSiteClusterDecay w) : UniformFiniteBackground w := by
  obtain ⟨m₀, A, q, hA, hq0, hq, hb⟩ := h
  let m₁ := max m₀ 1
  refine ⟨m₁ + (m₁ + 1 / (1 - q)) * A, fun L N hL μ => ?_⟩
  haveI : NeZero L := ⟨by omega⟩
  have hmass := stationary_backgroundMassFrom_le_of_geometric μ m₁ (le_max_right _ _)
    (g := A * L) (mul_nonneg hA (Nat.cast_nonneg _)) hq0 hq
    (fun m hm => hb L N hL μ m ((le_max_left _ _).trans hm))
  have h1 := meanBackgroundMass_le_massFrom μ m₁
  calc _ ≤ (m₁ : ℝ) * L + ((m₁ : ℝ) + 1 / (1 - q)) * (A * L) := by linarith
    _ = _ := by ring

theorem finiteBackground_of_perSiteClusterDecay {w : ℝ} (h : PerSiteClusterDecay w) :
    FiniteBackground w :=
  finiteBackground_of_uniform (uniformFiniteBackground_of_perSiteClusterDecay h)

/-- The supercondensation hypothesis implies the finite-background one. -/
theorem perSiteClusterDecay_of_clusterCountDecay {w : ℝ} (h : ClusterCountDecay w) :
    PerSiteClusterDecay w := by
  obtain ⟨m₀, q, g, hq0, hq, hg0, hg, hb⟩ := h
  obtain ⟨A, hA⟩ := hg.bddAbove_range
  refine ⟨m₀, max A 0, q, le_max_right _ _, hq0, hq, fun L N _ hL μ m hm => ?_⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hgL : g L ≤ max A 0 * L := by
    have h1 : g L / L ≤ A := hA ⟨L, rfl⟩
    rw [div_le_iff₀ hLpos] at h1
    nlinarith [le_max_left A 0]
  calc _ ≤ g L * q ^ m := hb L N hL μ m hm
    _ ≤ max A 0 * L * q ^ m := mul_le_mul_of_nonneg_right hgL (pow_nonneg hq0 _)

/-! ## The background as a sum of tail counts; sparsity of large piles -/

/-- Layer cake for the whole background. The expected background mass is the sum
over `m` of the expected number of background sites holding at least `m`
particles. A finite background is the statement that this sum is `O(L)`. -/
theorem meanBackgroundMass_eq_sum_tailCounts {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) :
    meanBackgroundMass μ = ∑ m ∈ Finset.Icc 1 N, meanBackgroundTailCount μ m := by
  have hpoint (x : State L N) : ((N - largest x : ℕ) : ℝ) = backgroundMassFrom 1 x := by
    rw [backgroundCast_eq]
    unfold backgroundMassFrom
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : i ≠ peakSite x
    · by_cases h1 : 1 ≤ occ x i
      · rw [if_pos hp, if_pos ⟨hp, h1⟩]
      · rw [if_pos hp, if_neg (fun h => h1 h.2)]
        have h0 : occ x i = 0 := by omega
        simp [h0]
    · rw [if_neg hp, if_neg (fun h => hp h.1)]
  unfold meanBackgroundMass meanBackgroundTailCount
  simp_rw [hpoint, backgroundMassFrom_eq_tailCounts 1 le_rfl, Nat.sub_self, Nat.cast_zero,
    zero_mul, zero_add, Finset.mul_sum]
  exact Finset.sum_comm

theorem meanThresholdCount_antitone {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) {k k' : ℕ}
    (h : k ≤ k') : meanThresholdCount μ k' ≤ meanThresholdCount μ k :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => by
    by_cases h' : k' ≤ occ x i
    · rw [if_pos h', if_pos (h.trans h')]
    · rw [if_neg h']
      split_ifs <;> norm_num) (μ.nonneg x)

theorem meanBackgroundTailCount_le_meanThresholdCount {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (m : ℕ) :
    meanBackgroundTailCount μ m ≤ meanThresholdCount μ m :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (by
    unfold backgroundTailCount
    exact Finset.sum_le_sum fun i _ => by
      by_cases h : i ≠ peakSite x ∧ m ≤ occ x i
      · rw [if_pos h, if_pos h.2]
      · rw [if_neg h]
        split_ifs <;> norm_num) (μ.nonneg x)

/-- **Large piles are sparse.** Two piles of at least `k` particles at distance
`r` cost, through the capped-mass balance, at most `(2w + 3)^(r-1) w / (k + w)`
times the sites above `k`. Window packing then bounds the sites holding at least
`k` particles by `2 L / R` as soon as `2 w R (2w + 3)^R ≤ k + w`. The bound
holds for every stationary law and assumes nothing about the largest pile. -/
theorem stationary_thresholdCount_le_two_div {L N : ℕ} [NeZero L] (hL : 3 ≤ L) {w : ℝ}
    (hw : 0 < w) (μ : StationaryLaw L N w) (k R : ℕ) (hk : 2 ≤ k) (hR : 0 < R)
    (hRL : R ≤ L) (hkR : 2 * w * R * (2 * w + 3) ^ R ≤ k + w) :
    meanThresholdCount μ k ≤ 2 * L / R := by
  have hT0 := meanThresholdCount_nonneg μ k
  have hcap : meanAboveCapCount μ k ≤ meanThresholdCount μ k := by
    rw [meanAboveCapCount_eq_meanThresholdCount]
    exact meanThresholdCount_antitone μ (Nat.le_succ k)
  have hc : 1 ≤ 2 * w + 3 := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkw : (0 : ℝ) < k + w := by linarith
  have hpow : 0 ≤ (2 * w + 3) ^ R := pow_nonneg (by linarith) R
  set T := meanThresholdCount μ k with hTdef
  set b := (2 * w + 3) ^ R * (w * T / ((k : ℝ) + w)) with hbdef
  have hb : 0 ≤ b := mul_nonneg hpow (div_nonneg (mul_nonneg hw.le hT0) hkw.le)
  have hpair : ∀ r : ℕ, 0 < r → r < R → meanThresholdPairCountAt μ k (r : Fin L) ≤ b := by
    intro r hr hrR
    refine (stationary_thresholdPairCount_le hL hw.le μ k hk r hr (hrR.trans_le hRL)).trans ?_
    exact mul_le_mul (pow_le_pow_right₀ hc (by omega))
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcap hw.le) hkw.le)
      (div_nonneg (mul_nonneg hw.le (meanAboveCapCount_nonneg μ k)) hkw.le) hpow
  have hpack := stationary_threshold_window_packing μ k R hR b hb hpair
  change T / (L : ℝ) ≤ 1 / (R : ℝ) + (R : ℝ) * b / (L : ℝ) at hpack
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (NeZero.pos L)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hRb : (R : ℝ) * b ≤ T / 2 := by
    have hkey : (R : ℝ) * b = (2 * w * R * (2 * w + 3) ^ R) * T / (2 * ((k : ℝ) + w)) := by
      rw [hbdef]
      have := hkw.ne'
      field_simp
      ring
    rw [hkey, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * ((k : ℝ) + w))]
    nlinarith [mul_le_mul_of_nonneg_right hkR hT0]
  rw [div_le_iff₀ hLpos] at hpack
  have hexp : (1 / (R : ℝ) + (R : ℝ) * b / L) * L = L / R + R * b := by
    rw [add_mul, div_mul_cancel₀ _ hLpos.ne']
    ring
  rw [hexp] at hpack
  have hhalf : T / 2 ≤ (L : ℝ) / R := by linarith
  rw [le_div_iff₀ hRpos]
  have := (le_div_iff₀ hRpos).mp hhalf
  linarith

/-- **Uniform sparsity.** For every `ε > 0` there are a mass `k₀` and a ring size
`R₀`, depending only on `w` and `ε`, such that on every ring of at least `R₀`
sites, for every number of particles and every stationary law, sites holding
`k₀` or more particles number at most `ε L` in mean. -/
theorem exists_thresholdCount_le_uniform {w : ℝ} (hw : 0 < w) {ε : ℝ} (hε : 0 < ε) :
    ∃ k₀ R₀ : ℕ, ∀ (L N : ℕ) [NeZero L], 3 ≤ L → R₀ ≤ L → ∀ μ : StationaryLaw L N w,
      ∀ k, k₀ ≤ k → meanThresholdCount μ k ≤ ε * L := by
  obtain ⟨R, hR⟩ := exists_nat_gt (2 / ε)
  have hRpos : (0 : ℝ) < R := (by positivity : (0 : ℝ) < 2 / ε).trans hR
  have hR0 : 0 < R := by exact_mod_cast hRpos
  refine ⟨max 2 ⌈2 * w * R * (2 * w + 3) ^ R⌉₊, R, fun L N _ hL hRL μ k hk => ?_⟩
  have hk2 : 2 ≤ k := (le_max_left _ _).trans hk
  have hkR : 2 * w * R * (2 * w + 3) ^ R ≤ (k : ℝ) + w := by
    have h1 : 2 * w * R * (2 * w + 3) ^ R ≤ (⌈2 * w * R * (2 * w + 3) ^ R⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : (⌈2 * w * R * (2 * w + 3) ^ R⌉₊ : ℝ) ≤ k := by
      exact_mod_cast (le_max_right _ _).trans hk
    linarith
  refine (stationary_thresholdCount_le_two_div hL hw μ k R hk2 hR0 hRL hkR).trans ?_
  have h2R : 2 / (R : ℝ) ≤ ε := by
    rw [div_le_iff₀ hRpos]
    have := (div_lt_iff₀ hε).mp hR
    linarith
  calc 2 * (L : ℝ) / R = (2 / R) * L := by ring
    _ ≤ ε * L := mul_le_mul_of_nonneg_right h2R (Nat.cast_nonneg L)

/-! ## From occupied sites to background mass -/

/-- A window of at most `L` sites holds at most all the particles. -/
theorem windowMass_le_mass {L N : ℕ} [NeZero L] (r : ℕ) (hr : r ≤ L) (x : State L N)
    (j : Fin L) : windowMass r x j ≤ N := by
  unfold windowMass
  have hinj : Set.InjOn (fun s : ℕ => j - (s : Fin L)) (Finset.range r) := by
    intro s hs t ht h
    simp only [Finset.coe_range, Set.mem_Iio] at hs ht
    have h' : (s : Fin L) = (t : Fin L) := sub_right_injective h
    have hv := congrArg Fin.val h'
    rwa [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at hv
  rw [← Finset.sum_image (f := fun i => (occ x i : ℝ)) hinj]
  calc _ ≤ ∑ i, (occ x i : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.cast_nonneg _)
    _ = N := by exact_mod_cast x.property

/-- Each occupied site contributes at most `N` to the negative window rate
correction, and empty sites contribute nothing. -/
theorem neg_windowRateCorrection_le_occupied {L N : ℕ} [NeZero L] {w : ℝ} (hw : 0 ≤ w)
    (hw' : w ≤ 1) (r : ℕ) (hr1 : 1 ≤ r) (hrL : r ≤ L) (x : State L N) :
    -windowRateCorrection w r x ≤ (N : ℝ) * occupiedCount x := by
  unfold windowRateCorrection occupiedCount
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hF := windowMass_le_mass r hrL x (i + (r : Fin L))
  have hB := windowMass_le_mass r hrL x i
  have hF0 : 0 ≤ windowMass r x (i + (r : Fin L)) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hBa : (occ x i : ℝ) ≤ windowMass r x i := by
    unfold windowMass
    have h := Finset.single_le_sum (f := fun s : ℕ => (occ x (i - (s : Fin L)) : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_range.mpr (by omega : 0 < r))
    simpa using h
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  by_cases h2 : 2 ≤ occ x i
  · have h1 : 0 < occ x i := by omega
    simp only [rateCorrection, if_pos h2, if_pos h1, mul_one]
    have hB0 : (0 : ℝ) ≤ windowMass r x i := (Nat.cast_nonneg _).trans hBa
    nlinarith [mul_le_mul_of_nonneg_left hB hw, mul_nonneg hw hF0]
  · by_cases h1 : 1 ≤ occ x i
    · have ha : occ x i = 1 := by omega
      simp only [rateCorrection, if_neg h2, if_pos h1, if_pos (show 0 < occ x i by omega),
        mul_one]
      rw [ha, Nat.cast_one] at hBa
      have hw1 : 0 ≤ 1 - w := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hF hw1, mul_nonneg hw1 (sub_nonneg.mpr hBa)]
    · have h0 : occ x i = 0 := by omega
      simp [rateCorrection, h0]

/-- **Count to mass.** At every nonzero offset, the stationary mass product is at
most `N` times the mean number of occupied sites. -/
theorem stationary_massProductAt_le_occupied {L N : ℕ} [NeZero L] {w : ℝ} (hw : 0 ≤ w)
    (hw' : w ≤ 1) (r : ℕ) (hr1 : 1 ≤ r) (hrL : r < L) (μ : StationaryLaw L N w) :
    (∑ x, μ.weight x * massProductAt x (r : Fin L)) ≤ (N : ℝ) * meanOccupiedCount μ := by
  rw [stationary_massProductAt_eq r (natCast_fin_ne_zero (by omega) hrL) μ,
    ← Finset.sum_neg_distrib, meanOccupiedCount, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  rw [← mul_neg, mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    (neg_windowRateCorrection_le_occupied hw hw' r hr1 hrL.le x) (μ.nonneg x)

theorem meanOccupiedCount_nonneg {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) :
    0 ≤ meanOccupiedCount μ :=
  Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x)
    (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)

theorem meanOccupiedCount_le {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) :
    meanOccupiedCount μ ≤ L := by
  have hpoint (x : State L N) : occupiedCount x ≤ L := by
    unfold occupiedCount
    calc _ ≤ ∑ _i : Fin L, (1 : ℝ) :=
          Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
      _ = L := by simp
  calc meanOccupiedCount μ ≤ ∑ x, μ.weight x * (L : ℝ) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (μ.nonneg x)
    _ = L := by rw [← Finset.sum_mul, μ.normalized, one_mul]

/-- **The background is at most `L - 1` particles per occupied site.** Summing
the count-to-mass bound over the `L - 1` nonzero offsets bounds the particle
separation, and with it the background. Two macroscopic piles with nothing
else, for instance, cannot carry a background beyond `2 (L - 1)` in mean. -/
theorem meanBackgroundMass_le_occupied {L N : ℕ} [NeZero L] {w : ℝ} (hw : 0 ≤ w)
    (hw' : w ≤ 1) (μ : StationaryLaw L N w) :
    meanBackgroundMass μ ≤ ((L - 1 : ℕ) : ℝ) * meanOccupiedCount μ := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [meanBackgroundMass_eq, Nat.cast_zero, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (meanOccupiedCount_nonneg μ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsep := (meanBackground_le_meanParticleSeparation_le_twice μ hN).1
  have hH : meanParticleSeparation μ =
      (∑ d ∈ Finset.univ.erase (0 : Fin L), ∑ x, μ.weight x * massProductAt x d) /
        (N : ℝ) ^ 2 := by
    unfold meanParticleSeparation
    simp_rw [particleSeparation_eq_nonzeroOffsetProbability _ hN, div_eq_mul_inv,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hoff : ∀ d ∈ Finset.univ.erase (0 : Fin L),
      (∑ x, μ.weight x * massProductAt x d) ≤ (N : ℝ) * meanOccupiedCount μ := by
    intro d hd
    have hd0 : d ≠ 0 := Finset.ne_of_mem_erase hd
    have hval : 1 ≤ d.val := by
      rcases Nat.eq_zero_or_pos d.val with h | h
      · exact absurd (Fin.ext h) hd0
      · exact h
    have hcast : ((d.val : ℕ) : Fin L) = d := Fin.cast_val_eq_self d
    rw [← hcast]
    exact stationary_massProductAt_le_occupied hw hw' d.val hval d.isLt μ
  have hsum := Finset.sum_le_sum hoff
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [meanBackgroundMass_eq]
  calc (N : ℝ) * meanBackground μ ≤ (N : ℝ) * meanParticleSeparation μ :=
        mul_le_mul_of_nonneg_left hsep hNr.le
    _ ≤ (N : ℝ) * (((L - 1 : ℕ) : ℝ) * ((N : ℝ) * meanOccupiedCount μ) / (N : ℝ) ^ 2) := by
        rw [hH]
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hsum (sq_nonneg _)) hNr.le
    _ = _ := by
        field_simp
        ring

/-- **Supercondensation at superextensive density.** On every ring the
background fraction is at most `L² / N` in mean, so it vanishes along any
sequence with `L² / N → 0`, at every rate in `[0, 1]`. -/
theorem meanBackground_le_ring_sq {L N : ℕ} [NeZero L] {w : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1)
    (μ : StationaryLaw L N w) : meanBackground μ ≤ (L : ℝ) ^ 2 / N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h0 : meanBackground μ = 0 := by
      unfold meanBackground backgroundFraction
      simp
    rw [h0, Nat.cast_zero, div_zero]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := (meanBackgroundMass_le_occupied hw hw' μ).trans
    (mul_le_mul (by exact_mod_cast Nat.sub_le L 1 : ((L - 1 : ℕ) : ℝ) ≤ L)
      (meanOccupiedCount_le μ) (meanOccupiedCount_nonneg μ) (Nat.cast_nonneg L))
  rw [meanBackgroundMass_eq, ← sq] at h
  rw [le_div_iff₀ hNr, mul_comm]
  exact h

theorem tails_vanish_of_superextensive {L N : ℕ → ℕ} [∀ n, NeZero (L n)] {w : ℝ}
    (hw : 0 ≤ w) (hw' : w ≤ 1) (μ : (n : ℕ) → StationaryLaw (L n) (N n) w)
    (hscale : Tendsto (fun n => (L n : ℝ) ^ 2 / (N n : ℝ)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => backgroundTail (μ n) ε) atTop (𝓝 0) := by
  apply (tails_vanish_iff_mean_vanishes μ).mpr
  exact squeeze_zero (fun n => Finset.sum_nonneg fun x _ =>
    mul_nonneg ((μ n).nonneg x) (backgroundFraction_nonneg x))
    (fun n => meanBackground_le_ring_sq hw hw' (μ n)) hscale

/-- A uniformly bounded number of occupied sites gives a uniform finite
background with `ρc = max C 0`. -/
theorem uniformFiniteBackground_of_occupied_le {w C : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1)
    (h : ∀ (L N : ℕ), 3 ≤ L → ∀ μ : StationaryLaw L N w, meanOccupiedCount μ ≤ C) :
    UniformFiniteBackground w := by
  refine ⟨max C 0, fun L N hL μ => ?_⟩
  haveI : NeZero L := ⟨by omega⟩
  have hA : ((L - 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.sub_le L 1
  calc meanBackgroundMass μ ≤ ((L - 1 : ℕ) : ℝ) * meanOccupiedCount μ :=
        meanBackgroundMass_le_occupied hw hw' μ
    _ ≤ (L : ℝ) * max C 0 := mul_le_mul hA ((h L N hL μ).trans (le_max_left _ _))
        (meanOccupiedCount_nonneg μ) (Nat.cast_nonneg L)
    _ = max C 0 * L := mul_comm _ _

/-- **Conditional small-rate target from counts.** If at every small rate the
expected number of occupied sites is bounded uniformly in the ring, the
particle number and the stationary law, the small-rate finite-background
conjecture holds. The hypothesis concerns counts only; the window identity
converts it into a bound on mass. -/
theorem smallWFiniteBackground_of_occupied_bounded
    (h : ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ ≤ 1 ∧ ∀ w : ℝ, 0 < w → w < w₀ → ∃ C : ℝ,
      ∀ (L N : ℕ), 3 ≤ L → ∀ μ : StationaryLaw L N w, meanOccupiedCount μ ≤ C) :
    SmallWFiniteBackground := by
  obtain ⟨w₀, h0, h1, hw⟩ := h
  refine ⟨w₀, h0, h1, fun w hw0 hww => ?_⟩
  obtain ⟨C, hC⟩ := hw w hw0 hww
  exact finiteBackground_of_uniform
    (uniformFiniteBackground_of_occupied_le hw0.le (hww.le.trans h1) hC)

/-- The same holds for the background tail counts, which exclude one largest
pile. -/
theorem exists_backgroundTailCount_le_uniform {w : ℝ} (hw : 0 < w) {ε : ℝ} (hε : 0 < ε) :
    ∃ k₀ R₀ : ℕ, ∀ (L N : ℕ) [NeZero L], 3 ≤ L → R₀ ≤ L → ∀ μ : StationaryLaw L N w,
      ∀ k, k₀ ≤ k → meanBackgroundTailCount μ k ≤ ε * L := by
  obtain ⟨k₀, R₀, h⟩ := exists_thresholdCount_le_uniform hw hε
  exact ⟨k₀, R₀, fun L N _ hL hRL μ k hk =>
    (meanBackgroundTailCount_le_meanThresholdCount μ k).trans (h L N hL hRL μ k hk)⟩

end
end Chipping
