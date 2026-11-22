import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import ChippingSupercondensation.BigBackground

/-!
# Supercondensation from the decay of large cluster counts

The threshold-pair bound of `Background` holds at every cutoff `k ≥ 2`: two
piles of at least `k` particles at a fixed distance are charged to sites
holding more than `k`. With window packing, a vanishing density of sites with
at least `k + 1` particles forces a vanishing density of sites with at least
`k` (`thresholdDensity_tendsto_zero_of_succ`). Iterating downwards from any
fixed mass `m₀` reaches mass three.

Consequently only large clusters need control. For every fixed `m₀ ≥ 3`,
supercondensation is equivalent to the background mass in piles of at least
`m₀` particles being `o(N)`
(`supercondensesAt_iff_equilibrium_backgroundMassFrom_tendsto_zero`).

`ClusterCountDecay w` is a hypothesis on counts. Beyond some mass `m₀`, the
expected number of background sites holding at least `m` particles is at most
`g L * q ^ m`, with `q < 1` and a sublinear scale `g`. It implies
supercondensation at every positive density
(`supercondensesAt_of_clusterCountDecay`), and for all small rates it implies
`SmallWSupercondensation` (`smallWSupercondensation_of_clusterCountDecay`). A
power law `C L ^ θ` with `θ < 1` is a sublinear scale
(`clusterCountDecay_of_rpow`).
-/

namespace Chipping
open Filter
open scoped BigOperators Topology
noncomputable section

/-! ## Threshold densities propagate downwards -/

/-- The stationary mean number of sites holding at least `k` particles. -/
def meanThresholdCount {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) (k : ℕ) : ℝ :=
  ∑ x, μ.weight x * ∑ i, if k ≤ occ x i then (1 : ℝ) else 0

theorem meanThresholdCount_nonneg {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) (k : ℕ) :
    0 ≤ meanThresholdCount μ k :=
  Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x)
    (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)

theorem meanAboveCapCount_eq_meanThresholdCount {L N : ℕ} {w : ℝ}
    (μ : StationaryLaw L N w) (k : ℕ) :
    meanAboveCapCount μ k = meanThresholdCount μ (k + 1) := by
  unfold meanAboveCapCount aboveCapCount meanThresholdCount
  simp only [Nat.lt_iff_add_one_le]

/-- The window bound of `stationary_multipleDensity_le` at an arbitrary cutoff
`k ≥ 2`. -/
theorem stationary_thresholdDensity_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 < w) (μ : StationaryLaw L N w) (k : ℕ) (hk : 2 ≤ k)
    (R : ℕ) (hR : 0 < R) (hRL : R ≤ L) :
    meanThresholdCount μ k / (L : ℝ) ≤
      1 / (R : ℝ) + ((R : ℝ) * (2 * w + 3) ^ R) * (meanThresholdCount μ (k + 1) / (L : ℝ)) := by
  have hc : 1 ≤ 2 * w + 3 := by linarith
  have hcap := meanAboveCapCount_nonneg μ k
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hfactor : w * meanAboveCapCount μ k / ((k : ℝ) + w) ≤ meanAboveCapCount μ k := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith
  have hb : 0 ≤ (2 * w + 3) ^ R * meanAboveCapCount μ k :=
    mul_nonneg (pow_nonneg (by linarith) R) hcap
  have h := stationary_threshold_window_packing μ k R hR _ hb (by
      intro r hr hrR
      have hpair := stationary_thresholdPairCount_le hL hw.le μ k hk r hr (hrR.trans_le hRL)
      exact hpair.trans (mul_le_mul (pow_le_pow_right₀ hc (by omega))
        hfactor (by positivity) (pow_nonneg (by linarith) R)))
  rw [← meanAboveCapCount_eq_meanThresholdCount]
  convert h using 1
  ring

/-- A vanishing density of sites with at least `k + 1` particles forces a
vanishing density of sites with at least `k`, for every `k ≥ 2`. -/
theorem thresholdDensity_tendsto_zero_of_succ {L N : ℕ → ℕ} [∀ n, NeZero (L n)] {w : ℝ}
    (hL : ∀ n, 3 ≤ L n) (hLlim : Tendsto L atTop atTop) (hw : 0 < w)
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) (k : ℕ) (hk : 2 ≤ k)
    (h : Tendsto (fun n => meanThresholdCount (μ n) (k + 1) / (L n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => meanThresholdCount (μ n) k / (L n : ℝ)) atTop (𝓝 0) :=
  density_tendsto_zero_of_window_bounds hLlim
    (fun n => div_nonneg (meanThresholdCount_nonneg (μ n) k) (Nat.cast_nonneg _)) h
    (fun R hR => ⟨_, fun n hn => stationary_thresholdDensity_le (hL n) hw (μ n) k hk R hR hn⟩)

/-- Iterating `thresholdDensity_tendsto_zero_of_succ` from any larger cutoff. -/
theorem thresholdDensity_tendsto_zero_of_le {L N : ℕ → ℕ} [∀ n, NeZero (L n)] {w : ℝ}
    (hL : ∀ n, 3 ≤ L n) (hLlim : Tendsto L atTop atTop) (hw : 0 < w)
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) (k m : ℕ) (hk : 2 ≤ k) (hkm : k ≤ m)
    (h : Tendsto (fun n => meanThresholdCount (μ n) m / (L n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => meanThresholdCount (μ n) k / (L n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  induction d generalizing k with
  | zero => simpa using h
  | succ d ih =>
    apply thresholdDensity_tendsto_zero_of_succ hL hLlim hw μ k hk
    exact ih (k + 1) (by omega) (by omega) (by rwa [show k + 1 + d = k + (d + 1) by omega])

/-! ## Background mass in piles above a fixed size -/

/-- Background sites holding at least `m` particles. A chosen largest site is
excluded. -/
def backgroundTailCount {L N : ℕ} [NeZero L] (m : ℕ) (x : State L N) : ℝ :=
  ∑ i, if i ≠ peakSite x ∧ m ≤ occ x i then 1 else 0

/-- Mass on background sites holding at least `m` particles. -/
def backgroundMassFrom {L N : ℕ} [NeZero L] (m : ℕ) (x : State L N) : ℝ :=
  ∑ i, if i ≠ peakSite x ∧ m ≤ occ x i then (occ x i : ℝ) else 0

def meanBackgroundTailCount {L N : ℕ} [NeZero L] {w : ℝ} (μ : StationaryLaw L N w)
    (m : ℕ) : ℝ :=
  ∑ x, μ.weight x * backgroundTailCount m x

def meanBackgroundMassFrom {L N : ℕ} [NeZero L] {w : ℝ} (μ : StationaryLaw L N w)
    (m : ℕ) : ℝ :=
  ∑ x, μ.weight x * backgroundMassFrom m x

theorem meanBigBackgroundMass_eq_meanBackgroundMassFrom {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) : meanBigBackgroundMass μ = meanBackgroundMassFrom μ 3 := rfl

theorem meanBackgroundMassFrom_nonneg {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (m : ℕ) : 0 ≤ meanBackgroundMassFrom μ m :=
  Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x)
    (Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity)

private theorem mean_le_of_pointwise {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w)
    {f g : State L N → ℝ} (h : ∀ x, f x ≤ g x) :
    (∑ x, μ.weight x * f x) ≤ ∑ x, μ.weight x * g x :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x)

private theorem backgroundMassFrom_le_big {L N : ℕ} [NeZero L] (m : ℕ) (hm : 3 ≤ m)
    (x : State L N) : backgroundMassFrom m x ≤ bigBackgroundMass x := by
  unfold backgroundMassFrom bigBackgroundMass
  apply Finset.sum_le_sum
  intro i _
  by_cases h : i ≠ peakSite x ∧ m ≤ occ x i
  · rw [if_pos h, if_pos ⟨h.1, hm.trans h.2⟩]
  · rw [if_neg h]
    split_ifs <;> positivity

/-- Sites with at least `m` particles: the peak, plus background mass over `m`. -/
private theorem thresholdCount_le_massFrom {L N : ℕ} [NeZero L] (m : ℕ) (hm : 1 ≤ m)
    (x : State L N) :
    (∑ i, if m ≤ occ x i then (1 : ℝ) else 0) ≤ 1 + backgroundMassFrom m x / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold backgroundMassFrom
  rw [div_eq_mul_inv, Finset.sum_mul]
  have hsplit (j : Fin L) : (if m ≤ occ x j then (1 : ℝ) else 0) ≤
      (if j = peakSite x then 1 else 0) +
        (if j ≠ peakSite x ∧ m ≤ occ x j then (occ x j : ℝ) else 0) * (m : ℝ)⁻¹ := by
    by_cases hj : j = peakSite x
    · rw [if_pos hj, if_neg (show ¬(j ≠ peakSite x ∧ m ≤ occ x j) from fun h => h.1 hj),
        zero_mul, add_zero]
      split_ifs <;> norm_num
    · rw [if_neg hj, zero_add]
      by_cases hk : m ≤ occ x j
      · rw [if_pos hk, if_pos ⟨hj, hk⟩, ← div_eq_mul_inv, le_div_iff₀ hm', one_mul]
        exact_mod_cast hk
      · rw [if_neg hk, if_neg (fun h => hk h.2), zero_mul]
  refine (Finset.sum_le_sum fun j _ => hsplit j).trans_eq ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

/-- Background piles of three or more: those below `m` hold fewer than `m`
particles each. -/
private theorem big_le_threshold_add_massFrom {L N : ℕ} [NeZero L] (m : ℕ) (x : State L N) :
    bigBackgroundMass x ≤ (m : ℝ) * (∑ i, if 3 ≤ occ x i then (1 : ℝ) else 0) +
      backgroundMassFrom m x := by
  unfold bigBackgroundMass backgroundMassFrom
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : i ≠ peakSite x ∧ 3 ≤ occ x i
  · rw [if_pos h, if_pos h.2, mul_one]
    by_cases hm : m ≤ occ x i
    · rw [if_pos ⟨h.1, hm⟩]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · rw [if_neg (fun h' => hm h'.2), add_zero]
      exact_mod_cast (Nat.lt_of_not_le hm).le
  · rw [if_neg h]
    split_ifs <;> positivity

/-- Along a positive-density sequence, the background mass in piles of three or
more is `o(N)` exactly when the background mass in piles of at least `m₀` is,
for any fixed `m₀ ≥ 3`. -/
theorem bigBackgroundMass_tendsto_zero_iff_backgroundMassFrom
    {L N : ℕ → ℕ} [∀ n, NeZero (L n)] {w ρ : ℝ}
    (hL : ∀ n, 3 ≤ L n) (hLlim : Tendsto L atTop atTop) (hw : 0 < w) (hρ : 0 < ρ)
    (hdensity : Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ))
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) (m₀ : ℕ) (hm₀ : 3 ≤ m₀) :
    Tendsto (fun n => meanBigBackgroundMass (μ n) / (N n : ℝ)) atTop (𝓝 0) ↔
      Tendsto (fun n => meanBackgroundMassFrom (μ n) m₀ / (N n : ℝ)) atTop (𝓝 0) := by
  have hLpos (n : ℕ) : (0 : ℝ) < (L n : ℝ) := by exact_mod_cast (NeZero.pos (L n))
  have hpos := eventually_pos_mass_of_tendsto_density hρ hdensity
  constructor
  · intro h
    exact squeeze_zero (fun n => div_nonneg (meanBackgroundMassFrom_nonneg _ _) (Nat.cast_nonneg _))
      (fun n => div_le_div_of_nonneg_right
        (mean_le_of_pointwise (μ n) (backgroundMassFrom_le_big m₀ hm₀)) (Nat.cast_nonneg _)) h
  · intro h
    have hm₀' : (0 : ℝ) < m₀ := by exact_mod_cast (by omega : 0 < m₀)
    have hinvL : Tendsto (fun n => 1 / (L n : ℝ)) atTop (𝓝 0) := by
      simp only [one_div]
      exact (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hLlim
    -- sites with at least `m₀` particles have vanishing density
    have htop : Tendsto (fun n => meanThresholdCount (μ n) m₀ / (L n : ℝ)) atTop (𝓝 0) := by
      have hlim := hinvL.add ((h.mul hdensity).div_const (m₀ : ℝ))
      simp only [zero_mul, zero_div, add_zero] at hlim
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      · exact Eventually.of_forall fun n =>
          div_nonneg (meanThresholdCount_nonneg _ _) (hLpos n).le
      · filter_upwards [hpos] with n hn
        have hN : (N n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        have hmean : meanThresholdCount (μ n) m₀ ≤ 1 + meanBackgroundMassFrom (μ n) m₀ / m₀ := by
          calc
            _ ≤ ∑ x, (μ n).weight x * (1 + backgroundMassFrom m₀ x / m₀) :=
              mean_le_of_pointwise (μ n) (thresholdCount_le_massFrom m₀ (by omega))
            _ = _ := by
              simp only [mul_add, mul_one, Finset.sum_add_distrib, (μ n).normalized,
                meanBackgroundMassFrom, div_eq_mul_inv, Finset.sum_mul, mul_assoc]
        refine (div_le_div_of_nonneg_right hmean (hLpos n).le).trans_eq ?_
        rw [div_mul_div_comm, mul_comm (N n : ℝ) (L n : ℝ), mul_div_mul_right _ _ hN]
        ring
    -- hence so do sites with at least three
    have hthree := thresholdDensity_tendsto_zero_of_le hL hLlim hw μ 3 m₀ (by norm_num) hm₀ htop
    have hinv : Tendsto (fun n => (L n : ℝ) / (N n : ℝ)) atTop (𝓝 ρ⁻¹) := by
      simpa only [inv_div] using hdensity.inv₀ hρ.ne'
    have hlim := ((hthree.mul hinv).const_mul (m₀ : ℝ)).add h
    simp only [zero_mul, mul_zero, zero_add] at hlim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    · exact Eventually.of_forall fun n =>
        div_nonneg ((meanBackgroundMassFrom_nonneg (μ n) 3).trans_eq
          (meanBigBackgroundMass_eq_meanBackgroundMassFrom (μ n)).symm) (Nat.cast_nonneg _)
    · refine Eventually.of_forall fun n => ?_
      have hmean : meanBigBackgroundMass (μ n) ≤
          (m₀ : ℝ) * meanThresholdCount (μ n) 3 + meanBackgroundMassFrom (μ n) m₀ := by
        calc
          _ ≤ ∑ x, (μ n).weight x * ((m₀ : ℝ) * (∑ i, if 3 ≤ occ x i then (1 : ℝ) else 0) +
              backgroundMassFrom m₀ x) :=
            mean_le_of_pointwise (μ n) (big_le_threshold_add_massFrom m₀)
          _ = _ := by
            simp only [mul_add, Finset.sum_add_distrib, meanThresholdCount,
              meanBackgroundMassFrom, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro i _
            ring
      refine (div_le_div_of_nonneg_right hmean (Nat.cast_nonneg _)).trans_eq ?_
      rw [add_div, div_mul_div_comm, mul_comm (L n : ℝ) (N n : ℝ),
        mul_div_mul_right _ _ (hLpos n).ne', mul_div_assoc]

/-- **Only large clusters need control.** For every fixed `m₀ ≥ 3`, along any
positive-density thermodynamic sequence at fixed positive rate, the tails of
the background fraction vanish exactly when the background mass in piles of at
least `m₀` particles is `o(N)`. -/
theorem tails_vanish_iff_backgroundMassFrom_tendsto_zero
    {L N : ℕ → ℕ} [∀ n, NeZero (L n)] {w ρ : ℝ}
    (hL : ∀ n, 3 ≤ L n) (hLlim : Tendsto L atTop atTop) (hw : 0 < w) (hρ : 0 < ρ)
    (hdensity : Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ))
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) (m₀ : ℕ) (hm₀ : 3 ≤ m₀) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => backgroundTail (μ n) ε) atTop (𝓝 0)) ↔
      Tendsto (fun n => meanBackgroundMassFrom (μ n) m₀ / (N n : ℝ)) atTop (𝓝 0) :=
  (tails_vanish_iff_bigBackgroundMass_tendsto_zero hL hLlim hw hρ hdensity μ).trans
    (bigBackgroundMass_tendsto_zero_iff_backgroundMassFrom hL hLlim hw hρ hdensity μ m₀ hm₀)

/-- The global target in terms of the unique equilibrium and any fixed mass
cutoff `m₀ ≥ 3`. -/
theorem supercondensesAt_iff_equilibrium_backgroundMassFrom_tendsto_zero {w ρ : ℝ}
    (hw : 0 < w) (hρ : 0 < ρ) (m₀ : ℕ) (hm₀ : 3 ≤ m₀) :
    SupercondensesAt w ρ ↔
      ∀ (L N : ℕ → ℕ) (hL : ∀ n, 3 ≤ L n) [∀ n, NeZero (L n)],
        Tendsto L atTop atTop →
        Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ) →
        Tendsto (fun n => meanBackgroundMassFrom (equilibrium (N := N n) (hL n) hw) m₀ /
          (N n : ℝ)) atTop (𝓝 0) := by
  rw [supercondensesAt_iff_equilibrium_bigBackgroundMass_tendsto_zero hw hρ]
  constructor
  · intro h L N hL _ hLlim hd
    exact (bigBackgroundMass_tendsto_zero_iff_backgroundMassFrom hL hLlim hw hρ hd _ m₀ hm₀).mp
      (h L N hL hLlim hd)
  · intro h L N hL _ hLlim hd
    exact (bigBackgroundMass_tendsto_zero_iff_backgroundMassFrom hL hLlim hw hρ hd _ m₀ hm₀).mpr
      (h L N hL hLlim hd)

/-! ## From cluster counts to cluster mass -/

/-- Layer-cake decomposition. A pile of `a ≥ m₀` particles contributes `m₀ - 1`
through the first tail count and one through each count from `m₀` to `a`. -/
theorem backgroundMassFrom_eq_tailCounts {L N : ℕ} [NeZero L] (m₀ : ℕ) (hm₀ : 1 ≤ m₀)
    (x : State L N) :
    backgroundMassFrom m₀ x = ((m₀ - 1 : ℕ) : ℝ) * backgroundTailCount m₀ x +
      ∑ m ∈ Finset.Icc m₀ N, backgroundTailCount m x := by
  unfold backgroundMassFrom backgroundTailCount
  rw [Finset.mul_sum, Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hN : occ x i ≤ N := Nat.lt_succ_iff.mp (x.val i).isLt
  by_cases hp : i = peakSite x
  · simp [hp]
  · simp only [ne_eq, hp, not_false_eq_true, true_and]
    rw [Finset.sum_boole]
    have hfilter : (Finset.Icc m₀ N).filter (fun m => m ≤ occ x i) = Finset.Icc m₀ (occ x i) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hfilter, Nat.card_Icc]
    split_ifs with h
    · rw [mul_one, ← Nat.cast_add]
      congr 1
      omega
    · rw [mul_zero, zero_add, show occ x i + 1 - m₀ = 0 by omega, Nat.cast_zero]

/-- Any bound on the tail counts from `m₀` on bounds the background mass in
piles of at least `m₀` particles. -/
theorem stationary_backgroundMassFrom_le_of_tailCounts {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (b : ℕ → ℝ)
    (hb : ∀ m, m₀ ≤ m → meanBackgroundTailCount μ m ≤ b m) :
    meanBackgroundMassFrom μ m₀ ≤ ((m₀ - 1 : ℕ) : ℝ) * b m₀ + ∑ m ∈ Finset.Icc m₀ N, b m := by
  have h : meanBackgroundMassFrom μ m₀ = ((m₀ - 1 : ℕ) : ℝ) * meanBackgroundTailCount μ m₀ +
      ∑ m ∈ Finset.Icc m₀ N, meanBackgroundTailCount μ m := by
    unfold meanBackgroundMassFrom meanBackgroundTailCount
    simp_rw [backgroundMassFrom_eq_tailCounts m₀ hm₀, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro x _
      ring
    · exact Finset.sum_comm
  rw [h]
  exact add_le_add (mul_le_mul_of_nonneg_left (hb m₀ le_rfl) (Nat.cast_nonneg _))
    (Finset.sum_le_sum fun m hm => hb m (Finset.mem_Icc.mp hm).1)

/-- Geometric decay of the tail counts at scale `g` bounds the mass by a fixed
multiple of `g`. -/
theorem stationary_backgroundMassFrom_le_of_geometric {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) {g q : ℝ} (hg : 0 ≤ g)
    (hq0 : 0 ≤ q) (hq : q < 1)
    (hb : ∀ m, m₀ ≤ m → meanBackgroundTailCount μ m ≤ g * q ^ m) :
    meanBackgroundMassFrom μ m₀ ≤ ((m₀ : ℝ) + 1 / (1 - q)) * g := by
  refine (stationary_backgroundMassFrom_le_of_tailCounts μ m₀ hm₀ _ hb).trans ?_
  have hq1 : 0 < 1 - q := by linarith
  have hpow : q ^ m₀ ≤ 1 := pow_le_one₀ hq0 hq.le
  have hgeom : ∑ m ∈ Finset.Icc m₀ N, q ^ m ≤ 1 / (1 - q) := by
    rw [← Nat.Ico_succ_right]
    exact (geom_sum_Ico_le_of_lt_one hq0 hq).trans
      (div_le_div_of_nonneg_right hpow hq1.le)
  have hcast : ((m₀ - 1 : ℕ) : ℝ) ≤ m₀ := by exact_mod_cast Nat.sub_le m₀ 1
  rw [← Finset.mul_sum]
  have h1 : ((m₀ - 1 : ℕ) : ℝ) * (g * q ^ m₀) ≤ (m₀ : ℝ) * g := by
    have := mul_le_mul_of_nonneg_left hpow hg
    rw [mul_one] at this
    exact mul_le_mul hcast this (mul_nonneg hg (pow_nonneg hq0 _)) (Nat.cast_nonneg _)
  have h2 : g * ∑ m ∈ Finset.Icc m₀ N, q ^ m ≤ g * (1 / (1 - q)) :=
    mul_le_mul_of_nonneg_left hgeom hg
  linarith

/-- **Conditional supercondensation along a sequence.** Suppose that, beyond a
fixed mass `m₀`, the expected number of background sites holding at least `m`
particles is eventually at most `g n * q ^ m`, with `q < 1` and `g n = o(L n)`.
Then the tails of the background fraction vanish. Nothing is assumed about
piles of fewer than `m₀` particles. -/
theorem tails_vanish_of_tailCount_le {L N : ℕ → ℕ} [∀ n, NeZero (L n)] {w ρ : ℝ}
    (hL : ∀ n, 3 ≤ L n) (hLlim : Tendsto L atTop atTop) (hw : 0 < w) (hρ : 0 < ρ)
    (hdensity : Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ))
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) (m₀ : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1)
    (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg : Tendsto (fun n => g n / (L n : ℝ)) atTop (𝓝 0))
    (hcount : ∀ᶠ n in atTop, ∀ m, m₀ ≤ m → meanBackgroundTailCount (μ n) m ≤ g n * q ^ m) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => backgroundTail (μ n) ε) atTop (𝓝 0) := by
  let m₁ := max m₀ 3
  have hm₁ : 3 ≤ m₁ := le_max_right _ _
  apply (tails_vanish_iff_backgroundMassFrom_tendsto_zero hL hLlim hw hρ hdensity μ m₁ hm₁).mpr
  have hLpos (n : ℕ) : (0 : ℝ) < (L n : ℝ) := by exact_mod_cast (NeZero.pos (L n))
  have hinv : Tendsto (fun n => (L n : ℝ) / (N n : ℝ)) atTop (𝓝 ρ⁻¹) := by
    simpa only [inv_div] using hdensity.inv₀ hρ.ne'
  have hlim := (hg.mul hinv).const_mul ((m₁ : ℝ) + 1 / (1 - q))
  simp only [zero_mul, mul_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall fun n =>
      div_nonneg (meanBackgroundMassFrom_nonneg _ _) (Nat.cast_nonneg _)
  · filter_upwards [hcount] with n hn
    have hmass := stationary_backgroundMassFrom_le_of_geometric (μ n) m₁ (by omega) (hg0 n)
      hq0 hq (fun m hm => hn m ((le_max_left _ _).trans hm))
    refine (div_le_div_of_nonneg_right hmass (Nat.cast_nonneg _)).trans_eq ?_
    rw [div_mul_div_comm, mul_comm (L n : ℝ) (N n : ℝ), mul_div_mul_right _ _ (hLpos n).ne',
      mul_div_assoc]

/-! ## The hypothesis and the conditional theorem -/

/-- **Decay of cluster counts in mass.** Beyond some fixed mass `m₀`, on every
ring and for every stationary law, the expected number of background sites
holding at least `m` particles is at most `g L * q ^ m`. Here `q < 1` and the
scale `g` is sublinear in the ring size. The background excludes one largest
site. Nothing is assumed about piles of fewer than `m₀` particles. -/
def ClusterCountDecay (w : ℝ) : Prop :=
  ∃ (m₀ : ℕ) (q : ℝ) (g : ℕ → ℝ), 0 ≤ q ∧ q < 1 ∧ (∀ L, 0 ≤ g L) ∧
    Tendsto (fun L => g L / (L : ℝ)) atTop (𝓝 0) ∧
    ∀ (L N : ℕ) [NeZero L], 3 ≤ L → ∀ μ : StationaryLaw L N w, ∀ m, m₀ ≤ m →
      meanBackgroundTailCount μ m ≤ g L * q ^ m

/-- **Conditional supercondensation.** At a fixed positive rate, decay of the
large cluster counts gives supercondensation at every positive density. -/
theorem supercondensesAt_of_clusterCountDecay {w : ℝ} (hw : 0 < w)
    (h : ClusterCountDecay w) {ρ : ℝ} (hρ : 0 < ρ) : SupercondensesAt w ρ := by
  obtain ⟨m₀, q, g, hq0, hq, hg0, hg, hbound⟩ := h
  refine ⟨fun _ _ hL => stationaryLaw_exists (by omega) hw.le, ?_⟩
  intro L N hL hLlim hd μ
  letI (n : ℕ) : NeZero (L n) := ⟨by have := hL n; omega⟩
  exact tails_vanish_of_tailCount_le hL hLlim hw hρ hd μ m₀ hq0 hq (fun n => g (L n))
    (fun n => hg0 (L n)) (hg.comp hLlim)
    (Eventually.of_forall fun n => hbound (L n) (N n) (hL n) (μ n))

/-- The small-rate conjecture follows from decay of the large cluster counts at
every small rate. -/
theorem smallWSupercondensation_of_clusterCountDecay
    (h : ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ ≤ 1 ∧ ∀ w : ℝ, 0 < w → w < w₀ → ClusterCountDecay w) :
    SmallWSupercondensation := by
  obtain ⟨w₀, h0, h1, hw⟩ := h
  exact ⟨w₀, h0, h1, fun w hw0 hww ρ hρ =>
    supercondensesAt_of_clusterCountDecay hw0 (hw w hw0 hww) hρ⟩

/-- A power law `C L ^ θ` with `θ < 1` is a sublinear scale. -/
theorem clusterCountDecay_of_rpow {w C θ q : ℝ} (m₀ : ℕ) (hC : 0 ≤ C) (hθ : θ < 1)
    (hq0 : 0 ≤ q) (hq : q < 1)
    (h : ∀ (L N : ℕ) [NeZero L], 3 ≤ L → ∀ μ : StationaryLaw L N w, ∀ m, m₀ ≤ m →
      meanBackgroundTailCount μ m ≤ C * (L : ℝ) ^ θ * q ^ m) :
    ClusterCountDecay w := by
  refine ⟨m₀, q, fun L => C * (L : ℝ) ^ θ, hq0, hq,
    fun L => mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg L) θ), ?_, h⟩
  have hpow : Tendsto (fun L : ℕ => (L : ℝ) ^ (θ - 1)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).comp tendsto_natCast_atTop_atTop
    simpa only [neg_sub, Function.comp_def] using this
  have hlim := hpow.const_mul C
  rw [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [Real.rpow_sub_one hL', mul_div_assoc]

end
end Chipping
