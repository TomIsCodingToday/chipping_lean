import Mathlib.Data.Real.Sqrt
import ChippingSupercondensation.PileBirths
import ChippingSupercondensation.PileCount

/-! # Unconditional reduction to mass in background piles of size at least three -/

namespace Chipping
open Filter
open scoped BigOperators Topology
noncomputable section

def meanBigBackgroundMass {L N : ℕ} [NeZero L] {w : ℝ} (μ : StationaryLaw L N w) : ℝ :=
  ∑ x, μ.weight x * bigBackgroundMass x

private theorem meanBigBackgroundMass_bounds {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) :
    0 ≤ meanBigBackgroundMass μ ∧ meanBigBackgroundMass μ ≤ meanMultipleBackgroundMass μ ∧
    meanMultipleBackgroundMass μ ≤ meanBigBackgroundMass μ + 2 * meanMultipleCount μ ∧
    meanAboveCapCount μ 2 ≤ 1 + meanBigBackgroundMass μ / 3 := by
  have hmass (x : State L N) : multipleBackgroundMass x =
      ∑ i, if i ≠ peakSite x ∧ 2 ≤ occ x i then (occ x i : ℝ) else 0 := by
    unfold multipleBackgroundMass
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (peakSite x))]
    simp only [add_sub_cancel_left]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (peakSite x))]
    simp only [ne_self_iff_false, false_and, if_false, zero_add]
    exact Finset.sum_congr rfl (fun i hi => by simp [(Finset.mem_erase.mp hi).1])
  have hpoint (x : State L N) : bigBackgroundMass x ≤ multipleBackgroundMass x ∧
      multipleBackgroundMass x ≤ bigBackgroundMass x + 2 * multipleCount x := by
    rw [hmass]
    unfold bigBackgroundMass multipleCount
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    constructor <;> apply Finset.sum_le_sum <;> intro i _
    all_goals
      by_cases hp : i = peakSite x
      · subst i
        simp only [ne_self_iff_false, false_and, if_false, zero_add]
        first | exact le_rfl | split_ifs <;> norm_num
      · by_cases h3 : 3 ≤ occ x i <;> by_cases h2 : 2 ≤ occ x i <;>
          simp [h3, h2, hp]
        all_goals omega
  refine ⟨Finset.sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x)
    (Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity))),
    Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x).1 (μ.nonneg x)), ?_, ?_⟩
  · calc
      _ ≤ ∑ x, μ.weight x * (bigBackgroundMass x + 2 * multipleCount x) :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x).2 (μ.nonneg x))
      _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib, meanBigBackgroundMass,
                    meanMultipleCount, Finset.mul_sum, mul_left_comm (2 : ℝ)]
  · calc
      _ ≤ ∑ x, μ.weight x * (1 + bigBackgroundMass x / 3) :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (bigCount_le x) (μ.nonneg x))
      _ = _ := by simp_rw [mul_add, mul_one, Finset.sum_add_distrib, μ.normalized,
                    meanBigBackgroundMass, div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]

/-- Along any positive-density thermodynamic sequence at fixed positive rate,
controlling the mass in piles of size at least three outside one largest pile
is equivalent to supercondensation in probability. -/
theorem tails_vanish_iff_bigBackgroundMass_tendsto_zero
    {L N : ℕ → ℕ} [∀ n, NeZero (L n)] {w ρ : ℝ}
    (hL : ∀ n, 3 ≤ L n) (hLlim : Tendsto L atTop atTop) (hw : 0 < w) (hρ : 0 < ρ)
    (hdensity : Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ))
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => backgroundTail (μ n) ε) atTop (𝓝 0)) ↔
      Tendsto (fun n => meanBigBackgroundMass (μ n) / (N n : ℝ)) atTop (𝓝 0) := by
  rw [tails_vanish_iff_multipleBackgroundMass_tendsto_zero hL hLlim hw hρ hdensity]
  have hb := fun n => meanBigBackgroundMass_bounds (μ n)
  have hpos := eventually_pos_mass_of_tendsto_density hρ hdensity
  have hLpos (n : ℕ) : (0 : ℝ) < (L n : ℝ) := by exact_mod_cast (NeZero.pos (L n))
  constructor
  · intro h
    exact squeeze_zero (fun n => div_nonneg (hb n).1 (by positivity))
      (fun n => div_le_div_of_nonneg_right (hb n).2.1 (by positivity)) h
  · intro hbig
    have hinv : Tendsto (fun n => 1 / (L n : ℝ)) atTop (𝓝 0) := by
      simp only [one_div]
      exact (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hLlim
    have hcap : Tendsto (fun n => meanAboveCapCount (μ n) 2 / (L n : ℝ)) atTop (𝓝 0) := by
      have h := hinv.add ((hbig.mul hdensity).div_const 3)
      simp only [zero_mul, zero_div, add_zero] at h
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      · exact Eventually.of_forall fun n => div_nonneg (Finset.sum_nonneg fun x _ =>
          mul_nonneg ((μ n).nonneg x) (Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num))
          (hLpos n).le
      · filter_upwards [hpos] with n hn
        have hN : (N n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        refine (div_le_div_of_nonneg_right (hb n).2.2.2 (hLpos n).le).trans_eq ?_
        field_simp [hN, (hLpos n).ne', mul_comm]
    have hmult := multipleDensity_tendsto_zero_of_bigDensity_tendsto_zero hL hLlim hw μ hcap
    have hratio := hmult.div hdensity hρ.ne'
    rw [zero_div] at hratio
    have htwo : Tendsto (fun n => meanMultipleCount (μ n) / (N n : ℝ)) atTop (𝓝 0) := by
      refine hratio.congr' (Eventually.of_forall fun n => ?_)
      change (_ / (L n : ℝ)) / ((N n : ℝ) / (L n : ℝ)) = _
      rw [div_div_div_cancel_right₀ (hLpos n).ne']
    have h := hbig.add (htwo.const_mul 2)
    simp only [mul_zero, add_zero] at h
    apply squeeze_zero _ _ h
    · intro n
      exact div_nonneg ((hb n).1.trans (hb n).2.1) (by positivity)
    · intro n
      refine (div_le_div_of_nonneg_right (hb n).2.2.1 (by positivity)).trans_eq ?_
      ring

/-- The global target expressed using the unique equilibrium and mass-three cutoff. -/
theorem supercondensesAt_iff_equilibrium_bigBackgroundMass_tendsto_zero {w ρ : ℝ}
    (hw : 0 < w) (hρ : 0 < ρ) :
    SupercondensesAt w ρ ↔
      ∀ (L N : ℕ → ℕ) (hL : ∀ n, 3 ≤ L n) [∀ n, NeZero (L n)],
        Tendsto L atTop atTop →
        Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ) →
        Tendsto (fun n => meanBigBackgroundMass (equilibrium (N := N n) (hL n) hw) /
          (N n : ℝ)) atTop (𝓝 0) := by
  constructor
  · intro h L N hL inst hlim hd
    exact (tails_vanish_iff_bigBackgroundMass_tendsto_zero hL hlim hw hρ hd _).mp
      (h.2 L N hL hlim hd _)
  · intro h
    refine ⟨fun _ _ hL => stationaryLaw_exists (by omega) hw.le, ?_⟩
    intro L N hL hlim hd μ
    letI (n : ℕ) : NeZero (L n) := ⟨by have := hL n; omega⟩
    apply (tails_vanish_iff_bigBackgroundMass_tendsto_zero hL hlim hw hρ hd μ).mpr
    have heq : μ = fun n => equilibrium (N := N n) (hL n) hw :=
      funext (fun n => stationaryLaw_eq (hL n) hw (μ n) _)
    rw [heq]
    exact h L N hL hlim hd

/-! ## Mass within a short distance of a largest pile -/

/-- The largest pile dominates the mass at its displaced site. Their product
occurs as one summand of the correlation at that offset. -/
private theorem peak_neighbor_sq_le {L N : ℕ} [NeZero L] (x : State L N) (d : Fin L) :
    (occ x (peakSite x + d) : ℝ) ^ 2 ≤ massProductAt x d := by
  have hmax : occ x (peakSite x + d) ≤ occ x (peakSite x) := by
    rw [occ_peakSite]
    exact Finset.le_sup (Finset.mem_univ _)
  have hreal : (occ x (peakSite x + d) : ℝ) ≤ occ x (peakSite x) := by exact_mod_cast hmax
  rw [sq]
  exact (mul_le_mul_of_nonneg_right hreal (Nat.cast_nonneg _)).trans
    (Finset.single_le_sum (f := fun i => (occ x i : ℝ) * (occ x (i + d) : ℝ))
      (fun _ _ => by positivity) (Finset.mem_univ _))

/-- Both orientations have the same upper bound, even when the choice of a
largest site breaks a tie. -/
theorem stationary_peak_neighbor_fraction_le {L N : ℕ} [NeZero L] {w : ℝ}
    (hw : 0 ≤ w) (hw' : w ≤ 1) (μ : StationaryLaw L N w) (r : ℕ) (hr : (r : Fin L) ≠ 0)
    (backward : Bool) :
    (∑ x, μ.weight x * ((occ x (peakSite x + (if backward then -(r : Fin L) else r)) : ℝ) / N)) ≤
      Real.sqrt (((r : ℝ) + 1) / N) := by
  let d : Fin L := if backward then -(r : Fin L) else r
  let f := fun x : State L N => (occ x (peakSite x + d) : ℝ) / N
  have hcorr (x : State L N) : massProductAt x d = massProductAt x (r : Fin L) := by
    cases backward <;> simp [d, massProductAt_neg]
  have hsite (x : State L N) : f x ^ 2 ≤ massProductAt x (r : Fin L) / (N : ℝ) ^ 2 := by
    rw [← hcorr x]
    simpa [f, div_pow] using div_le_div_of_nonneg_right (peak_neighbor_sq_le x d)
      (sq_nonneg (N : ℝ))
  have hsq := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (r := fun x => μ.weight x * f x) (f := μ.weight) (g := fun x => μ.weight x * f x ^ 2)
    (fun x _ => μ.nonneg x) (fun x _ => mul_nonneg (μ.nonneg x) (sq_nonneg _)) (fun _ _ => by ring)
  rw [μ.normalized, one_mul] at hsq
  apply Real.le_sqrt_of_sq_le
  refine hsq.trans ((Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hsite x) (μ.nonneg x))).trans ?_)
  simpa only [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul] using
    (normalized_stationary_massProductAt_bounds hw hw' r hr μ).2

/-- The stationary mean fraction on the first R sites ahead of, or behind,
one largest pile. The peak itself is excluded whenever R < L. -/
def meanPeakWindowFraction {L N : ℕ} [NeZero L] {w : ℝ} (μ : StationaryLaw L N w)
    (R : ℕ) (backward : Bool) : ℝ :=
  ∑ j ∈ Finset.range R, ∑ x, μ.weight x * ((occ x (peakSite x +
    (if backward then -((j + 1 : ℕ) : Fin L) else ((j + 1 : ℕ) : Fin L))) : ℝ) / N)

/-- The entire window has vanishing mass fraction up to radii o(N^(1/3)). -/
theorem stationary_peakWindowFraction_le {L N : ℕ} [NeZero L] {w : ℝ}
    (hw : 0 ≤ w) (hw' : w ≤ 1) (μ : StationaryLaw L N w) (R : ℕ) (hR : R < L) (backward : Bool) :
    meanPeakWindowFraction μ R backward ≤ Real.sqrt ((R : ℝ) ^ 2 * (R + 1) / N) := by
  calc
    _ ≤ ∑ _j ∈ Finset.range R, Real.sqrt (((R : ℝ) + 1) / N) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjR : j + 1 ≤ R := Finset.mem_range.mp hj
      refine (stationary_peak_neighbor_fraction_le hw hw' μ (j + 1)
        (natCast_fin_ne_zero (by omega) (hjR.trans_lt hR)) backward).trans ?_
      exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
        (add_le_add_right (by exact_mod_cast hjR) 1) (Nat.cast_nonneg _))
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_assoc,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

theorem meanPeakWindowFraction_tendsto_zero {L N R : ℕ → ℕ} [∀ n, NeZero (L n)]
    {w : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1) (μ : (n : ℕ) → StationaryLaw (L n) (N n) w)
    (hR : ∀ᶠ n in atTop, R n < L n)
    (hscale : Tendsto (fun n => (R n : ℝ) ^ 2 * (R n + 1) / N n) atTop (𝓝 0))
    (backward : Bool) :
    Tendsto (fun n => meanPeakWindowFraction (μ n) (R n) backward) atTop (𝓝 0) := by
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hscale
  rw [Real.sqrt_zero] at hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
  · exact Eventually.of_forall fun n => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun x _ =>
      mul_nonneg ((μ n).nonneg x) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact hR.mono fun n hn => stationary_peakWindowFraction_le hw hw' (μ n) (R n) hn backward

/-! ## Separating smaller background piles from a second macroscopic pile -/

/-- Mass in background piles of size between three and the cutoff, inclusive. -/
def bigBackgroundMassUpTo {L N : ℕ} [NeZero L] (b : ℕ) (x : State L N) : ℝ :=
  ∑ i, if i ≠ peakSite x ∧ 3 ≤ occ x i ∧ occ x i ≤ b then (occ x i : ℝ) else 0

def meanBigBackgroundMassUpTo {L N : ℕ} [NeZero L] {w : ℝ} (μ : StationaryLaw L N w)
    (b : ℕ) : ℝ := ∑ x, μ.weight x * bigBackgroundMassUpTo b x

private theorem two_marks_of_background_above {L N : ℕ} [NeZero L] (x : State L N)
    (b : ℕ) (i : Fin L) (hi : i ≠ peakSite x) (hb : b < occ x i) :
    2 ≤ maskCount (largePileMask b x) := by
  have hp : b < occ x (peakSite x) := by
    rw [occ_peakSite]
    exact hb.trans_le (Finset.le_sup (f := occ x) (Finset.mem_univ i))
  let marked := fun j => (bitMass (largePileMask b x j) : ℝ)
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({i, peakSite x} : Finset (Fin L)))
    (f := marked) (fun j _ _ => Nat.cast_nonneg _)
  rw [Finset.sum_pair hi] at h
  have hi' : marked i = 1 := by simp [marked, largePileMask, bitMass, hb]
  have hp' : marked (peakSite x) = 1 := by simp [marked, largePileMask, bitMass, hp]
  rw [hi', hp'] at h
  exact (by norm_num : (2 : ℝ) = 1 + 1) ▸ h

/-- Above a given cutoff the background can have mass only when two distinct
piles cross that cutoff. This also covers ties for the maximum. -/
theorem meanBigBackgroundMass_le_cutoff {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (b : ℕ) :
    meanBigBackgroundMass μ ≤ meanBigBackgroundMassUpTo μ b + (N : ℝ) * twoLargePilesProbability μ b := by
  have hstate (x : State L N) : bigBackgroundMass x ≤ bigBackgroundMassUpTo b x +
      (if 2 ≤ maskCount (largePileMask b x) then (N : ℝ) else 0) := by
    by_cases h : 2 ≤ maskCount (largePileMask b x)
    · rw [if_pos h]
      have htotal : (∑ i, (occ x i : ℝ)) = N := by exact_mod_cast x.property
      have hle : bigBackgroundMass x ≤ N := by
        rw [← htotal]
        exact Finset.sum_le_sum fun i _ => by split_ifs <;> first | exact le_rfl | positivity
      exact hle.trans (le_add_of_nonneg_left
        (Finset.sum_nonneg fun i _ => by split_ifs <;> positivity))
    · rw [if_neg h, add_zero]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ≠ peakSite x ∧ 3 ≤ occ x i
      · have hb : occ x i ≤ b := le_of_not_gt (fun hgt =>
          h (two_marks_of_background_above x b i hi.1 hgt))
        simp [hi.1, hi.2, hb]
      · simp only [if_neg hi]
        split_ifs <;> positivity
  calc
    _ ≤ ∑ x, μ.weight x * (bigBackgroundMassUpTo b x +
        (if 2 ≤ maskCount (largePileMask b x) then (N : ℝ) else 0)) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hstate x) (μ.nonneg x)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, meanBigBackgroundMassUpTo, twoLargePilesProbability,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> ring

/-- Any cutoff sequence can be used: it suffices to control the mean mass
from three through the cutoff and the probability of two piles above it. -/
theorem tails_vanish_of_band_mass_and_twoLargePiles {L N : ℕ → ℕ} [∀ n, NeZero (L n)]
    {w ρ : ℝ} (hL : ∀ n, 3 ≤ L n) (hLlim : Tendsto L atTop atTop) (hw : 0 < w) (hρ : 0 < ρ)
    (hdensity : Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ))
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) (b : ℕ → ℕ)
    (hband : Tendsto (fun n => meanBigBackgroundMassUpTo (μ n) (b n) / (N n : ℝ)) atTop (𝓝 0))
    (hpair : Tendsto (fun n => twoLargePilesProbability (μ n) (b n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => backgroundTail (μ n) ε) atTop (𝓝 0) := by
  apply (tails_vanish_iff_bigBackgroundMass_tendsto_zero hL hLlim hw hρ hdensity μ).mpr
  have h := hband.add hpair
  rw [add_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · exact Eventually.of_forall fun n =>
      div_nonneg (meanBigBackgroundMass_bounds (μ n)).1 (by positivity)
  · filter_upwards [eventually_pos_mass_of_tendsto_density hρ hdensity] with n hn
    have hN : (0 : ℝ) < N n := by exact_mod_cast hn
    have hle := div_le_div_of_nonneg_right (meanBigBackgroundMass_le_cutoff (μ n) (b n)) hN.le
    rwa [add_div, mul_div_cancel_left₀ _ hN.ne'] at hle

/-- A global finite-volume bound with an explicit nearby-chip error. The same
cutoff controls whole-pile and distant-chip births. -/
theorem stationary_bigBackgroundFraction_le_band_and_births {L N : ℕ} [NeZero L]
    (hL : 3 ≤ L) {w α β : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1) (hα : 0 < α) (hβ : 0 < β)
    (hN : 0 < N) (μ : StationaryLaw L N w) (a b R : ℕ) (hab : a ≤ b) (hR : R < L)
    (halow : α * (N : ℝ) ≤ (a : ℝ)) (hwidth : β * (N : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ)) :
    ∃ k ∈ Finset.Icc a b, meanBigBackgroundMass μ / (N : ℝ) ≤
      meanBigBackgroundMassUpTo μ b / N + (meanWholeAndDistantChipBirthDamage μ k R +
        (w / (α ^ 3 * β)) * ((L : ℝ) / N) * ((R : ℝ) ^ 2 * (R + 1) / N)) / 2 := by
  obtain ⟨k, hk, hdamage⟩ := stationary_twoLargePilesProbability_le_wholeAndDistantChipBirthDamage
    hL hw hw' hα hβ hN μ a b R hab hR halow hwidth
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := div_le_div_of_nonneg_right (meanBigBackgroundMass_le_cutoff μ b) hN'.le
  rw [add_div, mul_div_cancel_left₀ _ hN'.ne'] at h
  exact ⟨k, hk, h.trans (add_le_add_left (by linarith only [hdamage]) _)⟩

/-- Sites at positive offsets one through R in a chosen direction. -/
private def windowSite {L N : ℕ} [NeZero L] (x : State L N) (backward : Bool) (j : ℕ) : Fin L :=
  peakSite x + (if backward then -((j + 1 : ℕ) : Fin L) else ((j + 1 : ℕ) : Fin L))

def peakNeighborhood {L N : ℕ} [NeZero L] (x : State L N) (R : ℕ) : Finset (Fin L) :=
  (Finset.range R).image (windowSite x false) ∪ (Finset.range R).image (windowSite x true)

/-- Stationary mass fraction outside the 2R neighbors of the peak, with site
masses restricted to the interval from three through b. -/
def meanDistantBandFraction {L N : ℕ} [NeZero L] {w : ℝ} (μ : StationaryLaw L N w)
    (b R : ℕ) : ℝ :=
  ∑ x, μ.weight x * ∑ i ∈ (peakNeighborhood x R)ᶜ,
    if i ≠ peakSite x ∧ 3 ≤ occ x i ∧ occ x i ≤ b then (occ x i : ℝ) / N else 0

private theorem band_le_distant_and_windows {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (b R : ℕ) :
    meanBigBackgroundMassUpTo μ b / N ≤ meanDistantBandFraction μ b R +
      meanPeakWindowFraction μ R false + meanPeakWindowFraction μ R true := by
  let mass (x : State L N) (i : Fin L) := (occ x i : ℝ) / N
  let band (x : State L N) (i : Fin L) :=
    if i ≠ peakSite x ∧ 3 ≤ occ x i ∧ occ x i ≤ b then mass x i else 0
  have hnon (x : State L N) (i : Fin L) : 0 ≤ mass x i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hwin (x : State L N) (rear : Bool) :
      ∑ i ∈ (Finset.range R).image (windowSite x rear), mass x i ≤
      ∑ j ∈ Finset.range R, mass x (windowSite x rear j) :=
    Finset.sum_image_le_of_nonneg (fun i _ => hnon x i)
  have hstate (x : State L N) : (∑ i, band x i) ≤
      (∑ i ∈ (peakNeighborhood x R)ᶜ, band x i) +
      (∑ j ∈ Finset.range R, mass x (windowSite x false j)) +
      (∑ j ∈ Finset.range R, mass x (windowSite x true j)) := by
    rw [← Finset.sum_add_sum_compl (peakNeighborhood x R) (band x)]
    have hnear : ∑ i ∈ peakNeighborhood x R, band x i ≤ ∑ i ∈ peakNeighborhood x R, mass x i := by
      apply Finset.sum_le_sum
      intro i _
      unfold band
      split_ifs <;> first | exact le_rfl | exact hnon _ _
    let A := (Finset.range R).image (windowSite x false)
    let B := (Finset.range R).image (windowSite x true)
    have hu := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := mass x)
    have hnn : 0 ≤ ∑ i ∈ A ∩ B, mass x i := Finset.sum_nonneg fun i _ => hnon x i
    change (∑ i ∈ A ∪ B, mass x i) + _ = _ at hu
    change _ ≤ ∑ i ∈ A ∪ B, mass x i at hnear
    linarith only [hnear, hu, hnn, hwin x false, hwin x true]
  have hmean (rear : Bool) : (∑ x, μ.weight x * ∑ j ∈ Finset.range R, mass x (windowSite x rear j)) =
      meanPeakWindowFraction μ R rear := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    rfl
  have hband (x : State L N) : bigBackgroundMassUpTo b x / N = ∑ i, band x i := by
    unfold bigBackgroundMassUpTo
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [band, mass, div_eq_mul_inv]
    split_ifs <;> ring
  have h := Finset.sum_le_sum (s := Finset.univ) fun x _ => mul_le_mul_of_nonneg_left (hstate x) (μ.nonneg x)
  simp only [mul_add, Finset.sum_add_distrib, hmean] at h
  unfold meanBigBackgroundMassUpTo
  calc
    _ = ∑ x, μ.weight x * (bigBackgroundMassUpTo b x / N) := by
      simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]
    _ ≤ _ := by simpa only [hband] using h

/-- Global bound with only two unknown terms: mass in distant intermediate
piles, and whole-pile or distant-chip births at a selected macroscopic cutoff. -/
theorem stationary_bigBackgroundFraction_le_distantBand_and_births {L N : ℕ} [NeZero L]
    (hL : 3 ≤ L) {w α β : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1) (hα : 0 < α) (hβ : 0 < β)
    (hN : 0 < N) (μ : StationaryLaw L N w) (a b R : ℕ) (hab : a ≤ b) (hR : R < L)
    (halow : α * (N : ℝ) ≤ (a : ℝ)) (hwidth : β * (N : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ)) :
    ∃ k ∈ Finset.Icc a b, meanBigBackgroundMass μ / (N : ℝ) ≤ meanDistantBandFraction μ b R +
      2 * Real.sqrt ((R : ℝ) ^ 2 * (R + 1) / N) + (meanWholeAndDistantChipBirthDamage μ k R +
      (w / (α ^ 3 * β)) * ((L : ℝ) / N) * ((R : ℝ) ^ 2 * (R + 1) / N)) / 2 := by
  obtain ⟨k, hk, h⟩ := stationary_bigBackgroundFraction_le_band_and_births
    hL hw hw' hα hβ hN μ a b R hab hR halow hwidth
  exact ⟨k, hk, by linarith only [h, band_le_distant_and_windows μ b R,
    stationary_peakWindowFraction_le hw hw' μ R hR false, stationary_peakWindowFraction_le hw hw' μ R hR true]⟩

end
end Chipping
