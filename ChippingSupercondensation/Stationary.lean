import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Sequences
import ChippingSupercondensation.Basic

/-!
# Stationary laws and the reduction to particle separation

The particle separation `H` is the probability that two particles sampled with
replacement lie at different sites, and `B/N ≤ H ≤ 2B/N`. Every nonempty ring
has a stationary law at every nonnegative rate (`stationaryLaw_exists`). At
positive rate it is unique (`stationaryLaw_eq`, `equilibrium`) and invariant
under rotation (`stationaryWeight_rotateState`).
`supercondensesAt_iff_meanParticleSeparation_tendsto_zero` and
`supercondensesAt_iff_equilibrium_meanParticleSeparation_tendsto_zero` reduce
`SupercondensesAt` at positive density to the limit of `E[H]`.
-/

namespace Chipping

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The fraction of particles at site `i`. -/
def siteMassFraction {L N : ℕ} (x : State L N) (i : Fin L) : ℝ :=
  (occ x i : ℝ) / (N : ℝ)

/-- For positive total mass, the probability that two particles sampled
independently with replacement are at different sites. -/
def particleSeparation {L N : ℕ} (x : State L N) : ℝ :=
  1 - ∑ i, siteMassFraction x i ^ 2

/-- The probability of particle separation is within a factor of two of
the fraction of mass outside a largest pile. -/
theorem backgroundFraction_le_particleSeparation_le_twice {L N : ℕ}
    (x : State L N) (hN : 0 < N) :
    backgroundFraction x ≤ particleSeparation x ∧
      particleSeparation x ≤ 2 * backgroundFraction x := by
  have htotal : ∑ i, occ x i = N := x.property
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmass : ∑ i, siteMassFraction x i = 1 := by
    simp only [siteMassFraction, div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Nat.cast_sum, htotal, ← div_eq_mul_inv, div_self hNreal.ne']
  have hocc_le_largest (i : Fin L) : occ x i ≤ largest x :=
    Finset.le_sup (Finset.mem_univ i)
  have hlargest_le_total : largest x ≤ N := by
    apply Finset.sup_le
    intro i _
    calc
      occ x i ≤ ∑ j, occ x j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (occ x j)) (Finset.mem_univ i)
      _ = N := htotal
  let m : ℝ := (largest x : ℝ) / (N : ℝ)
  have hbackground : backgroundFraction x = 1 - m := by
    unfold backgroundFraction m
    rw [Nat.cast_sub hlargest_le_total, sub_div, div_self hNreal.ne']
  have hsites : (Finset.univ : Finset (Fin L)).Nonempty := by
    by_cases h : (Finset.univ : Finset (Fin L)).Nonempty
    · exact h
    · rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at htotal
      omega
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hsites (occ x)
  have hmax : m = siteMassFraction x i := by
    unfold m siteMassFraction largest
    rw [hi]
  have hlower : m ^ 2 ≤ ∑ j, siteMassFraction x j ^ 2 := by
    rw [hmax]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (siteMassFraction x j))
      (Finset.mem_univ i)
  have hupper : ∑ j, siteMassFraction x j ^ 2 ≤ m := by
    calc
      ∑ j, siteMassFraction x j ^ 2 ≤ ∑ j, m * siteMassFraction x j := by
        apply Finset.sum_le_sum
        intro j _
        have hle : siteMassFraction x j ≤ m :=
          div_le_div_of_nonneg_right (by exact_mod_cast hocc_le_largest j) hNreal.le
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right hle (by unfold siteMassFraction; positivity)
      _ = m := by rw [← Finset.mul_sum, hmass, mul_one]
  rw [hbackground]
  unfold particleSeparation
  exact ⟨sub_le_sub_left hupper 1, by nlinarith [sq_nonneg (1 - m)]⟩

/-- The expected particle separation under a stationary law. -/
def meanParticleSeparation {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) : ℝ :=
  ∑ x, μ.weight x * particleSeparation x

/-- The pointwise comparison also holds for stationary expectations. -/
theorem meanBackground_le_meanParticleSeparation_le_twice {L N : ℕ} {w : ℝ}
    (μ : StationaryLaw L N w) (hN : 0 < N) :
    meanBackground μ ≤ meanParticleSeparation μ ∧
      meanParticleSeparation μ ≤ 2 * meanBackground μ := by
  unfold meanBackground meanParticleSeparation
  constructor
  · exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
      (backgroundFraction_le_particleSeparation_le_twice x hN).1 (μ.nonneg x))
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    calc
      μ.weight x * particleSeparation x ≤ μ.weight x * (2 * backgroundFraction x) :=
        mul_le_mul_of_nonneg_left
          (backgroundFraction_le_particleSeparation_le_twice x hN).2 (μ.nonneg x)
      _ = 2 * (μ.weight x * backgroundFraction x) := by ring

/-- Vanishing background tails are equivalent to vanishing mean particle
separation along sequences with eventually positive total mass. -/
theorem tails_vanish_iff_meanParticleSeparation_vanishes {L N : ℕ → ℕ} {w : ℝ}
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) (hN : ∀ᶠ n in atTop, 0 < N n) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => backgroundTail (μ n) ε) atTop (𝓝 0)) ↔
      Tendsto (fun n => meanParticleSeparation (μ n)) atTop (𝓝 0) := by
  rw [tails_vanish_iff_mean_vanishes μ]
  have hlower : ∀ᶠ n in atTop, meanBackground (μ n) ≤ meanParticleSeparation (μ n) :=
    hN.mono (fun n hn => (meanBackground_le_meanParticleSeparation_le_twice (μ n) hn).1)
  have hupper : ∀ᶠ n in atTop, meanParticleSeparation (μ n) ≤ 2 * meanBackground (μ n) :=
    hN.mono (fun n hn => (meanBackground_le_meanParticleSeparation_le_twice (μ n) hn).2)
  constructor
  · intro h
    have htwice : Tendsto (fun n => 2 * meanBackground (μ n)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h htwice hlower hupper
  · intro h
    have hnonneg (n : ℕ) : 0 ≤ meanBackground (μ n) :=
      Finset.sum_nonneg (fun x _ => mul_nonneg ((μ n).nonneg x) (backgroundFraction_nonneg x))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall hnonneg) hlower

private theorem finite_stationary_weights {S : Type*} [Fintype S]
    (initial : S) (P : S → S → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) :
    ∃ p ∈ stdSimplex ℝ S, ∀ y, (∑ x, p x * P x y) = p y := by
  classical
  let step (p : S → ℝ) (y : S) : ℝ := ∑ x, p x * P x y
  have hstep (p : S → ℝ) (hp : p ∈ stdSimplex ℝ S) : step p ∈ stdSimplex ℝ S := by
    constructor
    · intro y
      exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp.1 x) (hP x y))
    · unfold step
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hrow, mul_one]
      exact hp.2
  let orbit (n : ℕ) : S → ℝ :=
    Nat.rec (fun y => if y = initial then 1 else 0) (fun _ p => step p) n
  have horbit (n : ℕ) : orbit n ∈ stdSimplex ℝ S := by
    induction n with
    | zero =>
      constructor
      · intro y
        change 0 ≤ (if y = initial then (1 : ℝ) else 0)
        split_ifs <;> norm_num
      · change (∑ y, if y = initial then (1 : ℝ) else 0) = 1
        simp
    | succ n hn => exact hstep (orbit n) hn
  let avg (n : ℕ) (y : S) : ℝ := ((n : ℝ) + 1)⁻¹ * ∑ t ∈ Finset.range (n + 1), orbit t y
  have havg (n : ℕ) : avg n ∈ stdSimplex ℝ S := by
    constructor
    · intro y
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun t _ => (horbit t).1 y))
    · unfold avg
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [(horbit _).2]
      simp [Nat.cast_add, (show (n : ℝ) + 1 ≠ 0 by positivity)]
  obtain ⟨p, hp, φ, hφ, hp_lim⟩ := (isCompact_stdSimplex (ι := S)).tendsto_subseq havg
  refine ⟨p, hp, fun y => ?_⟩
  have horbit_le_one (t : ℕ) : orbit t y ≤ 1 := by
    calc
      orbit t y ≤ ∑ x, orbit t x :=
        Finset.single_le_sum (fun x _ => (horbit t).1 x) (Finset.mem_univ y)
      _ = 1 := (horbit t).2
  have htel (n : ℕ) :
      step (avg n) y - avg n y =
        ((n : ℝ) + 1)⁻¹ * (orbit (n + 1) y - orbit 0 y) := by
    have hstep_avg : step (avg n) y =
        ((n : ℝ) + 1)⁻¹ * ∑ t ∈ Finset.range (n + 1), orbit (t + 1) y := by
      unfold step avg
      simp_rw [mul_assoc, Finset.sum_mul]
      rw [← Finset.mul_sum, Finset.sum_comm]
    rw [hstep_avg]
    unfold avg
    rw [← mul_sub, ← Finset.sum_sub_distrib, sum_range_forward_diff (fun t => orbit t y)]
  have hsmall (n : ℕ) : |step (avg n) y - avg n y| ≤ ((n : ℝ) + 1)⁻¹ := by
    rw [htel, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((n : ℝ) + 1)⁻¹)]
    apply mul_le_of_le_one_right (by positivity)
    exact abs_le.mpr ⟨by linarith [(horbit (n + 1)).1 y, horbit_le_one 0],
      by linarith [horbit_le_one (n + 1), (horbit 0).1 y]⟩
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hzero : Tendsto (fun n => step (avg n) y - avg n y) atTop (𝓝 0) := by
    have hneg : Tendsto (fun n : ℕ => -((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa using hinv.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg hinv
      (fun n => (abs_le.mp (hsmall n)).1) (fun n => (abs_le.mp (hsmall n)).2)
  have hcontinuous : Continuous (fun q : S → ℝ => step q y - q y) := by
    unfold step
    fun_prop
  have hfixed : step p y - p y = 0 :=
    tendsto_nhds_unique (hcontinuous.continuousAt.tendsto.comp hp_lim)
      (hzero.comp hφ.tendsto_atTop)
  exact sub_eq_zero.mp hfixed

/-- Weight of a transition in one clock tick, including inactive attempts. -/
private def chippingStepWeight {L N : ℕ} (w : ℝ) (x y : State L N) : ℝ := by
  classical
  exact ∑ i, ((if y = chipOrStay x i then w else 0) +
    (if y = wholePileOrStay x i then 1 else 0))

private theorem chippingStepWeight_sum_mul {L N : ℕ} (w : ℝ) (x : State L N)
    (f : State L N → ℝ) :
    (∑ y, chippingStepWeight w x y * f y) =
      ((L : ℝ) * (w + 1)) * f x + generator w f x := by
  classical
  unfold chippingStepWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, one_mul]
  have hlocal (i : Fin L) :
      w * f (chipOrStay x i) + f (wholePileOrStay x i) = (w + 1) * f x + atSite w f x i := by
    by_cases hchip : 1 ≤ occ x i <;> by_cases hwhole : 2 ≤ occ x i <;>
      simp [chipOrStay, wholePileOrStay, atSite, hchip, hwhole] <;> ring
  rw [← Finset.sum_add_distrib]
  simp_rw [hlocal]
  simp [generator, Finset.sum_add_distrib, nsmul_eq_mul, mul_assoc]

private theorem chippingStepWeight_nonneg {L N : ℕ} {w : ℝ} (hw : 0 ≤ w)
    (x y : State L N) : 0 ≤ chippingStepWeight w x y := by
  unfold chippingStepWeight
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> linarith

private theorem chippingStepWeight_sum {L N : ℕ} (w : ℝ) (x : State L N) :
    (∑ y, chippingStepWeight w x y) = (L : ℝ) * (w + 1) := by
  have hconst : generator w (fun _ : State L N => 1) x = 0 := by
    unfold generator
    apply Finset.sum_eq_zero
    intro i _
    unfold atSite
    split_ifs <;> ring
  simpa only [mul_one, hconst, add_zero] using chippingStepWeight_sum_mul w x (fun _ => 1)

/-- Every nonempty ring has a stationary law for every nonnegative chip rate.
Use a discrete step that chooses one of the site clocks and stays put if it
cannot fire. Invariance for this step is invariance for the original generator. -/
theorem stationaryLaw_exists {L N : ℕ} (hL : 0 < L) {w : ℝ} (hw : 0 ≤ w) :
    Nonempty (StationaryLaw L N w) := by
  classical
  let site : Fin L := ⟨0, hL⟩
  have hinitial : Nonempty (State L N) := by
    refine ⟨⟨fun i => if i = site then ⟨N, Nat.lt_succ_self N⟩ else 0, ?_⟩⟩
    simp [apply_ite]
  let c := (L : ℝ) * (w + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  let P (x y : State L N) := chippingStepWeight w x y / c
  have hP (x y : State L N) : 0 ≤ P x y := by
    exact div_nonneg (chippingStepWeight_nonneg hw x y) hc.le
  have hscale (x : State L N) (f : State L N → ℝ) :
      c * (∑ y, P x y * f y) = c * f x + generator w f x := by
    rw [Finset.mul_sum, ← chippingStepWeight_sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    dsimp [P]
    field_simp [hc.ne']
  have hrow (x : State L N) : (∑ y, P x y) = 1 := by
    simp only [P, div_eq_mul_inv, ← Finset.sum_mul, chippingStepWeight_sum]
    exact mul_inv_cancel₀ hc.ne'
  obtain ⟨p, hp, hfixed⟩ := finite_stationary_weights hinitial.some P hP hrow
  refine ⟨⟨p, hp.1, hp.2, fun f => ?_⟩⟩
  have hobs :
      (∑ x, p x * ∑ y, P x y * f y) = ∑ y, p y * f y := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hfixed]
  have hscaled :
      (∑ x, p x * (c * ∑ y, P x y * f y)) = ∑ x, p x * (c * f x) := by
    simp_rw [mul_left_comm _ c, ← Finset.mul_sum]
    exact congrArg (c * ·) hobs
  simp_rw [hscale, mul_add, Finset.sum_add_distrib] at hscaled
  linarith

private def distanceToZero {L : ℕ} (i : Fin L) : ℕ :=
  if i.val = 0 then 0 else L - i.val

private theorem distanceToZero_right {L : ℕ} (i : Fin L) (hi : i.val ≠ 0) :
    distanceToZero (right i) + 1 = distanceToZero i := by
  have hlt := i.isLt
  unfold distanceToZero
  change (if (i.val + 1) % L = 0 then 0 else L - (i.val + 1) % L) + 1 =
    (if i.val = 0 then 0 else L - i.val)
  rw [if_neg hi]
  by_cases hnext : i.val + 1 < L
  · rw [Nat.mod_eq_of_lt hnext, if_neg (by omega)]
    omega
  · have heq : i.val + 1 = L := by omega
    rw [heq, Nat.mod_self, if_pos rfl]
    omega

private def chipDistance {L N : ℕ} (x : State L N) : ℕ :=
  ∑ i, distanceToZero i * occ x i

private theorem chipDistance_move {L N : ℕ} (hL : 3 ≤ L) (x : State L N)
    (i : Fin L) (hi : i.val ≠ 0) (hm : 1 ≤ occ x i) :
    chipDistance (move x i 1 hm) < chipDistance x := by
  have hmove := sum_indexedSiteObservable_move hL
    (fun j a => (distanceToZero j : ℝ) * (a : ℝ)) x i 1 hm
  push_cast [Nat.cast_sub hm] at hmove
  have hdist : (distanceToZero (right i) : ℝ) + 1 = (distanceToZero i : ℝ) := by
    exact_mod_cast distanceToZero_right i hi
  have hdiff :
      (∑ j, (distanceToZero j : ℝ) * (occ (move x i 1 hm) j : ℝ)) <
        ∑ j, (distanceToZero j : ℝ) * (occ x j : ℝ) := by
    nlinarith
  unfold chipDistance
  exact_mod_cast hdiff

/-- Any nonempty set closed under all chip moves contains the state with all
mass at zero. Minimize the remaining clockwise travel distance to zero. -/
private theorem chip_closed_contains_concentrated {L N : ℕ} (hL : 3 ≤ L)
    (A : State L N → Prop) (hA : ∃ x, A x)
    (hclosed : ∀ (x : State L N) (i : Fin L) (hm : 1 ≤ occ x i), A x → A (move x i 1 hm)) :
    ∃ x, A x ∧ ∀ i : Fin L, i.val ≠ 0 → occ x i = 0 := by
  classical
  have hex : ∃ n : ℕ, ∃ x, A x ∧ chipDistance x = n := by
    obtain ⟨x, hx⟩ := hA
    exact ⟨chipDistance x, x, hx, rfl⟩
  obtain ⟨x, hx, hd⟩ := Nat.find_spec hex
  refine ⟨x, hx, fun i hi => ?_⟩
  by_contra hmass
  have hm : 1 ≤ occ x i := by omega
  have hmin := Nat.find_min' hex ⟨move x i 1 hm, hclosed x i hm hx, rfl⟩
  exact (not_lt_of_ge (hd.trans_le hmin)) (chipDistance_move hL x i hi hm)

private theorem eq_of_concentrated {L N : ℕ} (hL : 3 ≤ L) {x y : State L N}
    (hx : ∀ i : Fin L, i.val ≠ 0 → occ x i = 0)
    (hy : ∀ i : Fin L, i.val ≠ 0 → occ y i = 0) : x = y := by
  let site : Fin L := ⟨0, by omega⟩
  have hmass (z : State L N) (hz : ∀ i : Fin L, i.val ≠ 0 → occ z i = 0) :
      occ z site = N := by
    calc
      occ z site = ∑ i, occ z i := by
        symm
        apply Finset.sum_eq_single_of_mem site (Finset.mem_univ site)
        intro i _ hi
        exact hz i (fun h => hi (Fin.ext h))
      _ = N := z.property
  apply Subtype.ext
  funext i
  apply Fin.ext
  change occ x i = occ y i
  by_cases hi : i.val = 0
  · have heq : i = site := Fin.ext hi
    rw [heq, hmass x hx, hmass y hy]
  · rw [hx i hi, hy i hi]

private theorem stationaryWeight_step {L N : ℕ} {w : ℝ}
    (μ : StationaryLaw L N w) (y : State L N) :
    (∑ x, μ.weight x * chippingStepWeight w x y) = ((L : ℝ) * (w + 1)) * μ.weight y := by
  classical
  let c := (L : ℝ) * (w + 1)
  let f (z : State L N) : ℝ := if z = y then 1 else 0
  have hstep (x : State L N) :
      chippingStepWeight w x y = c * f x + generator w f x := by
    simpa [f, mul_ite] using chippingStepWeight_sum_mul w x f
  have hsum : (∑ x, μ.weight x * f x) = μ.weight y := by simp [f, mul_ite]
  simp_rw [hstep, mul_add, Finset.sum_add_distrib, μ.invariant f, add_zero,
    mul_left_comm _ c, ← Finset.mul_sum, hsum]
  simp [c, mul_add]

/-- A mass-preserving positive step fixes the positive part of any signed
invariant vector. Pointwise domination and equality of the sums force this. -/
private theorem positivePart_step {S : Type*} [Fintype S] (W : S → S → ℝ) {c : ℝ}
    (hW : ∀ x y, 0 ≤ W x y) (hrows : ∀ x, ∑ y, W x y = c)
    (d : S → ℝ) (hd : ∀ y, (∑ x, d x * W x y) = c * d y) (y : S) :
    (∑ x, max (d x) 0 * W x y) = c * max (d y) 0 := by
  classical
  let b (y : S) := ∑ x, max (d x) 0 * W x y
  have hle (y : S) : c * max (d y) 0 ≤ b y := by
    by_cases hy : 0 ≤ d y
    · rw [max_eq_left hy, ← hd y]
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (hW x y))
    · rw [max_eq_right (le_of_not_ge hy), mul_zero]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg (le_max_right _ _) (hW x y))
  have hsum : (∑ y, b y) = ∑ y, c * max (d y) 0 := by
    unfold b
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hrows]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  change b y = c * max (d y) 0
  by_contra hne
  have hlt := Finset.sum_lt_sum (fun z _ => hle z)
    ⟨y, Finset.mem_univ y, lt_of_le_of_ne (hle y) (Ne.symm hne)⟩
  rw [hsum] at hlt
  exact (lt_irrefl _ hlt)

private theorem chippingStepWeight_chip_pos {L N : ℕ} {w : ℝ} (hw : 0 < w)
    (x : State L N) (i : Fin L) (hm : 1 ≤ occ x i) :
    0 < chippingStepWeight w x (move x i 1 hm) := by
  unfold chippingStepWeight
  apply lt_of_lt_of_le hw
  have hterm : (if move x i 1 hm = chipOrStay x i then w else 0) = w := by
    simp [chipOrStay, hm]
  have hnonneg (j : Fin L) :
      0 ≤ (if move x i 1 hm = chipOrStay x j then w else 0) +
        (if move x i 1 hm = wholePileOrStay x j then (1 : ℝ) else 0) := by
    split_ifs <;> linarith
  calc
    w ≤ (if move x i 1 hm = chipOrStay x i then w else 0) +
        (if move x i 1 hm = wholePileOrStay x i then 1 else 0) := by
      rw [hterm]
      split_ifs <;> linarith
    _ ≤ _ := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)

private theorem stationary_positive_difference_chip_closed {L N : ℕ} {w : ℝ}
    (hw : 0 < w) (μ ν : StationaryLaw L N w)
    (x : State L N) (i : Fin L) (hm : 1 ≤ occ x i)
    (hx : ν.weight x < μ.weight x) :
    ν.weight (move x i 1 hm) < μ.weight (move x i 1 hm) := by
  let d (z : State L N) := μ.weight z - ν.weight z
  let c := (L : ℝ) * (w + 1)
  have hd (y : State L N) : (∑ z, d z * chippingStepWeight w z y) = c * d y := by
    simp only [d, sub_mul, Finset.sum_sub_distrib, stationaryWeight_step, c, mul_sub]
  let y := move x i 1 hm
  have hfixed := positivePart_step (chippingStepWeight w) (chippingStepWeight_nonneg hw.le)
    (chippingStepWeight_sum w) d hd y
  have hone : 0 < max (d x) 0 * chippingStepWeight w x y :=
    mul_pos ((sub_pos.mpr hx).trans_le (le_max_left _ _)) (chippingStepWeight_chip_pos hw x i hm)
  have hsum : 0 < ∑ z, max (d z) 0 * chippingStepWeight w z y :=
    hone.trans_le (Finset.single_le_sum (fun z _ =>
      mul_nonneg (le_max_right _ _) (chippingStepWeight_nonneg hw.le z y)) (Finset.mem_univ x))
  rw [hfixed] at hsum
  change ν.weight y < μ.weight y
  by_contra! hny
  have hzero : max (d y) 0 = 0 := max_eq_right (sub_nonpos.mpr hny)
  rw [hzero, mul_zero] at hsum
  exact lt_irrefl _ hsum

/-- Positive chipping gives a unique stationary law on the canonical sector. -/
theorem stationaryLaw_eq {L N : ℕ} (hL : 3 ≤ L) {w : ℝ} (hw : 0 < w)
    (μ ν : StationaryLaw L N w) : μ = ν := by
  have hle (p q : StationaryLaw L N w) (x : State L N) : p.weight x ≤ q.weight x := by
    by_contra! hx
    have hother : ∃ y, p.weight y < q.weight y := by
      by_contra! hn
      have hlt := Finset.sum_lt_sum (fun y _ => hn y) ⟨x, Finset.mem_univ x, hx⟩
      rw [p.normalized, q.normalized] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨a, ha, hpa⟩ := chip_closed_contains_concentrated hL
      (fun z => q.weight z < p.weight z) ⟨x, hx⟩ (stationary_positive_difference_chip_closed hw p q)
    obtain ⟨b, hb, hpb⟩ := chip_closed_contains_concentrated hL
      (fun z => p.weight z < q.weight z) hother (stationary_positive_difference_chip_closed hw q p)
    have hab := eq_of_concentrated hL hpa hpb
    rw [← hab] at hb
    exact (not_lt_of_ge ha.le) hb
  have hweight : μ.weight = ν.weight := funext (fun x => le_antisymm (hle μ ν x) (hle ν μ x))
  cases μ
  cases ν
  cases hweight
  rfl

/-- The unique stationary law at positive chip rate. -/
def equilibrium {L N : ℕ} (hL : 3 ≤ L) {w : ℝ} (hw : 0 < w) : StationaryLaw L N w :=
  (stationaryLaw_exists (show 0 < L by omega) hw.le).some

/-- Rotate the ring by `d`, carrying site `i` to `i + d`. -/
def rotateState {L N : ℕ} [NeZero L] (d : Fin L) (x : State L N) : State L N :=
  ⟨fun i => x.val (i + -d), Equiv.sum_comp (Equiv.addRight (-d)) (occ x) |>.trans x.property⟩

theorem occ_rotateState {L N : ℕ} [NeZero L] (d : Fin L) (x : State L N) (i : Fin L) :
    occ (rotateState d x) i = occ x (i + -d) := rfl

private theorem rotateState_neg_rotateState {L N : ℕ} [NeZero L]
    (d : Fin L) (x : State L N) : rotateState (-d) (rotateState d x) = x := by
  apply Subtype.ext
  funext i
  change x.val (i + -(-d) + -d) = x.val i
  simp

def rotateStateEquiv {L N : ℕ} [NeZero L] (d : Fin L) : State L N ≃ State L N where
  toFun := rotateState d
  invFun := rotateState (-d)
  left_inv := rotateState_neg_rotateState d
  right_inv x := by simpa using rotateState_neg_rotateState (-d) x

private theorem rotateState_move {L N : ℕ} [NeZero L] (d : Fin L) (x : State L N)
    (i : Fin L) (k : ℕ) (hk : k ≤ occ x i) :
    rotateState d (move x i k hk) =
      move (rotateState d x) (i + d) k (by simpa [occ_rotateState] using hk) := by
  apply Subtype.ext
  funext j
  apply Fin.ext
  change occ (rotateState d (move x i k hk)) j = occ (move (rotateState d x) (i + d) k _) j
  have hright : right (i + d) = right i + d := by
    simp only [right_eq_add_one]
    abel
  simp only [occ_rotateState, occ_move, transfer, hright, ← sub_eq_add_neg, sub_eq_iff_eq_add]

private theorem generator_rotateState {L N : ℕ} [NeZero L] (w : ℝ) (d : Fin L)
    (f : State L N → ℝ) (x : State L N) :
    generator w (fun y => f (rotateState d y)) x = generator w f (rotateState d x) := by
  unfold generator
  calc
    _ = ∑ i : Fin L, atSite w f (rotateState d x) (i + d) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold atSite
      have hm : occ (rotateState d x) (i + d) = occ x i := by simp [occ_rotateState]
      by_cases hchip : 1 ≤ occ x i <;> by_cases hwhole : 2 ≤ occ x i <;>
        simp [hm, hchip, hwhole, rotateState_move]
    _ = _ := Equiv.sum_comp (Equiv.addRight d) (atSite w f (rotateState d x))

private def rotateLaw {L N : ℕ} [NeZero L] {w : ℝ} (d : Fin L) (μ : StationaryLaw L N w) :
    StationaryLaw L N w where
  weight x := μ.weight (rotateState (-d) x)
  nonneg _ := μ.nonneg _
  normalized := (Equiv.sum_comp (rotateStateEquiv (-d)) μ.weight).trans μ.normalized
  invariant f := by
    let g (y : State L N) := μ.weight (rotateState (-d) y) * generator w f y
    calc
      _ = ∑ x, g (rotateState d x) := (Equiv.sum_comp (rotateStateEquiv d) g).symm
      _ = 0 := by
        simp only [g, rotateState_neg_rotateState, ← generator_rotateState]
        exact μ.invariant (fun x => f (rotateState d x))

/-- At positive chipping rate, the stationary law is invariant under rotation. -/
theorem stationaryWeight_rotateState {L N : ℕ} [NeZero L] (hL : 3 ≤ L) {w : ℝ} (hw : 0 < w)
    (μ : StationaryLaw L N w) (d : Fin L) (x : State L N) : μ.weight (rotateState d x) = μ.weight x := by
  have h := congrArg (fun law : StationaryLaw L N w => law.weight x)
    (stationaryLaw_eq hL hw (rotateLaw (-d) μ) μ)
  simpa [rotateLaw] using h

/-- Once stationary existence is proved, the fixed-rate claim is equivalent
to the limit for mean particle separation along the same sequences. -/
theorem supercondensesAt_iff_meanParticleSeparation_tendsto_zero {w ρ : ℝ}
    (hw : 0 ≤ w) (hρ : 0 < ρ) :
    SupercondensesAt w ρ ↔
      ∀ (L N : ℕ → ℕ), (∀ n, 3 ≤ L n) →
        Tendsto L atTop atTop →
        Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ) →
        ∀ (μ : (n : ℕ) → StationaryLaw (L n) (N n) w),
          Tendsto (fun n => meanParticleSeparation (μ n)) atTop (𝓝 0) := by
  constructor
  · intro h L N hL hL_lim hdensity μ
    exact (tails_vanish_iff_meanParticleSeparation_vanishes μ
      (eventually_pos_mass_of_tendsto_density hρ hdensity)).mp
      (h.2 L N hL hL_lim hdensity μ)
  · intro h
    refine ⟨fun _ _ hL => stationaryLaw_exists (by omega) hw, ?_⟩
    intro L N hL hL_lim hdensity μ
    exact (tails_vanish_iff_meanParticleSeparation_vanishes μ
      (eventually_pos_mass_of_tendsto_density hρ hdensity)).mpr
      (h L N hL hL_lim hdensity μ)

/-- At positive rate, the limit can be proved for the unique equilibrium
on each ring. -/
theorem supercondensesAt_iff_equilibrium_meanParticleSeparation_tendsto_zero {w ρ : ℝ}
    (hw : 0 < w) (hρ : 0 < ρ) :
    SupercondensesAt w ρ ↔
      ∀ (L N : ℕ → ℕ) (hL : ∀ n, 3 ≤ L n),
        Tendsto L atTop atTop →
        Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ) →
        Tendsto (fun n => meanParticleSeparation (equilibrium (N := N n) (hL n) hw)) atTop (𝓝 0) := by
  rw [supercondensesAt_iff_meanParticleSeparation_tendsto_zero hw.le hρ]
  constructor
  · intro h L N hL hL_lim hdensity
    exact h L N hL hL_lim hdensity (fun n => equilibrium (hL n) hw)
  · intro h L N hL hL_lim hdensity μ
    have heq : μ = fun n => equilibrium (hL n) hw :=
      funext (fun n => stationaryLaw_eq (hL n) hw (μ n) _)
    rw [heq]
    exact h L N hL hL_lim hdensity

end
end Chipping
