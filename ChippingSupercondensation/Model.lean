import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The totally asymmetric chipping model

The ring has `L` sites and exactly `N` particles. Every occupied site chips one
particle to its right at rate `w`. A site with at least two particles also moves
its entire pile to the right at rate one, so a site holding a single particle
moves it only at the chipping rate.

The declarations below are the checked baseline of `ChippingProofStarter.md`,
unchanged: the conservative moves and generator, stationary laws in weak form,
the background fraction `B/N`, the tail/mean equivalence
`tails_vanish_iff_mean_vanishes`, and the open propositions `SupercondensesAt`
and `SmallWSupercondensation`.
-/

namespace Chipping

open Filter
open scoped BigOperators Topology

noncomputable section

/-- A finite state space. The subtype enforces the canonical mass constraint. -/
abbrev State (L N : ℕ) :=
  {x : Fin L → Fin (N + 1) // ∑ i, (x i).val = N}

def occ {L N : ℕ} (x : State L N) (i : Fin L) : ℕ := (x.val i).val

def right {L : ℕ} (i : Fin L) : Fin L :=
  ⟨(i.val + 1) % L, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- Move k particles in the ambient natural-valued configuration. -/
def transfer {L : ℕ} (x : Fin L → ℕ) (i : Fin L) (k : ℕ) (j : Fin L) : ℕ :=
  (x j - (if j = i then k else 0)) + (if j = right i then k else 0)

theorem transfer_conserves {L : ℕ} (x : Fin L → ℕ) (i : Fin L) (k : ℕ)
    (hk : k ≤ x i) : ∑ j, transfer x i k j = ∑ j, x j := by
  have restore (j : Fin L) :
      (x j - (if j = i then k else 0)) + (if j = i then k else 0) = x j := by
    by_cases h : j = i
    · subst j
      simpa using Nat.sub_add_cancel hk
    · simp [h]
  calc
    ∑ j, transfer x i k j
        = ∑ j, ((x j - (if j = i then k else 0)) +
                  (if j = i then k else 0)) := by simp [transfer, Finset.sum_add_distrib]
    _ = ∑ j, x j := by simp_rw [restore]

/-- The generator can only call this move with k particles available. -/
def move {L N : ℕ} (x : State L N) (i : Fin L) (k : ℕ) (hk : k ≤ occ x i) :
    State L N := by
  let y := transfer (occ x) i k
  have hsum : ∑ j, y j = N := (transfer_conserves _ _ _ hk).trans x.property
  have hbound (j : Fin L) : y j ≤ N := by
    rw [← hsum]
    exact Finset.single_le_sum (fun t _ => Nat.zero_le (y t)) (Finset.mem_univ j)
  exact ⟨fun j => ⟨y j, Nat.lt_succ_of_le (hbound j)⟩, hsum⟩

/-- The contribution of the two possible departures from site i to Q f. -/
def atSite {L N : ℕ} (w : ℝ) (f : State L N → ℝ) (x : State L N) (i : Fin L) : ℝ :=
  (if h : 1 ≤ occ x i then w * (f (move x i 1 h) - f x) else 0) +
  (if 2 ≤ occ x i then f (move x i (occ x i) le_rfl) - f x else 0)

theorem singleton_atSite {L N : ℕ} (w : ℝ) (f : State L N → ℝ)
    (x : State L N) (i : Fin L) (h : occ x i = 1) :
    atSite w f x i = w * (f (move x i 1 (by omega)) - f x) := by
  have h₁ : 1 ≤ occ x i := by omega
  have h₂ : ¬ 2 ≤ occ x i := by omega
  simp [atSite, h₁, h₂]

def generator {L N : ℕ} (w : ℝ) (f : State L N → ℝ) (x : State L N) : ℝ :=
  ∑ i, atSite w f x i

/-- A stationary probability vector on the canonical sector, in weak form. -/
structure StationaryLaw (L N : ℕ) (w : ℝ) where
  weight : State L N → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1
  invariant : ∀ f : State L N → ℝ, ∑ x, weight x * generator w f x = 0

def largest {L N : ℕ} (x : State L N) : ℕ := Finset.univ.sup (occ x)

/-- The fraction of all particles outside one largest pile. Ties need no choice.
At N = 0 Lean's real division gives zero. Positive limiting density excludes
zero total mass eventually. -/
def backgroundFraction {L N : ℕ} (x : State L N) : ℝ :=
  ((N - largest x : ℕ) : ℝ) / (N : ℝ)

theorem backgroundFraction_nonneg {L N : ℕ} (x : State L N) :
    0 ≤ backgroundFraction x := by
  unfold backgroundFraction
  positivity

theorem backgroundFraction_le_one {L N : ℕ} (x : State L N) :
    backgroundFraction x ≤ 1 := by
  cases N with
  | zero => simp [backgroundFraction]
  | succ n =>
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((n+1 : ℕ) : ℝ))).2
    rw [one_mul]
    exact_mod_cast Nat.sub_le (n+1) (largest x)

def meanBackground {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) : ℝ :=
  ∑ x, μ.weight x * backgroundFraction x

def backgroundTail {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) (ε : ℝ) : ℝ :=
  ∑ x, if ε ≤ backgroundFraction x then μ.weight x else 0

/-- Markov's inequality for the missing mass fraction, in product form. -/
theorem threshold_mul_tail_le_mean {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w)
    (ε : ℝ) : ε * backgroundTail μ ε ≤ meanBackground μ := by
  unfold backgroundTail meanBackground
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : ε ≤ backgroundFraction x
  · simpa [h, mul_comm ε] using mul_le_mul_of_nonneg_left h (μ.nonneg x)
  · simpa [h] using mul_nonneg (μ.nonneg x) (backgroundFraction_nonneg x)

/-- The converse estimate uses the deterministic bound B/N ≤ 1. -/
theorem mean_le_threshold_add_tail {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w)
    {ε : ℝ} (hε : 0 ≤ ε) : meanBackground μ ≤ ε + backgroundTail μ ε := by
  calc
    meanBackground μ ≤ ∑ x, (μ.weight x * ε +
        (if ε ≤ backgroundFraction x then μ.weight x else 0)) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases h : ε ≤ backgroundFraction x
      · simp only [if_pos h]
        have hle : μ.weight x * backgroundFraction x ≤ μ.weight x := by
          simpa using mul_le_mul_of_nonneg_left (backgroundFraction_le_one x) (μ.nonneg x)
        exact hle.trans (le_add_of_nonneg_left (mul_nonneg (μ.nonneg x) hε))
      · simp only [if_neg h, add_zero]
        exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) (μ.nonneg x)
    _ = ε + backgroundTail μ ε := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, μ.normalized, one_mul]
      rfl

/-- A stationary first-moment estimate is exactly sufficient for the
probability formulation, along any sequence of rings and masses. -/
theorem tails_vanish_iff_mean_vanishes {L N : ℕ → ℕ} {w : ℝ}
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => backgroundTail (μ n) ε) atTop (𝓝 0)) ↔
      Tendsto (fun n => meanBackground (μ n)) atTop (𝓝 0) := by
  have hm (n : ℕ) : 0 ≤ meanBackground (μ n) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg ((μ n).nonneg x) (backgroundFraction_nonneg x))
  have ht (n : ℕ) (ε : ℝ) : 0 ≤ backgroundTail (μ n) ε := by
    unfold backgroundTail
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact (μ n).nonneg x
    · exact le_rfl
  constructor
  · intro h
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun n => ha.trans_le (hm n))
    · intro b hb
      have half := half_pos hb
      filter_upwards [(tendsto_order.1 (h (b / 2) half)).2 (b / 2) half] with n hn
      have bound := mean_le_threshold_add_tail (μ n) half.le
      linarith
  · intro h ε hε
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun n => ha.trans_le (ht n ε))
    · intro b hb
      filter_upwards [(tendsto_order.1 h).2 (ε * b) (mul_pos hε hb)] with n hn
      exact (mul_lt_mul_left hε).mp ((threshold_mul_tail_le_mean (μ n) ε).trans_lt hn)

/-- For every thermodynamic sequence at density ρ and every choice of stationary
law on those rings, the largest pile carries a fraction tending to one in
probability. Existence on each finite ring is included to exclude vacuity. -/
def SupercondensesAt (w ρ : ℝ) : Prop :=
  (∀ L N : ℕ, 3 ≤ L → Nonempty (StationaryLaw L N w)) ∧
  ∀ (L N : ℕ → ℕ), (∀ n, 3 ≤ L n) →
    Tendsto L atTop atTop →
    Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ) →
    ∀ (μ : (n : ℕ) → StationaryLaw (L n) (N n) w),
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => backgroundTail (μ n) ε) atTop (𝓝 0)

/-- The small-w conjecture. The same w₀ works for every positive density. -/
def SmallWSupercondensation : Prop :=
  ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ ≤ 1 ∧
    ∀ w : ℝ, 0 < w → w < w₀ → ∀ ρ : ℝ, 0 < ρ → SupercondensesAt w ρ

end
end Chipping
