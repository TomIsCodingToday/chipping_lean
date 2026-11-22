import Mathlib.Algebra.Group.Fin.Basic
import ChippingSupercondensation.Model

/-!
# Shared lemmas about ring sites and moves

On rings with at least three sites the right neighbour differs from the site,
and it agrees with `i + 1`. The file also records occupancies and sums of site
observables after a move, the chip and whole-pile transitions as total
functions, a telescoping sum, and eventual positivity of the total mass along
sequences with positive limiting density.
-/

namespace Chipping

open Filter
open scoped BigOperators Topology

noncomputable section

theorem right_ne_self {L : ℕ} (hL : 3 ≤ L) (i : Fin L) : right i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [right] at hv
  have hi := i.isLt
  by_cases hnext : i.val + 1 < L
  · rw [Nat.mod_eq_of_lt hnext] at hv
    omega
  · have heq : i.val + 1 = L := by omega
    rw [heq, Nat.mod_self] at hv
    omega

theorem occ_move {L N : ℕ} (x : State L N) (i : Fin L) (k : ℕ)
    (hk : k ≤ occ x i) (j : Fin L) :
    occ (move x i k hk) j = transfer (occ x) i k j := rfl

/-- For a sum of site observables, only the two ends of the bond change. -/
theorem sum_indexedSiteObservable_move {L N : ℕ} (hL : 3 ≤ L) (f : Fin L → ℕ → ℝ)
    (x : State L N) (i : Fin L) (k : ℕ) (hk : k ≤ occ x i) :
    (∑ j, f j (occ (move x i k hk) j)) - (∑ j, f j (occ x j)) =
      (f i (occ x i - k) - f i (occ x i)) +
      (f (right i) (occ x (right i) + k) - f (right i) (occ x (right i))) := by
  classical
  have hne := right_ne_self hL i
  rw [← Finset.sum_sub_distrib]
  have local_eq (j : Fin L) :
      f j (occ (move x i k hk) j) - f j (occ x j) =
      (if j = i then f i (occ x i - k) - f i (occ x i) else 0) +
      (if j = right i then f (right i) (occ x (right i) + k) - f (right i) (occ x (right i))
        else 0) := by
    by_cases hi : j = i
    · subst j
      simp [occ_move, transfer, hne, Ne.symm hne]
    · by_cases hr : j = right i
      · subst j
        simp [occ_move, transfer, hne]
      · simp [occ_move, transfer, hi, hr]
  simp_rw [local_eq]
  simp [Finset.sum_add_distrib]

theorem sum_siteObservable_move {L N : ℕ} (hL : 3 ≤ L) (f : ℕ → ℝ)
    (x : State L N) (i : Fin L) (k : ℕ) (hk : k ≤ occ x i) :
    (∑ j, f (occ (move x i k hk) j)) - (∑ j, f (occ x j)) =
      (f (occ x i - k) - f (occ x i)) +
      (f (occ x (right i) + k) - f (occ x (right i))) :=
  sum_indexedSiteObservable_move hL (fun _ => f) x i k hk

theorem right_eq_add_one {L : ℕ} [NeZero L] (i : Fin L) : right i = i + 1 := by
  apply Fin.ext
  change (i.val + 1) % L = (i.val + 1 % L) % L
  exact (Nat.add_mod_mod _ _ _).symm

theorem sum_range_forward_diff (f : ℕ → ℝ) (r : ℕ) :
    (∑ s ∈ Finset.range r, (f (s + 1) - f s)) = f r - f 0 := by
  induction r with
  | zero => simp
  | succ r h => rw [Finset.sum_range_succ, h]; ring

def chipOrStay {L N : ℕ} (x : State L N) (i : Fin L) : State L N :=
  if h : 1 ≤ occ x i then move x i 1 h else x

def wholePileOrStay {L N : ℕ} (x : State L N) (i : Fin L) : State L N :=
  if 2 ≤ occ x i then move x i (occ x i) le_rfl else x

/-- At positive limiting density, the mass is eventually positive. -/
theorem eventually_pos_mass_of_tendsto_density {L N : ℕ → ℕ} {ρ : ℝ}
    (hρ : 0 < ρ) (hdensity : Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ)) :
    ∀ᶠ n in atTop, 0 < N n := by
  have hpos : ∀ᶠ n in atTop, 0 < (N n : ℝ) / (L n : ℝ) :=
    (tendsto_order.mp hdensity).1 0 hρ
  filter_upwards [hpos] with n hn
  by_contra! hN
  have hzero : N n = 0 := Nat.eq_zero_of_le_zero hN
  simp [hzero] at hn

theorem occ_move_right {L N : ℕ} (hL : 3 ≤ L) (x : State L N)
    (i : Fin L) (k : ℕ) (hk : k ≤ occ x i) :
    occ (move x i k hk) (right i) = occ x (right i) + k := by
  simp [occ_move, transfer, right_ne_self hL i]

theorem natCast_fin_ne_zero {L : ℕ} [NeZero L] {s : ℕ}
    (hpos : 0 < s) (hlt : s < L) : (s : Fin L) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_natCast, Nat.mod_eq_of_lt hlt, Fin.val_zero] at hv
  omega

end
end Chipping
