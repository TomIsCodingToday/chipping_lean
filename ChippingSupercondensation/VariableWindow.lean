import Mathlib.Algebra.Order.Archimedean.Basic
import ChippingSupercondensation.Basic

/-! # An isolated-group certificate at arbitrarily small positive chip rates

Coordinates are the gaps between two or three clockwise-ordered particles.
Zero gaps encode particles on the same site. The radius and the weights are
chosen as functions of the fixed chip rate and are independent of ring size.
-/

namespace Chipping.VariableWindow
noncomputable section

private def ramp (t : ℝ) := max t 0

private theorem ramp_nonneg (t : ℝ) : 0 ≤ ramp t := le_max_right _ _
private theorem le_ramp (t : ℝ) : t ≤ ramp t := le_max_left _ _
private theorem ramp_mono {a b : ℝ} (h : a ≤ b) : ramp a ≤ ramp b := max_le_max_right 0 h
private theorem ramp_step {a b d : ℝ} (hd : 0 ≤ d) (h : a ≤ b + d) : ramp a ≤ ramp b + d :=
  max_le (h.trans (add_le_add_right (le_ramp b) d)) (add_nonneg (ramp_nonneg b) hd)

def radius (w : ℝ) : ℕ := ⌈1 / (8 * w ^ 2)⌉₊

private structure Scale (w R K : ℝ) : Prop where
  pos : 0 < w
  small : w ≤ 1/32
  slope : 1 ≤ K
  unitRate : w * K = 1
  width : 2 * K ≤ R
  upper : 2 * w * R ≤ K / 2
  credit : 1 / (64 * w) + w * (3 - R / 2) ≤ 0

private theorem scale_of_rate {w : ℝ} (hw : 0 < w) (hs : w ≤ 1/32) :
    Scale w (radius w : ℝ) (1/w) := by
  have hden : 0 < 8 * w ^ 2 := by positivity
  have hlo : 1 / (8 * w ^ 2) ≤ (radius w : ℝ) := Nat.le_ceil _
  have hhi : (radius w : ℝ) < 1 / (8 * w ^ 2) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hlo' := (div_le_iff₀ hden).mp hlo
  have hhi' : (radius w : ℝ) - 1 < 1 / (8 * w ^ 2) := by linarith
  have hupper := (lt_div_iff₀ hden).mp hhi'
  have hw2 : w ^ 2 ≤ (1/32 : ℝ) ^ 2 := pow_le_pow_left₀ hw.le hs 2
  refine ⟨hw, hs, (le_div_iff₀ hw).mpr (by linarith), by field_simp, ?_, ?_, ?_⟩
  · rw [mul_one_div, div_le_iff₀ hw]
    by_contra! h
    nlinarith [mul_lt_mul_of_pos_right h hw]
  · apply (mul_le_mul_iff_of_pos_right hw).mp
    rw [show (1/w)/2 * w = 1/2 by field_simp]
    nlinarith only [hupper, hw2]
  · have hc : 1/(64*w) ≤ -(w*(3-(radius w : ℝ)/2)) :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hlo', hw2])
    linarith

/-- The gap to the singleton ahead of a pile determines its excess price. -/
private def ahead (R d : ℝ) : ℝ := 3 + ramp (R - d)
private def behind (R K d : ℝ) : ℝ := 3 + ramp (R - K*d) / 2
private def debris (R K a b : ℝ) : ℝ := ramp (R - b - K*a)
private def bare (w R : ℝ) : ℝ := ahead R 1 + 1 + 1 / (64*w)

/-- One, two, or three clockwise-ordered particles, modulo a common shift. -/
inductive Group
  | one
  | two (gap : ℕ)
  | three (leftGap rightGap : ℕ)
  deriving DecidableEq

/-- Group price extended across a split by the sum of the fragment prices. -/
def price (w R K : ℝ) : Group → ℝ
  | .one => 0
  | .two 0 => 3
  | .two (_+1) => 0
  | .three 0 0 => bare w R
  | .three 0 (b+1) => ahead R (b+1)
  | .three (a+1) 0 => behind R K (a+1)
  | .three (a+1) (b+1) => debris R K (a+1) (b+1)

/-- The chip and whole-move generator in gap coordinates, with the group's
share of the first moment. A whole translation preserves every gap. -/
def drift (w : ℝ) (V : Group → ℝ) : Group → ℝ
  | .one => w - 1
  | .two 0 => w + w * (V (.two 1) - V (.two 0))
  | .two (a+1) => 2*w - 2 + w * (V (.two a) + V (.two (a+2)) - 2*V (.two (a+1)))
  | .three 0 0 => w + w * (V (.three 0 1) - V (.three 0 0))
  | .three 0 (b+1) =>
    2*w - 1 + w * (V (.three 1 b) + V (.three 0 (b+2)) - 2*V (.three 0 (b+1))) +
      (V (.three 0 b) - V (.three 0 (b+1)))
  | .three (a+1) 0 =>
    2*w - 1 + w * (V (.three a 0) + V (.three (a+1) 1) - 2*V (.three (a+1) 0)) +
      (V (.three (a+2) 0) - V (.three (a+1) 0))
  | .three (a+1) (b+1) =>
    3*w - 3 + w * (V (.three a (b+1)) + V (.three (a+2) b) + V (.three (a+1) (b+2)) -
      3*V (.three (a+1) (b+1)))

private theorem ahead_step {R d : ℝ} : ahead R d - ahead R (d+1) ≤ 1 := by
  unfold ahead
  linarith [ramp_step (a := R-d) (b := R-(d+1)) (d := 1) (by norm_num) (by linarith)]

private theorem ahead_mono {R d e : ℝ} (h : d ≤ e) : ahead R e ≤ ahead R d :=
  add_le_add_left (ramp_mono (by linarith)) _

/-- Dissolved debris from a leading pile is paid for by its next whole move
away from the singleton behind it. -/
private theorem behind_payment {w R K : ℝ} (h : Scale w R K) {d : ℝ} (hd : 0 ≤ d) :
    w * debris R K d 1 + (behind R K (d+1) - behind R K d) ≤ 0 := by
  let z := R - K*d
  have hC : debris R K d 1 ≤ ramp z := ramp_mono (by dsimp [z]; linarith)
  have hn := mul_le_mul_of_nonneg_left hC h.pos.le
  have hzR : z ≤ R := by dsimp [z]; nlinarith [mul_nonneg (show 0 ≤ K by linarith [h.slope]) hd]
  have hs : R - K*(d+1) = z-K := by dsimp [z]; ring
  unfold behind
  rw [hs]
  change _ + ((3 + ramp (z-K)/2) - (3 + ramp z/2)) ≤ 0
  by_cases hz : z ≤ 0
  · have hz' : z-K ≤ 0 := by linarith [h.slope]
    simp only [ramp, max_eq_right hz, max_eq_right hz'] at hn ⊢
    linarith
  · by_cases hk : z ≤ K
    · have hs' := mul_le_mul_of_nonneg_right (show w ≤ 1/2 by linarith [h.small]) (le_of_not_ge hz)
      simp only [ramp, max_eq_left (le_of_not_ge hz), max_eq_right (sub_nonpos.mpr hk)] at hn ⊢
      calc
        _ ≤ (1/2)*z + (3 + 0/2 - (3 + z/2)) := add_le_add_right (hn.trans hs') _
        _ = 0 := by ring
    · have hup := mul_le_mul_of_nonneg_left hzR h.pos.le
      simp only [ramp, max_eq_left (le_of_not_ge hz), max_eq_left (sub_nonneg.mpr (le_of_not_ge hk))] at hn ⊢
      nlinarith only [hn, hup, h.upper, h.pos, h.slope]

private theorem ahead_adjacent {w R K : ℝ} (h : Scale w R K) :
    2*w-1 + w*(behind R K 1 + ahead R 2 - 2*ahead R 1) + (bare w R - ahead R 1) ≤ 0 := by
  have hr : 0 ≤ R-1 := by linarith [h.width, h.slope]
  have hb : behind R K 1 ≤ 3 + R/2 := by
    unfold behind ramp
    have : max (R-K*1) 0 ≤ R := max_le (by linarith [h.slope]) (by linarith [h.width, h.slope])
    linarith
  have he : ahead R 1 = 3 + (R-1) := by simp [ahead, ramp, max_eq_left hr]
  have hc : behind R K 1 + ahead R 2 - 2*ahead R 1 ≤ 1 - R/2 := by
    linarith [ahead_mono (R := R) (by norm_num : (1:ℝ) ≤ 2)]
  unfold bare
  nlinarith only [mul_le_mul_of_nonneg_left hc h.pos.le, h.credit]

private theorem ahead_separated {w R K : ℝ} (h : Scale w R K) (d : ℝ) :
    2*w-1 + w*(debris R K 1 d + ahead R (d+2) - 2*ahead R (d+1)) +
      (ahead R d - ahead R (d+1)) ≤ 0 := by
  have hc : debris R K 1 d ≤ ahead R (d+1) - 3 := by
    unfold debris ahead
    rw [add_sub_cancel_left]
    apply ramp_mono
    linarith [h.slope]
  have hs := ahead_mono (R := R) (by linarith : d+1 ≤ d+2)
  have hm := mul_le_mul_of_nonneg_left (show debris R K 1 d + ahead R (d+2) -
    2*ahead R (d+1) ≤ -3 by linarith) h.pos.le
  linarith [ahead_step (R := R) (d := d), h.pos]

private theorem behind_adjacent {w R K : ℝ} (h : Scale w R K) :
    2*w-1 + w*(bare w R + debris R K 1 1 - 2*behind R K 1) +
      (behind R K 2 - behind R K 1) ≤ 0 := by
  have hR : 0 ≤ R-1 := by linarith [h.width, h.slope]
  have h1 : 0 ≤ R-K*1 := by linarith [h.width, h.slope]
  have h2 : 0 ≤ R-K*2 := by linarith [h.width]
  have he : behind R K 2 - behind R K 1 = -K/2 := by
    simp only [behind, ramp, max_eq_left h1, max_eq_left h2]
    ring
  have hc : debris R K 1 1 ≤ R := max_le (by linarith [h.slope]) (by linarith)
  have ht : bare w R = 3 + R + 1/(64*w) := by
    simp only [bare, ahead, ramp, max_eq_left hR]
    ring
  have hb : 3 ≤ behind R K 1 := by unfold behind; linarith [ramp_nonneg (R-K*1)]
  have hcost := mul_le_mul_of_nonneg_left (show bare w R + debris R K 1 1 - 2*behind R K 1 ≤
    2*R + 1/(64*w) by linarith) h.pos.le
  have hcancel : w*(1/(64*w)) = 1/64 := by field_simp [h.pos.ne']; ring
  rw [mul_add, hcancel] at hcost
  linarith [h.small, h.upper]

private theorem behind_separated {w R K : ℝ} (h : Scale w R K) {d : ℝ} (hd : 0 ≤ d) :
    2*w-1 + w*(behind R K d + debris R K (d+1) 1 - 2*behind R K (d+1)) +
      (behind R K (d+2) - behind R K (d+1)) ≤ 0 := by
  have hstep := ramp_step (a := R-K*d) (b := R-K*(d+1)) (d := K)
    (by linarith [h.slope]) (by linarith)
  have hb : behind R K d - 2*behind R K (d+1) ≤ K/2 := by
    unfold behind
    linarith [ramp_nonneg (R-K*(d+1))]
  have hm := mul_le_mul_of_nonneg_left hb h.pos.le
  have hp := behind_payment h (show 0 ≤ d+1 by linarith)
  rw [show d+1+1 = d+2 by ring] at hp
  nlinarith only [hm, hp, h.small, h.unitRate]

private theorem singles_moves {w R K : ℝ} (h : Scale w R K) (a b : ℕ) :
    drift w (price w R K) (.three (a+1) (b+1)) ≤ 0 := by
  let v := debris R K (a+1) (b+1)
  have hK : 0 ≤ K := by linarith [h.slope]
  have hleft : price w R K (.three a (b+1)) ≤ v + K + 3 := by
    cases a with
    | zero =>
      simp only [price, ahead, v, debris, Nat.cast_zero, zero_add, mul_one]
      linarith [ramp_step (a := R-(b+1)) (b := R-(b+1)-K) hK (by linarith)]
    | succ a =>
      simp only [price, v, debris, Nat.cast_succ]
      linarith [ramp_step (a := R-(b+1)-K*(a+1)) (b := R-(b+1)-K*(a+1+1)) hK (by linarith)]
  have hmid : price w R K (.three (a+2) b) ≤ v + 3 := by
    cases b with
    | zero =>
      simp only [price, behind, v, debris, Nat.cast_succ, Nat.cast_zero, zero_add]
      have hl : ramp (R-K*(a+1+1)) ≤ ramp (R-1-K*(a+1)) := ramp_mono (by linarith [h.slope])
      linarith [ramp_nonneg (R-1-K*(a+1))]
    | succ b =>
      simp only [price, v, debris, Nat.cast_succ]
      have hl : ramp (R-(b+1)-K*(a+1+1)) ≤ ramp (R-(b+1+1)-K*(a+1)) := ramp_mono (by linarith [h.slope])
      linarith
  have hright : price w R K (.three (a+1) (b+2)) ≤ v := by
    simp only [price, v, debris, Nat.cast_succ]
    apply ramp_mono
    linarith
  have hsum := mul_le_mul_of_nonneg_left (show price w R K (.three a (b+1)) +
    price w R K (.three (a+2) b) + price w R K (.three (a+1) (b+2)) - 3*v ≤ K+6 by linarith) h.pos.le
  change 3*w-3 + w*(price w R K (.three a (b+1)) + price w R K (.three (a+2) b) +
    price w R K (.three (a+1) (b+2)) - 3*v) ≤ 0
  nlinarith only [hsum, h.unitRate, h.small]

/-- A single rate-dependent family gives a uniform drift credit of one
sixty-fourth to every bare triple, at every rate in (0, 1/32]. -/
theorem smallRate_drift_le {w : ℝ} (hw : 0 < w) (hs : w ≤ 1/32) (g : Group) :
    drift w (price w (radius w) (1/w)) g ≤ if g = .three 0 0 then -(1/64 : ℝ) else 0 := by
  let R : ℝ := radius w
  let K : ℝ := 1/w
  have h : Scale w R K := scale_of_rate hw hs
  change drift w (price w R K) g ≤ _
  cases g with
  | one => simp [drift]; linarith
  | two a =>
    rcases a with _ | _ | a <;> simp [drift, price] <;> linarith
  | three a b =>
    cases a with
    | zero =>
      rcases b with _ | _ | b
      · simp [drift, price, bare]
        apply le_of_eq
        field_simp [hw.ne']
        ring
      · simpa [drift, price, one_add_one_eq_two] using ahead_adjacent h
      · simpa [drift, price, Nat.cast_succ, add_assoc, one_add_one_eq_two,
          show (1:ℝ)+2=2+1 by norm_num] using ahead_separated h (b+1)
    | succ a =>
      cases b with
      | zero =>
        cases a with
        | zero => simpa [drift, price, one_add_one_eq_two] using behind_adjacent h
        | succ a => simpa [drift, price, Nat.cast_succ, add_assoc, one_add_one_eq_two,
              show (1:ℝ)+2=2+1 by norm_num] using
              behind_separated h (d := (a:ℝ)+1) (by positivity)
      | succ b => simpa using singles_moves h a b

/-- All local prices are nonnegative, so removing an isolated group cannot
increase the sum of group prices. -/
theorem price_nonneg {w : ℝ} (hw : 0 < w) (g : Group) :
    0 ≤ price w (radius w) (1/w) g := by
  cases g with
  | one => exact le_rfl
  | two a => cases a <;> norm_num [price]
  | three a b =>
    cases a <;> cases b <;> simp only [price, ahead, behind, bare, debris, ramp] <;> positivity

/-- At or beyond the cutoff, splitting a triple at either gap leaves exactly
the sum of the two fragment prices. This includes the first contact of two
groups when a gap closes to the cutoff. -/
theorem price_at_cutoff {w : ℝ} (hw : 0 < w) (hs : w ≤ 1/32) (a b : ℕ) :
    let V := price w (radius w) (1/w)
    (radius w ≤ a → V (.three a b) = V (.two b)) ∧
    (radius w ≤ b → V (.three a b) = V (.two a)) ∧
    (radius w ≤ a → V (.two a) = 0) := by
  let R : ℝ := radius w
  let K : ℝ := 1/w
  have h : Scale w R K := scale_of_rate hw hs
  have hr : 0 < radius w := by
    have hp : 0 < R := by linarith [h.width, h.slope]
    dsimp [R] at hp
    exact_mod_cast hp
  have hk : 0 ≤ K := by linarith [h.slope]
  change (radius w ≤ a → price w R K (.three a b) = _) ∧
    (radius w ≤ b → price w R K (.three a b) = _) ∧ (radius w ≤ a → price w R K (.two a) = 0)
  constructor
  · intro ha
    have ha' : R ≤ (a : ℝ) := by dsimp [R]; exact_mod_cast ha
    have hslope := mul_le_mul_of_nonneg_right h.slope (Nat.cast_nonneg a : (0:ℝ) ≤ a)
    cases a with
    | zero => omega
    | succ a =>
      cases b <;> simp only [price, behind, debris, ramp, Nat.cast_succ] at * <;>
        rw [max_eq_right (by linarith)]
      all_goals norm_num
  · constructor
    · intro hb
      have hb' : R ≤ (b : ℝ) := by dsimp [R]; exact_mod_cast hb
      cases b with
      | zero => omega
      | succ b =>
        cases a with
        | zero => simp only [price, ahead, ramp, Nat.cast_succ] at *; rw [max_eq_right (by linarith)]; ring
        | succ a =>
          simp only [price, debris, ramp, Nat.cast_succ] at *
          exact max_eq_right (by nlinarith [mul_nonneg hk (show (0:ℝ) ≤ a+1 by positivity)])
    · intro ha
      cases a with
      | zero => omega
      | succ a => rfl

/-- A bound independent of ring size, including the bare-pile surcharge. -/
def priceBound (w : ℝ) : ℝ := 4 + (radius w : ℝ) + 1/(64*w)

theorem price_le_priceBound {w : ℝ} (hw : 0 < w) (g : Group) :
    price w (radius w) (1/w) g ≤ priceBound w := by
  let R := (radius w : ℝ)
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hbonus : 0 ≤ 1/(64*w) := by positivity
  have hramp (t : ℝ) (ht : t ≤ R) : ramp t ≤ R := max_le ht hR
  have ha (d : ℝ) (hd : 0 ≤ d) : ahead R d ≤ 3+R :=
    add_le_add_left (hramp _ (by linarith)) _
  have hb (d : ℝ) (hd : 0 ≤ d) : behind R (1/w) d ≤ 3+R := by
    have h := hramp (R-(1/w)*d) (sub_le_self _ (mul_nonneg (by positivity) hd))
    unfold behind
    linarith
  have hc (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : debris R (1/w) a b ≤ R :=
    hramp _ (by nlinarith [mul_nonneg (show 0 ≤ 1/w by positivity) ha])
  change price w R (1/w) g ≤ 4+R+1/(64*w)
  rcases g with _ | (_ | a) | ⟨(_ | a), (_ | b)⟩
  all_goals simp only [price, bare]
  all_goals first | linarith | linarith [ha 1 (by norm_num)] |
    linarith [ha (b+1) (by positivity)] | linarith [hb (a+1) (by positivity)] |
    linarith [hc (a+1) (b+1) (by positivity) (by positivity)]

end
end Chipping.VariableWindow
