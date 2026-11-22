import ChippingSupercondensation.PeakFrame

/-! # A radius-eight window certificate for chip rates from one sixth to one fifth

Weights are stored in half units. The two endpoint drifts are scaled by ten and twelve. The finite check uses
integer arithmetic. The projection lemmas below interpret each internal bond
as a bond of the original ring, including windows crossing site zero.
-/

namespace Chipping.WindowEight
open scoped BigOperators

/-- Two gaps of nine and one final move fit in twenty consecutive sites. -/
abbrev Profile := Fin 20 → ℕ

/-- The sorted particle positions of a window, with multiplicities. -/
def particles (v : Profile) : List ℕ :=
  (List.finRange 20).flatMap fun i => List.replicate (v i) i.val

/-- Connected components of a sorted particle list at interaction range eight. -/
def groups (p : List ℕ) : List (List ℕ) :=
  p.splitBy fun a b => decide (b ≤ a + 8)

/-- Twice the weight of a connected group. Inputs are positions in increasing
order, allowing equality for particles on the same site. -/
def groupUnits : List ℕ → ℕ
  | [x, y] => if x = y then 10 else 0
  | [x, y, z] =>
    match y - x, z - y with
    | 0, 0 => 52
    | 0, 1 => 44 | 0, 2 => 38 | 0, 3 => 32 | 0, 4 => 26
    | 0, 5 => 21 | 0, 6 => 17 | 0, 7 => 13 | 0, 8 => 10
    | 1, 0 => 10 | 2, 0 => 2 | 3, 0 => 1 | 4, 0 => 2
    | 5, 0 => 3 | 6, 0 => 4 | 7, 0 => 6 | 8, 0 => 8
    | 1, 1 => 10 | 1, 2 => 6 | 1, 3 => 3 | 1, 4 => 1
    | _, _ => 0
  | _ => 0

def units (v : Profile) : ℤ :=
  ((groups (particles v)).map groupUnits).sum

/-- An internal departure and its right neighbour are both in the window. -/
def jump (v : Profile) (s : Fin 19) (k : ℕ) (j : Fin 20) : ℕ :=
  (v j - (if j = s.castSucc then k else 0)) + (if j = s.succ then k else 0)

def profile (p : List ℕ) (j : Fin 20) : ℕ := p.count j.val

/-- The coefficient of the chip rate in twice the internal drift. -/
def chipTerm (v : Profile) (s : Fin 19) : ℤ :=
  if 1 ≤ v s.castSucc then units (jump v s 1) - units v + 2 else 0

/-- Twice the whole-move contribution, including the linear moment's loss per singleton. -/
def wholeTerm (v : Profile) (s : Fin 19) : ℤ :=
  let m := v s.castSucc
  (if 2 ≤ m then units (jump v s m) - units v else 0) - (if m = 1 then 2 else 0)

def chipTotal (v : Profile) : ℤ := ((List.finRange 19).map (chipTerm v)).sum
def wholeTotal (v : Profile) : ℤ := ((List.finRange 19).map (wholeTerm v)).sum

/-- At chip rate 1/d, the combined drift multiplied by 2d. -/
def drift (d : ℤ) (v : Profile) : ℤ := chipTotal v + d * wholeTotal v

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem isolated_drift (d : ℤ) (hd : d = 5 ∨ d = 6) :
    drift d (profile [0]) ≤ 0 ∧
    (∀ a : Fin 9, drift d (profile [0, a.val]) ≤ 0) ∧
    (∀ a b : Fin 9, drift d (profile [0, a.val, a.val + b.val]) ≤
      if a.val = 0 ∧ b.val = 0 then -d else 0) := by
  rcases hd with rfl | rfl <;> decide

/-- Subadditivity at the first contact of two groups. A one-step move closes
a separating gap of nine to eight. These are all possible cuts with total
mass at most three. Larger merged groups have zero weight. -/
theorem contact_subadditive :
    groupUnits [0, 8] ≤ groupUnits [0] + groupUnits [8] ∧
    (∀ a : Fin 9, groupUnits [0, 8, 8 + a.val] ≤ groupUnits [0] + groupUnits [8, 8 + a.val]) ∧
    (∀ a : Fin 9, groupUnits [0, a.val, a.val + 8] ≤ groupUnits [0, a.val] + groupUnits [a.val + 8]) := by
  decide

/-- All connected shapes of mass one, two or three, rooted at their first particle. -/
inductive Shape
  | single
  | pair (gap : Fin 9)
  | triple (leftGap rightGap : Fin 9)

def Shape.positions : Shape → List ℕ
  | .single => [0]
  | .pair a => [0, a.val]
  | .triple a b => [0, a.val, a.val + b.val]

def Shape.bareThree : Shape → Bool
  | .triple a b => a.val == 0 && b.val == 0
  | _ => false

private theorem drift_shape (d : ℤ) (hd : d = 5 ∨ d = 6) (g : Shape) :
    drift d (profile g.positions) ≤ if g.bareThree then -d else 0 := by
  cases g with
  | single => exact (isolated_drift d hd).1
  | pair a => exact (isolated_drift d hd).2.1 a
  | triple a b => simpa [Shape.positions, Shape.bareThree] using (isolated_drift d hd).2.2 a b

/-- Disconnected configurations from which one rightward move can join two
groups of total mass at most three, up to translation. -/
inductive ContactShape
  | pair
  | tripleLeft (gap : Fin 9)
  | tripleRight (gap : Fin 9)

def ContactShape.positions : ContactShape → List ℕ
  | .pair => [0, 9]
  | .tripleLeft a => [0, 9, 9 + a.val]
  | .tripleRight a => [0, a.val, a.val + 9]

private def mergeCheck (p : List ℕ) (s : Fin 19) : Prop :=
  let v := profile p
  let check := fun k => (groups (particles (jump v s k))).length < (groups (particles v)).length →
    units (jump v s k) ≤ units v
  (1 ≤ v s.castSucc → check 1) ∧ (2 ≤ v s.castSucc → check (v s.castSucc))

private instance (p : List ℕ) (s : Fin 19) : Decidable (mergeCheck p s) := by
  unfold mergeCheck
  infer_instance

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem merge_moves (g : ContactShape) (s : Fin 19) : mergeCheck g.positions s := by
  cases g with
  | pair => exact (by decide : ∀ j : Fin 19, mergeCheck ContactShape.pair.positions j) s
  | tripleLeft a =>
    exact (by decide : ∀ (a : Fin 9) (j : Fin 19), mergeCheck (ContactShape.tripleLeft a).positions j) a s
  | tripleRight a =>
    exact (by decide : ∀ (a : Fin 9) (j : Fin 19), mergeCheck (ContactShape.tripleRight a).positions j) a s

section Ring
variable {L N : ℕ} [NeZero L]

def site (base : Fin L) (j : Fin 20) : Fin L := base + (j.val : Fin L)

def project (base : Fin L) (x : State L N) : Profile := fun j => occ x (site base j)

private theorem site_injective (hL : 20 ≤ L) (base : Fin L) : Function.Injective (site base) := by
  intro i j h
  have hval := congrArg Fin.val (add_left_cancel h : (i.val : Fin L) = (j.val : Fin L))
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt (i.isLt.trans_le hL),
    Nat.mod_eq_of_lt (j.isLt.trans_le hL)] at hval
  exact Fin.ext hval

private theorem site_succ (base : Fin L) (s : Fin 19) :
    right (site base s.castSucc) = site base s.succ := by
  simp [site, right_eq_add_one, add_assoc, Nat.cast_add]

/-- An internal ring move projects exactly to the move used by the certificate. -/
theorem project_move (hL : 20 ≤ L) (base : Fin L) (x : State L N)
    (s : Fin 19) (k : ℕ) (hk : k ≤ occ x (site base s.castSucc)) :
    project base (move x (site base s.castSucc) k hk) = jump (project base x) s k := by
  funext j
  simp only [project, occ_move, transfer, jump, site_succ,
    (site_injective hL base).eq_iff]

noncomputable def potential (base : Fin L) (x : State L N) : ℝ :=
  (units (project base x) : ℝ) / 2

/-- A chip or whole move which joins two small groups cannot raise their
window weight in the ring. -/
theorem potential_move_le_of_merge (hL : 20 ≤ L) (base : Fin L) (x : State L N)
    (g : ContactShape) (hx : project base x = profile g.positions) (s : Fin 19)
    (k : ℕ) (hk : k ≤ occ x (site base s.castSucc))
    (hmove : k = 1 ∨ (2 ≤ k ∧ k = occ x (site base s.castSucc)))
    (hmerge : (groups (particles (project base (move x (site base s.castSucc) k hk)))).length <
      (groups (particles (project base x))).length) :
    potential base (move x (site base s.castSucc) k hk) ≤ potential base x := by
  have hm : occ x (site base s.castSucc) = profile g.positions s.castSucc :=
    congrFun hx s.castSucc
  rw [project_move hL, hx] at hmerge
  unfold potential
  rw [project_move hL, hx]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Int.cast_le.mpr
  have h := merge_moves g s
  rcases hmove with rfl | ⟨h2, heq⟩
  · exact h.1 (hm ▸ hk) hmerge
  · rw [heq, hm] at h2 hmerge ⊢
    exact h.2 h2 hmerge

/-- The part of the linear peak-frame drift allocated to a site of mass m. -/
def firstMomentShare (w : ℝ) (m : ℕ) : ℝ :=
  (if 1 ≤ m then w else 0) - (if m = 1 then 1 else 0)

/-- The certified internal contribution, expressed using the original ring
generator's site terms. Incoming moves and departures at the right boundary
are not internal bonds. -/
noncomputable def internalDrift (w : ℝ) (base : Fin L) (x : State L N) : ℝ :=
  ∑ s : Fin 19, (atSite w (potential base) x (site base s.castSucc) +
    firstMomentShare w (occ x (site base s.castSucc)))

theorem internalDrift_eq (hL : 20 ≤ L) (w : ℝ) (base : Fin L) (x : State L N) :
    2 * internalDrift w base x =
      w * (chipTotal (project base x) : ℝ) + (wholeTotal (project base x) : ℝ) := by
  rw [chipTotal, wholeTotal, ← Fin.sum_univ_def, ← Fin.sum_univ_def, Int.cast_sum, Int.cast_sum,
    internalDrift, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  let m := occ x (site base s.castSucc)
  have hm : project base x s.castSucc = m := rfl
  unfold atSite potential chipTerm wholeTerm firstMomentShare
  simp only [project_move hL, hm]
  by_cases h1 : 1 ≤ m <;> by_cases h2 : 2 ≤ m <;> by_cases hs : m = 1 <;>
    simp [← show m = occ x (site base s.castSucc) from rfl, h1, h2, hs] <;> ring

/-- A two-particle pile with a singleton one site ahead attains the lower
rate endpoint. The same table gives positive drift on this shape below 1/6. -/
theorem internalDrift_pair_single (hL : 20 ≤ L) (w : ℝ) (base : Fin L) (x : State L N)
    (hx : project base x = profile [0, 0, 1]) :
    internalDrift w base x = 3 - 18 * w := by
  have h := internalDrift_eq hL w base x
  rw [hx, show chipTotal (profile [0, 0, 1]) = -36 by decide,
    show wholeTotal (profile [0, 0, 1]) = 6 by decide] at h
  push_cast at h
  linarith

/-- Interpolation of the two integer endpoint checks on any embedded window.
Sites outside the window may have arbitrary occupancies. -/
theorem internalDrift_le (hL : 20 ≤ L) {w : ℝ} (hlo : 1 / 6 ≤ w) (hhi : w ≤ 1 / 5)
    (base : Fin L) (x : State L N) (g : Shape) (hx : project base x = profile g.positions) :
    internalDrift w base x ≤ if g.bareThree then -(1 / 2 : ℝ) else 0 := by
  have he := internalDrift_eq hL w base x
  rw [hx] at he
  have h5 := drift_shape 5 (Or.inl rfl) g
  have h6 := drift_shape 6 (Or.inr rfl) g
  cases hb : g.bareThree <;> simp only [hb, Bool.false_eq_true, if_false, if_true, drift] at h5 h6 ⊢
  all_goals
    have h5' := (Int.cast_le (R := ℝ)).mpr h5
    have h6' := (Int.cast_le (R := ℝ)).mpr h6
    push_cast at h5' h6'
    by_cases hs : 0 ≤ (chipTotal (profile g.positions) : ℝ)
    · nlinarith only [he, h5', mul_nonneg (sub_nonneg.mpr hhi) hs]
    · nlinarith only [he, h6', mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlo) (le_of_not_ge hs)]

/-- Internal bonds are indexed by their departure sites. -/
def internalSites (base : Fin L) : Finset (Fin L) :=
  Finset.univ.image fun s : Fin 19 => site base s.castSucc

/-- The two edges at the ends of the block. On a ring of exactly twenty
sites the two ends use the same edge, which is counted once. -/
noncomputable def boundaryDrift (w : ℝ) (base : Fin L) (x : State L N) : ℝ :=
  ∑ i ∈ (internalSites base)ᶜ,
    if i = site base (Fin.last 19) ∨ right i = base then atSite w (potential base) x i else 0

private theorem atSite_outside (w : ℝ) (base : Fin L) (x : State L N) (i : Fin L)
    (hi : i ∉ internalSites base) (hlast : i ≠ site base (Fin.last 19)) (hrear : right i ≠ base) :
    atSite w (potential base) x i = 0 := by
  have hsrc (j : Fin 20) : site base j ≠ i := by
    refine Fin.lastCases hlast.symm (fun s h => hi ?_) j
    exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, h⟩
  have hdst (j : Fin 20) : site base j ≠ right i := by
    refine Fin.cases (by simpa [site] using hrear.symm) (fun s h => ?_) j
    rw [← site_succ, right_eq_add_one, right_eq_add_one] at h
    exact hsrc s.castSucc (add_right_cancel h)
  have hinv (k : ℕ) (hk : k ≤ occ x i) : project base (move x i k hk) = project base x := by
    funext j
    simp [project, occ_move, transfer, hsrc j, hdst j]
  unfold atSite potential
  split_ifs <;> simp [hinv]

noncomputable def blockShare (w : ℝ) (base : Fin L) (x : State L N) : ℝ :=
  ∑ s : Fin 19, firstMomentShare w (occ x (site base s.castSucc))

private theorem generator_window (hL : 20 ≤ L) (w : ℝ) (base : Fin L) (x : State L N) :
    generator w (potential base) x + blockShare w base x =
      internalDrift w base x + boundaryDrift w base x := by
  classical
  let f := atSite w (potential base) x
  have hint : ∑ i ∈ internalSites base, f i = ∑ s : Fin 19, f (site base s.castSucc) :=
    Finset.sum_image (fun a _ b _ h => Fin.castSucc_injective _ (site_injective hL base h))
  have hext : ∑ i ∈ (internalSites base)ᶜ, f i = boundaryDrift w base x := by
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with h
    · rfl
    · exact atSite_outside w base x i (Finset.mem_compl.mp hi) (fun h' => h (Or.inl h'))
        (fun h' => h (Or.inr h'))
  have hsplit := Finset.sum_add_sum_compl (internalSites base) f
  rw [hint, hext] at hsplit
  unfold generator blockShare internalDrift
  rw [Finset.sum_add_distrib]
  change (∑ i, f i) + _ = ((∑ s : Fin 19, f (site base s.castSucc)) + _) + _
  linarith only [hsplit]

open scoped Classical in
/-- For a stationary ring, the probability of exactly a bare triple at the
start of this window is controlled by the two boundary edges, the internal
drift of all other window configurations outside the certificate, and the
linear-moment share. No majority hypothesis enters the expectation. -/
theorem stationary_bareThree_window_le (hL : 20 ≤ L) {w : ℝ} (hlo : 1 / 6 ≤ w) (hhi : w ≤ 1 / 5)
    (μ : StationaryLaw L N w) (base : Fin L) :
    (∑ x, if project base x = profile [0, 0, 0] then μ.weight x else 0) / 2 ≤
      ∑ x, μ.weight x * (boundaryDrift w base x - blockShare w base x +
        (if ∃ g : Shape, project base x = profile g.positions then 0 else internalDrift w base x)) := by
  classical
  let F := potential (N := N) base
  have hpoint (x : State L N) :
      (if project base x = profile [0, 0, 0] then (1 / 2 : ℝ) else 0) + generator w F x ≤
        boundaryDrift w base x - blockShare w base x +
        (if ∃ g : Shape, project base x = profile g.positions then 0 else internalDrift w base x) := by
    have he := generator_window hL w base x
    change generator w F x + _ = _ at he
    by_cases hb : project base x = profile [0, 0, 0]
    · have hh : ∃ g : Shape, project base x = profile g.positions := ⟨.triple 0 0, hb⟩
      have h := internalDrift_le hL hlo hhi base x (.triple 0 0) hb
      simp only [if_pos hb, if_pos hh, add_zero]
      change internalDrift w base x ≤ -(1 / 2 : ℝ) at h
      linarith
    · simp only [if_neg hb, zero_add]
      split_ifs with hex
      · obtain ⟨g, hg⟩ := hex
        have h := internalDrift_le hL hlo hhi base x g hg
        split_ifs at h <;> linarith
      · linarith
  have h := Finset.sum_le_sum (s := Finset.univ) fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (μ.nonneg x)
  simp only [mul_add, Finset.sum_add_distrib, μ.invariant F, add_zero] at h ⊢
  refine (le_of_eq ?_).trans h
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> ring

end Ring
end Chipping.WindowEight
