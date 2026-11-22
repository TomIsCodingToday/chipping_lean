import ChippingSupercondensation.VariableWindow
import ChippingSupercondensation.WindowEight
import Mathlib.Data.Multiset.Sort
import Mathlib.Tactic.IntervalCases

/-! # Embedding the variable-radius certificate into the chipping generator

The particle positions of a block are recorded with multiplicity. For every
occupied site of a group, a slice records the sorted positions before and
after that pile. The ring move changes only that slice.
-/

namespace Chipping.VariableWindow
open scoped BigOperators
noncomputable section

def Group.positions : Group → List ℕ
  | .one => [0]
  | .two a => [0,a]
  | .three a b => [0,a,a+b]

def listValue (V : Group → ℝ) : List ℕ → ℝ
  | [_] => V .one
  | [x,y] => V (.two (y-x))
  | [x,y,z] => V (.three (y-x) (z-y))
  | _ => 0

structure Slice where
  left : List ℕ
  site : ℕ
  mass : ℕ
  right : List ℕ

def Slice.after (s : Slice) (k : ℕ) : List ℕ :=
  s.left ++ List.replicate (s.mass-k) s.site ++ List.replicate k (s.site+1) ++ s.right

def Group.slices : Group → List Slice
  | .one => [⟨[],0,1,[]⟩]
  | .two 0 => [⟨[],0,2,[]⟩]
  | .two (a+1) => [⟨[],0,1,[a+1]⟩, ⟨[0],a+1,1,[]⟩]
  | .three 0 0 => [⟨[],0,3,[]⟩]
  | .three 0 (b+1) => [⟨[],0,2,[b+1]⟩, ⟨[0,0],b+1,1,[]⟩]
  | .three (a+1) 0 => [⟨[],0,1,[a+1,a+1]⟩, ⟨[0],a+1,2,[]⟩]
  | .three (a+1) (b+1) =>
    [⟨[],0,1,[a+1,a+b+2]⟩, ⟨[0],a+1,1,[a+b+2]⟩, ⟨[0,a+1],a+b+2,1,[]⟩]

def Slice.drift (s : Slice) (w : ℝ) (V : Group → ℝ) : ℝ :=
  let before := listValue V (s.after 0)
  w * (listValue V (s.after 1) - before) +
    (if 2 ≤ s.mass then listValue V (s.after s.mass) - before else 0) +
    WindowEight.firstMomentShare w s.mass

theorem sum_slice_drift (g : Group) (w : ℝ) (V : Group → ℝ) :
    (g.slices.map (fun s => s.drift w V)).sum = drift w V g := by
  cases g with
  | one =>
    simp [Group.slices, Slice.drift, Slice.after, listValue, drift, WindowEight.firstMomentShare]
  | two a =>
    cases a <;> simp [Group.slices, Slice.drift, Slice.after, listValue, drift,
      WindowEight.firstMomentShare, List.replicate_succ] <;> ring
  | three a b =>
    cases a <;> cases b <;>
      simp [Group.slices, Slice.drift, Slice.after, listValue, drift,
        WindowEight.firstMomentShare, List.replicate_succ] <;> ring_nf
    simp only [show ∀ a b c : ℕ, c+a+b-a = c+b by omega]
    ring

/-- A histogram of the unwrapped offsets in a window based at a ring site. -/
def blockParticles {L N : ℕ} [NeZero L] (base : Fin L) (width : ℕ) (x : State L N) : Multiset ℕ :=
  ∑ j ∈ Finset.range width, Multiset.replicate (occ x (base+j)) j

def blockValue {L N : ℕ} [NeZero L] (V : Group → ℝ) (base : Fin L) (width : ℕ) (x : State L N) : ℝ :=
  listValue V ((blockParticles base width x).sort (· ≤ ·))

theorem count_blockParticles {L N : ℕ} [NeZero L] (base : Fin L) (width : ℕ)
    (x : State L N) (j : ℕ) :
    (blockParticles base width x).count j = if j < width then occ x (base+j) else 0 := by
  simp [blockParticles, Multiset.count_sum', Multiset.count_replicate]

theorem blockValue_of_sorted {L N : ℕ} [NeZero L] (V : Group → ℝ)
    (base : Fin L) (width : ℕ) (x : State L N) (p : List ℕ)
    (hp : blockParticles base width x = (p : Multiset ℕ)) (hs : p.Sorted (· ≤ ·)) :
    blockValue V base width x = listValue V p := by
  rw [blockValue, hp, Multiset.coe_sort, List.mergeSort_eq_self _ hs]

def Group.span : Group → ℕ
  | .one => 0
  | .two a => a
  | .three a b => a+b

theorem slice_facts (g : Group) (s : Slice) (hs : s ∈ g.slices) :
    s.after 0 = g.positions ∧ 0 < s.mass ∧ s.site ≤ g.span ∧
    (s.after 0).count s.site = s.mass ∧ ∀ k ≤ s.mass, (s.after k).Sorted (· ≤ ·) := by
  rcases g with _ | (_ | a) | ⟨(_ | a), (_ | b)⟩
  all_goals
    simp only [Group.slices, List.mem_cons, List.not_mem_nil, or_false] at hs
    repeat' first | subst s | rcases hs with (hs | hs)
  all_goals
    simp (disch := omega) [Group.positions, Group.span, Slice.after, List.replicate_succ,
      List.count_cons, List.Sorted, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals
    intro k hk
    interval_cases k <;> simp (disch := omega) [List.replicate_succ, Nat.add_assoc] <;> omega

theorem count_after (s : Slice) (k j : ℕ) (hk : k ≤ s.mass) :
    (s.after k).count j =
      (s.after 0).count j - (if j = s.site then k else 0) + (if j = s.site+1 then k else 0) := by
  simp only [Slice.after, List.count_append, List.count_replicate, beq_iff_eq, Nat.sub_zero]
  split_ifs <;> omega

theorem block_move_after {L N : ℕ} [NeZero L] (base : Fin L) (width : ℕ) (hL : width ≤ L)
    (x : State L N) (s : Slice) (hs : s.site+1 < width)
    (hx : blockParticles base width x = (s.after 0 : Multiset ℕ))
    (k : ℕ) (hkm : k ≤ s.mass) (hk : k ≤ occ x (base+s.site)) :
    blockParticles base width (move x (base+s.site) k hk) = (s.after k : Multiset ℕ) := by
  apply Multiset.ext.mpr
  intro j
  have hjx := congrArg (Multiset.count j) hx
  rw [count_blockParticles, Multiset.coe_count] at hjx
  rw [count_blockParticles, Multiset.coe_count, count_after s k j hkm, ← hjx]
  by_cases hj : j < width
  · have inj (q : ℕ) (hq : q < width) :
        (base + (j : Fin L) = base + (q : Fin L)) ↔ j = q := by
      rw [add_right_inj]
      constructor
      · intro he
        simpa [Fin.val_natCast, Nat.mod_eq_of_lt (hj.trans_le hL), Nat.mod_eq_of_lt (hq.trans_le hL)]
          using congrArg Fin.val he
      · rintro rfl; rfl
    have hr : right (base + (s.site : Fin L)) = base + ((s.site+1 : ℕ) : Fin L) := by
      simp [right_eq_add_one, add_assoc]
    simp only [if_pos hj, occ_move, transfer, hr, inj _ hs, inj _ (by omega : s.site < width)]
  · simp [hj, show j ≠ s.site by omega, show j ≠ s.site+1 by omega]

/-- The internal clocks of the group are the original atSite terms at its
occupied sites. Only the contents of the displayed block are specified. -/
theorem ring_drift_eq {L N : ℕ} [NeZero L] (w : ℝ) (V : Group → ℝ) (base : Fin L)
    (width : ℕ) (hL : width ≤ L) (x : State L N) (g : Group) (hroom : g.span+1 < width)
    (hx : blockParticles base width x = (g.positions : Multiset ℕ)) :
    (g.slices.map fun s => atSite w (blockValue V base width) x (base+s.site) +
      WindowEight.firstMomentShare w (occ x (base+s.site))).sum = drift w V g := by
  rw [← sum_slice_drift]
  congr 1
  apply List.map_congr_left
  intro s hs
  obtain ⟨hbefore, hpos, hspan, hcount, hsorted⟩ := slice_facts g s hs
  have hx' : blockParticles base width x = (s.after 0 : Multiset ℕ) := hbefore ▸ hx
  have hm := congrArg (Multiset.count s.site) hx'
  rw [count_blockParticles, if_pos (by omega : s.site < width), Multiset.coe_count, hcount] at hm
  have hv := blockValue_of_sorted V base width x _ hx' (hsorted 0 (Nat.zero_le _))
  have hmoved (k : ℕ) (hk : k ≤ s.mass) (ha : k ≤ occ x (base+s.site)) :
      blockValue V base width (move x (base+s.site) k ha) = listValue V (s.after k) :=
    blockValue_of_sorted V base width _ _ (block_move_after base width hL x s (by omega) hx' k hk ha)
      (hsorted k hk)
  unfold atSite Slice.drift
  simp only [dif_pos (by omega : 1 ≤ occ x (base+s.site)), hv, hmoved 1 hpos]
  by_cases h2 : 2 ≤ occ x (base+s.site)
  · simp [h2, hmoved _ hm.le, hm, show 2 ≤ s.mass by omega]
    exact hmoved _ le_rfl hm.ge
  · simp [h2, hm, show ¬2 ≤ s.mass by omega]

/-- The uniform one-sixty-fourth credit for a bare triple under the original
ring's internal clocks, for every sufficiently small positive rate. -/
theorem smallRate_ring_drift_le {L N : ℕ} [NeZero L] {w : ℝ} (hw : 0 < w) (hs : w ≤ 1/32)
    (base : Fin L) (width : ℕ) (hL : width ≤ L) (x : State L N) (g : Group)
    (hroom : g.span+1 < width) (hx : blockParticles base width x = (g.positions : Multiset ℕ)) :
    let V := price w (radius w) (1/w)
    (g.slices.map fun s => atSite w (blockValue V base width) x (base+s.site) +
      WindowEight.firstMomentShare w (occ x (base+s.site))).sum ≤
      if g = .three 0 0 then -(1/64 : ℝ) else 0 :=
  (ring_drift_eq w _ base width hL x g hroom hx).le.trans (smallRate_drift_le hw hs g)

/-! ## Positive drift from a block of mass at least four -/

theorem card_blockParticles_eq {L N : ℕ} [NeZero L] (base : Fin L) (n : ℕ) (x : State L N) :
    ((blockParticles base (n+1) x).card : ℝ) = windowMass (n+1) x (base+n) := by
  simp only [blockParticles, Multiset.card_sum, Multiset.card_replicate, Nat.cast_sum, windowMass]
  rw [← Finset.sum_range_reflect (fun j : ℕ => (occ x (base+(j : Fin L)) : ℝ)) (n+1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  simp only [Nat.add_sub_cancel, Nat.cast_sub hjn, add_sub_assoc]

theorem listValue_zero_of_mass {w : ℝ} (p : List ℕ) (hm : p.length < 2 ∨ 3 < p.length) :
    listValue (price w (radius w) (1/w)) p = 0 := by
  rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    simp_all [listValue, price]

theorem blockValue_le {L N : ℕ} [NeZero L] {w : ℝ} (hw : 0 < w) (base : Fin L)
    (width : ℕ) (x : State L N) :
    blockValue (price w (radius w) (1/w)) base width x ≤ priceBound w := by
  unfold blockValue
  generalize (blockParticles base width x).sort (· ≤ ·) = p
  rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    first | apply price_le_priceBound hw | exact (price_nonneg hw .one).trans (price_le_priceBound hw .one)

theorem blockValue_zero_of_mass {L N : ℕ} [NeZero L] {w : ℝ} (base : Fin L)
    (width : ℕ) (x : State L N)
    (hm : (blockParticles base width x).card < 2 ∨ 3 < (blockParticles base width x).card) :
    blockValue (price w (radius w) (1/w)) base width x = 0 :=
  listValue_zero_of_mass _ (by simpa only [Multiset.length_sort] using hm)

/-- On a heavy block only an exit that leaves two or three particles can
create positive price. The chip term requires mass exactly four. The whole
move term requires all but two or three particles to be on the final site. -/
theorem generator_largeBlock_le {L N : ℕ} [NeZero L] {w : ℝ} (hw : 0 < w)
    (base : Fin L) (n : ℕ) (hproper : n+1 < L) (x : State L N)
    (hheavy : 4 ≤ (blockParticles base (n+1) x).card) :
    let q := (blockParticles base (n+1) x).card
    let m := occ x (base+n)
    generator w (blockValue (price w (radius w) (1/w)) base (n+1)) x ≤
      (if q = 4 ∧ 1 ≤ m then w * priceBound w else 0) +
      (if 2 ≤ m ∧ 2 ≤ q-m ∧ q-m ≤ 3 then priceBound w else 0) := by
  let q := (blockParticles base (n+1) x).card
  let last : Fin L := base+n
  let F := blockValue (N := N) (price w (radius w) (1/w)) base (n+1)
  have hzero : F x = 0 := blockValue_zero_of_mass base (n+1) x (Or.inr hheavy)
  have hdelta (i : Fin L) (k : ℕ) (hk : k ≤ occ x i) :
      ((blockParticles base (n+1) (move x i k hk)).card : ℝ) - (q : ℝ) =
        (k : ℝ) * ((if last = i + ((n+1 : ℕ) : Fin L) then 1 else 0) -
                    (if last = i then 1 else 0)) := by
    simpa only [q, card_blockParticles_eq] using windowMass_move (n+1) x i k hk last
  have hout (i : Fin L) (hi : i ≠ last) (k : ℕ) (hk : k ≤ occ x i) :
      F (move x i k hk) = 0 := by
    have hd := hdelta i k hk
    rw [if_neg hi.symm] at hd
    have hle : (q : ℝ) ≤ ((blockParticles base (n+1) (move x i k hk)).card : ℝ) := by
      split_ifs at hd <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    apply blockValue_zero_of_mass
    exact Or.inr (hheavy.trans (by exact_mod_cast hle))
  have hexit (k : ℕ) (hk : k ≤ occ x last) :
      (blockParticles base (n+1) (move x last k hk)).card + k = q := by
    have hne := natCast_fin_ne_zero (by omega : 0 < n+1) hproper
    have h := hdelta last k hk
    have he : last ≠ last + ((n+1 : ℕ) : Fin L) := by simpa using hne
    rw [if_neg he, if_pos rfl] at h
    exact_mod_cast (show ((blockParticles base (n+1) (move x last k hk)).card : ℝ) + k = q by linarith)
  change generator w F x ≤ (if q = 4 ∧ 1 ≤ occ x last then _ else _) + _
  unfold generator
  rw [Finset.sum_eq_single last]
  · unfold atSite
    simp only [hzero, sub_zero]
    apply add_le_add
    · by_cases hc : 1 ≤ occ x last
      · rw [dif_pos hc]
        by_cases h4 : q = 4
        · rw [if_pos ⟨h4, hc⟩]
          exact mul_le_mul_of_nonneg_left (blockValue_le hw _ _ _) hw.le
        · rw [if_neg (fun h => h4 h.1)]
          have he := hexit 1 hc
          have hz : F (move x last 1 hc) = 0 := blockValue_zero_of_mass _ _ _ (Or.inr (by
            change 4 ≤ q at hheavy
            omega))
          simp [hz]
      · simp [hc]
    · let m := occ x last
      by_cases hm : 2 ≤ m
      · change (if 2 ≤ m then F (move x last m le_rfl) else 0) ≤
            if 2 ≤ m ∧ 2 ≤ q-m ∧ q-m ≤ 3 then priceBound w else 0
        rw [if_pos hm]
        by_cases hsmall : 2 ≤ q-m ∧ q-m ≤ 3
        · rw [if_pos ⟨hm, hsmall⟩]
          exact blockValue_le hw _ _ _
        · rw [if_neg (fun h => hsmall h.2)]
          have he := hexit m le_rfl
          exact (blockValue_zero_of_mass base (n+1) (move x last m le_rfl) (by omega)).le
      · change (if 2 ≤ m then _ else 0) ≤ if 2 ≤ m ∧ _ then _ else 0
        simp [hm]
  · intro i _ hi
    unfold atSite
    split_ifs <;> simp [hout i hi, hzero]
  · simp

/-- A bare triple at the start of an otherwise empty block has strictly
negative *full* generator. An arrival from outside either bypasses the block
or raises its mass to at least four, where the price vanishes. -/
theorem generator_bareThree_le {L N : ℕ} [NeZero L] {w : ℝ} (hw : 0 < w) (hs : w ≤ 1/32)
    (base : Fin L) (width : ℕ) (hL : width ≤ L) (hroom : 1 < width) (x : State L N)
    (hx : blockParticles base width x = (([0,0,0] : List ℕ) : Multiset ℕ)) :
    generator w (blockValue (price w (radius w) (1/w)) base width) x ≤ -(w+1/64) := by
  let V := price w (radius w) (1/w)
  let F := blockValue (N := N) V base width
  have hm := congrArg (Multiset.count 0) hx
  rw [count_blockParticles, if_pos (by omega : 0 < width), Multiset.coe_count] at hm
  have hbase : occ x base = 3 := by simpa using hm
  have hclock := smallRate_ring_drift_le hw hs base width hL x (.three 0 0) hroom hx
  have hc : atSite w F x base + w ≤ -(1/64 : ℝ) := by
    simpa [Group.slices, WindowEight.firstMomentShare, hbase, F, V] using hclock
  have hold : 0 ≤ F x := by
    rw [show F x = listValue V [0,0,0] from blockValue_of_sorted V base width x _ hx (by simp [List.Sorted])]
    exact price_nonneg hw (.three 0 0)
  have hout (i : Fin L) (hi : i ≠ base) (hiocc : 1 ≤ occ x i) (k : ℕ) (hk : k ≤ occ x i) :
      F (move x i k hk) ≤ F x := by
    have hmono : blockParticles base width x ≤ blockParticles base width (move x i k hk) := by
      apply Multiset.le_iff_count.mpr
      intro j
      simp only [count_blockParticles]
      split_ifs with hj
      · have hne : base + (j : Fin L) ≠ i := by
          intro he
          have hn := congrArg (Multiset.count j) hx
          rw [count_blockParticles, if_pos hj, he, Multiset.coe_count] at hn
          by_cases hz : j = 0
          · subst j; exact hi (by simpa using he.symm)
          · simp [List.count_cons, hz, Ne.symm hz] at hn
            omega
        simp [occ_move, transfer, hne]
      · exact le_rfl
    by_cases he : blockParticles base width x = blockParticles base width (move x i k hk)
    · unfold F blockValue
      rw [he]
    · have hlt := Multiset.card_lt_card (lt_of_le_of_ne hmono he)
      rw [hx] at hlt
      have hz := blockValue_zero_of_mass (w := w) base width (move x i k hk)
        (Or.inr (by simpa using hlt))
      change blockValue _ _ _ _ ≤ _
      rw [hz]
      exact hold
  have hother (i : Fin L) (hi : i ≠ base) : atSite w F x i ≤ 0 := by
    unfold atSite
    split_ifs with h1 h2 h2
    · exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hw.le (sub_nonpos.mpr (hout i hi h1 _ h1)))
        (sub_nonpos.mpr (hout i hi h1 _ le_rfl))
    · simpa using mul_nonpos_of_nonneg_of_nonpos hw.le (sub_nonpos.mpr (hout i hi h1 1 h1))
    · omega
    · norm_num
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => show atSite w F x i ≤
    (if i = base then atSite w F x base else 0) by
      by_cases hi : i = base
      · simp [hi]
      · simpa [hi] using hother i hi)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  change (∑ i, atSite w F x i) ≤ _
  linarith

/-- The stationary cost of a rooted bare triple is paid by other light
blocks and by the two exit events that can give a heavy block positive price. -/
theorem stationary_bareThree_le_lightDrift_and_exits {L N : ℕ} [NeZero L] {w : ℝ}
    (hw : 0 < w) (hs : w ≤ 1/32) (μ : StationaryLaw L N w) (base : Fin L) (n : ℕ)
    (hn : 0 < n) (hproper : n+1 < L) :
    let P := blockParticles (N := N) base (n+1)
    let F := blockValue (N := N) (price w (radius w) (1/w)) base (n+1)
    (w+1/64) * (∑ x, if P x = (([0,0,0] : List ℕ) : Multiset ℕ) then μ.weight x else 0) ≤
      ∑ x, μ.weight x * (if 4 ≤ (P x).card then
        (if (P x).card = 4 ∧ 1 ≤ occ x (base+n) then w * priceBound w else 0) +
        (if 2 ≤ occ x (base+n) ∧ 2 ≤ (P x).card - occ x (base+n) ∧
          (P x).card - occ x (base+n) ≤ 3 then priceBound w else 0)
        else if P x = (([0,0,0] : List ℕ) : Multiset ℕ) then 0 else generator w F x) := by
  intro P F
  let bare : Multiset ℕ := ([0,0,0] : List ℕ)
  rw [Finset.mul_sum]
  conv_lhs =>
    rw [← add_zero (∑ x, _)]
    rhs
    rw [← μ.invariant F]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hb : P x = bare
  · have hl : ¬4 ≤ (P x).card := by rw [hb]; decide
    change P x = (([0,0,0] : List ℕ) : Multiset ℕ) at hb
    simp only [if_pos hb, if_neg hl, mul_zero]
    have h := generator_bareThree_le hw hs base (n+1) hproper.le (by omega) x hb
    change _ + μ.weight x * generator w F x ≤ 0
    nlinarith only [mul_le_mul_of_nonneg_left h (μ.nonneg x)]
  · change P x ≠ (([0,0,0] : List ℕ) : Multiset ℕ) at hb
    simp only [if_neg hb, mul_zero, zero_add]
    by_cases hq : 4 ≤ (P x).card
    · rw [if_pos hq]
      exact mul_le_mul_of_nonneg_left (generator_largeBlock_le hw base n hproper x hq) (μ.nonneg x)
    · rw [if_neg hq]

end
end Chipping.VariableWindow
