/-
  InverseEGZ.lean — Inverse Erdős-Ginzburg-Ziv theorem

  The EGZ theorem says: among any 2n-1 elements of Z/nZ, there exist
  n whose sum is 0. The inverse EGZ characterizes the threshold 2n-2.

  **Inverse EGZ**: A multiset of 2n-2 elements in Z/nZ avoids having
  an n-element zero-sum submultiset iff it consists of (n-1) copies of
  a and (n-1) copies of b, with a-b a unit.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Multiset.Replicate
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Combinatorics.Additive.ErdosGinzburgZiv
import Zpnenp.Davenport
import Zpnenp.Inverse

open Multiset

/-! ## Definitions -/

/-- A multiset is **EGZ-free** if no submultiset of size n sums to 0. -/
def EGZFree {n : ℕ} (s : Multiset (ZMod n)) : Prop :=
  ∀ t ≤ s, t.card = n → t.sum ≠ 0

/-- The extremal EGZ-free multiset: (n-1) copies of a + (n-1) copies of b. -/
def egzExtremal (n : ℕ) (a b : ZMod n) : Multiset (ZMod n) :=
  Multiset.replicate (n - 1) a + Multiset.replicate (n - 1) b

theorem egzExtremal_card (n : ℕ) (a b : ZMod n) (hn : 1 ≤ n) :
    (egzExtremal n a b).card = 2 * n - 2 := by
  simp [egzExtremal, Multiset.card_replicate]; omega

/-! ## Forward direction -/

/-- Any n-element submultiset of the extremal construction consists of
    j copies of a and (n-j) copies of b, and sums to j*(a-b) mod n.
    Since a-b is a unit and 1 ≤ j ≤ n-1, this is nonzero. -/
theorem egzExtremal_free (n : ℕ) (hn : 1 < n) (a b : ZMod n)
    (hab : IsUnit (a - b)) :
    EGZFree (egzExtremal n a b) := by
  intro t ht htcard htsum
  -- Every element of t is a or b
  have hmem : ∀ x ∈ t, x = a ∨ x = b := by
    intro x hx
    have hxs := Multiset.subset_of_le ht hx
    rw [egzExtremal, Multiset.mem_add] at hxs
    rcases hxs with ha | hb
    · left; exact Multiset.eq_of_mem_replicate ha
    · right; exact Multiset.eq_of_mem_replicate hb
  -- Let j = number of copies of a in t
  set j := Multiset.count a t
  -- j ≤ n-1 (bounded by the number of a's available)
  -- a ≠ b (otherwise a - b = 0 is not a unit for n > 1)
  have hab' : a ≠ b := by
    intro h; subst h
    haveI : NeZero n := ⟨by omega⟩
    haveI : Fact (1 < n) := ⟨hn⟩
    have : a - a = 0 := sub_self a
    rw [this] at hab
    exact not_isUnit_zero hab
  have hj_le : j ≤ n - 1 := by
    have h := Multiset.count_le_of_le a ht
    simp only [egzExtremal, Multiset.count_add, Multiset.count_replicate,
      if_true, if_neg (Ne.symm hab')] at h
    omega
  -- t.sum = j * (a - b) mod n
  -- This is the key algebraic step
  -- Proof: t = j copies of a + (n-j) copies of b
  -- sum = j*a + (n-j)*b = j*a + n*b - j*b = j*(a-b) + n*b = j*(a-b) (mod n)
  have htsum_eq : t.sum = (j : ZMod n) * (a - b) := by
    haveI : NeZero n := ⟨by omega⟩
    -- Step 1: count a t + count b t = card t (all elements are a or b)
    have hcnt_sum : Multiset.count a t + Multiset.count b t = t.card := by
      suffices key : ∀ (s : Multiset (ZMod n)), (∀ x ∈ s, x = a ∨ x = b) →
          Multiset.count a s + Multiset.count b s = s.card from key t hmem
      intro s hs
      induction s using Multiset.induction with
      | empty => simp
      | cons x s ih =>
        simp only [Multiset.count_cons, Multiset.card_cons]
        have ih' := ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy))
        rcases hs x (Multiset.mem_cons_self x s) with rfl | rfl
        · simp [Ne.symm hab']; omega
        · simp [hab']; omega
    have hcb : Multiset.count b t = n - j := by omega
    -- Step 2: decompose t = replicate j a + replicate (n - j) b
    have ht_decomp : t = Multiset.replicate j a + Multiset.replicate (n - j) b := by
      ext x
      simp only [Multiset.count_add, Multiset.count_replicate]
      by_cases hxa : x = a
      · subst hxa
        rw [if_pos rfl, if_neg (Ne.symm hab'), Nat.add_zero]
      · by_cases hxb : x = b
        · subst hxb
          rw [if_neg hab', if_pos rfl, Nat.zero_add, hcb]
        · have hcnt : Multiset.count x t = 0 :=
            Multiset.count_eq_zero.mpr
              (fun hx => by rcases hmem x hx with rfl | rfl <;> contradiction)
          rw [if_neg (Ne.symm hxa), if_neg (Ne.symm hxb), hcnt]
    -- Step 3: compute sum
    rw [ht_decomp]
    simp only [Multiset.sum_add, multiset_sum_replicate]
    rw [nsmul_eq_mul, nsmul_eq_mul]
    have hj_le_n : j ≤ n := by omega
    rw [Nat.cast_sub hj_le_n]
    have hn0 : (n : ZMod n) = 0 := ZMod.natCast_self n
    rw [hn0, zero_sub, neg_mul, ← sub_eq_add_neg, ← mul_sub]
  -- j * (a-b) = 0 with a-b a unit means j = 0 mod n
  rw [htsum_eq] at htsum
  obtain ⟨u, hu⟩ := hab
  have hj_zero : (j : ZMod n) = 0 := by
    rw [← hu] at htsum
    have := congr_arg (· * (↑u⁻¹ : ZMod n)) htsum
    simp only [zero_mul, mul_assoc] at this
    rw [Units.mul_inv, mul_one] at this; exact this
  have hdvd : n ∣ j := by rwa [ZMod.natCast_eq_zero_iff] at hj_zero
  -- But 1 ≤ j ≤ n-1 (j can't be 0 or n)
  -- j = 0 would mean t has no copies of a, so all n copies are b
  -- But there are only n-1 copies of b available
  have hj_pos : 0 < j := by
    by_contra h; push_neg at h; simp only [Nat.le_zero] at h
    -- count a t = 0 and count b t ≤ n-1, but card t = n
    have hb_le : Multiset.count b t ≤ n - 1 := by
      have := Multiset.count_le_of_le b ht
      simp only [egzExtremal, Multiset.count_add, Multiset.count_replicate,
        if_true, if_neg hab'] at this
      omega
    -- All elements are b (since count a = 0 and all elements are a or b)
    have hall_b : ∀ x ∈ t, x = b := by
      intro x hx; rcases hmem x hx with rfl | rfl
      · exact absurd (Multiset.count_pos.mpr hx) (by omega)
      · rfl
    have hcb : Multiset.count b t = t.card :=
      Multiset.count_eq_card.mpr (fun y hy => (hall_b y hy).symm)
    omega
  exact absurd (Nat.le_of_dvd hj_pos hdvd) (by omega)

/-! ## Helper lemmas for backward direction -/

/-- In an EGZ-free multiset, no element can appear n or more times. -/
theorem EGZFree.count_le {n : ℕ} (hn : 1 < n) {s : Multiset (ZMod n)}
    (hfree : EGZFree s) (a : ZMod n) : Multiset.count a s ≤ n - 1 := by
  haveI : NeZero n := ⟨by omega⟩
  by_contra h; push_neg at h
  exact hfree (Multiset.replicate n a)
    (Multiset.le_count_iff_replicate_le.mp (by omega))
    (Multiset.card_replicate n a)
    (by rw [multiset_sum_replicate, nsmul_eq_mul, ZMod.natCast_self, zero_mul])

-- count_add_count helper is inlined in the backward direction proof
-- to avoid induction generalization issues with theorem parameters

/-- If a-b is not a unit, the extremal multiset has an n-element zero-sum submultiset. -/
theorem not_egzFree_of_not_isUnit (n : ℕ) (hn : 1 < n) (a b : ZMod n)
    (hab : a ≠ b) (hnu : ¬IsUnit (a - b)) :
    ¬EGZFree (egzExtremal n a b) := by
  haveI : NeZero n := ⟨by omega⟩
  -- Since a-b is not a unit in finite ring ZMod n, it has a nontrivial zero divisor
  have hzd : ∃ c : ZMod n, c ≠ 0 ∧ c * (a - b) = 0 := by
    by_contra hall; push_neg at hall
    have hinj : Function.Injective (· * (a - b) : ZMod n → ZMod n) := by
      intro x y (hxy : x * (a - b) = y * (a - b))
      by_contra hne
      have : (x - y) * (a - b) = 0 := by rw [sub_mul, hxy, sub_self]
      exact hall (x - y) (sub_ne_zero.mpr hne) this
    have hsurj := Finite.surjective_of_injective hinj
    obtain ⟨x, hx⟩ := hsurj 1
    have hab1 : (a - b) * x = 1 := by rw [mul_comm]; exact hx
    exact hnu ⟨⟨a - b, x, hab1, hx⟩, rfl⟩
  obtain ⟨c, hc_ne, hc_mul⟩ := hzd
  -- m = c.val ∈ {1, ..., n-1} and (m : ZMod n) * (a-b) = 0
  set m := c.val with hm_def
  have hm_pos : 0 < m := by
    rw [hm_def]; exact Nat.pos_of_ne_zero (fun h => hc_ne ((ZMod.val_eq_zero c).mp h))
  have hm_lt : m < n := ZMod.val_lt c
  have hm_cast : (m : ZMod n) = c := by
    show ((ZMod.val c : ℕ) : ZMod n) = c
    rw [ZMod.natCast_val, ZMod.cast_id]
  -- The submultiset: m copies of a + (n-m) copies of b
  intro hfree
  apply hfree (Multiset.replicate m a + Multiset.replicate (n - m) b)
  · -- t ≤ egzExtremal n a b
    rw [Multiset.le_iff_count]; intro x
    simp only [egzExtremal, Multiset.count_add, Multiset.count_replicate]
    by_cases hxa : x = a
    · subst hxa; simp [Ne.symm hab]; omega
    · by_cases hxb : x = b
      · subst hxb; simp [hab]; omega
      · simp [Ne.symm hxa, Ne.symm hxb]
  · -- card = n
    simp only [Multiset.card_add, Multiset.card_replicate]; omega
  · -- sum = 0
    simp only [Multiset.sum_add, multiset_sum_replicate, nsmul_eq_mul]
    rw [Nat.cast_sub (by omega : m ≤ n), ZMod.natCast_self, zero_sub,
        neg_mul, ← sub_eq_add_neg, ← mul_sub, hm_cast]
    exact hc_mul

/-- If s is EGZ-free with |s| = 2n-2, adding any element x gives a multiset where
    every n-element zero-sum must include x. Hence there exist n-1 elements
    of s summing to -x. -/
theorem EGZFree.exists_sum_eq {n : ℕ} (hn : 1 < n) {s : Multiset (ZMod n)}
    (hfree : EGZFree s) (hcard : s.card = 2 * n - 2) (x : ZMod n) :
    ∃ t ≤ s, t.card = n - 1 ∧ t.sum = -x := by
  haveI : NeZero n := ⟨by omega⟩
  -- s + {x} has size 2n-1, so by EGZ, it contains n elements summing to 0
  have hcard' : 2 * n - 1 ≤ (x ::ₘ s).card := by simp; omega
  obtain ⟨t, htles, htcard, htsum⟩ := ZMod.erdos_ginzburg_ziv_multiset (x ::ₘ s) hcard'
  -- t must include x (otherwise t ≤ s contradicts EGZ-free)
  by_cases hx : x ∈ t
  · -- t = x ::ₘ t', where t' ≤ s, |t'| = n-1, sum(t') = -x
    refine ⟨t.erase x, ?_, ?_, ?_⟩
    · -- t.erase x ≤ s
      have : t.erase x ≤ (x ::ₘ s).erase x := Multiset.erase_le_erase x htles
      rwa [Multiset.erase_cons_head] at this
    · -- card = n - 1
      have h := Multiset.card_erase_of_mem hx; rw [htcard] at h; exact h
    · -- sum = -x
      have hteq : t = x ::ₘ t.erase x := (Multiset.cons_erase hx).symm
      rw [hteq, Multiset.sum_cons] at htsum
      -- htsum : x + (t.erase x).sum = 0
      rw [add_comm] at htsum; exact eq_neg_of_add_eq_zero_left htsum
  · -- t doesn't contain x, so t ≤ s, contradicting EGZ-free
    exfalso
    exact hfree t ((Multiset.le_cons_of_notMem hx).mp htles) htcard htsum

/-- **Key Lemma**: An EGZ-free multiset of size 2n-2 has at most 2 distinct values.

    **Proof sketch** (not yet fully formalized):

    Suppose s has ≥ 3 distinct values. We derive a contradiction with EGZ-free.

    Step 1: By `exists_sum_eq`, for any x the complement of the (n-1)-submultiset
    summing to -x also has n-1 elements. If this complement is zero-sum free,
    by `inverse_davenport` it equals replicate (n-1) g for some unit g, so
    count(g, s) = n-1.

    Step 2: With count(g, s) = n-1, let R = s minus the g-copies (|R| = n-1,
    ≥ 2 distinct values, no copies of g).

    Step 3: Shift R by -g: the multiset R.map (· - g) has n-1 nonzero elements
    with ≥ 2 values. By `inverse_davenport` contrapositive, it has a nonempty
    zero-sum submultiset v of size m. The corresponding u ≤ R has sum = m*g.

    Step 4: u + replicate (n-m) g has n elements summing to n*g = 0,
    contradicting EGZ-free.

    The gap: Step 1 requires finding x where the complement IS zero-sum free,
    and Step 4 requires n-m ≤ n-1 (ensured by m ≥ 1). When no complement is
    zero-sum free, or when count(g,s) < n-1 for all g, a more sophisticated
    argument involving iterated Davenport applications is needed. -/
theorem EGZFree.at_most_two_values {n : ℕ} (hn : 1 < n) {s : Multiset (ZMod n)}
    (hfree : EGZFree s) (hcard : s.card = 2 * n - 2) :
    ∃ a b : ZMod n, ∀ x ∈ s, x = a ∨ x = b := by
  sorry

/-! ## The Inverse EGZ Theorem -/

/-- **Inverse EGZ Theorem for Z/nZ.**

    A multiset of 2n-2 elements is EGZ-free iff it has the extremal form.
    Forward direction: proved above.
    Backward direction: uses structural lemmas above. The one remaining sorry
    is `EGZFree.at_most_two_values` — the fact that EGZ-free multisets of
    size 2n-2 have at most 2 distinct values. -/
theorem inverse_egz (n : ℕ) (hn : 1 < n) (s : Multiset (ZMod n))
    (hcard : s.card = 2 * n - 2) :
    EGZFree s ↔ ∃ a b : ZMod n, IsUnit (a - b) ∧ s = egzExtremal n a b := by
  constructor
  · intro hfree
    -- Step 1: s has at most 2 distinct values
    obtain ⟨a, b, hmem⟩ := EGZFree.at_most_two_values hn hfree hcard
    -- Step 2: a ≠ b (if a = b, all elements equal a, count ≥ 2n-2 ≥ n, impossible)
    have hab : a ≠ b := by
      intro h; subst h
      have hall : ∀ y ∈ s, y = a := fun y hy => by
        rcases hmem y hy with rfl | rfl <;> rfl
      have hle : Multiset.count a s = s.card :=
        Multiset.count_eq_card.mpr (fun y hy => (hall y hy).symm)
      have := EGZFree.count_le hn hfree a
      omega
    -- Step 3: each value appears exactly n-1 times
    have hcnt : Multiset.count a s + Multiset.count b s = s.card := by
      suffices key : ∀ (t : Multiset (ZMod n)), (∀ x ∈ t, x = a ∨ x = b) →
          Multiset.count a t + Multiset.count b t = t.card from key s hmem
      intro t ht
      induction t using Multiset.induction with
      | empty => simp
      | cons x t ih =>
        simp only [Multiset.count_cons, Multiset.card_cons]
        have ih' := ih (fun y hy => ht y (Multiset.mem_cons_of_mem hy))
        rcases ht x (Multiset.mem_cons_self x t) with rfl | rfl
        · simp [Ne.symm hab]; omega
        · simp [hab]; omega
    have hca_le := EGZFree.count_le hn hfree a
    have hcb_le := EGZFree.count_le hn hfree b
    have hca : Multiset.count a s = n - 1 := by omega
    have hcb : Multiset.count b s = n - 1 := by omega
    -- Step 4: s = egzExtremal n a b
    have hs_eq : s = egzExtremal n a b := by
      ext x
      simp only [egzExtremal, Multiset.count_add, Multiset.count_replicate]
      by_cases hxa : x = a
      · subst hxa; rw [if_pos rfl, if_neg (Ne.symm hab)]; omega
      · by_cases hxb : x = b
        · subst hxb; rw [if_neg hab, if_pos rfl]; omega
        · have : Multiset.count x s = 0 :=
            Multiset.count_eq_zero.mpr
              (fun hx => by rcases hmem x hx with rfl | rfl <;> contradiction)
          rw [if_neg (Ne.symm hxa), if_neg (Ne.symm hxb)]; omega
    -- Step 5: a - b is a unit
    have hab_unit : IsUnit (a - b) := by
      by_contra hnu
      exact not_egzFree_of_not_isUnit n hn a b hab hnu (hs_eq ▸ hfree)
    exact ⟨a, b, hab_unit, hs_eq⟩
  · rintro ⟨a, b, hab, rfl⟩; exact egzExtremal_free n hn a b hab

/-! ## Significance

The inverse EGZ extends the inverse Davenport in two ways:

1. **Larger threshold**: Davenport is at size n-1 (any nonempty zero-sum).
   EGZ is at size 2n-2 (n-element zero-sum). Both thresholds have
   rigid extremal instances.

2. **Two elements instead of one**: Davenport extremals are (n-1) copies
   of one unit. EGZ extremals are (n-1) copies each of two elements
   whose difference is a unit. The "structural complexity" of extremal
   instances grows, but remains bounded.

For P ≠ NP: even at the EGZ threshold (which is FURTHER from the
guaranteed-existence regime), the adversary's optimal strategy is
rigidly constrained to a 2-parameter family. The adversary cannot
escape structure.
-/
