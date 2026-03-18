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
import Zpnenp.Davenport

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

/-! ## The Inverse EGZ Theorem -/

/-- **Inverse EGZ Theorem for Z/nZ.**

    A multiset of 2n-2 elements is EGZ-free iff it has the extremal form.
    Forward direction: proved above.
    Backward direction: requires showing any EGZ-free multiset of size
    2n-2 has exactly 2 distinct values, each with multiplicity n-1. -/
theorem inverse_egz (n : ℕ) (hn : 1 < n) (s : Multiset (ZMod n))
    (hcard : s.card = 2 * n - 2) :
    EGZFree s ↔ ∃ a b : ZMod n, IsUnit (a - b) ∧ s = egzExtremal n a b := by
  constructor
  · intro hfree; sorry  -- backward direction
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
