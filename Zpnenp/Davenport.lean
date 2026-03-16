/-
  Davenport.lean — The Davenport constant for ℤ/nℤ

  The Davenport constant D(G) of a finite abelian group G is the smallest d
  such that every sequence of d elements from G contains a non-empty
  subsequence summing to zero.

  We prove D(ℤ/nℤ) = n by establishing both bounds:
  - Upper: every multiset of n elements in ZMod n has a nonempty
    submultiset summing to 0 (pigeonhole on prefix sums)
  - Lower: the multiset {1, 1, ..., 1} of n−1 copies has no nonempty
    submultiset summing to 0
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Data.List.Infix

/-! ## Zero-sum free sequences -/

/-- A multiset over an additive group is **zero-sum free** if no nonempty
    submultiset sums to zero. -/
def ZeroSumFree {G : Type*} [AddCommMonoid G] (s : Multiset G) : Prop :=
  ∀ t ≤ s, t ≠ 0 → t.sum ≠ 0

/-! ## Auxiliary lemma: sum of replicate -/

/-- The sum of k copies of a in an additive commutative monoid is k • a. -/
theorem multiset_sum_replicate {G : Type*} [AddCommMonoid G] (k : ℕ) (a : G) :
    (Multiset.replicate k a).sum = k • a := by
  induction k with
  | zero => simp
  | succ n ih => simp [Multiset.replicate_succ, ih, add_nsmul, add_comm]

/-! ## Lower bound: D(ℤ/nℤ) ≥ n -/

/-- The multiset of (n−1) copies of 1 in ZMod n is zero-sum free,
    establishing D(ℤ/nℤ) ≥ n. -/
theorem zeroSumFree_replicate_one (n : ℕ) (hn : 1 < n) :
    ZeroSumFree (Multiset.replicate (n - 1) (1 : ZMod n)) := by
  intro t ht hne hsum
  have hmem : ∀ x ∈ t, x = (1 : ZMod n) :=
    fun x hx => Multiset.eq_of_mem_replicate (Multiset.subset_of_le ht hx)
  have hcard_pos : 0 < t.card := by rw [Multiset.card_pos]; exact hne
  have hcard_le : t.card ≤ n - 1 :=
    (Multiset.card_le_card ht).trans (Multiset.card_replicate _ _).le
  have ht_eq : t = Multiset.replicate t.card 1 := by
    ext x
    simp only [Multiset.count_replicate]
    split
    · next h => subst h; exact Multiset.count_eq_card.mpr (fun y hy => (hmem y hy).symm)
    · next h => exact Multiset.count_eq_zero.mpr (fun hx => h (hmem x hx).symm)
  rw [ht_eq, multiset_sum_replicate, nsmul_eq_mul, mul_one] at hsum
  have hdvd : n ∣ t.card := by rwa [ZMod.natCast_eq_zero_iff] at hsum
  exact absurd (Nat.le_of_dvd hcard_pos hdvd) (by omega)

/-! ## Upper bound: D(ℤ/nℤ) ≤ n -/

/-- Every multiset of n elements in ZMod n (n > 0) contains a nonempty
    submultiset summing to 0. This establishes D(ℤ/nℤ) ≤ n.

    Proof: convert to a list, compute prefix sums (n+1 values in ZMod n
    which has n elements), apply pigeonhole to find two equal prefix sums,
    and the elements between them form a nonempty zero-sum submultiset. -/
theorem davenport_upper (n : ℕ) (hn : 0 < n) (s : Multiset (ZMod n))
    (hs : Multiset.card s = n) :
    ∃ t ≤ s, t ≠ 0 ∧ t.sum = 0 := by
  haveI : NeZero n := ⟨by omega⟩
  -- Get a list representation
  set l := s.toList with hl_def
  have hperm : (↑l : Multiset (ZMod n)) = s := Multiset.coe_toList s
  have hlen : l.length = n := by
    have h1 := Multiset.length_toList s
    simp only [hl_def] at h1 ⊢
    omega
  -- Define prefix sums: ps(i) = sum of first i elements
  let ps : Fin (n + 1) → ZMod n := fun i => (l.take i.val).sum
  -- Pigeonhole: n+1 prefix sums in ZMod n (which has n elements)
  have hcard : Fintype.card (ZMod n) < Fintype.card (Fin (n + 1)) := by
    rw [ZMod.card n, Fintype.card_fin]; omega
  obtain ⟨a, b, hab, hps⟩ := Fintype.exists_ne_map_eq_of_card_lt ps hcard
  -- Ensure i < j (order the two indices)
  have hne : a.val ≠ b.val := Fin.val_ne_of_ne hab
  obtain ⟨i, j, hij, hilen, hjlen, hpseq⟩ :
      ∃ i j, i < j ∧ i ≤ n ∧ j ≤ n ∧ (l.take i).sum = (l.take j).sum := by
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact ⟨a.val, b.val, h, by omega, by omega, hps⟩
    · exact ⟨b.val, a.val, h, by omega, by omega, hps.symm⟩
  -- The slice l[i..j) is the contiguous sublist
  set slice := (l.drop i).take (j - i) with hslice_def
  -- Key identity: l.take j = l.take i ++ slice
  have htake_eq : l.take j = l.take i ++ slice := by
    simp only [slice]
    have h1 : i ≤ j := Nat.le_of_lt hij
    have h2 : j ≤ l.length := by omega
    rw [show j = i + (j - i) from by omega]
    rw [List.take_add]
    have : i + (j - i) - i = j - i := by omega
    rw [this]
  -- Slice sums to 0
  have hslice_sum : slice.sum = 0 := by
    have happ : (l.take j).sum = (l.take i).sum + slice.sum := by
      rw [htake_eq, List.sum_append]
    -- hpseq: (l.take i).sum = (l.take j).sum
    -- happ:  (l.take j).sum = (l.take i).sum + slice.sum
    -- Substituting: (l.take i).sum + slice.sum = (l.take i).sum
    rw [hpseq] at happ
    -- happ: (l.take i).sum + slice.sum = (l.take i).sum  (after rewriting LHS of happ)
    -- Wait, happ is (l.take j).sum = ..., and we replaced the LHS occurrence
    -- Actually after rw [hpseq], happ becomes about equal things
    -- Let's just use algebra
    -- After rewrite, happ : (l.take i).sum = (l.take i).sum + slice.sum
    -- So slice.sum = 0
    have h : (l.take j).sum + 0 = (l.take j).sum + slice.sum := by
      rw [add_zero]; exact happ
    exact (add_left_cancel h).symm
  -- Slice is nonempty
  have hslice_ne : slice.length ≠ 0 := by
    simp only [slice, List.length_take, List.length_drop, hlen]
    omega
  -- Slice is a sublist of l
  have hslice_sub : List.Sublist slice l := by
    change List.Sublist ((l.drop i).take (j - i)) l
    have h1 := List.take_sublist (j - i) (l.drop i)
    have h2 := List.drop_sublist i l
    exact h1.trans h2
  -- Therefore its multiset is ≤ s
  have hslice_le : (↑slice : Multiset (ZMod n)) ≤ s := by
    rw [← hperm]; exact Multiset.coe_le.mpr hslice_sub.subperm
  -- Assemble
  refine ⟨↑slice, hslice_le, ?_, ?_⟩
  · intro h
    rw [Multiset.coe_eq_zero] at h
    exact hslice_ne (by simp [h])
  · rw [Multiset.sum_coe]; exact hslice_sum

/-! ## The Davenport constant: D(ℤ/nℤ) = n -/

/-- **D(ℤ/nℤ) = n**: the Davenport constant of the cyclic group of order n.

    - **Upper bound** (`davenport_upper`): n elements in ZMod n always
      contain a nonempty zero-sum submultiset.
    - **Lower bound** (`zeroSumFree_replicate_one`): n−1 copies of 1
      in ZMod n have no nonempty zero-sum submultiset.

    For our P ≠ NP program: D(ℤ/nℤ) = n marks the exact threshold
    where modular subset sum transitions from "adversary can avoid
    zero-sum" to "zero-sum is forced." The lower bound witness
    (all 1s) reveals that extremal instances are maximally structured. -/
theorem davenport_ZMod (n : ℕ) (hn : 1 < n) :
    -- Upper bound: n elements suffice
    (∀ (s : Multiset (ZMod n)), s.card = n → ∃ t ≤ s, t ≠ 0 ∧ t.sum = 0) ∧
    -- Lower bound: n−1 elements do not suffice
    (∃ s : Multiset (ZMod n), s.card = n - 1 ∧ ZeroSumFree s) := by
  exact ⟨fun s hs => davenport_upper n (by omega) s hs,
         ⟨Multiset.replicate (n - 1) 1, Multiset.card_replicate _ _,
          zeroSumFree_replicate_one n hn⟩⟩
