/-
  Inverse.lean — Inverse zero-sum theorems

  The inverse Davenport theorem characterizes ALL maximal zero-sum free
  sequences in ℤ/nℤ: they are (n-1) copies of a single unit element.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Zpnenp.Davenport

open Multiset

/-! ## Forward direction: replicate of any unit is zero-sum free -/

/-- Replicate (n-1) copies of a unit g in ZMod n is zero-sum free. -/
theorem zeroSumFree_replicate_unit (n : ℕ) (hn : 1 < n) (g : ZMod n)
    (hg : IsUnit g) :
    ZeroSumFree (Multiset.replicate (n - 1) g) := by
  intro t ht hne hsum
  have hmem : ∀ x ∈ t, x = g :=
    fun x hx => Multiset.eq_of_mem_replicate (Multiset.subset_of_le ht hx)
  have hcard_pos : 0 < t.card := by rw [Multiset.card_pos]; exact hne
  have hcard_le : t.card ≤ n - 1 :=
    (Multiset.card_le_card ht).trans (Multiset.card_replicate _ _).le
  have ht_eq : t = Multiset.replicate t.card g := by
    ext x; simp only [Multiset.count_replicate]; split
    · next h => subst h; exact Multiset.count_eq_card.mpr (fun y hy => (hmem y hy).symm)
    · next h => exact Multiset.count_eq_zero.mpr (fun hx => h (hmem x hx).symm)
  rw [ht_eq, multiset_sum_replicate] at hsum
  obtain ⟨u, hu⟩ := hg
  have : (t.card : ZMod n) = 0 := by
    rw [nsmul_eq_mul, ← hu] at hsum
    have := congr_arg (· * (↑u⁻¹ : ZMod n)) hsum
    simp only [zero_mul, mul_assoc] at this
    rw [Units.mul_inv, mul_one] at this; exact this
  have hdvd : n ∣ t.card := by rwa [ZMod.natCast_eq_zero_iff] at this
  exact absurd (Nat.le_of_dvd hcard_pos hdvd) (by omega)

/-! ## Prefix sums are injective -/

/-- Prefix sums of a zero-sum free list are all distinct. -/
theorem ZeroSumFree.prefix_sums_injective {n : ℕ} (hn : 0 < n)
    {l : List (ZMod n)} (hzsf : ZeroSumFree (↑l : Multiset (ZMod n)))
    {i j : ℕ} (hi : i ≤ l.length) (hj : j ≤ l.length) (hij : i ≠ j)
    : (l.take i).sum ≠ (l.take j).sum := by
  intro heq
  wlog h : i < j with H
  · push_neg at h
    exact H hn hzsf hj hi hij.symm heq.symm (lt_of_le_of_ne h (Ne.symm hij))
  set slice := (l.drop i).take (j - i)
  have htake_eq : l.take j = l.take i ++ slice := by
    simp only [slice]
    rw [show j = i + (j - i) from by omega, List.take_add]
    have : i + (j - i) - i = j - i := by omega
    rw [this]
  have hslice_sum : slice.sum = 0 := by
    have happ : (l.take j).sum = (l.take i).sum + slice.sum := by
      rw [htake_eq, List.sum_append]
    rw [heq] at happ
    have hh : (l.take j).sum + 0 = (l.take j).sum + slice.sum := by
      rw [add_zero]; exact happ
    exact (add_left_cancel hh).symm
  have hslice_ne : slice ≠ [] := by
    intro hh
    have : slice.length = 0 := by simp [hh]
    simp only [slice, List.length_take, List.length_drop] at this; omega
  have hslice_sub : List.Sublist slice l := by
    change List.Sublist ((l.drop i).take (j - i)) l
    exact (List.take_sublist _ _).trans (List.drop_sublist _ _)
  exact hzsf (↑slice) (Multiset.coe_le.mpr hslice_sub.subperm)
    (by rwa [Ne, Multiset.coe_eq_zero])
    (by rw [Multiset.sum_coe]; exact hslice_sum)

/-- Prefix sums of a maximal zero-sum free list are a permutation of ℤ/nℤ. -/
theorem ZeroSumFree.prefix_sums_surjective {n : ℕ} (hn : 1 < n)
    {l : List (ZMod n)} (hzsf : ZeroSumFree (↑l : Multiset (ZMod n)))
    (hlen : l.length = n - 1) :
    ∀ x : ZMod n, ∃ i : Fin n, (l.take i.val).sum = x := by
  haveI : NeZero n := ⟨by omega⟩
  have hinj : Function.Injective (fun i : Fin n => (l.take i.val).sum) := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    simp only at heq
    by_contra hij
    have hne : i ≠ j := fun h => hij (Fin.ext h)
    exact ZeroSumFree.prefix_sums_injective (by omega) hzsf
      (by omega) (by omega) hne heq
  have hbij := (Fintype.bijective_iff_injective_and_card
    (fun i : Fin n => (l.take i.val).sum)).mpr
    ⟨hinj, by rw [Fintype.card_fin, ZMod.card]⟩
  intro x; exact hbij.surjective x

/-! ## Elements of zero-sum free sequences -/

/-- In a zero-sum free multiset, every element is nonzero. -/
theorem ZeroSumFree.ne_zero {n : ℕ} {s : Multiset (ZMod n)}
    (hzsf : ZeroSumFree s) {a : ZMod n} (ha : a ∈ s) : a ≠ 0 := by
  intro h; subst h
  exact hzsf {0} (Multiset.singleton_le.mpr ha) (by simp) (by simp)

/-- Two injective functions from Fin n into an n-element type that agree
    on all inputs except possibly one must agree everywhere. -/
private theorem injective_agree_of_agree_except {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {f g : Fin n → α}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hcard : Fintype.card α = n)
    {k : Fin n} (h : ∀ i, i ≠ k → f i = g i) : f k = g k := by
  by_contra hne
  have hf_bij := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hf, by rw [Fintype.card_fin, hcard]⟩
  obtain ⟨j, hj⟩ := hf_bij.surjective (g k)
  have hjk : j ≠ k := by intro h'; subst h'; exact hne hj
  have hfg : f j = g j := h j hjk
  -- g k = f j = g j, so k = j by injectivity, contradiction
  have : g k = g j := by rw [← hfg, ← hj]
  exact hjk.symm (hg this)

theorem ZeroSumFree.all_eq {n : ℕ} (hn : 1 < n) {s : Multiset (ZMod n)}
    (hzsf : ZeroSumFree s) (hcard : s.card = n - 1)
    {a b : ZMod n} (ha : a ∈ s) (hb : b ∈ s) : a = b := by
  haveI : NeZero n := ⟨by omega⟩
  by_contra hab; push_neg at hab
  -- Extract a and b from s, build two list orderings
  have hb' : b ∈ s.erase a := by
    rw [Multiset.mem_erase_of_ne (Ne.symm hab)]; exact hb
  -- s = a ::ₘ b ::ₘ rest
  have hs1 : s = a ::ₘ (s.erase a) := (Multiset.cons_erase ha).symm
  have hs2 : s.erase a = b ::ₘ ((s.erase a).erase b) := (Multiset.cons_erase hb').symm
  set rest := (s.erase a).erase b
  set rl := rest.toList
  have hrl : (↑rl : Multiset _) = rest := Multiset.coe_toList rest
  -- l₁ = [a, b, ...rest], l₂ = [b, a, ...rest]
  set l₁ : List (ZMod n) := a :: b :: rl
  set l₂ : List (ZMod n) := b :: a :: rl
  -- ↑l₁ = a ::ₘ b ::ₘ rest = s
  have hcoe : ∀ (x y : ZMod n), (↑(x :: y :: rl) : Multiset _) = x ::ₘ y ::ₘ rest := by
    intro x y; change x ::ₘ y ::ₘ (↑rl : Multiset _) = x ::ₘ y ::ₘ rest; rw [hrl]
  have hl₁ : (↑l₁ : Multiset _) = s := by rw [hcoe, hs1, hs2]
  have hl₂ : (↑l₂ : Multiset _) = s := by
    rw [hcoe]; rw [Multiset.cons_swap]; rw [hs1, hs2]
  -- Prefix sum functions
  let ps₁ : Fin n → ZMod n := fun i => (l₁.take i.val).sum
  let ps₂ : Fin n → ZMod n := fun i => (l₂.take i.val).sum
  -- Length facts
  have hlen₁ : l₁.length = n - 1 := by
    have h := congrArg Multiset.card hl₁; simp at h; omega
  have hlen₂ : l₂.length = n - 1 := by
    have h := congrArg Multiset.card hl₂; simp at h; omega
  -- Both are injective
  have hinj₁ : Function.Injective ps₁ := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    by_contra hij; push_neg at hij
    have hi' : i ≤ l₁.length := by omega
    have hj' : j ≤ l₁.length := by omega
    exact prefix_sums_injective (by omega) (hl₁ ▸ hzsf) hi' hj'
      (fun h => hij (Fin.ext h)) heq
  have hinj₂ : Function.Injective ps₂ := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    by_contra hij; push_neg at hij
    have hi' : i ≤ l₂.length := by omega
    have hj' : j ≤ l₂.length := by omega
    exact prefix_sums_injective (by omega) (hl₂ ▸ hzsf) hi' hj'
      (fun h => hij (Fin.ext h)) heq
  -- ps₁ and ps₂ agree at all positions except 1
  -- At position 0: both are 0
  -- At position 1: ps₁ = a, ps₂ = b
  -- At position k ≥ 2: both are a + b + (sum of first k-2 of rl)
  have hps_agree : ∀ i : Fin n, i ≠ ⟨1, by omega⟩ → ps₁ i = ps₂ i := by
    intro ⟨i, hi⟩ hne
    simp only [ps₁, ps₂, l₁, l₂]
    rcases i with _ | i
    · -- i = 0
      simp
    · rcases i with _ | i
      · -- i = 1, excluded
        exfalso; exact hne rfl
      · -- i ≥ 2
        simp only [List.take_succ_cons, List.sum_cons]
        -- Both: a + (b + (rl.take i).sum) vs b + (a + (rl.take i).sum)
        rw [add_left_comm]
  -- Apply the general lemma
  have h1 := injective_agree_of_agree_except hinj₁ hinj₂ (by rw [ZMod.card]) hps_agree
  -- h1 : ps₁ ⟨1, _⟩ = ps₂ ⟨1, _⟩, i.e., a = b
  simp only [ps₁, ps₂, l₁, l₂, List.take_succ_cons, List.take_zero,
    List.sum_cons, List.sum_nil, add_zero] at h1
  exact hab h1

/-- If (n-1) copies of g are zero-sum free, then g is a unit. -/
theorem isUnit_of_replicate_zeroSumFree {n : ℕ} (hn : 1 < n) {g : ZMod n}
    (hzsf : ZeroSumFree (Multiset.replicate (n - 1) g)) : IsUnit g := by
  haveI : NeZero n := ⟨by omega⟩
  have hg_ne : g ≠ 0 := by
    apply ZeroSumFree.ne_zero hzsf
    exact Multiset.mem_replicate.mpr ⟨by omega, rfl⟩
  set l := List.replicate (n - 1) g
  have hlen : l.length = n - 1 := by simp [l]
  have hcoe : (↑l : Multiset (ZMod n)) = Multiset.replicate (n - 1) g := by
    simp [l, Multiset.coe_replicate]
  -- Prefix sums hit every element, in particular 1
  obtain ⟨⟨k, hk⟩, hkg⟩ := ZeroSumFree.prefix_sums_surjective hn (hcoe ▸ hzsf) hlen 1
  -- (l.take k).sum = k • g since all elements are g
  have hk_le : k ≤ n - 1 := by omega
  have htake_sum : (l.take k).sum = k • g := by
    have : l.take k = List.replicate k g := by
      simp [l, List.take_replicate, Nat.min_eq_left hk_le]
    rw [this, List.sum_replicate]
  rw [htake_sum, nsmul_eq_mul] at hkg
  -- (k : ZMod n) * g = 1, so g is a unit
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hkg)

/-! ## Inverse Davenport Theorem -/

/-- **Inverse Davenport Theorem for ℤ/nℤ.**

    A multiset s of length n-1 in ℤ/nℤ (n > 1) is zero-sum free iff
    s = replicate (n-1) g for some unit g. -/
theorem inverse_davenport (n : ℕ) (hn : 1 < n) (s : Multiset (ZMod n))
    (hcard : s.card = n - 1) :
    ZeroSumFree s ↔ ∃ g : ZMod n, IsUnit g ∧ s = Multiset.replicate (n - 1) g := by
  constructor
  · intro hzsf
    -- All elements are equal (sorry: adjacent swap argument)
    have hne : s ≠ 0 := by intro h; simp [h] at hcard; omega
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
    have hall : ∀ x ∈ s, x = a := fun x hx => ZeroSumFree.all_eq hn hzsf hcard hx ha
    set g := a
    -- s = replicate (n-1) g
    have hs_eq : s = Multiset.replicate (n - 1) g := by
      ext x
      simp only [Multiset.count_replicate]
      by_cases hx : g = x
      · subst hx; simp
        have := Multiset.count_eq_card.mpr (fun y hy => (hall y hy).symm)
        omega
      · simp [hx]
        intro hxm; exact hx (hall x hxm).symm
    -- g is a unit (from prefix sums being a permutation)
    exact ⟨g, isUnit_of_replicate_zeroSumFree hn (hs_eq ▸ hzsf), hs_eq⟩
  · rintro ⟨g, hg, rfl⟩
    exact zeroSumFree_replicate_unit n hn g hg

/-! ## Corollaries of the Inverse Davenport Theorem -/

/-- A zero-sum free multiset of size n-1 has all elements equal. -/
theorem ZeroSumFree.eq_replicate {n : ℕ} (hn : 1 < n) {s : Multiset (ZMod n)}
    (hzsf : ZeroSumFree s) (hcard : s.card = n - 1) :
    ∃ g : ZMod n, s = Multiset.replicate (n - 1) g :=
  let ⟨g, _, hg⟩ := (inverse_davenport n hn s hcard).mp hzsf
  ⟨g, hg⟩

/-- The common element of a maximal zero-sum free multiset is a unit. -/
theorem ZeroSumFree.common_element_isUnit {n : ℕ} (hn : 1 < n) {s : Multiset (ZMod n)}
    (hzsf : ZeroSumFree s) (hcard : s.card = n - 1) :
    ∃ g : ZMod n, IsUnit g ∧ s = Multiset.replicate (n - 1) g :=
  (inverse_davenport n hn s hcard).mp hzsf

/-- A multiset of size n-1 with ≥ 2 distinct values is NOT zero-sum free.
    Contrapositive of the inverse Davenport theorem. -/
theorem not_zeroSumFree_of_two_values {n : ℕ} (hn : 1 < n) {s : Multiset (ZMod n)}
    (hcard : s.card = n - 1) {a b : ZMod n} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ¬ZeroSumFree s :=
  fun hzsf => hab (ZeroSumFree.all_eq hn hzsf hcard ha hb)
