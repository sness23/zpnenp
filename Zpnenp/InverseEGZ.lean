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

/-! ## Key Lemma: At most 2 distinct values

**Key Lemma**: An EGZ-free multiset of size 2n-2 has at most 2 distinct values.

**Proof sketch**:

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
    argument involving iterated Davenport applications is needed.

    The full proof uses exists_sum_eq to show that for any c ∈ s, the
    complement of the (n-1)-submultiset summing to 0 (after translating by c)
    has n-1 nonzero elements. If this complement has ≥ 2 values, inverse
    Davenport gives a zero-sum of size m ≥ 2. Combined with n-m copies of c
    (need count(c,s) ≥ n-m), this gives an n-element zero-sum.

    When max_count ≥ n-2, we always have n-m ≤ n-2 ≤ max_count since m ≥ 2.

    The remaining open case is when ALL values appear ≤ n-3 times (requires n ≥ 5).
    For n ≤ 4, the pigeonhole principle forces some value to have count ≥ n-2. -/

/-- Given d with count n-1 in an EGZ-free multiset, the remaining elements
    form a constant multiset. This gives exactly 2 values. -/
private theorem two_values_of_count_pred {n : ℕ} (hn : 1 < n) {s : Multiset (ZMod n)}
    (hfree : EGZFree s) (hcard : s.card = 2 * n - 2)
    {d : ZMod n} (hd_count : Multiset.count d s = n - 1) :
    ∃ a b : ZMod n, ∀ x ∈ s, x = a ∨ x = b := by
  haveI : NeZero n := ⟨by omega⟩
  have hd_le : Multiset.replicate (n - 1) d ≤ s :=
    Multiset.le_count_iff_replicate_le.mp (by omega)
  set R := s - Multiset.replicate (n - 1) d with hR_def
  have hR_add : s = Multiset.replicate (n - 1) d + R := by
    rw [hR_def, add_comm]; exact (Multiset.sub_add_cancel hd_le).symm
  have hR_card : R.card = n - 1 := by
    have := congr_arg Multiset.card hR_add
    simp [Multiset.card_add, Multiset.card_replicate] at this; omega
  have hR_no_d : Multiset.count d R = 0 := by
    have h := congr_arg (Multiset.count d) hR_add
    simp [Multiset.count_add, Multiset.count_replicate] at h; omega
  -- R.map (· - d) is zero-sum free
  -- (If not, the zero-sum preimage + copies of d forms n-element zero-sum in s)
  have hR'_zsf : ZeroSumFree (R.map (· - d)) := by
    intro v hv hv_ne hv_sum
    -- v ≤ R.map (·-d), v nonempty, v.sum = 0
    have hv_card_pos : 0 < v.card := by
      rwa [Multiset.card_pos, ← Multiset.empty_eq_zero]
    -- All elements of R.map (·-d) are nonzero (since R has no d's)
    have hno_zero : ∀ x ∈ R.map (· - d), x ≠ (0 : ZMod n) := by
      intro x hx hx0; subst hx0
      rw [Multiset.mem_map] at hx
      obtain ⟨y, hy, hyd⟩ := hx
      have : y = d := by rwa [sub_eq_zero] at hyd
      subst this
      exact absurd (Multiset.count_pos.mpr hy) (by rw [hR_no_d]; omega)
    -- v.card ≥ 2 (single nonzero element can't sum to 0)
    have hv_ge2 : 2 ≤ v.card := by
      by_contra hlt; push_neg at hlt
      have : v.card = 1 := by omega
      obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp this
      simp only [Multiset.sum_singleton] at hv_sum
      exact hno_zero x (Multiset.mem_of_le hv (Multiset.mem_singleton_self x)) hv_sum
    -- Preimage u = v.map (·+d) satisfies u ≤ R
    set u := v.map (· + d)
    have hu_le_R : u ≤ R := by
      -- v ≤ R.map (·-d), so v.map (·+d) ≤ R.map (·-d).map (·+d) = R
      have hinv : (R.map (· - d)).map (· + d) = R := by
        rw [Multiset.map_map]; simp [Function.comp]
      rw [show u = v.map (· + d) from rfl, ← hinv]
      exact Multiset.map_le_map hv
    have hu_card : u.card = v.card := Multiset.card_map _ _
    -- u.sum = v.card • d (since v.sum = 0 and each element shifted by +d)
    have hu_sum : u.sum = v.card • d := by
      suffices hsuff : ∀ (w : Multiset (ZMod n)),
          (w.map (· + d)).sum = w.sum + w.card • d by
        rw [show u = v.map (· + d) from rfl, hsuff, hv_sum, zero_add]
      intro w
      induction w using Multiset.induction with
      | empty => simp
      | cons a t ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, succ_nsmul]
        rw [ih]; ring
    -- Construct n-element zero-sum: u + replicate(n - v.card, d)
    have hle_card : v.card ≤ (R.map (· - d)).card := Multiset.card_le_card hv
    rw [Multiset.card_map, hR_card] at hle_card
    have hcomb_le : u + Multiset.replicate (n - v.card) d ≤ s := by
      rw [hR_add, add_comm u]
      exact add_le_add
        (Multiset.le_count_iff_replicate_le.mp (by simp; omega)) hu_le_R
    have hcomb_card : (u + Multiset.replicate (n - v.card) d).card = n := by
      rw [Multiset.card_add, hu_card, Multiset.card_replicate]; omega
    have hcomb_sum : (u + Multiset.replicate (n - v.card) d).sum = 0 := by
      rw [Multiset.sum_add, hu_sum, multiset_sum_replicate, ← add_nsmul,
          show v.card + (n - v.card) = n from by omega,
          nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    exact hfree _ hcomb_le hcomb_card hcomb_sum
  -- By inverse_davenport: R.map (·-d) = replicate(n-1, h) for unit h
  have hR'_card : (R.map (· - d)).card = n - 1 := by
    rw [Multiset.card_map]; exact hR_card
  obtain ⟨h, _, hR'_eq⟩ := (inverse_davenport n hn _ hR'_card).mp hR'_zsf
  -- R = replicate(n-1, d + h): recover from the shifted form
  have hR_eq : R = Multiset.replicate (n - 1) (d + h) := by
    have hinj : Function.Injective (· - d : ZMod n → ZMod n) := sub_left_injective
    ext x
    rw [← Multiset.count_map_eq_count' _ _ hinj x]
    rw [hR'_eq, Multiset.count_replicate, Multiset.count_replicate]
    split_ifs with h1 h2 h2 <;> [rfl; exfalso; exfalso; rfl]
    · exact h2 (by simp [h1])
    · exact h1 (by rw [← h2]; ring)
  -- Every element of s is d or d + h
  refine ⟨d, d + h, fun x hx => ?_⟩
  rw [hR_add, hR_eq, Multiset.mem_add] at hx
  rcases hx with hx | hx
  · left; exact Multiset.eq_of_mem_replicate hx
  · right; exact Multiset.eq_of_mem_replicate hx

/-- **Structural claim**: In an EGZ-free multiset of size 2n-2, some element
    appears exactly n-1 times.

    For any a ∈ s, applying `exists_sum_eq` gives complement R with no copies
    of a. If R is constant (1 value), that value has count n-1. Otherwise,
    the complement's shift has a zero-sum, leading to contradiction when
    count(a, s) ≥ n-2 (which holds for n ≤ 4 by pigeonhole, and for the
    max-count element when max count ≥ n-2). -/
private theorem exists_count_pred {n : ℕ} (hn : 1 < n) {s : Multiset (ZMod n)}
    (hfree : EGZFree s) (hcard : s.card = 2 * n - 2) :
    ∃ d, Multiset.count d s = n - 1 := by
  haveI : NeZero n := ⟨by omega⟩
  -- Pick element a with maximum count
  have hs_ne : s ≠ 0 := by intro h; simp [h] at hcard; omega
  obtain ⟨a, ha_max⟩ := Finite.exists_max (fun x : ZMod n => Multiset.count x s)
  have ha : a ∈ s := by
    rw [← Multiset.count_pos]; by_contra h; push_neg at h
    have : ∀ x, Multiset.count x s = 0 := fun x => Nat.le_zero.mp ((ha_max x).trans (by omega))
    have : s.card = 0 := by
      rw [Multiset.card_eq_zero]; ext x
      simp [Multiset.count_zero, Nat.le_zero.mp ((ha_max x).trans (by omega))]
    omega
  -- Apply exists_sum_eq to get t ≤ s with |t| = n-1, t.sum = -a
  obtain ⟨t, ht_le, ht_card, ht_sum⟩ := EGZFree.exists_sum_eq hn hfree hcard a
  set R := s - t with hR_def
  have hR_add : s = t + R := by rw [hR_def, add_comm]; exact (Multiset.sub_add_cancel ht_le).symm
  have hR_card : R.card = n - 1 := by
    have := congr_arg Multiset.card hR_add
    simp [Multiset.card_add] at this; omega
  -- All copies of a are in t (otherwise t + {a} is n-element zero-sum)
  have hR_no_a : Multiset.count a R = 0 := by
    by_contra h; push_neg at h
    have ha_in_R : a ∈ R := Multiset.count_pos.mp (by omega)
    exact hfree (t + {a})
      (by rw [hR_add]; exact Multiset.add_le_add_left (Multiset.singleton_le.mpr ha_in_R))
      (by simp [ht_card]; omega)
      (by simp [Multiset.sum_add, ht_sum, add_comm])
  -- Case 1: R has exactly 1 distinct value → that value has count n-1
  by_cases hR_const : ∃ d, ∀ x ∈ R, x = d
  · obtain ⟨d, hd_all⟩ := hR_const
    refine ⟨d, ?_⟩
    have hR_eq : R = Multiset.replicate (n - 1) d := by
      ext x
      by_cases hxd : d = x
      · subst hxd
        rw [Multiset.count_replicate_self]
        exact (Multiset.count_eq_card.mpr (fun y hy => (hd_all y hy).symm)).symm ▸ hR_card
      · rw [Multiset.count_replicate, if_neg hxd]
        exact Multiset.count_eq_zero.mpr (fun hx => hxd (hd_all x hx).symm)
    have hd_in_R : Multiset.count d R = n - 1 := by rw [hR_eq, Multiset.count_replicate_self]
    have hcount := congr_arg (Multiset.count d) hR_add
    simp [Multiset.count_add] at hcount
    have := EGZFree.count_le hn hfree d
    omega
  · -- Case 2: R has ≥ 2 distinct values
    push_neg at hR_const
    -- R.map (· - a) has n-1 elements with ≥ 2 nonzero values
    -- By all_eq contrapositive: NOT zero-sum free
    -- So ∃ nonempty zero-sum submultiset of size m ≥ 2
    -- Combined with copies of a → n-element zero-sum → contradiction with EGZ-free
    -- This works when count(a, s) ≥ n - 2
    -- For n ≤ 4: pigeonhole forces max count ≥ n - 2, so this always works
    -- For n ≥ 5: not guaranteed (requires deeper argument)
    -- First show R.map (·-a) is not zero-sum free
    have hR'_card : (R.map (· - a)).card = n - 1 := by rw [Multiset.card_map]; exact hR_card
    have hR'_not_zsf : ¬ZeroSumFree (R.map (· - a)) := by
      intro hzsf
      have hR_ne : R ≠ 0 := by intro h; simp [h] at hR_card; omega
      obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hR_ne
      have hall : ∀ x ∈ R, x = r := fun x hx =>
        sub_left_injective (ZeroSumFree.all_eq hn hzsf hR'_card
          (Multiset.mem_map_of_mem (· - a) hx) (Multiset.mem_map_of_mem (· - a) hr))
      obtain ⟨x, hx_mem, hx_ne⟩ := hR_const r
      exact hx_ne (hall x hx_mem)
    -- Extract the zero-sum: ¬ZeroSumFree means ∃ nonempty sub with sum = 0
    have ⟨v, hv_le, hv_ne, hv_sum⟩ : ∃ v ≤ R.map (· - a), v ≠ 0 ∧ v.sum = 0 := by
      by_contra hall; push_neg at hall
      exact hR'_not_zsf (fun v hv hne => hall v hv hne)
    -- All elements of R.map (·-a) are nonzero (R has no a's)
    have hno_zero : ∀ x ∈ R.map (· - a), x ≠ (0 : ZMod n) := by
      intro x hx hx0; subst hx0
      rw [Multiset.mem_map] at hx
      obtain ⟨y, hy, hyd⟩ := hx
      have : y = a := by rwa [sub_eq_zero] at hyd
      subst this
      exact absurd (Multiset.count_pos.mpr hy) (by rw [hR_no_a]; omega)
    -- v.card ≥ 2 (no zeros, so single element can't sum to 0)
    have hv_card_pos : 0 < v.card := by rwa [Multiset.card_pos, ← Multiset.empty_eq_zero]
    have hv_card_pos : 0 < v.card := by
      rw [Multiset.card_pos]; rwa [← Multiset.empty_eq_zero]
    have hv_ge2 : 2 ≤ v.card := by
      by_contra hlt; push_neg at hlt
      have hv1 : v.card = 1 := by omega
      obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hv1
      simp only [Multiset.sum_singleton] at hv_sum
      exact hno_zero x (Multiset.mem_of_le hv_le (Multiset.mem_singleton_self x)) hv_sum
    -- Preimage u = v.map (·+a) ≤ R with u.sum = v.card • a
    set u := v.map (· + a)
    have hu_le_R : u ≤ R := by
      have hinv : (R.map (· - a)).map (· + a) = R := by
        rw [Multiset.map_map]; simp [Function.comp]
      rw [show u = v.map (· + a) from rfl, ← hinv]
      exact Multiset.map_le_map hv_le
    have hu_card : u.card = v.card := Multiset.card_map _ _
    have hu_sum : u.sum = v.card • a := by
      suffices hsuff : ∀ (w : Multiset (ZMod n)),
          (w.map (· + a)).sum = w.sum + w.card • a by
        rw [show u = v.map (· + a) from rfl, hsuff, hv_sum, zero_add]
      intro w; induction w using Multiset.induction with
      | empty => simp
      | cons x t ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, succ_nsmul]
        rw [ih]; ring
    have hle_card : v.card ≤ n - 1 := by
      have := Multiset.card_le_card hv_le; rw [hR'_card] at this; exact this
    -- Need count(a, s) ≥ n - v.card to build the n-element zero-sum
    -- count(a, s) = count(a, t) + count(a, R) = count(a, t) + 0 = count(a, t) ≤ n-1
    have ha_count : Multiset.count a s ≤ n - 1 := EGZFree.count_le hn hfree a
    -- If count(a, s) ≥ n - v.card: build zero-sum → contradiction
    by_cases hcount_big : n - v.card ≤ Multiset.count a s
    · exfalso
      have ha_in_t : Multiset.count a s = Multiset.count a t := by
        have := congr_arg (Multiset.count a) hR_add
        simp [Multiset.count_add, hR_no_a] at this; omega
      have hcomb_le : u + Multiset.replicate (n - v.card) a ≤ s := by
        rw [hR_add, add_comm u]
        exact add_le_add
          (Multiset.le_count_iff_replicate_le.mp (by simp; omega)) hu_le_R
      have hcomb_card : (u + Multiset.replicate (n - v.card) a).card = n := by
        rw [Multiset.card_add, hu_card, Multiset.card_replicate]; omega
      have hcomb_sum : (u + Multiset.replicate (n - v.card) a).sum = 0 := by
        rw [Multiset.sum_add, hu_sum, multiset_sum_replicate, ← add_nsmul,
            show v.card + (n - v.card) = n from by omega,
            nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      exact hfree _ hcomb_le hcomb_card hcomb_sum
    · -- count(a, s) < n - v.card, i.e., count(a, s) ≤ n - 3 (since v.card ≥ 2)
      push_neg at hcount_big
      have ha_small : Multiset.count a s ≤ n - 3 := by omega
      -- Since a has max count, ALL elements have count ≤ n - 3
      have hall_small : ∀ x, Multiset.count x s ≤ n - 3 :=
        fun x => (ha_max x).trans ha_small
      -- For n ≤ 4: derive contradiction (max count ≤ n-3 ≤ 1 is too small)
      -- For n ≥ 5: deep remaining case
      have ha_pos : 0 < Multiset.count a s := Multiset.count_pos.mpr ha
      -- n ≤ 3: n - 3 = 0, so count a s = 0, but a ∈ s gives count > 0
      -- n = 4: count ≤ 1 for all elements. s has ≤ 4 distinct values (ZMod 4),
      --        each appearing ≤ 1 time, so s.card ≤ 4 < 6 = 2n-2.
      -- n ≥ 5: sorry
      by_cases hn4 : n ≤ 4
      · exfalso
        by_cases hn3 : n ≤ 3
        · -- n ≤ 3: n - 3 = 0, count a s ≤ 0, contradicts a ∈ s
          omega
        · -- n = 4: all counts ≤ 1, so s ≤ univ.val, card ≤ 4 < 6
          push_neg at hn3
          have hn_eq : n = 4 := by omega
          subst hn_eq
          have hle_univ : s ≤ (Finset.univ : Finset (ZMod 4)).val := by
            rw [Multiset.le_iff_count]; intro x
            have hx_count := hall_small x -- count x s ≤ 1
            have hx_in : x ∈ (Finset.univ : Finset (ZMod 4)).val :=
              Finset.mem_univ x
            have hx_pos := Multiset.count_pos.mpr hx_in
            omega
          have := Multiset.card_le_card hle_univ
          simp [Finset.card_univ, ZMod.card] at this
          omega
      · -- n ≥ 5: the deep structural subcase
        push_neg at hn4
        sorry

theorem EGZFree.at_most_two_values {n : ℕ} (hn : 1 < n) {s : Multiset (ZMod n)}
    (hfree : EGZFree s) (hcard : s.card = 2 * n - 2) :
    ∃ a b : ZMod n, ∀ x ∈ s, x = a ∨ x = b := by
  obtain ⟨d, hd⟩ := exists_count_pred hn hfree hcard
  exact two_values_of_count_pred hn hfree hcard hd

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
