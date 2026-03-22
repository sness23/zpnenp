/-
  SubsetSum.lean — Core definitions of the Subset Sum problem

  We define Subset Sum in two forms:
  1. Mathematical (Finset-based): natural for proving structural theorems
  2. Decision problem (List-based): natural for complexity-theoretic statements
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/-! ## Mathematical Definition -/

/-- A Finset of integers has a subset summing to target `t`. -/
def SubsetSum (s : Finset ℤ) (t : ℤ) : Prop :=
  ∃ s' ∈ s.powerset, s'.sum id = t

/-- The zero-sum variant: does `s` have a nonempty subset summing to 0? -/
def SubsetSumZero (s : Finset ℤ) : Prop :=
  ∃ s' ∈ s.powerset, s' ≠ ∅ ∧ s'.sum id = 0

/-! ## Basic Properties -/

/-- The empty subset sums to 0, so SubsetSum s 0 is always true. -/
theorem subsetSum_zero (s : Finset ℤ) : SubsetSum s 0 := by
  exact ⟨∅, mem_powerset.mpr (empty_subset s), sum_empty⟩

/-- SubsetSum is monotone: if s ⊆ t, then any sum achievable from s
    is achievable from t. -/
theorem subsetSum_mono {s t : Finset ℤ} (h : s ⊆ t) {target : ℤ}
    (hs : SubsetSum s target) : SubsetSum t target := by
  obtain ⟨s', hs'mem, hs'sum⟩ := hs
  exact ⟨s', mem_powerset.mpr ((mem_powerset.mp hs'mem).trans h), hs'sum⟩

/-- For a singleton {a}, SubsetSum {a} t iff t = 0 or t = a. -/
theorem subsetSum_singleton (a : ℤ) :
    ∀ t, SubsetSum ({a} : Finset ℤ) t ↔ t = 0 ∨ t = a := by
  intro t
  constructor
  · rintro ⟨s', hs'mem, hs'sum⟩
    have hs'sub := mem_powerset.mp hs'mem
    rw [subset_singleton_iff] at hs'sub
    rcases hs'sub with rfl | rfl
    · left; simpa using hs'sum.symm
    · right; simpa using hs'sum.symm
  · intro h
    rcases h with rfl | ht
    · exact subsetSum_zero _
    · rw [ht]
      exact ⟨{a}, mem_powerset.mpr (Subset.refl _), by simp⟩

/-! ## The set of all achievable subset sums -/

/-- The set of all values achievable as subset sums of `s`. -/
def subsetSums (s : Finset ℤ) : Finset ℤ :=
  s.powerset.image (fun s' => s'.sum id)

theorem mem_subsetSums {s : Finset ℤ} {t : ℤ} :
    t ∈ subsetSums s ↔ SubsetSum s t := by
  simp [subsetSums, SubsetSum, mem_image]

/-- Subset sums are monotone: larger sets have more achievable sums. -/
theorem subsetSums_mono {s t : Finset ℤ} (h : s ⊆ t) :
    subsetSums s ⊆ subsetSums t := by
  intro x hx
  rw [mem_subsetSums] at hx ⊢
  exact subsetSum_mono h hx

/-- 0 is always an achievable subset sum (the empty subset). -/
theorem zero_mem_subsetSums (s : Finset ℤ) : (0 : ℤ) ∈ subsetSums s := by
  rw [mem_subsetSums]; exact subsetSum_zero s

/-- Each element is an achievable subset sum (the singleton subset). -/
theorem mem_subsetSums_of_mem {s : Finset ℤ} {a : ℤ} (ha : a ∈ s) :
    a ∈ subsetSums s := by
  rw [mem_subsetSums]
  exact ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha), by simp⟩

/-- The empty set has exactly one achievable sum: 0. -/
theorem subsetSums_empty : subsetSums (∅ : Finset ℤ) = {0} := by
  ext x; simp [subsetSums, SubsetSum, mem_image, mem_powerset]

/-- SubsetSum is decidable for any finite set and target. -/
instance SubsetSum.decidable (s : Finset ℤ) (t : ℤ) : Decidable (SubsetSum s t) := by
  rw [show SubsetSum s t ↔ t ∈ subsetSums s from mem_subsetSums.symm]
  exact inferInstance

/-- SubsetSumZero relates to SubsetSum with target 0, but requires nonempty witness. -/
theorem subsetSumZero_iff (s : Finset ℤ) :
    SubsetSumZero s ↔ ∃ s' ∈ s.powerset, s' ≠ ∅ ∧ s'.sum id = 0 := by
  rfl

/-- The total sum of all elements is an achievable subset sum. -/
theorem sum_mem_subsetSums (s : Finset ℤ) : s.sum id ∈ subsetSums s := by
  rw [mem_subsetSums]
  exact ⟨s, mem_powerset.mpr (Subset.refl s), rfl⟩
