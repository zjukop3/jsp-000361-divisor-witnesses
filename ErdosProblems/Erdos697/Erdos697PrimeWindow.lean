import Mathlib
import ErdosProblems.Erdos697.Erdos697PrimeHarmonic

/-!
# Prime windows for Erdős Problem 697

This is an attributed compatibility excerpt from
`plby/lean-proofs` commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`,
retaining the finite prime-window definitions and the elementary square
reciprocal estimate used by the Erdős 444 proof.  The original file also
contains residue-class estimates for Erdős 697; those declarations are not
part of the dependency interface of this submission and are intentionally
left out so that unrelated analytic imports are not compiled.
-/

open scoped BigOperators

namespace Erdos697.PrimeWindow

noncomputable section

def primes (L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter Nat.Prime

@[simp] theorem mem_primes {L U p : ℕ} :
    p ∈ primes L U ↔ L < p ∧ p ≤ U ∧ p.Prime := by
  simp [primes, and_assoc]

def reciprocalMass (L U : ℕ) : ℝ :=
  ∑ p ∈ primes L U, 1 / (p : ℝ)

theorem reciprocalMass_eq_sub (hLU : L ≤ U) :
    reciprocalMass L U = PrimeHarmonic.sum U - PrimeHarmonic.sum L := by
  classical
  unfold reciprocalMass PrimeHarmonic.sum primes
  have hsplit : Nat.primesLE U = Nat.primesLE L ∪
      (Finset.Ioc L U).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_union, Finset.mem_filter,
      Finset.mem_Ioc]
    constructor
    · intro hp
      by_cases hpL : p ≤ L
      · exact Or.inl ⟨hpL, hp.2⟩
      · exact Or.inr ⟨⟨by omega, hp.1⟩, hp.2⟩
    · rintro (hp | hp)
      · exact ⟨hp.1.trans hLU, hp.2⟩
      · exact ⟨hp.1.2, hp.2⟩
  have hdisj : Disjoint (Nat.primesLE L)
      ((Finset.Ioc L U).filter Nat.Prime) := by
    apply Finset.disjoint_left.mpr
    intro p hpL hpW
    have := (Finset.mem_filter.mp hpW).1
    have hpLE := (Nat.mem_primesLE.mp hpL).1
    simp only [Finset.mem_Ioc] at this
    omega
  rw [hsplit, Finset.sum_union hdisj]
  ring

private theorem sum_Ioc_inv_diff (L U : ℕ) (hL : 1 ≤ L) :
    (∑ n ∈ Finset.Ioc L U,
      (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) ≤ 1 / (L : ℝ) := by
  by_cases hLU : L ≤ U
  · have htel :
        (∑ n ∈ Finset.Ioc L U,
          (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) =
            1 / (L : ℝ) - 1 / (U : ℝ) := by
      induction U, hLU using Nat.le_induction with
      | base => simp
      | succ U hLU ih =>
          rw [Finset.sum_Ioc_succ_top hLU]
          rw [ih]
          have hUne : (U : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hL.trans hLU)))
          have hUsucc : ((U + 1 : ℕ) : ℝ) = U + 1 := by norm_num
          rw [hUsucc]
          ring
    rw [htel]
    exact sub_le_self _ (by positivity)
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp

/-- The density cost of allowing a repeated prime above `L`. -/
theorem squareReciprocalMass_le {L U : ℕ} (hL : 1 ≤ L) :
    (∑ p ∈ primes L U, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      1 / (L : ℝ) := by
  calc
    (∑ p ∈ primes L U, (1 : ℝ) / (p : ℝ) ^ 2) ≤
        ∑ p ∈ primes L U,
          (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpprime := (mem_primes.mp hp).2.2
      have hpR : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
      rw [show 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) =
          1 / ((p : ℝ) * ((p : ℝ) - 1)) by
        field_simp [ne_of_gt (by positivity : (0 : ℝ) < p),
          ne_of_gt (by linarith : (0 : ℝ) < p - 1)]
        ring]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ ≤ ∑ n ∈ Finset.Ioc L U,
        (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro n hnIoc hnnot
      have hn : L < n := (Finset.mem_Ioc.mp hnIoc).1
      have hnreal : (1 : ℝ) < n := by exact_mod_cast hL.trans_lt hn
      have hnne : (n : ℝ) ≠ 0 := by linarith
      have hnsubne : (n : ℝ) - 1 ≠ 0 := by linarith
      rw [show 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) =
          1 / ((n : ℝ) * ((n : ℝ) - 1)) by
            field_simp [hnne, hnsubne]
            ring]
      positivity
    _ ≤ 1 / (L : ℝ) := sum_Ioc_inv_diff L U hL
end

end Erdos697.PrimeWindow
