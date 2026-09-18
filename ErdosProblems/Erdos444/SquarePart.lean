import Mathlib

/-!
# Square and odd parts

The two definitions and the reconstruction lemma below are an attributed
excerpt of `ErdosProblems.Erdos387.RoughDivisorBound` from
`plby/lean-proofs` commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
Only this elementary interface is needed by the Erdős 444 repeated-prime
argument; importing the complete rough-divisor development would pull in an
unrelated analytic dependency chain.
-/

namespace Erdos387

noncomputable section

def factorizationSquarePart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)

def factorizationOddPart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p % 2)

theorem factorizationSquarePart_sq_mul_oddPart {n : ℕ} (hn : n ≠ 0) :
    factorizationSquarePart n ^ 2 * factorizationOddPart n = n := by
  rw [factorizationSquarePart, factorizationOddPart,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  calc
    ∏ p ∈ n.primeFactors,
        (p ^ (n.factorization p / 2)) ^ 2 *
          p ^ (n.factorization p % 2) =
        ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

end
end Erdos387
