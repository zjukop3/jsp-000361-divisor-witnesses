import Mathlib

/-!
# Elementary symmetric list mass

This is an attributed excerpt of the finite combinatorial interface in
`ErdosProblems.Erdos851.BetaSieveFailureCombinatorics` from
`plby/lean-proofs` commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
The recursive sieve declarations surrounding it are not needed by the
Erdős 444 union bound.
-/

namespace Erdos851.BetaSieveFundamental

noncomputable section

def sublistsLenMass {α : Type*} (x : α → ℝ) (l : List α) (r : ℕ) : ℝ :=
  ((l.sublistsLen r).map fun s => (s.map x).prod).sum

@[simp]
theorem sublistsLenMass_zero {α : Type*} (x : α → ℝ) (l : List α) :
    sublistsLenMass x l 0 = 1 := by
  simp [sublistsLenMass]

theorem sublistsLenMass_succ_cons {α : Type*} (x : α → ℝ)
    (a : α) (l : List α) (r : ℕ) :
    sublistsLenMass x (a :: l) (r + 1) =
      sublistsLenMass x l (r + 1) + x a * sublistsLenMass x l r := by
  simp only [sublistsLenMass, List.sublistsLen_succ_cons, List.map_append,
    List.sum_append, List.map_map]
  congr 1
  change
    (List.map (fun s => x a * (s.map x).prod) (l.sublistsLen r)).sum = _
  exact List.sum_map_mul_left (l.sublistsLen r)
    (fun s => (s.map x).prod) (x a)

theorem factorial_mul_sublistsLenMass_le_sum_pow {α : Type*}
    (x : α → ℝ) (hx : ∀ a, 0 ≤ x a) :
    ∀ (l : List α) (r : ℕ),
      (r.factorial : ℝ) * sublistsLenMass x l r ≤
        (l.map x).sum ^ r := by
  intro l
  induction l with
  | nil =>
      intro r
      cases r <;> simp [sublistsLenMass]
  | cons a l ih =>
      intro r
      cases r with
      | zero => simp
      | succ r =>
          have hsum0 : 0 ≤ (l.map x).sum :=
            List.sum_nonneg fun y hy => by
              obtain ⟨b, _hb, rfl⟩ := List.mem_map.mp hy
              exact hx b
          have hmain := ih (r + 1)
          have hprev := ih r
          have hfac : (((r + 1).factorial : ℕ) : ℝ) =
              ((r + 1 : ℕ) : ℝ) * (r.factorial : ℝ) := by
            rw [Nat.factorial_succ]
            norm_num
          rw [sublistsLenMass_succ_cons]
          calc
            ((r + 1).factorial : ℝ) *
                (sublistsLenMass x l (r + 1) +
                  x a * sublistsLenMass x l r) =
                ((r + 1).factorial : ℝ) * sublistsLenMass x l (r + 1) +
                  ((r + 1 : ℕ) : ℝ) * x a *
                    ((r.factorial : ℝ) * sublistsLenMass x l r) := by
              rw [hfac]
              ring
            _ ≤ (l.map x).sum ^ (r + 1) +
                ((r + 1 : ℕ) : ℝ) * x a * (l.map x).sum ^ r := by
              exact add_le_add hmain (mul_le_mul_of_nonneg_left hprev
                (mul_nonneg (Nat.cast_nonneg _) (hx a)))
            _ ≤ ((l.map x).sum + x a) ^ (r + 1) := by
              simpa [Nat.cast_add, Nat.cast_one, mul_assoc, mul_comm,
                mul_left_comm] using
                (pow_add_mul_le_add_pow (R := ℝ) hsum0
                  (add_nonneg (mul_nonneg (by norm_num) hsum0) (hx a))
                  (r + 1))
            _ = ((a :: l).map x).sum ^ (r + 1) := by
              simp [add_comm]

end
end Erdos851.BetaSieveFundamental
