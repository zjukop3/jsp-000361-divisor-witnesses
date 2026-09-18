import ErdosProblems.Erdos444

open Filter
open scoped Topology

namespace DivisorWitnesses

noncomputable section

/-- The number of positive members of A dividing the argument. -/
abbrev count := Erdos444.divisorCount

/-- The literal half-open reciprocal sum from the original problem. -/
abbrev mass := Erdos444.reciprocalMassNat

/-- The original cutoff theorem also holds with 1 + reciprocal mass, so no
small or vanishing denominator is responsible for the large ratios. -/
theorem normalized_large_cutoff (A : Set ℕ) (hA : A.Infinite) (k : ℕ)
    (C : ℝ) (hC : 0 ≤ C) (N : ℕ) :
    ∃ X : ℕ, N ≤ X ∧
      C * (1 + mass A X) ^ k < (Erdos444.maxDivisorCountNat A X : ℝ) := by
  obtain ⟨a, haA, ha⟩ := hA.exists_gt 0
  let b := mass A (a + 1)
  have hb : 0 < b := Erdos444.reciprocalMassNat_pos_of_mem haA ha (by omega)
  let c := (1 + b) / b
  have hc : 0 < c := div_pos (by linarith) hb
  have hcb : c * b = 1 + b := div_mul_cancel₀ _ hb.ne'
  have hc1 : 1 ≤ c := by nlinarith
  obtain ⟨X, hXN, hX⟩ :=
    Erdos444.tailUnbounded_ratioNat_of_infinite A hA k (C * c ^ k) (max N (a + 1))
  have haX : a + 1 ≤ X := (le_max_right _ _).trans hXN
  have hbX : b ≤ mass A X := Erdos444.reciprocalMassNat_mono A haX
  have hmass : 0 < mass A X := hb.trans_le hbX
  have hscale : 1 + mass A X ≤ c * mass A X := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hbX)]
  have hpow : (1 + mass A X) ^ k ≤ c ^ k * mass A X ^ k := by
    simpa [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 + mass A X) hscale k
  have hlarge : C * c ^ k * mass A X ^ k < (Erdos444.maxDivisorCountNat A X : ℝ) := by
    exact (lt_div_iff₀ (pow_pos hmass k)).1 hX
  refine ⟨X, (le_max_left _ _).trans hXN, ?_⟩
  calc
    C * (1 + mass A X) ^ k ≤ C * (c ^ k * mass A X ^ k) :=
      mul_le_mul_of_nonneg_left hpow hC
    _ = C * c ^ k * mass A X ^ k := by ring
    _ < _ := hlarge

/-- The large value occurs at an arbitrarily large integer itself, using
its own reciprocal prefix, rather than merely a maximum below a cutoff. -/
theorem pointwise_large_value (A : Set ℕ) (hA : A.Infinite) (k : ℕ)
    (C : ℝ) (hC : 0 ≤ C) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ C * (1 + mass A n) ^ k < (count A n : ℝ) := by
  classical
  let B : ℝ := max C ((Erdos444.maxDivisorCountNat A (N + 1) : ℝ) + 1)
  have hB : 0 ≤ B := hC.trans (le_max_left _ _)
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  obtain ⟨X, _, hlarge⟩ := normalized_large_cutoff A hA k B hB 1
  have hmass : 1 ≤ 1 + mass A X := by
    linarith [Erdos444.reciprocalMassNat_nonneg A X]
  have hp : 1 ≤ (1 + mass A X) ^ k := one_le_pow₀ hmass
  have hmax : B < (Erdos444.maxDivisorCountNat A X : ℝ) := by
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hp)]
  have hX : 1 < X := by
    by_contra h
    have he : Erdos444.positiveBelowNat X = ∅ := by
      simp [Erdos444.positiveBelowNat, Finset.Ico_eq_empty_of_le (by omega : X ≤ 1)]
    have hz : Erdos444.maxDivisorCountNat A X = 0 := by
      simp [Erdos444.maxDivisorCountNat, he]
    rw [hz, Nat.cast_zero] at hmax
    linarith
  have hnonempty : (Erdos444.positiveBelowNat X).Nonempty :=
    ⟨1, Erdos444.mem_positiveBelowNat_iff.mpr ⟨le_rfl, hX⟩⟩
  obtain ⟨n, hn, hcount⟩ := Finset.exists_mem_eq_sup
    (Erdos444.positiveBelowNat X) hnonempty (count A)
  have hn' := Erdos444.mem_positiveBelowNat_iff.mp hn
  change Erdos444.maxDivisorCountNat A X = count A n at hcount
  rw [hcount] at hmax hlarge
  have hN : N ≤ n := by
    by_contra h
    have hnsmall : count A n ≤ Erdos444.maxDivisorCountNat A (N + 1) :=
      Erdos444.divisorCount_le_maxDivisorCountNat hn'.1 (by omega)
    have hnreal : (count A n : ℝ) ≤ Erdos444.maxDivisorCountNat A (N + 1) := by
      exact_mod_cast hnsmall
    have hb := le_max_right C ((Erdos444.maxDivisorCountNat A (N + 1) : ℝ) + 1)
    linarith
  refine ⟨n, hN, hn'.1, ?_⟩
  have hm : mass A n ≤ mass A X := Erdos444.reciprocalMassNat_mono A hn'.2.le
  have hpow : (1 + mass A n) ^ k ≤ (1 + mass A X) ^ k :=
    pow_le_pow_left₀ (by linarith [Erdos444.reciprocalMassNat_nonneg A n])
      (by linarith) k
  calc
    C * (1 + mass A n) ^ k ≤ C * (1 + mass A X) ^ k :=
      mul_le_mul_of_nonneg_left hpow hC
    _ ≤ B * (1 + mass A X) ^ k :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ < _ := hlarge

def nextWitness (A : Set ℕ) (hA : A.Infinite) (k N : ℕ) : ℕ :=
  Classical.choose (pointwise_large_value A hA k (k + 1) (by positivity) N)

lemma nextWitness_spec (A : Set ℕ) (hA : A.Infinite) (k N : ℕ) :
    N ≤ nextWitness A hA k N ∧ 0 < nextWitness A hA k N ∧
      ((k : ℝ) + 1) * (1 + mass A (nextWitness A hA k N)) ^ k <
        (count A (nextWitness A hA k N) : ℝ) :=
  Classical.choose_spec (pointwise_large_value A hA k (k + 1) (by positivity) N)

def diagonal (A : Set ℕ) (hA : A.Infinite) : ℕ → ℕ
  | 0 => nextWitness A hA 0 1
  | k + 1 => nextWitness A hA (k + 1) (diagonal A hA k + 1)

theorem diagonal_strictMono (A : Set ℕ) (hA : A.Infinite) : StrictMono (diagonal A hA) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact (Nat.lt_succ_self _).trans_le (nextWitness_spec A hA (k + 1) _).1

theorem diagonal_bound (A : Set ℕ) (hA : A.Infinite) (j : ℕ) :
    0 < diagonal A hA j ∧
      ((j : ℝ) + 1) * (1 + mass A (diagonal A hA j)) ^ j <
        (count A (diagonal A hA j) : ℝ) := by
  cases j with
  | zero => exact (nextWitness_spec A hA 0 1).2
  | succ k => exact (nextWitness_spec A hA (k + 1) (diagonal A hA k + 1)).2

/-- One and the same increasing sequence makes every real-power-normalized
pointwise divisor count tend to infinity. The exponent may be negative. -/
theorem diagonal_tendsto (A : Set ℕ) (hA : A.Infinite) (r : ℝ) :
    Tendsto (fun j : ℕ =>
      (count A (diagonal A hA j) : ℝ) / (1 + mass A (diagonal A hA j)) ^ r)
      atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro C
  filter_upwards [eventually_ge_atTop ⌈r⌉₊, eventually_ge_atTop ⌈C⌉₊] with j hr hC
  have hrj : r ≤ (j : ℝ) := (Nat.le_ceil r).trans (by exact_mod_cast hr)
  have hCj : C ≤ (j : ℝ) + 1 := by
    have h : C ≤ (j : ℝ) := (Nat.le_ceil C).trans (by exact_mod_cast hC)
    linarith
  have hbase : 1 ≤ 1 + mass A (diagonal A hA j) := by
    linarith [Erdos444.reciprocalMassNat_nonneg A (diagonal A hA j)]
  have hpow : (1 + mass A (diagonal A hA j)) ^ r ≤
      (1 + mass A (diagonal A hA j)) ^ j := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hbase hrj
  have hpos : 0 < (1 + mass A (diagonal A hA j)) ^ r :=
    Real.rpow_pos_of_pos (by linarith) r
  apply le_of_lt
  apply (lt_div_iff₀ hpos).2
  calc
    C * (1 + mass A (diagonal A hA j)) ^ r ≤
        ((j : ℝ) + 1) * (1 + mass A (diagonal A hA j)) ^ r :=
      mul_le_mul_of_nonneg_right hCj hpos.le
    _ ≤ ((j : ℝ) + 1) * (1 + mass A (diagonal A hA j)) ^ j :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ < _ := (diagonal_bound A hA j).2

theorem simultaneous_witnesses (A : Set ℕ) (hA : A.Infinite) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ (∀ j, 0 < n j) ∧
      ∀ r : ℝ, Tendsto (fun j => (count A (n j) : ℝ) / (1 + mass A (n j)) ^ r)
        atTop atTop :=
  ⟨diagonal A hA, diagonal_strictMono A hA, fun j => (diagonal_bound A hA j).1,
    diagonal_tendsto A hA⟩

theorem infinite_iff_diagonal (A : Set ℕ) :
    A.Infinite ↔ ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ j : ℕ,
      ((j : ℝ) + 1) * (1 + mass A (n j)) ^ j < (count A (n j) : ℝ) := by
  classical
  constructor
  · intro hA
    exact ⟨diagonal A hA, diagonal_strictMono A hA, fun j => (diagonal_bound A hA j).2⟩
  · rintro ⟨n, _, hn⟩
    by_contra hA
    have hfinite : A.Finite := Set.not_infinite.mp hA
    let m := hfinite.toFinset.card
    have hcount : count A (n m) ≤ m := by
      apply Finset.card_le_card
      intro a ha
      exact hfinite.mem_toFinset.mpr (Finset.mem_filter.mp ha).2
    have hcountR : (count A (n m) : ℝ) ≤ m := by exact_mod_cast hcount
    have hbase : 1 ≤ 1 + mass A (n m) := by
      linarith [Erdos444.reciprocalMassNat_nonneg A (n m)]
    have hp : 1 ≤ (1 + mass A (n m)) ^ m := one_le_pow₀ hbase
    have hh := hn m
    nlinarith [mul_nonneg (by positivity : 0 ≤ (m : ℝ) + 1) (sub_nonneg.mpr hp)]

/-- The full original statement, retained with its original proof attribution. -/
theorem jsp_000361 : ∀ A : Set ℕ, A.Infinite → ∀ k : ℕ,
    atTop.limsup (fun x : ℝ => (Erdos444.ratio A k x : EReal)) = ⊤ :=
  Erdos444.erdos_444

end
end DivisorWitnesses
