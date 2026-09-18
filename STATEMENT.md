# Problem statement

For an infinite set `A ⊆ ℕ`, let `d_A(n)` be the number of positive elements
of `A` dividing `n`.  Erdős and Sárközy proved that, for every `k ∈ ℕ`,

```text
limsup_{x → ∞} max_{1 ≤ n < x} d_A(n)
  / (sum_{a ∈ A, 1 ≤ a < x} 1/a)^k = ∞.
```

The Lean theorem `Erdos444.erdos_444` is the complete formal statement.  The
paper reference is [ErSa80], *Some asymptotic formulas on generalized divisor
functions IV*, Studia Sci. Math. Hungar. 15 (1980), 467–479.
