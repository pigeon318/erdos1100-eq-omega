# Erdős Problem 1100: formal proof of `eq_omega`

A Lean 4 proof of `erdos_1100.variants.eq_omega` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/1100.lean`, commit `5c783f7`).

## Statement

For every `k` there is a squarefree `n` with `ω(n) = k` and `τ⊥(n) = k`. Here `τ⊥(n)` counts the
adjacent pairs `d_i < d_{i+1}` of divisors of `n` that are coprime.

```lean
theorem erdos_1100.variants.eq_omega (k : ℕ) :
    ∃ n : ℕ, Squarefree n ∧ ω n = k ∧ tauPerp n = k
```

The definition of `tauPerp` and the statement are copied verbatim from formal-conjectures. The proof
was also checked against the repository's own declaration, by importing
`FormalConjectures.ErdosProblems.«1100»` and closing `type_of% Erdos1100.erdos_1100.variants.eq_omega`
with this proof.

## Proof

This is the observation of Erdős and Hall [ErHa78, p. 480]. Take primes `p₁ < p₂ < ⋯` with each
`pᵢ > p₁ ⋯ pᵢ₋₁`, and let `n = p₁ ⋯ p_k`.

1. `Nat.nth (· ∣ n) i` is the `i`-th entry of the sorted divisor list of `n` (`nth_dvd_eq`).
2. If `p` is a prime with `p > n`, the sorted divisors of `n * p` are the sorted divisors of `n`
   followed by `p` times them (`D_mul`).
3. In that list, pairs inside the first half are unchanged, pairs inside the second half share the
   factor `p`, and the pair `(n, p)` at the join is coprime. So `τ⊥(n * p) = τ⊥(n) + 1`
   (`S_append`).
4. Induction on `k` from `n = 1`, choosing each new prime with `Nat.exists_infinite_primes`.

## Layout

This repository follows the [Palomar](https://palomar-registry.org/) submission layout.

- `Challenge.lean`: the definition and statement, copied verbatim from formal-conjectures, with `sorry`.
- `Solution.lean`: the same statement, proved.
- `Erdos1100EqOmega/Basic.lean`: the proof development.
- `comparator.json`: tells Comparator to check that `Solution` proves exactly the `Challenge`
  statement, with the same `tauPerp`, using only `propext`, `Classical.choice` and `Quot.sound`.
- `formalization.yaml`: metadata, including the AI-use record.

## Checking

```
lake exe cache get
lake build
```

There is no `sorry` outside `Challenge.lean`, no `native_decide`, and no custom axiom.

Toolchain: Lean `v4.35.0-rc2` and the matching Mathlib tag `v4.35.0-rc2`. The proof was first
checked on Lean `v4.33.1` with Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, the versions
pinned by formal-conjectures at commit `5c783f7`.

## AI disclosure

This proof was written with AI assistance (Claude, by Anthropic). The Lean kernel checks every step.

## Licence note

The definition of `tauPerp` and the theorem statement are copied from formal-conjectures, which is
licensed under the Apache License 2.0.

## Reference

[ErHa78] Erdős, P. and Hall, R. R., *On some unconventional problems on the divisors of integers*.
J. Austral. Math. Soc. Ser. A 25 (1978), 479-485.
