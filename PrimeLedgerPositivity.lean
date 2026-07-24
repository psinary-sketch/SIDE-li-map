import LiLinearMap

/-!
# Prime-Ledger Positivity — the Euler-product ingredient anchor

PLACE TO STAND programme. Vanilla Lean 4 (no Mathlib), federation pin v4.29.0-rc8.
Work-order W-ORD-LAMBDA-NONNEG. Sibling anchor to `LiLinearMap.lam_add`.

## CEILING (author ruling — carried verbatim)

"compile the ingredient — Λ ≥ 0 wired to the lam_add channel anchor — an
ingredient compilation; it reaches the σ=1 edge classically and must not be
presented as reaching the center."

That is: this file compiles the PRIME-LEDGER POSITIVITY ingredient — von
Mangoldt Λ(n) ≥ 0, the arithmetic shadow of the Euler product. Classically this
ingredient yields ONLY the σ = 1 zero-free region (de la Vallée Poussin, via the
3-4-1 positivity), NOT the critical line. The gap from "zero-free near σ = 1" to
"zeros on σ = 1/2" is the open sign layer (the clause h2). Nothing here is phrased
as reaching σ = 1/2 or as closing anything. This is the INGREDIENT, not the
inequality λ_Z ≥ −λ_A, and not RH.

## Survey note (honest scope; see W-ORD report)

This kernel is VANILLA Lean 4 with NO Mathlib dependency (two files, no lakefile).
Consequently Mathlib's `ArithmeticFunction.vonMangoldt_nonneg` cannot be
re-exported here. Faithful to the kernel's own charter — "the analytic
identification of η with actual Taylor coefficients … is the manuscript/Mathlib
leg; this kernel carries the algebra" (LiLinearMap.lean) — the ARITHMETIC fact
Λ(n) ≥ 0 itself remains a manuscript/Mathlib-leg re-export. What the algebra CAN
carry, and what is proved below, is the kernel-altitude shadow of that ingredient
and its genuine type-level wiring to the `lam` channel:

  • `NonnegStream η`         — a coefficient stream is pointwise nonnegative
                               (the algebraic shadow of "the prime ledger Λ ≥ 0").
  • `lam_nonneg_of_nonneg`   — positivity of a stream propagates through the Li
                               channel: `NonnegStream η → 0 ≤ lam η n` for all n.

The binomial channel weights `binom (n-1) (n-j)` are Nat-valued, hence nonneg,
so the Li map is positivity-preserving on the coefficient stream. This is the
honest sense in which "Λ ≥ 0 wires to the lam_add channel anchor": the Euler
channel, fed a nonnegative ledger stream, returns a nonnegative Li contribution.
It is a SIBLING anchor to `lam_add` (same namespace/module family), not a
retrofit of Λ into the integer-stream signature.
-/

namespace LiLinearMap

/-- The kernel-altitude shadow of the prime-ledger positivity ingredient:
    a coefficient stream is pointwise nonnegative. Classically instantiated by
    the von Mangoldt ledger `η j = Λ(j)`, whose nonnegativity `Λ(n) ≥ 0` is the
    manuscript/Mathlib-leg re-export (`ArithmeticFunction.vonMangoldt_nonneg`). -/
def NonnegStream (η : Nat → Int) : Prop := ∀ k, 0 ≤ η k

/-- Positivity of the inner sum `S` under a pointwise-nonnegative summand. -/
theorem S_nonneg (f : Nat → Int) (hf : ∀ k, 0 ≤ f k) (n : Nat) : 0 ≤ S f n := by
  induction n with
  | zero => rw [S_zero]; omega
  | succ n ih => rw [S_succ]; have h := hf (n+1); omega

/-- INGREDIENT WIRING (sibling anchor to `lam_add`): the Li channel is
    positivity-preserving. A pointwise-nonnegative coefficient stream — the
    algebraic shadow of the prime ledger Λ ≥ 0 — yields a nonnegative Li value
    at every index, because the binomial channel weights are Nat-valued.

    CEILING: this reaches the σ = 1 edge classically only; it is the ingredient,
    not λ_Z ≥ −λ_A, and not RH. -/
theorem lam_nonneg_of_nonneg (η : Nat → Int) (hη : NonnegStream η) (n : Nat) :
    0 ≤ lam η n := by
  unfold lam
  refine Int.mul_nonneg (Int.natCast_nonneg n) ?_
  apply S_nonneg
  intro k
  exact Int.mul_nonneg (Int.natCast_nonneg _) (hη k)

end LiLinearMap
