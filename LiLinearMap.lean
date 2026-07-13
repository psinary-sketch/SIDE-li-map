/-!
# The Li Linear Map and Channel Additivity

PLACE TO STAND programme. Vanilla Lean 4 (no Mathlib), federation pin v4.29.0-rc8.

Li's coefficients arise from Taylor coefficients η_j of log ξ at s = 1 via
  λ_n = n · Σ_{j=1..n} C(n−1, n−j) · η_j.
This file certifies the map's LINEARITY over the coefficient stream — the
formal content of channel additivity: for any decomposition of log ξ into
channels with coefficient streams η^A, η^Z,
  λ_n = λ_A(n) + λ_Z(n)   for every n
(THE_SINGLE_INDEFINITE_TERM §III; FINDINGS F.2026-07-09-g).
The analytic identification of η with actual Taylor coefficients of log ξ
is the manuscript/Mathlib leg; this kernel carries the algebra.
-/

namespace LiLinearMap

/-- Binomial coefficients, defined recursively (vanilla; no Mathlib). -/
def binom : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _+1   => 0
  | n+1,   k+1   => binom n k + binom n (k+1)

theorem binom_self_zero (n : Nat) : binom n 0 = 1 := by cases n <;> rfl

/-- Sum of f(j+1) for j = 0..n−1, i.e. Σ_{j=1..n} f j. -/
def S (f : Nat → Int) (n : Nat) : Int :=
  ((List.range n).map (fun j => f (j+1))).sum

theorem S_zero (f : Nat → Int) : S f 0 = 0 := rfl

theorem S_succ (f : Nat → Int) (n : Nat) :
    S f (n+1) = S f n + f (n+1) := by
  simp [S, List.range_succ]

/-- Additivity of the inner sum. -/
theorem S_add (f g : Nat → Int) (n : Nat) :
    S (fun j => f j + g j) n = S f n + S g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [S_succ, ih]; omega

/-- The constant-zero summand gives zero sum. -/
theorem S_zero_fun (n : Nat) : S (fun _ => (0 : Int)) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [S_succ, ih]; omega

/-- The Li linear map over an abstract coefficient stream η. -/
def lam (η : Nat → Int) (n : Nat) : Int :=
  n * S (fun j => (binom (n-1) (n-j) : Int) * η j) n

/-- CHANNEL ADDITIVITY: the Li map is additive in the coefficient stream.
    Instance: λ_n = λ_A(n) + λ_Z(n) for the archimedean / pole+Euler split. -/
theorem lam_add (η η' : Nat → Int) (n : Nat) :
    lam (fun j => η j + η' j) n = lam η n + lam η' n := by
  unfold lam
  have h : S (fun j => (binom (n-1) (n-j) : Int) * (η j + η' j)) n
         = S (fun j => (binom (n-1) (n-j) : Int) * η j) n
         + S (fun j => (binom (n-1) (n-j) : Int) * η' j) n := by
    have hs := S_add (fun j => (binom (n-1) (n-j) : Int) * η j)
                     (fun j => (binom (n-1) (n-j) : Int) * η' j) n
    rw [← hs]
    congr 1; funext j; exact Int.mul_add _ _ _
  rw [h]; exact Int.mul_add _ _ _

/-- The zero stream maps to zero at every n. -/
theorem lam_zero (n : Nat) : lam (fun _ => 0) n = 0 := by
  unfold lam
  have h : (fun j => (binom (n-1) (n-j) : Int) * 0) = (fun _ => (0 : Int)) := by
    funext j; exact Int.mul_zero _
  rw [h, S_zero_fun, Int.mul_zero]

/-- λ_1 = η_1: the first Li coefficient is the first Taylor coefficient. -/
theorem lam_one (η : Nat → Int) : lam η 1 = η 1 := by
  unfold lam S
  simp [binom]

end LiLinearMap
