import Interval.Tactic.Interval

/-!
# The inequality from Alweiss et al.

Exploring Claim 3 of https://arxiv.org/abs/2211.11731.
-/

open Real (log sqrt)
open Set
noncomputable section

def φ : ℝ := (sqrt 5 - 1) / 2

def H (x : ℝ) : ℝ := -x * log x - (1 - x) * log (1 - x)

lemma phi_pos : 0 < φ := by
  simp only [φ]
  have h : (1 : ℝ) < sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  nlinarith

lemma alweiss_somewhere : 0.9 * H 0.9 ≤ φ * H (0.9 ^ 2) := by
  simp only [φ, H]
  norm_num
  exact Interval.approx_le
    (((9 / 10 : Interval)) * (-((9 / 10 : Interval) * (9 / 10 : Interval).log) - (1 / 10 : Interval) * (1 / 10 : Interval).log))
    ((((5 : Interval).sqrt - 1) / 2) * (-((81 / 100 : Interval) * (81 / 100 : Interval).log) - (19 / 100 : Interval) * (19 / 100 : Interval).log))
    _ _ (by approx) (by approx) (by decide +kernel)

/-- It would be nice if `interval` did this -/
proof_wanted alweiss : ∀ x ∈ Icc φ 1, x * H x ≤ φ * H (x ^ 2)
