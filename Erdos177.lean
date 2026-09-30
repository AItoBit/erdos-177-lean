module

public import Mathlib

/-!
# Erdős Problem 177

Find the smallest `h(d)` such that there is `f : ℕ → {-1, 1}` with
`max_{P_d} |∑_{n ∈ P_d} f n| ≤ h(d)` for every `d ≥ 1`, where `P_d` ranges over all finite
arithmetic progressions with common difference `d`.

The exact growth of the optimal `h` is **open** (known: `d^{1/2} ≪ h(d)`, by Roth, and
`h(d) ≤ d^{8+ε}`, by Beck). This file formalises the problem (`Admissible`) and proves, without
`sorry`:

* `admissible_eight_factorial` : `h(d) = 8 · d!` is admissible (Cantor–Erdős–Schreiber–Straus,
  `h(d) ≪ d!`), via `f(n) = (-1)^(sum of the factorial-base digits of n)`;
* `Admissible.one_le` : every admissible `h` has `h(d) ≥ 1`;
* `exists_large_apSum`, `Admissible.not_bounded` : by van der Waerden's theorem, no admissible
  `h` is bounded.
-/

@[expose] public section

open Finset

namespace Erdos177

/-- `digitSum c n` : digit sum of `n` in the mixed radix with bases `c+2, c+3, c+4, …`. -/
def digitSum (c n : ℕ) : ℕ :=
  if h : n = 0 then 0 else n % (c + 2) + digitSum (c + 1) (n / (c + 2))
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)

lemma digitSum_zero (c : ℕ) : digitSum c 0 = 0 := by
  rw [digitSum]; simp

lemma digitSum_eq (c n : ℕ) : digitSum c n = n % (c + 2) + digitSum (c + 1) (n / (c + 2)) := by
  by_cases h : n = 0
  · subst h; simp [digitSum_zero]
  · rw [digitSum]; simp [h]

/-- `radix c K = (c+2)(c+3)⋯(c+K+1)`. -/
def radix (c : ℕ) : ℕ → ℕ
  | 0 => 1
  | K + 1 => (c + 2) * radix (c + 1) K

lemma radix_pos (c K : ℕ) : 0 < radix c K := by
  induction K generalizing c with
  | zero => simp [radix]
  | succ K ih => simp only [radix]; exact Nat.mul_pos (by omega) (ih _)

lemma digitSum_block (K : ℕ) : ∀ c j x, x < radix c K →
    digitSum c (j * radix c K + x) = digitSum c x + digitSum (c + K) j := by
  induction K with
  | zero => intro c j x hx; simp [radix] at hx; subst hx; simp [radix, digitSum_zero]
  | succ K ih =>
    intro c j x hx
    simp only [radix] at hx ⊢
    have hx' : x / (c + 2) < radix (c + 1) K := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; linarith
    have e : j * ((c + 2) * radix (c + 1) K) + x
        = x % (c + 2) + (c + 2) * (j * radix (c + 1) K + x / (c + 2)) := by
      have := Nat.mod_add_div x (c + 2); nlinarith
    rw [digitSum_eq c (j * _ + x), digitSum_eq c x, e, Nat.add_mul_mod_self_left,
      Nat.add_mul_div_left _ _ (by omega), Nat.mod_mod,
      Nat.div_eq_of_lt (Nat.mod_lt _ (by omega)), zero_add, ih (c + 1) j _ hx',
      show c + 1 + K = c + (K + 1) by omega]
    ring

lemma radix_zero_eq (K : ℕ) : radix 0 K = (K + 1).factorial := by
  suffices ∀ c, radix c K * (c + 1).factorial = (c + K + 1).factorial by
    simpa using this 0
  induction K with
  | zero => intro c; simp [radix]
  | succ K ih =>
    intro c
    simp only [radix]
    rw [show c + (K + 1) + 1 = (c + 1) + K + 1 by omega, ← ih (c + 1),
      Nat.factorial_succ (c + 1)]
    ring

/-- `±1`-valued sign attached to the mixed-radix digit sum. -/
def sgn (c n : ℕ) : ℤ := (-1) ^ digitSum c n

/-- The Cantor–Erdős–Schreiber–Straus type colouring: `(-1)` to the factorial-base digit sum. -/
def cessF (n : ℕ) : ℤ := sgn 0 n

lemma sgn_sq (c n : ℕ) : sgn c n = 1 ∨ sgn c n = -1 := by
  unfold sgn; exact neg_one_pow_eq_or ℤ _

lemma abs_sgn (c n : ℕ) : |sgn c n| = 1 := by
  rcases sgn_sq c n with h | h <;> simp [h]

lemma sgn_block (K c j x : ℕ) (hx : x < radix c K) :
    sgn c (j * radix c K + x) = sgn c x * sgn (c + K) j := by
  unfold sgn; rw [digitSum_block K c j x hx, pow_add]

lemma sgn_pair (e m : ℕ) (he : Even e) : sgn e (2 * m + 1) = - sgn e (2 * m) := by
  obtain ⟨k, rfl⟩ := he
  set q := 2 * m / (k + k + 2)
  set t := 2 * m % (k + k + 2)
  have h1 : (k + k + 2) * q + t = 2 * m := Nat.div_add_mod (2 * m) (k + k + 2)
  have ht : t < k + k + 2 := Nat.mod_lt _ (by omega)
  have htev : t % 2 = 0 := by
    simp only [t]
    rw [Nat.mod_mod_of_dvd _ ⟨k + 1, by ring⟩]; omega
  have ht1 : t + 1 < k + k + 2 := by omega
  have e1 : 2 * m + 1 = (t + 1) + (k + k + 2) * q := by linarith
  have e2 : 2 * m = t + (k + k + 2) * q := by linarith
  unfold sgn
  rw [digitSum_eq _ (2 * m + 1), digitSum_eq _ (2 * m), e1, e2,
    Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by omega), Nat.add_mul_div_left _ _ (by omega),
    Nat.mod_eq_of_lt ht1, Nat.mod_eq_of_lt ht, Nat.div_eq_of_lt ht1, Nat.div_eq_of_lt ht]
  ring

lemma sum_sgn_bound (e : ℕ) (he : Even e) (n : ℕ) : |∑ i ∈ range n, sgn e i| ≤ 1 := by
  have h2 : ∀ M, ∑ i ∈ range (2 * M), sgn e i = 0 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
        sgn_pair e M he]
      ring
  obtain ⟨M, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp [h2]
  · rw [sum_range_succ, h2, zero_add, abs_sgn]

/-! ### Statement of the problem -/

/-- `f` takes only the values `1` and `-1`. -/
def IsSignFunction (f : ℕ → ℤ) : Prop := ∀ n, f n = 1 ∨ f n = -1

/-- Sum of `f` over the arithmetic progression `a, a + d, …, a + (N-1) d`. -/
def apSum (f : ℕ → ℤ) (a d N : ℕ) : ℤ := ∑ i ∈ range N, f (a + i * d)

/-- `h` is *admissible* (Erdős Problem 177): there is `f : ℕ → {-1, 1}` such that for every
`d ≥ 1`, every finite arithmetic progression `P_d` of positive integers with common difference
`d` satisfies `|∑_{n ∈ P_d} f n| ≤ h d`. Erdős asked for the smallest (growth of) such `h`. -/
def Admissible (h : ℕ → ℝ) : Prop :=
  ∃ f : ℕ → ℤ, IsSignFunction f ∧ ∀ d ≥ 1, ∀ a ≥ 1, ∀ N, |(apSum f a d N : ℝ)| ≤ h d

/-! ### Upper bound `h(d) ≪ d!` -/

lemma apSum_eq_sub (f : ℕ → ℤ) (a d N : ℕ) (hd : 0 < d) :
    apSum f a d N = ∑ n ∈ range (a + N * d), (if n % d = a % d then f n else 0)
      - ∑ n ∈ range a, (if n % d = a % d then f n else 0) := by
  rw [← Finset.sum_Ico_eq_sub _ (by omega)]
  induction N with
  | zero => simp [apSum]
  | succ N ih =>
    rw [apSum, sum_range_succ, ← apSum, ih, show a + (N + 1) * d = a + N * d + d by ring,
      ← Finset.sum_Ico_consecutive _ (show a ≤ a + N * d by omega)
        (show a + N * d ≤ a + N * d + d by omega)]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range, show a + N * d + d - (a + N * d) = d by omega,
      Finset.sum_eq_single 0]
    · simp [Nat.add_mul_mod_self_right]
    · intro k hk hk0
      refine ite_eq_right_iff.2 fun h => absurd h ?_
      intro h
      rw [show a + N * d + k = a + k + N * d by ring, Nat.add_mul_mod_self_right] at h
      have h' : k ≡ 0 [MOD d] := Nat.ModEq.add_left_cancel' a (by simpa [Nat.ModEq] using h)
      have := Nat.mod_eq_of_lt (Finset.mem_range.1 hk)
      simp [Nat.ModEq] at h'
      omega
    · intro h; exact absurd (Finset.mem_range.2 hd) h

section Partial

variable (d K r : ℕ)

/-- The indicator-weighted colouring along one residue class. -/
def resG (n : ℕ) : ℤ := if n % d = r % d then cessF n else 0

lemma resG_block (hdP : d ∣ radix 0 K) (j y : ℕ) (hy : y < radix 0 K) :
    resG d r (j * radix 0 K + y) = resG d r y * sgn K j := by
  obtain ⟨Q, hQ⟩ := hdP
  unfold resG cessF
  have hm : (j * radix 0 K + y) % d = y % d := by
    rw [hQ, show j * (d * Q) + y = y + d * (j * Q) by ring, Nat.add_mul_mod_self_left]
  rw [hm, sgn_block K 0 j y hy, zero_add]
  split_ifs <;> simp

lemma resG_count (hd : 0 < d) (hdP : d ∣ radix 0 K) (x : ℕ) (hx : x ≤ radix 0 K) :
    |∑ y ∈ range x, resG d r y| ≤ ((radix 0 K / d : ℕ) : ℤ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∑ y ∈ range x, |resG d r y| = ((Nat.count (fun y => y ≡ r [MOD d]) x : ℕ) : ℤ) := by
    rw [Nat.count_eq_card_filter_range, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold resG Nat.ModEq
    split_ifs <;> simp [*, abs_sgn, cessF]
  rw [h1, Nat.count_modEq_card x hd r]
  have : x / d + (if r % d < x % d then 1 else 0) ≤ radix 0 K / d := by
    rcases hx.lt_or_eq with hx | rfl
    · have := Nat.div_lt_div_of_lt_of_dvd hdP hx
      split_ifs <;> omega
    · rw [Nat.mod_eq_zero_of_dvd hdP]; simp
  exact_mod_cast this

lemma resG_partial_bound (hd : 0 < d) (hK : Even K) (hdP : d ∣ radix 0 K) (M : ℕ) :
    |∑ n ∈ range M, resG d r n| ≤ 2 * ((radix 0 K / d : ℕ) : ℤ) := by
  set P := radix 0 K with hP
  have hPpos : 0 < P := radix_pos 0 K
  set T := ∑ y ∈ range P, resG d r y
  have hblocks : ∀ q, ∑ n ∈ range (q * P), resG d r n = T * ∑ j ∈ range q, sgn K j := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show (q + 1) * P = q * P + P by ring, sum_range_add, ih, sum_range_succ, mul_add]
      congr 1
      simp only [T, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [resG_block d K r hdP q y (Finset.mem_range.1 hy)]
  have htail : ∀ q x, x ≤ P →
      ∑ y ∈ range x, resG d r (q * P + y) = sgn K q * ∑ y ∈ range x, resG d r y := by
    intro q x hx
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [resG_block d K r hdP q y (by have := Finset.mem_range.1 hy; omega)]
    ring
  have hM : M = M / P * P + M % P := by rw [Nat.div_add_mod']
  rw [hM, sum_range_add, hblocks, htail _ _ (Nat.mod_lt _ hPpos).le]
  have hT := resG_count d K r hd hdP P le_rfl
  have hx := resG_count d K r hd hdP (M % P) (Nat.mod_lt _ hPpos).le
  have hE := sum_sgn_bound K hK (M / P)
  calc _ ≤ |T * ∑ j ∈ range (M / P), sgn K j| + |sgn K (M / P) * ∑ y ∈ range (M % P), resG d r y| :=
        abs_add_le _ _
    _ = |T| * |∑ j ∈ range (M / P), sgn K j| + |∑ y ∈ range (M % P), resG d r y| := by
        rw [abs_mul, abs_mul, abs_sgn, one_mul]
    _ ≤ ((P / d : ℕ) : ℤ) * 1 + ((P / d : ℕ) : ℤ) := by
        gcongr
    _ = _ := by ring

end Partial

lemma cessF_apSum_bound (d K a N : ℕ) (hd : 0 < d) (hK : Even K) (hdP : d ∣ radix 0 K) :
    |apSum cessF a d N| ≤ 4 * ((radix 0 K / d : ℕ) : ℤ) := by
  rw [apSum_eq_sub _ _ _ _ hd]
  have h1 := resG_partial_bound d K a hd hK hdP (a + N * d)
  have h2 := resG_partial_bound d K a hd hK hdP a
  unfold resG at h1 h2
  calc _ ≤ _ := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

lemma cessF_isSign : IsSignFunction cessF := fun n => sgn_sq 0 n

/-- For every `d ≥ 1` and every finite arithmetic progression with common difference `d`
(starting anywhere in `ℕ`), the sum of `cessF` over it is at most `8 · d!` in absolute value. -/
theorem cessF_bound (d : ℕ) (hd : 1 ≤ d) (a N : ℕ) :
    |apSum cessF a d N| ≤ 8 * (d.factorial : ℤ) := by
  rcases Nat.even_or_odd d with hev | hodd
  · -- `K = d`, block length `(d+1)!`
    have hdP : d ∣ radix 0 d := by
      rw [radix_zero_eq]; exact Nat.dvd_factorial hd (by omega)
    refine (cessF_apSum_bound d d a N hd hev hdP).trans ?_
    have : radix 0 d / d ≤ 2 * d.factorial := by
      apply Nat.div_le_of_le_mul
      rw [radix_zero_eq, Nat.factorial_succ]
      have := Nat.factorial_pos d
      nlinarith
    have : ((radix 0 d / d : ℕ) : ℤ) ≤ 2 * d.factorial := by exact_mod_cast this
    linarith
  · -- `K = d - 1`, block length `d!`
    have hK : Even (d - 1) := by
      obtain ⟨k, rfl⟩ := hodd; simp
    have hdP : d ∣ radix 0 (d - 1) := by
      rw [radix_zero_eq, Nat.sub_add_cancel hd]; exact Nat.dvd_factorial hd le_rfl
    refine (cessF_apSum_bound d (d - 1) a N hd hK hdP).trans ?_
    have : radix 0 (d - 1) / d ≤ d.factorial := by
      rw [radix_zero_eq, Nat.sub_add_cancel hd]; exact Nat.div_le_self _ _
    have : ((radix 0 (d - 1) / d : ℕ) : ℤ) ≤ d.factorial := by exact_mod_cast this
    have : (0 : ℤ) ≤ d.factorial := by positivity
    linarith

/-- **Cantor–Erdős–Schreiber–Straus**: `h(d) = 8 · d!` is admissible, so `h(d) ≪ d!`. -/
theorem admissible_eight_factorial : Admissible (fun d => 8 * (d.factorial : ℝ)) := by
  refine ⟨cessF, cessF_isSign, fun d hd a _ N => ?_⟩
  dsimp only
  rw [← Int.cast_abs]
  exact_mod_cast cessF_bound d hd a N

/-! ### Lower bounds -/

lemma apSum_abs_of_const (f : ℕ → ℤ) (a d N : ℕ) (c : ℤ) (hc : |c| = 1)
    (h : ∀ i < N, f (a + i * d) = c) : |apSum f a d N| = N := by
  rw [apSum, Finset.sum_congr rfl fun i hi => h i (Finset.mem_range.1 hi)]
  simp [abs_mul, hc]

/-- Trivial lower bound: every admissible `h` satisfies `h d ≥ 1` for `d ≥ 1`
(a one-term progression). -/
theorem Admissible.one_le {h : ℕ → ℝ} (hh : Admissible h) (d : ℕ) (hd : 1 ≤ d) : 1 ≤ h d := by
  obtain ⟨f, hf, hb⟩ := hh
  have := hb d hd 1 le_rfl 1
  rcases hf 1 with h1 | h1 <;> simpa [apSum, h1] using this

/-- **Van der Waerden** consequence: for every `±1` function `f` and every bound `C`, some
arithmetic progression of positive integers has `|∑ f| > C`. -/
theorem exists_large_apSum (f : ℕ → ℤ) (hf : IsSignFunction f) (C : ℝ) :
    ∃ d ≥ 1, ∃ a ≥ 1, ∃ N, C < |(apSum f a d N : ℝ)| := by
  obtain ⟨d, hd, b, col, hcol⟩ :=
    Combinatorics.exists_mono_homothetic_copy (range (⌈C⌉₊ + 1)) (fun n : ℕ => f (n + 1) = 1)
  refine ⟨d, hd, b + 1, by omega, ⌈C⌉₊ + 1, ?_⟩
  have hconst : ∀ i < ⌈C⌉₊ + 1, f (b + 1 + i * d) = f (b + 1) := by
    intro i hi
    have h1 := hcol i (Finset.mem_range.2 hi)
    have h0 := hcol 0 (Finset.mem_range.2 (by omega))
    simp only [smul_eq_mul, mul_zero, zero_add] at h1 h0
    rw [show b + 1 + i * d = d * i + b + 1 by ring]
    rcases hf (d * i + b + 1) with e | e <;> rcases hf (b + 1) with e' | e' <;>
      simp_all
  have := apSum_abs_of_const f (b + 1) d _ (f (b + 1))
    (by rcases hf (b + 1) with e | e <;> simp [e]) hconst
  have hC := Nat.le_ceil C
  rw [← Int.cast_abs, this]
  push_cast
  linarith

/-- Consequently no admissible `h` is bounded: `h(d)` is unbounded as `d → ∞`. -/
theorem Admissible.not_bounded {h : ℕ → ℝ} (hh : Admissible h) :
    ¬ ∃ C : ℝ, ∀ d ≥ 1, h d ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨f, hf, hb⟩ := hh
  obtain ⟨d, hd, a, ha, N, hN⟩ := exists_large_apSum f hf C
  linarith [hb d hd a ha N, hC d hd]

end Erdos177
