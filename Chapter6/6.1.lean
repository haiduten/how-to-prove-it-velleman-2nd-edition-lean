import HTPILib.Chap6
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
namespace HTPI.Exercises

open scoped BigOperators
theorem Example_6_1_1 :
    ∀ (n : Nat), (Sum i from 0 to n, 2 ^ i)=  2 ^ (n + 1) - 1:= by
  by_induc
  ·
    rw[sum_base]
    simp
  ·
    intro n h
    rw[sum_from_zero_step]
    rw[h]
    calc
      2 ^ (n + 1) - 1 + 2 ^ (n + 1) = 2 ^ (n + 1) + 2 ^ (n + 1) - 1 := by
        calc
          _ = (2 ^ (n + 1) - 1) + 2 ^ (n + 1) := by rfl
          _ = 2 ^ (n + 1) + (2 ^ (n + 1) - 1) := by exact Nat.add_comm (2 ^ (n + 1) - 1) (2 ^ (n + 1))
          _ = 2 ^ (n + 1) + 2 ^ (n + 1) - 1 := by
            refine Eq.symm (Nat.add_sub_assoc ?_ (2 ^ (n + 1)))
            have : 2 ≤ 2 ^ (n + 1) := by
              refine Nat.le_pow ?_
              exact Nat.zero_lt_succ n
            exact Nat.one_le_two_pow
      _ = 2 * 2 ^ (n + 1) - 1 := by
        have: 2 ^ (n + 1) + 2 ^ (n + 1) = 2 * 2 ^ (n + 1) := by exact Eq.symm (Nat.two_mul (2 ^ (n + 1)))
        rw[this]
      _ = 2 ^ (n + 1 + 1) - 1 := by
        have : 2 * 2 ^ (n + 1) = 2 ^ (n + 1 + 1) := by exact Eq.symm Nat.pow_succ'
        rw[this]

theorem Example_6_1_2 :
    ∀ (n : Nat), 3 ∣ n ^ 3 - n := by
  by_induc
  ·
    exists 0
  ·
    intro n hn
    have ⟨k, hk⟩ := hn
    define
    exists k + n^2 + n
    have : (n + 1) ^ 3 = n^3 + 3 * n^2 + 3 * n  + 1 := by ring
    rw[this]
    calc
     _ =   n ^ 3 + 3 * n ^ 2 + 3 * n  - n  := by omega
     _ = n ^ 3 - n + 3 * n ^ 2 + 3 * n := by
      have hn : n ≤ n ^ 3 := by
        refine Nat.le_self_pow ?_ n
        norm_num
      omega
     _ = 3 * k + 3 * n ^ 2 + 3 * n := by rw[hk]
     _ = 3 * (k + n ^ 2 + n) := by ring

theorem Example_6_1_3 : ∀ n ≥ 5, 2 ^ n > n ^ 2 := by
    by_induc
    ·
      simp
    ·
      intro n hn hn'
      rw[gt_iff_lt] at hn'
      rw[gt_iff_lt]
      rw[← mul_lt_mul_iff_of_pos_left (by norm_num : 0 < 2)] at hn'
      have :2 * 2 ^ n = 2 ^ (n + 1) := by exact Eq.symm Nat.pow_succ'
      rw[this] at hn'
      apply lt_trans _ hn'
      have: ∀ n ≥ 5, (n + 1) ^ 2 < 2 * n ^ 2 := by
        by_induc
        · simp
        ·
          intro n hn hn'
          have :(n + 1) ^ 2 = n^2 + 2* n + 1:= by ring
          rw[this] at hn'
          have hn': 2 * n + 1 < n^2 := by linarith
          have : (n + 1 + 1) ^ 2  = n^2 + 4 *n  + 4 := by ring
          rw[this]
          have : 2 * (n + 1) ^ 2 = 2* n^2 + 4 * n + 2 := by ring
          rw[this]
          linarith
      exact this n hn

theorem Exercise_6_1_1 :
    ∀ (n : Nat), 2 * Sum i from 0 to n, i = n * (n + 1)  := by
  by_induc
  ·
    simp
    rw[sum_base]
  ·
    intro n hn
    rw[sum_from_zero_step]
    have:  2 * ((Sum i from 0 to n, i) + (n + 1)) = 2 * (Sum i from 0 to n, i) + 2 *  (n + 1) := by ring
    rw[this]
    rw[hn]
    have :  n * (n + 1) + 2 * (n + 1) = n^2 + 3 *n + 2 := by ring
    rw[this]
    have : (n + 1) * (n + 1 + 1) = n^2 + 3 *n + 2 := by ring
    rw[this]

theorem Exercise_6_1_2 :
    ∀ (n : Nat), 6 * Sum i from 0 to n, i^2 = n * (n + 1) * (2*n + 1)  := by
    by_induc
    ·
      simp
      rw[sum_base]
      simp
    ·
      intro n hn
      rw[sum_from_zero_step]
      have: 6 * ((Sum i from 0 to n, i ^ 2) + (n + 1) ^ 2) = 6 *(Sum i from 0 to n, i ^ 2) + 6 * (n + 1) ^ 2 := by linarith
      rw[this]
      rw[hn]
      linarith

theorem Exercise_6_1_3:
    ∀ (n : Nat), 4 * Sum i from 0 to n, i^3 = (n * (n + 1))^2  := by
  by_induc
  ·
    simp
    rw[sum_base]
    simp
  ·
    intro n hn
    rw[sum_from_zero_step]
    linarith


theorem Exercise_6_1_4:
    ∀ (n : Nat), 1 ≤ n →  Sum i from 1 to n, (2*i - (1: ℤ)) = n^2  := by
    by_induc
    ·
      decide
    ·
      intro n hn hn'
      rw[sum_step,hn']
      push_cast
      linarith
      exact hn

theorem Exercise_6_1_5:
    ∀ (n : Nat),  3 * Sum i from 0 to n, i * (i + 1) = n * (n + 1) * (n + 2)  := by
    by_induc
    ·
      decide
    ·
      intro n hn
      rw[sum_from_zero_step]
      have: 3 * ((Sum i from 0 to n, i * (i + 1)) + (n + 1) * (n + 1 + 1)) = 3 * (Sum i from 0 to n, i * (i + 1)) + 3 * ((n + 1) * (n + 1 + 1))  := by linarith
      rw[this, hn]
      nlinarith

theorem Exercise_6_1_6:
    ∀ (n : Nat),  4 * Sum i from 0 to n, i * (i + 1) * (i + 2) = n * (n + 1) * (n + 2) * (n + 3) := by
    by_induc
    ·
      decide
    ·
      intro n hn
      rw[sum_from_zero_step]
      have : 4 * ((Sum i from 0 to n, i * (i + 1) * (i + 2)) + (n + 1) * (n + 1 + 1) * (n + 1 + 2)) = 4 * (Sum i from 0 to n, i * (i + 1) * (i + 2)) + 4 * ((n + 1) * (n + 1 + 1) * (n + 1 + 2)) := by ring
      rw[this, hn]
      nlinarith

theorem Exercise_6_1_7 :
    ∀ (n : Nat), 2 * (Sum i from 0 to n, 3 ^ i)=  3 ^ (n + 1) - (1: ℤ) := by
    by_induc
    ·
      decide
    ·
      intro n hn
      rw[sum_from_zero_step]
      have: (2: ℤ) * ((Sum i from 0 to n, 3 ^ i) + 3 ^ (n + 1)) = 2 * (Sum i from 0 to n, 3 ^ i) + 2 * (3 ^ (n + 1)) := by linarith
      rw[this, hn]
      ring


theorem Exercise_6_1_8:
  let f: ℚ → ℚ := fun x => 1/(2* x -1) - 1 / (2 * x)
  let g: ℚ → ℚ → ℚ := fun n => fun x => 1/(n + x)
  ∀ (n: Nat), ∑ i ∈ Finset.range n, f (i + 1) =  ∑ i ∈ Finset.range n, g n (i + 1) := by
  intro f g n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw[Finset.sum_range_succ, ih]
    suffices h :
    f ((n : ℚ) + 1) =
      (∑ i ∈ Finset.range (n + 1),
          g (↑(n + 1)) (↑i + 1))
      -
      (∑ i ∈ Finset.range n,
          g (↑n) (↑i + 1)) by
      linarith
    rw [Finset.sum_range_succ]
    suffices h :
     f (↑n + 1) = ∑ x ∈ Finset.range n, g (↑(n + 1)) (↑x + 1)
        - ∑ i ∈ Finset.range n, g (↑n) (↑i + 1)
        + g (↑(n + 1)) (↑n + 1) by
        linarith
    rw[← Finset.sum_sub_distrib]

    push_cast
    have hsum :
    (∑ x ∈ Finset.range n,
        (g (↑n + 1) (↑x + 1) -
          g (↑n) (↑x + 1))) =
      ∑ x ∈ Finset.range n,
        (g (↑n) (↑x + 1 + 1) -
          g (↑n) (↑x + 1)) := by
      apply Finset.sum_congr rfl
      intro x hx
      dsimp[g]
      have h₁: (↑n + (x + 1)) ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one (n.add x))
      have h₂: (↑(n + 1) + (x + 1)) ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one ((n + 1).add x))
      field_simp
      push_cast
      linarith
    rw[hsum]
    dsimp[g]
    let h : ℕ → ℚ :=
      fun k => 1 / ((n : ℚ) + ((k : ℚ) + 1))

    have htel :
        (∑ x ∈ Finset.range n,
          (1 / ((n : ℚ) + ((x : ℚ) + 1 + 1)) -
          1 / ((n : ℚ) + ((x : ℚ) + 1)))) =
          h n - h 0 := by
      have h1 := (Finset.sum_range_sub h n)
      dsimp[h] at h1
      push_cast at h1
      exact h1

    rw [htel]
    dsimp[f]
    have h₁: (2 * (↑n + 1)) ≠ 0 := by positivity
    have h₂: (↑n + 1 + (↑n + 1)) ≠ 0 := by positivity
    have h₃ : (2 * (↑n + 1) - 1) ≠ 0 := by
      rw[mul_add]
      simp
    dsimp[h]
    have h₄: (↑n + (↑n + 1)) ≠ 0 := by positivity
    have h₅: (↑n + (0 + 1)) ≠ 0 := by positivity
    have h₆: (2 * ((n: ℚ) + 1) - 1) ≠ 0 := by
      rw[mul_add]
      have hn : (0 : ℚ) ≤ n := by
        positivity
      nlinarith
    field_simp [h₆]
    ring


theorem Exercise_6_1_9_a : ∀ (n : Nat), 2 ∣ n ^ 2 + n := by
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have ⟨k, hk⟩ := ih
    exists k + n + 1
    rw[mul_add, mul_add]
    rw[← hk]
    simp
    nlinarith

theorem Exercise_6_1_9_b : ∀ (n : Nat), 6 ∣ n ^ 3 - (n: ℝ) := by
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have ⟨k, hk⟩ := ih
    push_cast
    have : ((n: ℝ) + 1) ^ 3 = n^3 + 3 *n^2 + 3 * n + 1 := by linarith
    rw[this]
    have : (n: ℝ) ^ 3 + 3 * n ^ 2 + 3 * n + 1 - (n + 1) = n ^ 3  - n + (3 * n ^ 2 + 3 * n) := by linarith
    rw[this]
    rw[hk]
    apply dvd_add
    ·
      exists k
    ·
      have: (3:ℝ) * n ^ 2 + 3 * n =  3 * (n ^ 2 + n) := by linarith
      rw[this]
      have: (6: ℝ) = 3 * 2 := by linarith
      rw[this]
      have: (3: ℝ) ≠ 0 := by norm_num
      rw[mul_dvd_mul_iff_left this]
      cases Nat.even_or_odd n
      case inl heven =>
        rw[even_iff_two_dvd] at heven
        have ⟨k', hk'⟩ := heven
        have hk' : n = (2: ℝ) * k' := by exact_mod_cast hk'
        exists 2 * k'^2 + k'
        have: (2: ℝ) * (2 * ↑k' ^ 2 + ↑k') = (2 * k') * (2 * k') + (2 * k') := by nlinarith
        rw[this, ←hk']
        nlinarith
      case inr hodd =>
        rw[odd_iff_exists_bit1] at hodd
        have ⟨k', hk'⟩ := hodd
        have hk' : n = (2: ℝ) * k' + 1 := by exact_mod_cast hk'
        exists (2 * k'^2 + 3 * k' + 1)
        have : (2:ℝ) * (2 * ↑k' ^ 2 + 3 * ↑k' + 1) = (2 * ↑k' + 1)^2  + (2 * ↑k' + 1) := by linarith
        rw[this]
        rw[← hk']

theorem Exercise_6_1_10 : ∀ (n : Nat), 64 ∣ (9: ℝ)^n - 8 * n - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have ⟨k, hk⟩ := ih
      exists 9 * k + n
      have : 64 * (9 * k + ↑n) = 9 * (64 * k) + 64 * ↑n := by linarith
      rw[this, ← hk]
      have:  (9: ℝ) * (9 ^ n - 8 * ↑n - 1) + 64 * ↑n =   (9 *  9 ^ n - 8 * ↑n - 9 * 1)  := by nlinarith
      rw[this]
      have : (9:ℝ) * 9 ^ n = 9 ^ (n + 1) := by exact Eq.symm (pow_succ' 9 n)
      rw[this]
      push_cast
      rw[mul_add]
      linarith

theorem Exercise_6_1_11 : ∀ (n : Nat), 9 ∣ (4: ℝ)^n + 6 * n - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have ⟨k, hk⟩ := ih
      exists (4 *k - 2 * n + 1)
      have:  (9: ℝ) * (4 * k - 2 * ↑n + 1) =   (4 * (9 * k) - 9 * 2 * ↑n + 9 * 1) := by linarith
      rw[this, ← hk]
      push_cast
      have : (4: ℝ) * (4 ^ n + 6 * ↑n - 1) = 4 * 4 ^ n + 4*  6 * ↑n - 4 := by linarith
      rw[this]
      have : (4:ℝ) * 4 ^ n = 4 ^ (n + 1) := by exact Eq.symm (pow_succ' 4 n)
      rw[this, mul_add]
      nlinarith

theorem Exercise_6_1_12_a : ∀ (n : Nat), Even (7^n - 5^n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      cases Nat.even_or_odd (7^n)
      case inl h7 =>
        cases Nat.even_or_odd (5^n)
        case inl h5 =>
          have : 5 ^ (n + 1) ≤ 7 ^ (n + 1) := by
            refine Nat.pow_le_pow_left ?_ (n + 1)
            norm_num
          have :=  Nat.even_sub this
          rw[this]
          constructor
          intro _
          rw[even_iff_two_dvd]
          rw[even_iff_two_dvd] at h5
          have ⟨k, hk⟩ := h5
          exists 5 * k
          have : 2 * (5 * k)= 5 * (2 * k) := by linarith
          rw[this,← hk]
          exact Nat.pow_succ'
          intro _
          rw[even_iff_two_dvd]
          rw[even_iff_two_dvd] at h7
          have ⟨k, hk⟩ := h7
          exists 7 * k
          have : 2 * (7 * k)= 7 * (2 * k) := by linarith
          rw[this,← hk]
          exact Nat.pow_succ'
        case inr h5 =>
          by_contra h'
          have : 5 ^ (n) ≤ 7 ^ (n) := by
            refine Nat.pow_le_pow_left ?_ n
            norm_num
          rw[Nat.even_sub this] at ih
          have ⟨ih, ih'⟩ := ih
          contradict ih h7
          rw[Nat.not_even_iff_odd]
          exact h5
      case inr h7 =>
        cases Nat.even_or_odd (5^n)
        case inl h5 =>
          by_contra h'
          have : 5 ^ (n) ≤ 7 ^ (n) := by
            refine Nat.pow_le_pow_left ?_ n
            norm_num
          rw[Nat.even_sub this] at ih
          have ⟨ih, ih'⟩ := ih
          contradict ih' h5
          rw[Nat.not_even_iff_odd]
          exact h7
        case inr h5 =>
          have : 5 ^ (n + 1) ≤ 7 ^ (n + 1) := by
            refine Nat.pow_le_pow_left ?_ (n + 1)
            norm_num
          have :=  Nat.even_sub' this
          rw[this]
          constructor
          intro _
          rw[odd_iff_exists_bit1]
          rw[odd_iff_exists_bit1] at h5
          have ⟨k, hk⟩ := h5
          exists 5 * k + 2
          have : 5 ^ (n + 1)  = 5 * 5^n := by exact Nat.pow_succ'
          rw[this, hk]
          nlinarith
          intro _
          rw[odd_iff_exists_bit1]
          rw[odd_iff_exists_bit1] at h7
          have : 7 ^ (n + 1)  = 7 * 7^n := by exact Nat.pow_succ'
          rw[this]
          have ⟨k, hk⟩ := h7
          exists 7 * k + 3
          rw[hk]
          linarith

theorem Exercise_6_1_12_b : ∀ (n : Nat), 24 ∣ (2: ℝ) *7^n - 3 * 5^n - 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have ⟨k', hk'⟩ := Exercise_6_1_12_a n
      have: k' + k' = 2 * k' := by nlinarith
      rw[this] at hk'
      have ⟨k, hk⟩ := ih
      exists k + k'
      rw[mul_add, ← hk]
      have: (24: ℝ) * ↑k' = 12 * (2 * ↑k') := by linarith
      rw[this]
      have hk' := congrArg (fun x : ℕ => (x : ℝ)) hk'
      simp at hk'
      have :  5^n ≤ 7^n := by
        refine Nat.pow_le_pow_left ?_ n
        norm_num
      rw[Nat.cast_sub this] at hk'
      rw[← hk']
      have : (7:ℝ) ^ (n + 1) = 7 * 7 ^ n := by exact pow_succ' 7 n
      rw[this]
      have : (5:ℝ) ^ (n + 1) = 5 * 5 ^ n := by exact pow_succ' 5 n
      rw[this]
      field_simp
      have : (12: ℝ) * (7 ^ n - 5 ^ n) = 12 * 7 ^n - 12 * 5^ n := by  exact mul_sub_left_distrib 12 (7 ^ n) (5 ^ n)
      push_cast
      nlinarith

theorem Exercise_6_1_13 :
    ∀ (a b : Int) (n : Nat), (a - b) ∣ (a ^ n - b ^ n) := by
    intro a b n
    induction n with
    | zero => simp
    | succ n ih =>
      have ⟨k, hk⟩ := ih
      exists a *k + b^n
      have : (a - b) * (a * k + b ^ n) = a * ((a - b) * k) + (a - b) *  b ^ n := by linarith
      rw[this, ← hk]
      have: a ^ (n + 1)  = a * a ^ n := by exact Int.pow_succ' a n
      rw[this]
      have: b ^ (n + 1)  = b * b ^ n := by exact Int.pow_succ' b n
      rw[this]
      nlinarith

theorem Exercise_6_1_14 :
    ∀ (a b : Int) (n : Nat), (a + b) ∣ (a ^ (2* n + 1) + b ^ (2* n + 1)) := by
    intro a b n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      have ⟨k, hk⟩ := ih
      exists a^2 *k + (b^(2*n+ 2) - a * b^(2*n + 1))
      have : (2 * (n + 1) + 1) = (2 * (n) + 3) := by linarith
      rw[this]
      have: (a + b) * (a ^ 2 * k + (b ^ (2 * n + 2) - a * b ^ (2 * n + 1))) =  a ^ 2 * ((a + b) * k) + (a + b) * (b ^ (2 * n + 2) - a * b ^ (2 * n + 1)) := by linarith
      rw[this, ← hk, add_comm a b, mul_sub, add_mul, add_mul, mul_add]
      #check pow_add
      have : a ^ 2 * a ^ (2 * n + 1) = a ^ (2 * n + 3) := by
        calc
        a ^ 2 * a ^ (2 * n + 1)  = _ := by rw[← pow_add ]
        _ = a^(2*n + 3) := by
          have : 2 + (2 * n + 1) = (2 * n + 3) := by linarith
          rw[this]
      rw[this]
      have : (b * b ^ (2 * n + 2) + a * b ^ (2 * n + 2) - (b * (a * b ^ (2 * n + 1)) + a * (a * b ^ (2 * n + 1)))) = (b * b ^ (2 * n + 2) + a * b ^ (2 * n + 2) - b * (a * b ^ (2 * n + 1)) - a ^2 * b ^ (2 * n + 1)) := by linarith
      rw[this]
      #check pow_one
      have: b * (a * b ^ (2 * n + 1)) = a * b ^ (2 * n + 2) := by
        calc
          b * (a * b ^ (2 * n + 1)) = a * (b * b ^ (2 * n + 1)) := by exact Int.mul_left_comm b a (b ^ (2 * n + 1))
          _ = a * ((b^1) * b ^ (2 * n + 1)) := by rw[pow_one]
          _ = _ := by
            rw[← pow_add]
            have : 1 + (2 * n + 1) = 2 * n + 2 := by linarith
            rw[this]
      rw[this]
      have : b * b ^ (2 * n + 2) = b ^ (2 * n + 3) := by
        calc
          b * b ^ (2 * n + 2) = b ^ (1) * b ^ (2 * n + 2) := by
            nth_rewrite 1 [← pow_one b]
            rfl
          _ = _ := by
            rw[← pow_add]
            have : 1 + (2 * n + 2) = 2 * n + 3 := by linarith
            rw[this]
      rw[this]
      nlinarith

theorem Exercise_6_1_15 : ∀ n ≥ 10, 2 ^ n > n ^ 3 := by
    by_induc
    ·
      simp
    ·
      intro n hn ih
      calc
        2 ^ (n + 1) = 2 * 2 ^ n := by rw[pow_add, mul_comm, pow_one]
        _ > 2 * (n^3) := by
          rw[gt_iff_lt]
          have h': 0 < 2 := by positivity
          exact (mul_lt_mul_iff_of_pos_left h').mpr ih
        _ = n^3 + n^3 := by exact Nat.two_mul (n ^ 3)
        _ ≥ n^3 + 10 * n^2 := by
          refine Nat.add_le_add_iff_left.mpr ?_
          have : n^3 = n * n^2 := by exact Nat.pow_succ'
          rw[this]
          refine mul_le_mul ?_ ?_ ?_ ?_
          exact hn
          rfl
          exact sq_nonneg n
          exact Nat.zero_le n
        _ = n^3 + 3 * n^2 + 3 * n^2 + 4 * n^2 := by nlinarith
        _ ≥ n^3 + 3 * n^2 + 3 *n + 1:= by
          rw[ge_iff_le]
          refine add_le_add ?_ ?_
          refine add_le_add ?_ ?_
          refine add_le_add ?_ ?_
          rfl
          rfl
          refine Nat.mul_le_mul ?_ ?_
          rfl
          refine Nat.le_self_pow ?_ n
          norm_num
          refine Nat.one_le_iff_ne_zero.mpr ?_
          refine Nat.mul_ne_zero ?_ ?_
          norm_num
          refine pow_ne_zero 2 ?_
          exact Nat.ne_zero_of_lt hn
        _ = (n+1)^3 := by nlinarith

def nat_even (n : Nat) : Prop := ∃ (k : Nat), n = 2 * k

def nat_odd (n : Nat) : Prop := ∃ (k : Nat), n = 2 * k + 1

theorem Exercise_6_1_16a1 :
    ∀ (n : Nat), nat_even n ∨ nat_odd n := by
    by_induc
    ·
      left
      exists 0
    ·
      intro n ih
      cases ih
      case inl ih =>
        have ⟨k, hk⟩ := ih
        right
        exists k
        rw[← hk]
      case inr ih =>
        have ⟨k, hk⟩ := ih
        left
        exists k + 1
        rw[mul_add, mul_one]
        have: 2 * k + 2 = (2 * k + 1) + 1 := by nlinarith
        rw[this, ← hk]

lemma nonzero_is_successor :
    ∀ (n : Nat), n ≠ 0 → ∃ (m : Nat), n = m + 1 := by
    intro n hn
    exists (n - 1)
    symm
    refine Nat.sub_add_cancel ?_
    exact Nat.one_le_iff_ne_zero.mpr hn

theorem Exercise_6_1_16a2 :
    ∀ (n : Nat), ¬(nat_even n ∧ nat_odd n) := by
  by_induc
  ·
    demorgan
    right
    intro h
    have ⟨k, hk⟩ := h
    have : ∃ l: ℕ, 0 = l + 1 := by
      exists 2 * k
    rw[Nat.exists_eq_add_one] at this
    contradict this
    norm_num
  ·
    intro n ih
    demorgan at ih
    cases ih
    case inl ih =>
      demorgan
      right
      intro h
      contradict ih
      have ⟨k, hk⟩ := h
      exists k
      exact Nat.add_right_cancel hk
    case inr ih =>
      demorgan
      left
      intro h
      contradict ih
      have ⟨k, hk⟩ := h
      have hkne0 : k ≠ 0 := by
        intro hkeq0
        rw[hkeq0, mul_zero] at hk
        symm at hk
        have : ∃ l: ℕ, 0 = n + 1 := by
          exists n
        have : ∃ l: ℕ, 0 = l + 1 := by
          exists n
        rw[Nat.exists_eq_add_one] at this
        contradict this
        norm_num
      have ⟨m ,hm⟩ := nonzero_is_successor k hkne0
      exists m
      have : n + 1 = (2 * m + 1) + 1 := by
        rw[add_assoc]
        have: 1 + 1 = 2 := by norm_num
        rw[this]
        have : 2 * m + 2 = 2 * (m + 1) := by linarith
        rw[this, ← hm]
        exact hk
      exact Nat.add_right_cancel this

theorem Exercise_6_1_16b1 :
    ∀ (n : Int), Even n ∨ Odd n := by
    intro n
    induction n with
    | zero =>
      left
      exists 0
    | pred n ih =>
      cases ih
      case inl ih =>
        right
        have ⟨k, hk⟩ := ih
        rw[← mul_two, mul_comm] at hk
        exists k - 1
        rw[mul_sub, ← hk, mul_one]
        ring
      case inr ih =>
        left
        have ⟨k, hk⟩ := ih
        exists k
        rw[← mul_two, mul_comm]
        have: 2 * k = 2 * k + 1 - 1 := by linarith
        rw[this]
        rw[← hk]
    | succ n ih =>
      cases ih
      case inl ih =>
        right
        have ⟨k, hk⟩ := ih
        rw[← mul_two, mul_comm] at hk
        exists k
        rw[← hk]
      case inr ih =>
        left
        have ⟨k, hk⟩ := ih
        exists k + 1
        have : k + 1 + (k + 1) = (2* k + 1) + 1 := by linarith
        rw[this, ←hk]

theorem Exercise_6_1_16b2 :
    ∀ (n : Int), ¬(Even n ∧ Odd n) := by
    intro n
    induction n with
    | zero =>
      demorgan
      right
      intro h
      have ⟨k, hk⟩ := h
      have h': 2 * k = -1 := by linarith
      rw[Int.mul_eq_neg_one_iff_eq_one_or_neg_one] at h'
      cases h'
      case inl h' =>
        contradict h'.1
        norm_num
      case inr h' =>
        contradict h'.1
        norm_num
    | succ n ih =>
      demorgan at ih
      demorgan
      cases ih
      case inl ih =>
        right
        intro h
        contradict ih
        have ⟨k, hk⟩ := h
        exists k
        rw[← mul_two, mul_comm]
        apply add_right_cancel
        exact hk
      case inr ih =>
        left
        intro h
        contradict ih
        have ⟨k, hk⟩ := h
        rw[← mul_two, mul_comm] at hk
        exists (k-1)
        rw[mul_sub, mul_one, ← hk]
        ring
    | pred n ih =>
      demorgan at ih
      demorgan
      cases ih
      case inl ih =>
        right
        intro h
        contradict ih
        have ⟨k, hk⟩ := h
        exists (k + 1)
        have : k + 1 + (k + 1) = 2 * k + 1 + 1 := by ring
        rw[this, ← hk]
        ring
      case inr ih =>
        left
        intro h
        contradict ih
        have ⟨k, hk⟩ := h
        rw[← mul_two, mul_comm] at hk
        exists k
        rw[← hk]
        ring

theorem Exercise_6_1_17:
    ∀ (n: Nat), ∑ i ∈ Finset.range n, (i + 2) * 2 ^ (i + 1) =  n * 2 ^ (n + 1)  := by
    intro n
    induction n with
    | zero =>
      rw[Finset.range_zero]
      simp
    | succ n ih =>
      rw[Finset.sum_range_succ, ih]
      have: n * 2 ^ (n + 1) + (n + 2) * 2 ^ (n + 1)  = (n + (n + 2)) * 2 ^ (n + 1) := by linarith
      rw[this]
      have : n + (n + 2) = 2 *n + 2 := by linarith
      rw[this]
      have: 2 ^ (n + 1 + 1) = 2^1 * 2 ^ (n + 1) := by exact Nat.pow_add' 2 (n + 1) 1
      rw[this]
      have: (n + 1) * (2 ^ 1 * 2 ^ (n + 1)) = (2* n + 2) * (2 ^ (n + 1)) := by linarith
      rw[this]


/-
Exercise_6_1_18_a
Missing the base case
-/

theorem Exercise_6_1_18b:
    ∀ (n: Nat), ∑ i ∈ Finset.range n, (2 * (i + 1) + 1) * 3 ^ (i + 1) =  n * 3 ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw[Finset.sum_range_succ, ih]
      symm
      have : 3 ^ (n + 1 + 1) = 3 ^ (n + 1) * 3 ^ 1 := by exact rfl
      rw[this]
      have: (n + 1) * (3 ^ (n + 1) * 3 ^ 1)  = (3 * n + 3) * (3 ^ (n + 1)) := by linarith
      rw[this]
      have : n * 3 ^ (n + 1) + (2 * (n + 1) + 1) * 3 ^ (n + 1) = (n + (2 * (n + 1) + 1)) * 3 ^ (n + 1) := by linarith
      rw[this]
      nlinarith

theorem Exercise_6_1_19 (a: ℝ) (ha: a < 0):
    ∀ (n: Nat), (Even n → 0 < a ^ n) ∧ (Odd n → a ^ n < 0) := by
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have ⟨ih, ih'⟩ := ih
    cases Nat.even_xor_odd n
    case inl hn =>
      have ⟨hn, hn'⟩ := hn
      constructor
      ·
        intro hnplusone
        by_contra _
        contradict hn
        rw[← Nat.even_add_one]
        assumption
      ·
        intro hnplusone
        have ih := ih hn
        rw[← mul_lt_mul_left_of_neg ha, mul_zero] at ih
        have hh:  a ^ (n + 1) =  a^ 1 * a ^ (n) := by
          rw[pow_add, mul_comm]
        rw[hh, pow_one]
        exact ih
    case inr hn =>
      have ⟨hn, hn'⟩ := hn
      constructor
      ·
        intro hnplusone
        have ih' := ih' hn
        rw[← mul_lt_mul_left_of_neg ha, mul_zero] at ih'
        nth_rewrite 1 [← pow_one a, ← pow_add, add_comm] at ih'
        exact ih'
      ·
        intro hnplusone
        rw[Nat.odd_add_one] at hnplusone
        by_contra
        exact hnplusone hn

theorem Exercise_6_1_20_a (a b : ℝ ) (ha: 0 < a) (hb: a < b):
    ∀ (n: Nat), 1 ≤ n → 0 < a^n ∧ a^n < b^n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      constructor
      ·
        rw[pow_one]
        exact ha
      ·
        rw[pow_one, pow_one]
        exact hb
    | succ n hn ih =>
      have ⟨ih, ih'⟩ := ih
      constructor
      ·
        rw[← mul_lt_mul_iff_of_pos_left ha, mul_zero] at ih
        nth_rewrite 1 [← pow_one a, ← pow_add, add_comm] at ih
        exact ih
      · rw[pow_add, pow_add, pow_one, pow_one, mul_comm, mul_comm (b ^ n)]
        rw[← mul_lt_mul_iff_of_pos_left ha] at ih'
        apply lt_trans ih'
        have : 0 < b^n := by
          apply lt_trans
          exact ih
          exact (mul_lt_mul_iff_of_pos_left ha).mp ih'

        rw[mul_lt_mul_iff_of_pos_right this]
        exact hb

theorem Exercise_6_1_20_b (a b : ℝ ) (ha: 0 < a) (hb: a < b):
    ∀ (n: Nat), 2 ≤ n → 0 < a^((1:ℝ)/n) ∧ a^((1:ℝ)/ n) < b^((1:ℝ) /n) := by
    intro n hn
    constructor
    · positivity
    ·
      refine Real.rpow_lt_rpow ?_ ?_ ?_
      exact Std.le_of_lt ha
      exact hb
      positivity

theorem Exercise_6_1_20_c (a b : ℝ ) (ha: 0 < a) (hb: a < b):
    ∀ (n: Nat), 1 ≤ n → a * b^n  + b * a^n < a^(n+1) + b^(n+1):= by
    intro n hn
    rw[add_comm, add_comm (a ^ (n + 1)), ← sub_lt_sub_iff]
    have : b * a ^ n - a ^ (n + 1)= a ^ n * (b - a) := by ring
    rw[this]
    have: b ^ (n + 1) - a * b ^ n = b ^ n * (b - a) := by ring
    rw[this, mul_comm, mul_comm (b ^ n )]
    have hpos: 0 < (b - a) := by exact sub_pos.mpr hb
    rw[mul_lt_mul_iff_of_pos_left hpos]
    exact (Exercise_6_1_20_a a b ha hb n hn).2

theorem Exercise_6_1_20_d (a b c d : ℝ ) (ha: 0 < a) (hb: a < b):
    ∀ (n: Nat), 2 ≤ n → ((a + b) / 2)^n < (a^n + b^n) / 2 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      nlinarith
    | succ n hn ih =>
      rw[pow_add, pow_one]
      have : ((a + b) / 2) ^ n * ((a + b) / 2) = ((a + b) / 2) ^ n * ((a + b)) /2:= by ring
      rw[this]
      have: 0 < (2: ℝ) := by norm_num
      rw [div_lt_div_iff_of_pos_right this, mul_comm, add_mul, add_comm (a ^ (n + 1))]
      rw[← sub_lt_sub_iff]
      rw[pow_add, pow_add, pow_one, pow_one, mul_comm (a^n), ← mul_sub, mul_comm (b^n), ← mul_sub]
      refine mul_lt_mul ?_ ?_ ?_ ?_
      exact hb
      rw[sub_le_sub_iff, ← mul_two]
      linarith
      rw[lt_sub_iff_add_lt, zero_add]
      apply pow_lt_pow_left₀
      linarith
      exact Std.le_of_lt ha
      exact Nat.ne_zero_of_lt hn
      apply le_of_lt
      exact lt_trans ha hb
