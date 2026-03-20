import HTPILib.Chap3
namespace HTPI.Exercises

/-
  3.1.1
  (a) Hypotheses: n: Z and n > 1. n is not prime.
  Conclusion: (2 ^ n) - 1 is not prime.
  When n = 6, 6 > 1 and 6 is not prime. (2 ^ 6) - 1 = 63
  7 * 9 = 63 so 63 is not prime. It is right
  (b) When n = 15. 15 is not prime (5 * 3) and greater than 1.
  2^15 - 1 = 32767. 7 divides into 32767. so 32767 is not prime.
  It is true
  (c) when n = 11, n is prime so the antecedent is not met so
  it is still true
-/

/-
  3.1.2
  (a) hypotheses: b^2 > 4ac. Conclusion ax^2 + bc + c = 0 has
  two real solutions
  (b) Because a,b,c are free variables
  (c) Correct. 1 and 1.5 are solutions
  (d) Correct. The hypothesis is not met
-/

/-
  3.1.3
  Hypotheses: n > 2, n is natural number, n is not prime.
  Conclusion: 2n+13 is not prime
  Counter example n = 2. 2 * 2 + 13 = 17. 17 is prime
-/

theorem Exercise_3_1_4 (a b : ℝ) (h1: 0 < a) (h2: a < b) : a ^ 2 < b ^ 2 := by
  have h3: 0 < b - a := sub_pos.mpr h2
  have bPos := lt_trans h1 h2
  have bb := add_lt_add h1 bPos;
  norm_num at bb
  have h3 := (mul_lt_mul_iff_of_pos_right bb).mpr h3
  norm_num at h3
  rw[show (b - a) * (a + b) = (b^2 - a^2) by ring] at h3
  show a ^ 2 < b ^ 2 from lt_add_neg_iff_lt.mp h3
  done

theorem Exercise_3_1_5 (a b: ℝ) (h1: a < b) (h2: b < 0): a^2 > b^2 := by
  have aSquaredNeg := lt_trans' h2 h1
  have BALtASquared := mul_lt_mul_of_neg_left h1 aSquaredNeg
  have BSquaredLtAb :=mul_lt_mul_of_neg_right h1 h2
  have final:= (lt_trans' BALtASquared BSquaredLtAb).gt
  rw[←pow_two a, ←pow_two b] at final
  show a ^ 2 > b ^ 2 from final.gt
  done

theorem Exercise_3_1_6 (a b : ℝ) (h1: 0 < a) (h2: a < b): 1/b < 1/a := by
  have bPos := lt_trans h1 h2
  have abPos := (mul_lt_mul_iff_of_pos_left h1).mpr bPos;
  norm_num at abPos
  have oneOverAbPos: 0 < 1 / (a * b) := one_div_pos.mpr abPos
  have aBNeZero := ne_of_lt abPos
  have final:= (mul_lt_mul_iff_of_pos_left oneOverAbPos).mpr h2
  have simpLeft : 1 / (a * b) * a =  1 / b := by field_simp
  have simpRight : 1 / (a * b) * b = 1 / a := by field_simp
  rw[simpLeft, simpRight] at final
  show 1/b < 1/a from final
  done

theorem Exercise_3_1_7 (a : ℝ) (h1: a^3 > a): a^5 > a := by
  have aNeZero: a ≠ 0 := by
    by_contra AIsZero
    have ZeroCubedIsZero: 0 ^ 3 = 0 := by simp
    rw[AIsZero] at h1
    norm_num at h1
  have aSquaredPos: a^2 ≥ 0 := sq_nonneg a
  have aSquaredNeZero: a^2 ≠ 0 := pow_ne_zero 2 aNeZero
  have aSquaredPos := lt_of_le_of_ne aSquaredPos.le aSquaredNeZero.symm
  have final:= (mul_lt_mul_iff_of_pos_left aSquaredPos).mpr h1
  show a^5 > a from
    calc a^5
      _ = a ^ 2 * a ^ 3 := by ring
      _ > a ^ 2 * a := final
      _ = a ^ 3 := by ring
      _ > a := h1
  done

theorem Exercise_3_1_8 (U : Type) (A B C D: Set U) (x : U)
  (h1: A \ B ⊆ C ∩ D) (h2: x ∈ A) : x ∉ D → x ∈ B := by
  contrapos
  assume xNotInB
  define at h1
  have h3 := h1 (And.intro h2 xNotInB)
  define at h3
  show x ∈ D from h3.right
  done

theorem Exercise_3_1_9 (U: Type) (A B C D: Set U) (x : U)
  (h1: A ∩ B ⊆ C \ D) : x ∈ A → x ∈ D → x ∉ B := by
  assume xInA
  contrapos
  assume xInB
  have xInCButNotInD := h1 (And.intro xInA xInB)
  show x ∉ D from xInCButNotInD.right
  done

theorem Exercise_3_1_10 (a b : ℝ) : a < b → (a + b) / 2 < b := by
  assume aLtB
  have aLtB := (add_lt_add_iff_left b).mpr aLtB
  have bPlusBEquivalanec : b + b = 2 * b := (two_mul b).symm
  rw[bPlusBEquivalanec] at aLtB
  have oneHalfPos: (0 : ℝ) < 1 / 2 := by norm_num
  have final := (mul_lt_mul_iff_of_pos_left oneHalfPos).mpr aLtB
  have simpLeft: 1 / 2 * (b + a) = (a + b) / 2 := by ring
  have simpRight: 1 / 2 * (2 * b) = b := by ring
  rw[simpLeft, simpRight] at final
  show (a + b) / 2 < b from final
  done
