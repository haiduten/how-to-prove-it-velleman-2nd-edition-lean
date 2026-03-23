import HTPILib.Chap3
namespace HTPI.Exercises

theorem Exercise_3_2_1a (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → R) : P → R := by
  assume h3: P
  have h4 : Q := h1 h3
  show R from h2 h4
  done

theorem Exercise_3_2_1b (P Q R : Prop)
    (h1 : ¬R → (P → ¬Q)) : P → (Q → R) := by
  assume h2: P
  contrapos
  assume h4: ¬R
  show ¬Q from h1 h4 h2
  done

theorem Exercise_3_2_2a (P Q R : Prop)
    (h1 : P → Q) (h2 : R → ¬Q) : P → ¬R := by
  assume h3: P
  have h4: Q := h1 h3
  contrapos at h2
  show ¬R from h2 h4
  done

theorem Exercise_3_2_2b (P Q : Prop)
    (h1 : P) : Q → ¬(Q → ¬P) := by
  contrapos
  assume h2: Q → ¬P
  contrapos at h2
  show ¬Q from h2 h1
  done

theorem Exercise_3_2_3 (U: Type) (A B C : Set U) (x: U)
  (h1: A ⊆ C) (h2: B ∩ C = ∅): x ∈ A → x ∉ B := by
  assume xInA
  have xInC := h1 xInA
  by_contra xInB;
  have xInBAndC: x ∈ B ∩ C := And.intro xInB xInC
  rw[h2] at xInBAndC;
  show False from xInBAndC
  done

theorem Exercise_3_2_4 (U: Type) (A B C: Set U) (x: U)
  (h1: (A \ B) ∩ C = ∅) (h2: x ∈ A): x ∈ C → x ∈ B := by
  assume xInC
  by_contra xNotInB
  have xInANotBAndC: x ∈ A \ B ∩ C := And.intro (And.intro h2 xNotInB) xInC
  rw[h1] at xInANotBAndC
  show False from xInANotBAndC
  done

theorem Exercise_3_2_5 (U: Type) (x: U) (A B C: Set U):
 x ∉ (A \ B) ∩ (B \ C) := by
 by_contra h1;
 define at h1;
 have xInANotB := h1.left; define at xInANotB
 have xInBNotC := h1.right; define at xInBNotC
 show False from xInANotB.right xInBNotC.left
 done

theorem Exercise_3_2_6 (U: Type) (a: U) (A B C: Set U)
  (h1: A ∩ C ⊆ B) (h2: a ∈ C): a ∉ A \ B := by
  by_contra h3; define at h3
  have xInB := h1 (And.intro h3.left h2)
  show False from h3.right xInB
  done

theorem Exercise_3_2_7 (U: Type) (a: U) (A B C: Set U)
  (h1: A ⊆ B) (h2: a ∈ A) (h3: a ∉ B \ C): a ∈ C := by
  by_contra aNotInC
  define at h3; demorgan at h3
  disj_syll h3 aNotInC
  have aInB := h1 h2
  show False from h3 aInB
  done

theorem Exercise_3_2_8 (x y: ℝ) (h1: y + x = 2 * y - x)
  (h2: x ≠ 0 ∨ y ≠ 0): y ≠ 0 := by
  by_contra yIsZero
  disj_syll h2 yIsZero
  apply_fun (fun z => ((z + x - y)/2)) at h1
  have simpLeft: (y + x + x - y) / 2 = x := by ring
  have simpRight: (2 * y - x + x - y) / 2 = y / 2 := by ring
  rw[simpLeft, simpRight, yIsZero] at h1
  have h1: x = 0 :=
    calc x
      _ = 0 / 2 := h1
      _ = 0 := by norm_num
  show False from h2 h1
  done

theorem Exercise_3_2_9 (a b: ℝ) (h1: a ≠ 0) (h2: b ≠ 0):
  a < 1 / a →  1 / a < b → b < 1 / b → a < -1 := by
  assume h3; assume h4; assume h5
  have aSquaredPos: a * a ≥ 0 := mul_self_nonneg a
  by_contra contra
  have contra := not_lt.mp contra
  by_cases ha: (0 ≤ a)
  · -- a is pos
    have ha := lt_or_eq_of_le ha
    disj_syll ha h1.symm
    have h6 := (mul_lt_mul_of_pos_left h3 ha)
    rw[(by field_simp:  a * (1 / a) = 1 )] at h6
    have h6 := Real.sqrt_lt_sqrt (mul_self_nonneg a) h6
    rw[(by norm_num: √1 = 1),Real.sqrt_mul_self (le_of_lt ha)] at h6
    have h7: (1: ℝ) < 1 /a := one_lt_one_div ha h6
    have bPos := lt_trans (by norm_num: (0: ℝ) < 1) (lt_trans h7 h4)
    have h8 := (mul_lt_mul_of_pos_left h5 bPos)
    rw[(by field: b * (1 / b) = 1)] at h8
    have h8 := Real.sqrt_lt_sqrt (mul_self_nonneg b) h8
    rw[(by norm_num: √1 = 1),Real.sqrt_mul_self (le_of_lt bPos)] at h8
    have d := lt_irrefl 1 (lt_trans (lt_trans h7 h4) h8)
    show False from d
    done
  · -- a is neg
    have ha: a < 0 := lt_of_not_ge ha
    have h6 := (mul_lt_mul_of_neg_left h3 ha)
    have simpLeft: a * (1 / a) = 1 := by field_simp
    rw[simpLeft] at h6
    have h6 := Real.sqrt_lt_sqrt (by norm_num: (0: ℝ) ≤ 1) h6
    have simpLeft: √1 = 1 := by norm_num
    rw[simpLeft, Real.sqrt_mul_self_eq_abs] at h6
    have h6 := lt_abs.mp h6
    have h7: 1 ≥ a :=
      calc 1
      _ ≥ (0: ℝ) := by norm_num
      _ ≥ a := nonpos_of_mul_nonneg_right aSquaredPos ha
    have h7 := not_lt.mpr h7.le
    disj_syll h6 h7
    have h6 := (mul_lt_mul_of_neg_left h6 (by norm_num: (-1: ℝ) < 0))
    rw[(by norm_num : -1 * -a = a), (by norm_num : (-1: ℝ) * 1 = -1)] at h6
    have h7: (-1: ℝ) < a ∨ -1 = a := lt_or_eq_of_le contra
    by_cases on h7
    · -- -1 < a
      show False from lt_irrefl a (lt_trans h6 h7)
      done
    · -- -1 = a
      rw[h7.symm] at h6
      show False from lt_irrefl (-1: ℝ) h6
      done
    done
  done

theorem Exercise_3_2_10 (x y: ℝ): x^2 * y = 2 * x + 7 → y ≠ 0 → x ≠ 0 := by
  assume h1
  assume h2
  by_contra h3
  rw[h3, (by norm_num:  0 ^ 2 * y  = 0), (by norm_num: (2: ℝ) * 0 + 7 = 7)] at h1
  have final: (0: ℝ) ≠ 0 :=
    calc 0
    _ = 7 := h1
    _ ≠ 0 := by norm_num
  show False from final (by norm_num: (0: ℝ) = 0)
  done

theorem Exercise_3_2_11 (x y: ℝ):
  x ≠ 0 → y = (3 * x^2 + 2 * y) / (x^2 + 2) → y = 3 := by
  assume h1
  assume h2
  apply_fun (fun z => ((z * (x^2 + 2)) - 2 * y) / x^2) at h2
  have simpLeft: (y * (x ^ 2 + 2) - 2 * y) / x ^ 2 = y := by field
  have simpRight: ((3 * x ^ 2 + 2 * y) / (x ^ 2 + 2) * (x ^ 2 + 2) - 2 * y) / x ^ 2 = 3 := by field
  rw[simpLeft, simpRight] at h2
  show y = 3 from h2

/-
Exercise 3.2.12
(a) Incorrect application of negation. Assume the conclusion to be false is x = 3 or y = 8
(b) x = 2 and y = 8
-/

/-
Exercise 3.2.13
(a) B ⊆ C means ∀ x ∈ B → x ∈ C. Since x ∉ B, we cannot conclude anything about
whether its part of C.
(b) Let A = set of even natural numbers. Let B = set of odd natural numbers. Let C = set of natural numbers
-/

/-
Skipping truth table problems from Exercise 3.2.14 to Exercise 3.2.17...
-/

/-
Exercise 3.2.18
No. If we assume y = 4. Then x^2 = 9. And x could be -3 and there's no contradiction
-/
