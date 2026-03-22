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
  (a < 1 / a) ∧ (1 / a < b) ∧ (b < 1 / b) → a < -1 := by

  done
