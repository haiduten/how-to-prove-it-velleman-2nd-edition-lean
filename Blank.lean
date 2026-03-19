import HTPILib.HTPIDefs
namespace HTPI



example (U : Type) (A B C : Set U) (h1 : A ⊆ B ∪ C)
    (h2 : ∀ (x : U), x ∈ A → x ∉ B) : A ⊆ C := by
  define
  fix y
  assume h3: y ∈ A
  have h4: y ∉ B := h2 y h3
  define at h1;
  have h5: y ∈ B ∪ C := h1 h3
  define at h5; conditional at h5
  show y ∈ C from h5 h4
  done

theorem Example_3_2_4
    (P Q R : Prop) (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h1: ¬R
  assume h2: P
  have h3: Q → R := h h2
  contrapos at h3
  show ¬Q from h3 h1
  done

theorem extremely_easy (P : Prop) (h : P) : P := h

theorem very_easy
    (P Q : Prop) (h1 : P → Q) (h2 : P) : Q := h1 h2

theorem easy (P Q R : Prop) (h1 : P → Q)
    (h2 : Q → R) (h3 : P) : R := h2 (h1 h3)

theorem two_imp (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → ¬R) : R → ¬P := by
  assume h3: R
  contrapos at h2
  have h4: ¬Q := h2 h3
  contrapos at h1
  show ¬P from h1 h4
  done

theorem Example_3_2_5_simple
    (B C : Set Nat) (a : Nat)
    (h1 : a ∈ B) (h2 : a ∉ B \ C) : a ∈ C := by
  define at h2; demorgan at h2; conditional at h2;
  show a ∈ C from h2 h1
  done

theorem Example_3_2_4_v2 (P Q R : Prop)
    (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  by_contra h4
  have h5: R := h h3 h4
  show False from absurd h5 h2
  done


theorem Example_3_2_4_v3 (P Q R : Prop)
    (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  contradict h4 with h4
  have h5: Q → R := h h3
  contrapos at h5
  show ¬Q from h5 h2
  done

theorem Like_Example_3_2_5
    (U : Type) (A B C : Set U) (a : U)
    (h1 : a ∈ A) (h2 : a ∉ A \ B)
    (h3 : a ∈ B → a ∈ C) : a ∈ C := by
  define at h2; demorgan at h2; conditional at h2;
  apply h3 _
  show a ∈ B from h2 h1
  done

example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), P x → ¬Q x)
    (h2 : ∀ (x : U), Q x) :
    ¬∃ (x : U), P x := by
  quant_neg
  fix y
  have h3: Q y := h2 y
  have h4: P y → ¬Q y := h1 y
  contrapos at h4
  show ¬P y from h4 h3
  done


example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), ∃ (y : U), P x → ¬ Q y)
    (h2 : ∃ (x : U), ∀ (y : U), P x → Q y) :
    ∃ (x : U), ¬P x := by
  obtain (u: U) (h3: ∀ (y : U), P u → Q y) from h2
  have h4: ∃ (y : U), P u → ¬Q y := h1 u
  obtain (z: U) (h5: P u → ¬Q z) from h4
  have h6: P u → Q z := h3 z
  apply Exists.intro u
  by_contra h7
  show False from (h5 h7) (h6 h7)
  done

theorem Example_3_3_5 (U : Type) (B : Set U)
    (F : Set (Set U)) : ⋃₀ F ⊆ B → F ⊆ 𝒫 B := by
  assume h1: ⋃₀ F ⊆ B
  define
  fix A
  assume h2: A ∈ F
  define
  fix x
  assume h3: x ∈ A
  apply h1; define
  apply Exists.intro A (And.intro h2 h3)
  done

theorem Like_Example_3_4_1 (U : Type)
    (A B C D : Set U) (h1 : A ⊆ B)
    (h2 : ¬∃ (c : U), c ∈ C ∩ D) :
    A ∩ C ⊆ B \ D := by
  define
  fix x
  assume h3: x ∈ A ∩ C
  define
  define at h3
  have h4: x ∈ B := h1 h3.left
  quant_neg at h2
  have h5: x ∉ C ∩ D := h2 x; define at h5; demorgan at h5; conditional at h5
  apply And.intro h4
  show x ∉ D from h5 h3.right
  done

example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), P x ↔ Q x) :
    (∃ (x : U), P x) ↔ ∃ (x : U), Q x := by
  apply Iff.intro _ _
  · -- Proof that ∃ (x : U), P x) → ∃ (x : U), Q x
    assume h2: (∃ (x : U), P x)
    obtain (u: U) (h3: P u) from h2
    have h4: Q u := (h1 u).ltr h3
    apply Exists.intro u h4
    done
  · --  Proof that (∃ (x : U), Q x) → ∃ (x : U), P x
    assume h2: (∃ (x : U), Q x)
    obtain (u: U) (h3: Q u) from h2
    have h4: P u := (h1 u).rtl h3
    apply Exists.intro u h4
    done

  done


theorem Example_3_5_2
    (U : Type) (A B C : Set U) :
    A \ (B \ C) ⊆ (A \ B) ∪ C := by
    define
    fix x
    assume h1: x ∈ A \ (B \ C)
    define
    define at h1
    have h2: x ∉ B \ C := h1.right
    define at h2; demorgan at h2
    by_cases on h2 with h3
    · -- x ∉ B
      apply Or.inl
      show x ∈ A \ B from And.intro h1.left h3
      done
    · -- x ∈ C
      apply Or.inr
      show x ∈ C from h3
      done
    done

example (U : Type) (A B C : Set U)
    (h1 : A \ B ⊆ C) : A ⊆ B ∪ C := by
    define
    fix x
    assume h2: x ∈ A
    define
    or_right with h3
    have h4: x ∈ A ∧ x ∉ B := And.intro h2 h3
    define at h1
    show x ∈ C from h1 h4
    done

example
    (U : Type) (A B C : Set U) (h1 : A ⊆ B ∪ C)
    (h2 : ¬∃ (x : U), x ∈ A ∩ B) : A ⊆ C := by
    define
    fix x
    assume h3: x ∈ A
    quant_neg at h2
    have h4: x ∉ A ∩ B := h2 x; define at h4; demorgan at h4;
    disj_syll h4 h3
    define at h1
    have h5: x ∈ B ∪ C := h1 h3
    disj_syll h5 h4
    show x ∈ C from h5
    done

theorem empty_union {U : Type} (B : Set U) :
    ∅ ∪ B = B := by
  apply Set.ext
  fix u
  apply Iff.intro
  · -- →
    assume h1: u ∈ ∅ ∪ B
    have h2: u ∉ ∅ := by
      define
      by_contra h3
      show False from h3
      done
    disj_syll h1 h2

    show u ∈ B from h1
    done
  · -- ←
    assume h1: u ∈ B
    show u ∈ ∅ ∪ B from Or.inr h1
    done
  done

theorem union_comm {U : Type} (X Y : Set U) :
    X ∪ Y = Y ∪ X := by
    apply Set.ext
    fix x
    apply Iff.intro
    · -- →
      assume h1: x ∈ X ∪ Y
      by_cases on h1
      · -- x ∈ X
        show x ∈ Y ∪ X from Or.inr h1
        done
      · -- X ∈ Y
        show x ∈ Y ∪ X from Or.inl h1
        done
      done
    · -- ←
      assume h1: x ∈ Y ∪ X
      by_cases on h1
      · -- X ∈ Y
        show x ∈ X ∪ Y from Or.inr h1
        done
      · -- x ∈ X
        show x ∈ X ∪ Y from Or.inl h1
        done
      done
    done



theorem Example_3_6_2 (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U),
    A ∪ B = B := by
    exists_unique
    · -- Existence
      apply Exists.intro ∅
      fix B
      show ∅ ∪ B = B from empty_union B
      done
    · -- Uniqueness
      fix Y
      fix Z
      assume h1: ∀ (B : Set U), Y ∪ B = B
      assume h2: ∀ (B : Set U), Z ∪ B = B
      have h3: Y ∪ Z = Z := h1 Z
      have h4: Z ∪ Y = Y := h2 Y
      show Y = Z from
        calc Y
          _ = Z ∪ Y := h4.symm
          _ = Y ∪ Z := union_comm Z Y
          _ = Z := h3
      done
    done



theorem Example_3_6_4 (U : Type) (A B C : Set U)
    (h1 : ∃ (x : U), x ∈ A ∩ B)
    (h2 : ∃ (x : U), x ∈ A ∩ C)
    (h3 : ∃! (x : U), x ∈ A) :
    ∃ (x : U), x ∈ B ∩ C := by
    obtain (u1) h4 from h1
    obtain (u2) h5 from h2
    define at h3
    obtain u h6 from h3
    define at h4; define at h5
    have h7: u1 = u2 := by
      have h7: u1 = u := h6.right u1 h4.left
      have h6: u2 = u := h6.right u2 h5.left
      show u1 = u2 from
        calc u1
          _ = u := h7
          _ = u2 := h6.symm
      done
    apply Exists.intro u1; define
    apply And.intro h4.right
    rewrite [h7.symm] at h5
    show u1 ∈ C from h5.right
    done

theorem Theorem_3_3_7 :
    ∀ (a b c : Int), a ∣ b → b ∣ c → a ∣ c := by
  fix a; fix b; fix c
  assume h1:  a ∣ b; define at h1
  assume h2: b ∣ c; define at h2
  obtain (k: Int) h3 from h1
  obtain (k_2: Int) h4 from h2
  rewrite [h3] at h4
  apply Exists.intro (k * k_2)
  rewrite [mul_assoc a k k_2] at h4
  show c = a * (k * k_2) from h4
  done

theorem Theorem_3_4_7 :
    ∀ (n : Int), 6 ∣ n ↔ 2 ∣ n ∧ 3 ∣ n := by
  fix n : Int
  apply Iff.intro
  · -- →
    assume h1: 6 ∣ n
    obtain (k : Int) h2 from h1
    apply And.intro
    · -- 2 | n
      define
      apply Exists.intro (3 * k)
      rw [← mul_assoc]
      show n = 2 * 3 * k from h2
      done
    · -- 3 | n
      define
      apply Exists.intro (2 * k)
      rw [← mul_assoc]
      show  n = 3 * 2 * k from h2
      done
    done
  · -- ←
    assume h1
    have h2 := h1.left; define at h2
    have h3 := h1.right; define at h3
    obtain (k1 : Int) h4 from h2
    obtain (k2 : Int) h5 from h3
    apply Exists.intro (k1 - k2)
    have final: 6 * (k1 - k2) = n :=
      calc 6 * (k1 - k2)
        _ = 6 * k1 - 6 * k2 := mul_sub_left_distrib 6 k1 k2
        _ = 3 * 2 * k1 - 2 * 3 * k2 := rfl
        _ = 3 * (2 * k1) - 2 * (3 * k2) := by rw [mul_assoc]; rw [mul_assoc]
        _ = 3 * n -  2 * n := by rw [← h4, ← h5]
        _ = n * 3 - n * 2 := by rw [mul_comm 3 n, mul_comm 2 n]
        _ = n * (3 - 2) := by rw [← mul_sub_left_distrib]
        _ = n * 1 := rfl
        _ = n := Int.mul_one n
    show n = 6 * (k1 - k2) from final.symm
    done
  done

theorem Example_3_5_4 (x : Real) (h1 : x ≤ x ^ 2) : x ≤ 0 ∨ 1 ≤ x := by
  or_right with h2;
  have h3 : x > 0 := lt_of_not_ge h2
  have h4: 1 * x ≤ x * x :=
    calc 1 * x
      _ = x * 1 := mul_comm 1 x
      _ = x := mul_one x
      _ ≤ x ^ 2 := h1
      _ = x * x := by ring
  show 1 ≤ x from le_of_mul_le_mul_right h4 h3
  done
