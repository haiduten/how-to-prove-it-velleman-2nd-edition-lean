import HTPILib.Chap3
namespace HTPI.Exercises


/- Sections 3.1 and 3.2 -/
-- 1.
theorem Exercise_3_2_1a (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → R) : P → R := by
  assume h3: P
  have h4 : Q := h1 h3
  show R from h2 h4
  done


-- 2.
theorem Exercise_3_2_1b (P Q R : Prop)
    (h1 : ¬R → (P → ¬Q)) : P → (Q → R) := by
  assume h2: P
  contrapos
  assume h4: ¬R
  show ¬Q from h1 h4 h2
  done

-- 3.
theorem Exercise_3_2_2a (P Q R : Prop)
    (h1 : P → Q) (h2 : R → ¬Q) : P → ¬R := by
  assume h3: P
  have h4: Q := h1 h3
  contrapos at h2
  show ¬R from h2 h4
  done

-- 4.
theorem Exercise_3_2_2b (P Q : Prop)
    (h1 : P) : Q → ¬(Q → ¬P) := by
  contrapos
  assume h2: Q → ¬P
  contrapos at h2
  show ¬Q from h2 h1
  done

/- Section 3.3 -/
-- 1.
theorem Exercise_3_3_1
    (U : Type) (P Q : Pred U) (h1 : ∃ (x : U), P x → Q x) :
    (∀ (x : U), P x) → ∃ (x : U), Q x := by
  assume h2: (∀ (x : U), P x)
  obtain (u: U) (h3: P u → Q u) from h1
  have h4: Q u := h3 (h2 u)
  apply Exists.intro u h4
  done

-- 2.
theorem Exercise_3_3_8 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  define
  fix x
  assume h2: x ∈ A
  define
  apply Exists.intro A  (And.intro h1 h2)
  done

-- 3.
theorem Exercise_3_3_9 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  define
  fix x
  assume h2: x ∈ ⋂₀ F
  define at h2
  apply h2
  show A ∈ F from h1
  done

-- 4.
theorem Exercise_3_3_10 (U : Type) (B : Set U) (F : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → B ⊆ A) : B ⊆ ⋂₀ F := by
  define
  fix x
  assume h2: x ∈ B
  define
  fix Q
  assume h3: Q ∈ F
  have h4: B ⊆ Q := h1 Q h3
  define at h4
  show x ∈ Q from h4 h2
  done

-- 5.
theorem Exercise_3_3_13 (U : Type)
    (F G : Set (Set U)) : F ⊆ G → ⋂₀ G ⊆ ⋂₀ F := by
  assume h1: F ⊆ G
  define
  fix x
  assume h2: x ∈ ⋂₀ G
  define
  fix X
  assume h3: X ∈ F
  define at h1
  have h4: X ∈ G := h1 h3
  define at h2
  show x ∈ X from h2 X h4
  done

/- Section 3.4 -/
-- 1.
theorem Exercise_3_4_2 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  fix x
  assume h3: x ∈ A
  apply And.intro
  · -- x ∈ B
    show x ∈ B from h1 h3
    done
  · -- X ∈ C
    show x ∈ C from h2 h3
    done
  done

-- 2.
theorem Exercise_3_4_4 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊈ C) : B ⊈ C := by
  define
  by_contra h3
  define at h2
  quant_neg at h2
  obtain (u: U) (h4: ¬(u ∈ A → u ∈ C)) from h2; conditional at h4;
  have h5: u ∉ C := h4.right
  have h6: u ∈ C := h3 (h1 h4.left)
  show False from h5 h6
  done

-- 3.
theorem Exercise_3_3_12 (U : Type)
    (F G : Set (Set U)) : F ⊆ G → ⋃₀ F ⊆ ⋃₀ G := by
  assume h1: F ⊆ G
  define
  fix x
  assume h2: x ∈ ⋃₀ F
  define at h2
  obtain (A: Set U) (h3: A ∈ F ∧ x ∈ A) from h2
  define at h1
  have h4: A ∈ G :=  h1 h3.left
  define
  apply Exists.intro A (And.intro h4 h3.right)
  done

-- 4.
theorem Exercise_3_3_16 (U : Type) (B : Set U)
    (F : Set (Set U)) : F ⊆ 𝒫 B → ⋃₀ F ⊆ B := by
  assume h1: F ⊆ 𝒫 B
  define
  fix x
  assume h2: x ∈ ⋃₀ F
  define at h2
  obtain (X: Set U) (h3: X ∈ F ∧ x ∈ X) from h2
  have h4: X ∈ 𝒫 B := h1 h3.left
  show x ∈ B from  h4 h3.right
  done

-- 5.
theorem Exercise_3_3_17 (U : Type) (F G : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ⊆ B) :
    ⋃₀ F ⊆ ⋂₀ G := by
    define
    fix x
    assume h2: x ∈ ⋃₀ F
    define
    define at h2
    obtain (A: Set U) (h4: A ∈ F ∧ x ∈ A) from h2
    fix B
    assume h5: B ∈ G
    have h6: x ∈ B := h1 A h4.left B h5 h4.right
    show x ∈ B from h6
    done

-- 6.
theorem Exercise_3_4_7 (U : Type) (A B : Set U) :
    𝒫 (A ∩ B) = 𝒫 A ∩ 𝒫 B := by
    apply Set.ext
    fix X
    apply Iff.intro
    · -- →
      assume h1: X ∈ 𝒫 (A ∩ B)
      define at h1
      define
      apply And.intro
      · -- X ∈ 𝒫 A
        define
        fix x
        assume h2: x ∈ X
        have h4: x ∈ A ∩ B := h1 h2
        define at h4
        show x ∈ A from h4.left
        done
      · -- X ∈ 𝒫 B
        define
        fix x
        assume h2: x ∈ X
        have h4: x ∈ A ∩ B := h1 h2
        define at h4
        show x ∈ B from h4.right
        done
      done
    · -- ←
      assume h1: X ∈ 𝒫 A ∩ 𝒫 B
      define
      fix x
      assume h2: x ∈ X
      define
      define at h1
      have h3: X ∈ 𝒫 A := h1.left
      have h4: X ∈ 𝒫 B := h1.right
      define at h3; define at h4
      show x ∈ A ∧ x ∈ B from And.intro (h3 h2) (h4 h2)
      done
    done

-- 7.
theorem Exercise_3_4_17 (U : Type) (A : Set U) : A = ⋃₀ (𝒫 A) := by
  apply Set.ext
  fix x
  apply Iff.intro
  · -- →
    assume h1: x ∈ A
    define
    apply Exists.intro (A)
    apply And.intro
    · -- A ∈ 𝒫 A
      define
      fix y
      assume h2: y ∈ A
      show y ∈ A from h2
      done
    · -- x ∈ A
      show x ∈ A from h1
      done
    done
  · -- ←
    assume h1: x ∈ ⋃₀ (𝒫 A)
    define at h1
    obtain (X: Set U) h2 from h1
    have h3: X ∈ 𝒫 A := h2.left
    define at h3
    show x ∈ A from h3 h2.right
    done
  done

-- 8.
theorem Exercise_3_4_18a (U : Type) (F G : Set (Set U)) :
    ⋃₀ (F ∩ G) ⊆ (⋃₀ F) ∩ (⋃₀ G) := by
    define
    fix x
    assume h1: x ∈ ⋃₀ (F ∩ G)
    define
    apply And.intro
    · -- x ∈ ⋃₀ F
      define
      define at h1
      obtain (A : Set U) (h2 : A ∈ F ∩ G ∧ x ∈ A) from h1
      apply Exists.intro A
      apply And.intro
      · -- A ∈ F
        have h3 :  A ∈ F ∩ G := h2.left
        define at h3
        show A ∈ F from h3.left
        done
      · -- x ∈ A
        show x ∈ A from h2.right
        done
      done
    · --  ∈ ⋃₀ G
      define
      define at h1
      obtain (A : Set U) (h2 : A ∈ F ∩ G ∧ x ∈ A) from h1
      have h3 := h2.left; define at h3
      apply Exists.intro A
      show A ∈ G ∧ x ∈ A from And.intro h3.right h2.right
      done
    done

-- 9.
theorem Exercise_3_4_19 (U : Type) (F G : Set (Set U)) :
    (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) ↔
      ∀ (A B : Set U), A ∈ F → B ∈ G → A ∩ B ⊆ ⋃₀ (F ∩ G) := by
    apply Iff.intro
    · -- →
      assume h1 : ⋃₀ F ∩ ⋃₀ G ⊆ ⋃₀ (F ∩ G); define at h1
      fix A; fix B
      assume h2 : A ∈ F
      assume h3 : B ∈ G
      define; fix x
      assume h4: x ∈ A ∩ B; define at h4
      define
      apply h1
      define
      apply And.intro
      · -- x ∈ ⋃₀ F
        define
        apply Exists.intro A (And.intro h2 h4.left)
        done
      · -- x ∈ ⋃₀ G
        apply Exists.intro B (And.intro h3 h4.right)
        done
      done
    · -- ←
      assume h1: ∀ (A B : Set U), A ∈ F → B ∈ G → A ∩ B ⊆ ⋃₀ (F ∩ G)
      define
      fix x
      assume h2: x ∈ ⋃₀ F ∩ ⋃₀ G; define at h2
      have h3: x ∈ ⋃₀ F := h2.left; define at h3
      have h4: x ∈ ⋃₀ G := h2.right; define at h4
      obtain (A: Set U) h5 from h3
      obtain (B: Set U) h6 from h4
      have h7: A ∩ B ⊆ ⋃₀ (F ∩ G) := h1 A B h5.left h6.left
      define at h7; apply h7
      define
      show x ∈ A ∧ x ∈ B from And.intro h5.right h6.right
      done
    done

/- Section 3.5 -/
-- 1.
theorem Exercise_3_5_2 (U : Type) (A B C : Set U) :
    (A ∪ B) \ C ⊆ A ∪ (B \ C) := by
  define
  fix x
  assume h1: x ∈ (A ∪ B) \ C
  define at h1
  define
  by_cases on h1.left with h2
  · -- x ∈ A
    apply Or.intro_left
    show x ∈ A from h2
    done
  · -- x ∈ B
    apply Or.intro_right
    define
    have h3: x ∈ B ∧ x ∉ C := And.intro h2 h1.right
    show x ∈ B ∧ x ∉ C from h3
    done


-- 2.
theorem Exercise_3_5_5 (U : Type) (A B C : Set U)
    (h1 : A ∩ C ⊆ B ∩ C) (h2 : A ∪ C ⊆ B ∪ C) : A ⊆ B := by
  fix x
  assume h3: x ∈ A
  define at h2
  have h4: x ∈ A ∨ x ∈ C := by
    apply Or.inl h3
    done
  have h6: x ∈ B ∪ C := h2 h4
  by_cases on h6
  · -- x ∈ B
    show x ∈ B from h6
    done
  · -- x ∈ C
    have h7: x ∈ A ∧ x ∈ C := And.intro h3 h6
    have h8: x ∈ B ∧ x ∈ C := h1 h7
    show x ∈ B from h8.left
    done
  done

-- 3.
theorem Exercise_3_5_7 (U : Type) (A B C : Set U) :
    A ∪ C ⊆ B ∪ C ↔ A \ C ⊆ B \ C := by
  apply Iff.intro
  · -- →
    assume h1: A ∪ C ⊆ B ∪ C
    define; fix x
    assume h2: x ∈ A \ C; define at h2
    have h3: x ∈ A ∨ x ∈ C := by
      apply Or.inl h2.left
      done
    disj_syll (h1 h3) h2.right with h4
    have h5 := And.intro h4 h2.right
    show x ∈ B \ C from h5
    done
  · -- ←
    assume h1: A \ C ⊆ B \ C
    fix x
    assume h2: x ∈ A ∪ C
    or_left with h3
    disj_syll h2 h3
    have h4:  x ∈ B \ C := h1 (And.intro h2 h3)
    show x ∈ B from h4.left
    done
  done

-- 4.
theorem Exercise_3_5_8 (U : Type) (A B : Set U) :
    𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B) := by
  fix Q
  assume h1: Q ∈ 𝒫 A ∪ 𝒫 B
  define; fix x
  assume h2: x ∈ Q
  define at h1
  by_cases on h1
  · -- Q ∈ 𝒫 A
    define; apply Or.inl
    define at h1;
    show x ∈ A from h1 h2
    done
  · -- Q ∈ 𝒫 B
    define; apply Or.inr
    define at h1;
    show x ∈ B from h1 h2
    done
  done

-- 5.
theorem Exercise_3_5_17b (U : Type) (F : Set (Set U)) (B : Set U) :
    B ∪ (⋂₀ F) = {x : U | ∀ (A : Set U), A ∈ F → x ∈ B ∪ A} := by
  apply Set.ext
  fix x
  apply Iff.intro
  · -- →
    assume h1: x ∈ B ∪ ⋂₀ F
    define; fix Q
    assume h2: Q ∈ F
    or_right with h3
    disj_syll h1 h3; define at h1
    show x ∈ Q from h1 Q h2
    done
  · -- ←
    assume h1: x ∈ {x : U | ∀ A ∈ F, x ∈ B ∪ A}; define at h1
    or_right with h2; define
    fix Q; assume h3: Q ∈ F
    have h4 := h1 Q h3
    disj_syll h4 h2
    show x ∈ Q from h4
    done
  done

-- 6.
theorem Exercise_3_5_18 (U : Type) (F G H : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ∪ B ∈ H) :
    ⋂₀ H ⊆ (⋂₀ F) ∪ (⋂₀ G) := by
  define; fix x
  assume h2: x ∈ ⋂₀ H; define at h2
  define; or_right with h3; define
  fix Q
  assume h4: Q ∈ G
  define at h3; quant_neg at h3;
  obtain (P: Set U) (h5: ¬(P ∈ F → x ∈ P)) from h3
  conditional at h5;
  have h6: P ∪ Q ∈ H := h1 P h5.left Q h4;
  have h7: x ∈ P ∪ Q := h2 (P ∪ Q) h6; define at h7
  disj_syll h7 h5.right
  show x ∈ Q from h7
  done

-- 7.
theorem Exercise_3_5_24a (U : Type) (A B C : Set U) :
    (A ∪ B) ∆ C ⊆ (A ∆ C) ∪ (B ∆ C) := by
  fix x
  assume h1: x ∈ (A ∪ B) ∆ C; define at h1
  define
  or_left with h2; define at h2; demorgan at h2
  define
  or_left with h3; define at h3; demorgan at h3
  define
  have h4 := h2.left; define at h4; demorgan at h4
  have h5 := h2.right; define at h5; demorgan at h5
  have h6: x ∉ C \ (A ∪ B) := by
    define ; demorgan
    or_left with h6; define at h6; demorgan at h6
    disj_syll h5 h6.right
    show x ∉ C from h5
    done
  disj_syll h1 h6
  apply And.intro _ h1.right
  disj_syll h4 h1.right
  disj_syll h1.left h4 with h7
  show x ∈ A from h7
  done

/- Section 3.6 -/
-- 1.
theorem Exercise_3_4_15 (U : Type) (B : Set U) (F : Set (Set U)) :
    ⋃₀ {X : Set U | ∃ (A : Set U), A ∈ F ∧ X = A \ B}
      ⊆ ⋃₀ (F \ 𝒫 B) := by
  define
  fix x
  assume h1: x ∈ ⋃₀ {X : Set U | ∃ A ∈ F, X = A \ B}
  define at h1
  obtain Q h2 from h1
  have h3: Q ∈ {X : Set U | ∃ A ∈ F, X = A \ B} := h2.left; define at h3
  have h4: x ∈ Q := h2.right
  define
  obtain P h5 from h3
  apply Exists.intro P
  apply And.intro
  · -- P ∈ F \ 𝒫 B
    define
    apply And.intro h5.left
    define; quant_neg;
    apply Exists.intro x; conditional;
    rewrite [h5.right] at h4; define at h4
    show x ∈ P ∧ x ∉ B from h4
    done
  · -- x ∈ P
    rewrite [h5.right] at h4; define at h4;
    show x ∈ P from h4.left
    done
  done

-- 2.
theorem Exercise_3_5_9 (U : Type) (A B : Set U)
    (h1 : 𝒫 (A ∪ B) = 𝒫 A ∪ 𝒫 B) : A ⊆ B ∨ B ⊆ A := by
  --Hint:  Start like this:
  have h2 : A ∪ B ∈ 𝒫 (A ∪ B) := by
    define
    fix x
    assume h2
    show x ∈ A ∪ B from h2
    done
  rewrite [h1] at h2; define at h2;
  by_cases on h2
  · -- A ∪ B ∈ 𝒫 A
    apply Or.inr
    define
    fix x
    assume h4: x ∈ B
    define at h2
    have h5: x ∈ A ∨ x ∈ B := by
      apply Or.inr
      show x ∈ B from h4
      done
    show x ∈ A from h2 h5
    done
  · -- A ∪ B ∈ 𝒫 B
    apply Or.inl
    define
    fix x
    assume h4: x ∈ A
    have h5: x ∈ A ∨ x ∈ B := by
      apply Or.inl
      show x ∈ A from h4
      done
    show x ∈ B from h2 h5
    done
  done



-- 3.
theorem Exercise_3_6_6b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∪ B = A := by
    set G := {x | x : U}
    exists_unique
    · -- Existence
      apply Exists.intro G
      fix B
      apply Set.ext
      fix x
      apply Iff.intro
      · -- →
        assume h2: x ∈ G ∪ B; define at h2
        by_cases on h2
        · -- x ∈ G
          show x ∈ G from h2
          done
        · -- x ∈ B
          apply Exists.intro x
          show x = x from rfl
          done
        done
      · -- ←
        assume h2: x ∈ G
        define
        show x ∈ G ∨ x ∈ B from Or.inl h2
        done
      done
    · -- Uniqueness
      fix Y; fix Z
      assume h1: ∀ (B : Set U), Y ∪ B = Y
      assume h2: ∀ (B : Set U), Z ∪ B = Z
      have h3: Y ∪ Z = Y := h1 Z
      have h4: Z ∪ Y = Z:= h2 Y
      show Y = Z from
        calc Y
          _ = Y ∪ Z := h3.symm
          _ = Z ∪ Y := union_comm Y Z
          _ = Z := h4
      done
    done

-- 4.
theorem Exercise_3_6_7b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∩ B = A := by
    exists_unique
    · -- Existence
      apply Exists.intro ∅
      fix B
      apply Set.ext
      fix x
      apply Iff.intro
      · -- →
        assume h1: x ∈ ∅ ∩ B
        show x ∈ ∅ from h1.left
        done
      · -- ←
        assume h1: x ∈ ∅
        by_contra
        show False from h1
        done
      done
    · -- Uniqueness
      fix Y; fix Z
      assume h1: ∀ (B : Set U), Y ∩ B = Y
      assume h2: (∀ (B : Set U), Z ∩ B = Z)
      have h3: Y ∩ Z = Y := h1 Z
      have h4: Z ∩ Y = Z := h2 Y
      show Y = Z from
        calc Y
          _ = Y ∩ Z := h3.symm
          _ = Z ∩ Y := Set.inter_comm Y Z
          _ = Z := h4
      done
    done

-- 5.
theorem Exercise_3_6_8a (U : Type) : ∀ (A : Set U),
    ∃! (B : Set U), ∀ (C : Set U), C \ A = C ∩ B := by
    set G := {x | x : U}
    fix A
    exists_unique
    · -- Existence
      apply Exists.intro (G \ A)
      have h2 : G \ A ∈ 𝒫 G := by
        define; fix x
        assume h2: x ∈ G \ A; define at h2
        show x ∈ G from h2.left
        done
      fix C
      apply Set.ext
      fix x
      apply Iff.intro
      · -- →
        assume h4: x ∈ C \ A; define at h4
        apply And.intro h4.left
        define
        apply And.intro _ h4.right
        define
        apply Exists.intro x
        show x = x from rfl
        done
      · -- ←
        assume h4: x ∈ C ∩ (G \ A)
        apply And.intro h4.left
        define at h4
        have h5: x ∈ G \ A := h4.right; define at h5
        show x ∉ A from h5.right
        done
        done
    · -- Uniqueness
      fix Y; fix Z
      rintro h2 h3
      have h10: G \ A = G ∩ Y := h2 G
      have h11: G \ A = G ∩ Z := h3 G
      have h12: G ∩ Y = G ∩ Z := Trans.trans h10.symm h11
      have h4: Y ⊆ G := by
        define
        fix x
        assume h1
        apply Exists.intro x
        show x = x from rfl
        done
      have h5: Z ⊆ G := by
        define
        fix x
        assume h1
        apply Exists.intro x
        show x = x from rfl
        done
      have h13: G ∩ Y = Y := Set.inter_eq_right.mpr h4
      have h14: G ∩ Z = Z := Set.inter_eq_right.mpr h5
      rewrite [h13] at h12; rewrite [h14] at h12
      show Y = Z from h12
      done
    done

-- 6.
theorem Exercise_3_6_10 (U : Type) (A : Set U)
    (h1 : ∀ (F : Set (Set U)), ⋃₀ F = A → A ∈ F) :
    ∃! (x : U), x ∈ A := by
  --Hint:  Start like this:
  set F0 : Set (Set U) := {X : Set U | X ⊆ A ∧ ∃! (x : U), x ∈ X}
  --Now F0 is in theUnique tactic state, with the definition above
  exists_unique
  · -- Existence
    by_contra emptyset
    quant_neg at emptyset
    have AIsEmptySet: A = ∅ := by
      apply Set.ext
      fix x
      apply Iff.intro
      · -- →
        assume h2: x ∈ A
        by_contra
        have h3 := emptyset x
        show False from h3 h2
        done
      · -- ←
        assume h2 : x ∈ ∅
        by_contra
        show False from h2
        done

    rw [AIsEmptySet] at h1
    have emptySetEltEmptySet := h1 {} Set.sUnion_empty
    show False from emptySetEltEmptySet
    done
  · -- Uniqueness
    fix Y; fix Z
    assume hY; assume hZ
    set keySet := {{Y}, {Z}, A\{Y,Z}}
    have unionKeySet : ⋃₀ keySet = A := by
      apply Set.ext
      fix x
      apply Iff.intro
      · -- →
        assume h2: x ∈ ⋃₀ keySet; define at h2
        obtain (Q: Set U) (h3: Q ∈ keySet ∧ x ∈ Q) from h2
        have possibleQs := h3.left; define at possibleQs
        have qElement := h3.right
        by_cases on possibleQs
        · -- Q = {Y}
          rw [possibleQs] at qElement; define at qElement;
          rw [qElement.symm] at hY
          show x ∈ A from hY
          done
        · -- remaining...
          define at possibleQs
          by_cases on possibleQs
          · -- Q = {Z}
            rw [possibleQs] at qElement; define at qElement;
            rw [qElement.symm] at hZ
            show x ∈ A from hZ
            done
          · -- Q ∈ {A \ {Y, Z}}
            define at possibleQs
            rw [possibleQs] at qElement; define at qElement
            show x ∈ A from qElement.left
            done
          done
        done
      · -- ←
        assume h2: x ∈ A
        by_cases h3: (x ∈ A \ {Y, Z})
        · -- x ∈ A \ {Y, Z}
          apply Exists.intro (A \ {Y, Z})
          apply And.intro _ h3
          or_right
          or_right
          show A \ {Y, Z} = A \ {Y, Z} from rfl
          done
        · -- x ∉ A \ {Y, Z}
          define at h3; demorgan at h3; disj_syll h3 h2; define at h3;
          by_cases on h3
          · -- x = Y
            apply Exists.intro {Y}
            apply And.intro _ h3
            define
            or_left
            show {Y} = {Y} from rfl
            done
          · -- x ∈ {Z}
            apply Exists.intro {Z}
            apply And.intro _ h3
            define
            or_right; or_left
            show {Z} = {Z} from rfl
            done
          done
        done
    have h2: A ∈ keySet:= h1 keySet unionKeySet
    define at h2
    by_cases on h2
    · -- A = {Y}
      rw [h2] at hZ
      define at hZ
      show Y = Z from hZ.symm
      done
    · -- rest
      define at h2
      have h3: A ∉ {A \ {Y, Z}} := by
        define
        by_contra h4
        rw [h4] at hY
        define at hY; have hY := hY.right
        define at hY; demorgan at hY; have hY := hY.left
        show False from hY rfl
        done
      disj_syll h2 h3
      rw [h2] at hY
      define at hY
      show Y = Z from hY
      done
    done
  done

/- Section 3.7 -/
-- 1.
theorem Exercise_3_3_18a (a b c : Int)
    (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ (b + c) := by
    obtain (k1 : Int) (hk1: b = a * k1) from h1
    obtain (k2 : Int) (hk2: c = a * k2) from h2
    apply Exists.intro (k1 + k2)
    have final: a * (k1 + k2) = b + c :=
      calc a * (k1 + k2)
        _ = a * k1 + a * k2 := mul_add a k1 k2
        _ = b + c := by rw [← hk1, ← hk2]
    show b + c = a * (k1 + k2) from final.symm
    done

-- 2.
theorem Exercise_3_4_6 (U : Type) (A B C : Set U) :
    A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  apply Set.ext
  fix x : U
  show x ∈ A \ (B ∩ C) ↔ x ∈ A \ B ∪ A \ C from
    calc x ∈ A \ (B ∩ C)
      _ ↔ x ∈ A ∧ ¬(x ∈ B ∧ x ∈ C) := by define: x ∈ A \ (B ∩ C); define: x ∉ B ∩ C; rfl
      _ ↔ x ∈ A ∧ (x ∉ B ∨ x ∉ C) := by demorgan: ¬(x ∈ B ∧ x ∈ C); rfl
      _ ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ A ∧ x ∉ C) := and_or_left
      _ ↔ x ∈ (A \ B) ∪ (A \ C) := by apply Iff.refl
  done

-- 3.
theorem Exercise_3_4_10 (x y : Int)
    (h1 : odd x) (h2 : odd y) : even (x - y) := by
    obtain (k1: Int) (hK1: x = 2 * k1 + 1) from h1
    obtain (k2: Int) (hK2: y = 2 * k2 + 1) from h2
    apply Exists.intro (k1 - k2)
    show x - y = 2 * (k1 - k2) from
      calc x - y
        _ = (2 * k1 + 1) - (2 * k2 + 1) := by rw [hK1, hK2]
        _ = 2 * (k1 - k2) := by ring
    done

-- 4.
theorem Exercise_3_4_27a :
    ∀ (n : Int), 15 ∣ n ↔ 3 ∣ n ∧ 5 ∣ n := by
  fix n
  apply Iff.intro
  · -- →
    assume h1: 15 ∣ n
    apply And.intro
    · -- prove 3 | n
      obtain (k: Int) (hk: n = 15 * k) from h1
      apply Exists.intro (5 * k)
      have final: 3 * (5 * k) = n :=
        calc 3 * (5 * k)
          _ = 3 * 5 * k := by rw[mul_assoc]
          _ = 15 * k := by ring
          _ = n := by rw[hk]
      show n = 3 * (5 * k) from final.symm
      done
    · -- prove 5 | n
      obtain (k: Int) (hk: n = 15 * k) from h1
      apply Exists.intro (3 * k)
      have final: 5 * (3 * k) = n :=
        calc 5 * (3 * k)
          _ = 5 * 3 * k := by rw[mul_assoc]
          _ = 15 * k := by ring
          _ = n := by rw[hk]
      show n = 5 * (3 * k) from final.symm
      done
    done
  · -- ←
    assume h1
    obtain (k3: Int) h3 from h1.left
    obtain (k5: Int) h5 from h1.right
    apply Exists.intro (2 * k5 - k3)
    have final: 15 * (2 * k5 - k3) = n :=
      calc 15 * (2 * k5 - k3)
        _ = 6 * (5 * k5) - 5 * (3 * k3) := by ring
        _ = 6 * n - 5 * n := by rw[←h5, ←h3]
        _= n := by ring
    show n = 15 * (2 * k5 - k3) from final.symm
    done
  done

-- 5.
theorem Like_Exercise_3_7_5 (U : Type) (F : Set (Set U))
    (h1 : 𝒫 (⋃₀ F) ⊆ ⋃₀ {𝒫 A | A ∈ F}) :
    ∃ (A : Set U), A ∈ F ∧ ∀ (B : Set U), B ∈ F → B ⊆ A := by
  define at h1;
  have h2: ⋃₀ F ∈ 𝒫 ⋃₀ F := by
    rw[Set.mem_powerset_iff]
    done
  have h3 := h1 h2; define at h3
  obtain i hi from h3; define: i ∈ {x : Set (Set U) | ∃ A ∈ F, 𝒫 A = x} at hi
  obtain G hG from hi.left
  apply Exists.intro G
  apply And.intro hG.left
  have h4 := hi.right
  rw[hG.right.symm] at h4
  rw[Set.mem_powerset_iff] at h4
  fix B
  assume hB
  have h6: B ⊆ ⋃₀ F := Set.subset_sUnion_of_mem hB
  show B ⊆ G from Set.Subset.trans h6 h4
  done
