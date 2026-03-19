import HTPILib.Chap3
namespace HTPI.Exercises

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
