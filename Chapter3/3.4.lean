import HTPILib.Chap3
namespace HTPI.Exercises

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
