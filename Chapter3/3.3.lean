import HTPILib.Chap3
namespace HTPI.Exercises

theorem Exercise_3_3_1
    (U : Type) (P Q : Pred U) (h1 : ∃ (x : U), P x → Q x) :
    (∀ (x : U), P x) → ∃ (x : U), Q x := by
  assume h2: (∀ (x : U), P x)
  obtain (u: U) (h3: P u → Q u) from h1
  have h4: Q u := h3 (h2 u)
  apply Exists.intro u h4
  done

theorem Exercise_3_3_8 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  define
  fix x
  assume h2: x ∈ A
  define
  apply Exists.intro A  (And.intro h1 h2)
  done

theorem Exercise_3_3_9 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  define
  fix x
  assume h2: x ∈ ⋂₀ F
  define at h2
  apply h2
  show A ∈ F from h1
  done

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
