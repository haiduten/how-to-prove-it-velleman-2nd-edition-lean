import HTPILib.Chap3
namespace HTPI.Exercises

theorem Exercise_3_7_1 (U : Type) (F: Set (Set U)) :
  ∃! (A : Set U), F ⊆ 𝒫 A ∧ ∀ (B : Set U), F ⊆ 𝒫 B → A ⊆ B := by
  exists_unique
  · -- existence
    apply Exists.intro (⋃₀ F)
    apply And.intro
    · -- prove F ⊆ 𝒫 ⋃₀ F
      fix Y
      assume h1: Y ∈ F
      fix x
      assume h2: x ∈ Y
      define
      apply Exists.intro Y
      show Y ∈ F ∧ x ∈ Y from And.intro h1 h2
      done
    · -- prove ∀ (B : Set U), F ⊆ 𝒫 B → ⋃₀ F ⊆ B
      fix B
      assume h1: F ⊆ 𝒫 B
      fix x
      assume h2: x ∈ ⋃₀ F
      define at h2
      obtain (Q : Set U) (h3: Q ∈ F ∧ x ∈ Q) from h2
      show x ∈ B from h1 h3.left h3.right
      done
    done
  · -- uniqueness
    fix Y
    fix Z
    rintro h1 h2
    have h3: Y ⊆ Z := h1.right Z h2.left
    have h4: Z ⊆ Y := h2.right Y h1.left
    show Y = Z from Set.Subset.antisymm h3 h4
    done
  done

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
