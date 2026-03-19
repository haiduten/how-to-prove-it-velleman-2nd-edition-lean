import HTPILib.Chap3
namespace HTPI.Exercises

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
