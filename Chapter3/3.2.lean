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
