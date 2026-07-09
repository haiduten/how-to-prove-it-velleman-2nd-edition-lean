import HTPILib.Chap5
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Function
namespace HTPI.Exercises



/-
 Exercise 5_3_1: the person sitting to the left

 Exercise 5_3_2: the missing element in X of A
-/

theorem Exercise_5_3_3_1:
  let f: ℝ → ℝ  := fun x => (2 * x + 5) / 3
  Function.Injective f ∧ Function.Surjective f := by
  constructor
  ·
    intro x y hxy
    field_simp at hxy
    nlinarith
  · intro y
    exists ((3 * y) - 5) / 2
    simp
    field_simp
    linarith

theorem Exercise_5_3_3_2:
    let f: ℝ → ℝ  := fun x => (2 * x + 5) / 3
    let g : ℝ → ℝ := fun x => ((3 * x) - 5) / 2
    (g ∘ f) = id ∧ (f ∘ g) = id := by
  constructor
  repeat
  ·
    funext x
    simp
    field_simp
    linarith

noncomputable def cbrt (x : ℝ) : ℝ :=
  if 0 ≤ x  then x ^ (1/3 : ℝ) else -((-x) ^ (1/3 : ℝ))

theorem Exercise_5_3_4_1:
    let f: ℝ → ℝ := fun x => (2: ℝ) * x^ (3: ℝ) - (3: ℝ)
    Function.Injective f ∧ Function.Surjective f := by
  constructor
  ·
    intro x y hxy
    dsimp at hxy
    have hxy_real : x ^ (3 : ℝ) = y ^ (3 : ℝ) := by linarith
    cases (Classical.em ((0: ℝ) ≤ x))
    case inl h =>
      have hx3 : (0: ℝ) ≤ x^ (3: ℝ) := by exact Real.rpow_nonneg h 3
      have hy3 : (0: ℝ) ≤ y^ (3: ℝ) := by
        calc
          (0: ℝ) ≤ x^ (3: ℝ) := by exact hx3
          _ = y^ (3: ℝ) := by rw[hxy_real]
      have hy : (0: ℝ) ≤ y := by
        have: Odd 3:= by
          define
          exists 1

        have hy3': 0 ≤ y ^ 3 := by
          norm_cast at hy3

        exact (Odd.pow_nonneg_iff (this)).mp hy3'


      calc
        x = x ^ (1: ℝ) := by exact Eq.symm (Real.rpow_one x)
        _ =  (x) ^((1 / 3: ℝ) * (3: ℝ)) := by
          symm
          have : (1 / 3: ℝ) * (3: ℝ) = 1 := by field_simp
          rw[this]
        _ = (x^ (3: ℝ))^(1 / 3 : ℝ) := by
          rw[← Real.rpow_mul h, mul_comm, Real.rpow_mul h]
         _ = (y ^ (3: ℝ)) ^ (1 / 3: ℝ) := by rw[hxy_real]
         _ = (y) ^ ((3: ℝ)* (1 / 3: ℝ)) := by
            rw[ Real.rpow_mul hy]
        _ = y := by simp
    case inr h =>
      push_neg at h
      have hx: 0 < -x := by linarith
      have hx: 0 ≤ -x := by exact Std.le_of_lt hx

      have hxnegx: (x) ^((1 / 3: ℝ) * (3: ℝ)) = -(-x) ^((1 / 3: ℝ) * (3: ℝ)) := by simp
      have hxcubed : x^ (3: ℝ) < 0 := by
        have: Odd 3:= by
          define
          exists 1
        have := Odd.pow_neg this h
        rw[← Real.rpow_natCast x 3] at this
        exact this

      have hycubed: y^(3: ℝ) < 0 := by
        rw[← hxy_real]
        assumption

      have hy: y < (0: ℝ) := by
        have: Odd 3:= by
          define
          exists 1
        have hycubed': y^3 < 0 := by
          norm_cast at hycubed
        exact (Odd.pow_neg_iff (this)).mp hycubed'

      have hy': 0 < -y := by linarith
      have hy': 0 ≤ -y := by exact Std.le_of_lt hy'

      have hynegy:  (y) ^((1 / 3: ℝ) * (3: ℝ)) = -(-y) ^((1 / 3: ℝ) * (3: ℝ)) := by simp

      have : (-x)^3 = -x^3:= by
        refine Odd.neg_pow ?_ x
        exists 1

      have :(-x)^(3: ℝ) = -x^(3: ℝ) := by
        norm_cast

      calc
        x =  (x) ^((1 / 3: ℝ) * (3: ℝ)) := by simp
        _ = -(-x) ^((1 / 3: ℝ) * (3: ℝ))  := by rw[hxnegx]
        _ = -(-x) ^((3: ℝ) * (1 / 3: ℝ)) := by simp
        _ = -((-x)^ (3: ℝ))^(1 / 3: ℝ) := by rw[ Real.rpow_mul hx]
        _ = -((-y)^ (3: ℝ))^(1 / 3: ℝ) := by
          rw[this, hxy_real]
          have : (-y)^3 = -y^3:= by
            refine Odd.neg_pow ?_ y
            exists 1

          have :(-y)^(3: ℝ) = -y^(3: ℝ) := by
            norm_cast
          rw[this]
        _ = -(-y) ^((3: ℝ) * (1 / 3: ℝ)) := by rw[ ← Real.rpow_mul hy']
        _ = y := by simp
  ·
    intro y
    simp
    exists cbrt ((y  +  (3: ℝ))/ (2: ℝ))
    cases (Classical.em ((0: ℝ) ≤ ((y  +  (3: ℝ))/ (2: ℝ))))
    case inl h =>
      dsimp[cbrt]
      rw[if_pos h]
      rw [← Real.rpow_natCast]
      rw[← Real.rpow_mul h]
      simp
      field_simp
      simp

    case inr h =>
      dsimp[cbrt]
      rw[if_neg h]
      push_neg at h
      have h': 0 ≤  -((y  +  (3: ℝ))/ (2: ℝ)) := by linarith
      rw [Odd.neg_pow (by use 1; simp)]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul h']
      field_simp
      simp
      field_simp
      simp


theorem Exercise_5_3_4_2_helper: Function.Injective fun (x : ℝ) => x ^ (3: ℝ) := by
  intro a b hab
  simp at hab
  rw [← Real.rpow_natCast, ← Real.rpow_natCast] at hab

  cases (Classical.em (0 ≤ a))
  case inl h =>
    have ha3 : (0: ℝ) ≤ a^ (3: ℝ) := by exact Real.rpow_nonneg h 3
    have hb3 : (0: ℝ) ≤ b^ (3: ℝ) := by
      calc
        (0: ℝ) ≤ a^ (3: ℝ) := by exact ha3
        _ = b^ (3: ℝ) := by
          exact hab
    have hb : (0: ℝ) ≤ b := by
      have: Odd 3:= by
        define
        exists 1

      have hb3': 0 ≤ b ^ 3 := by
        norm_cast at hb3

      exact (Odd.pow_nonneg_iff (this)).mp hb3'

    calc
      a = a ^((3: ℝ) * (1 / 3: ℝ)) := by simp
      _ = _ := by
        rw[ Real.rpow_mul h]
        simp at hab
        norm_cast
        rw[hab]
        rw [← Real.rpow_natCast]
        rw[←  Real.rpow_mul hb]
        simp
  case inr h =>
    dsimp at hab
    have hxy_real : a ^ (3 : ℝ) = b ^ (3 : ℝ) := by linarith
    push_neg at h
    have ha: 0 < -a := by linarith
    have ha: 0 ≤ -a := by exact Std.le_of_lt ha
    have hacubed : a^ (3: ℝ) < 0 := by
      have: Odd 3:= by
        define
        exists 1
      have := Odd.pow_neg this h
      rw[← Real.rpow_natCast a 3] at this
      exact this

    have hbcubed: b^(3: ℝ) < 0 := by
      simp at hab
      norm_cast
      rw[← hab]
      rw [← Real.rpow_natCast]
      assumption

    have hb: b < (0: ℝ) := by
      have: Odd 3:= by
        define
        exists 1
      have hbcubed': b^3 < 0 := by
        norm_cast at hbcubed
      exact (Odd.pow_neg_iff (this)).mp hbcubed'

    have hb': 0 < -b := by linarith
    have hb': 0 ≤ -b := by exact Std.le_of_lt hb'

    have hanega: (a) ^((1 / 3: ℝ) * (3: ℝ)) = -(-a) ^((1 / 3: ℝ) * (3: ℝ)) := by simp

    have : (-a)^3 = -a^3:= by
      refine Odd.neg_pow ?_ a
      exists 1

    have :(-a)^(3: ℝ) = -a^(3: ℝ) := by
      norm_cast
    calc
      a =  (a) ^((1 / 3: ℝ) * (3: ℝ)) := by simp
      _ = -(-a) ^((1 / 3: ℝ) * (3: ℝ))  := by rw[hanega]
      _ = -(-a) ^((3: ℝ) * (1 / 3: ℝ)) := by simp
      _ = -((-a)^ (3: ℝ))^(1 / 3: ℝ) := by rw[ Real.rpow_mul ha]
      _ = -((-b)^ (3: ℝ))^(1 / 3: ℝ) := by

        rw[this, hab]
        have : (-b)^3 = -b^3:= by
          refine Odd.neg_pow ?_ b
          exists 1

        have :(-b)^(3: ℝ) = -b^(3: ℝ) := by
          norm_cast
        rw[this]
      _ = -(-b) ^((3: ℝ) * (1 / 3: ℝ)) := by rw[ ← Real.rpow_mul hb']
      _ = b := by simp


theorem Exercise_5_3_4_2:
    let f: ℝ → ℝ  := fun x => ((2: ℝ) * x^ (3: ℝ)) - (3: ℝ)
    let g : ℝ → ℝ := fun x => cbrt (((x + (3: ℝ))/ (2: ℝ)))
    (g ∘ f) = id ∧ (f ∘ g) = id := by
  intro f g
  constructor
  ·
    funext x
    dsimp[g, f, cbrt]
    cases (Classical.em ((0: ℝ) ≤ ((2: ℝ) * x ^ (3: ℝ) - (3: ℝ) + (3: ℝ)) / (2: ℝ)))
    case inl h =>
      rw[if_pos h]
      apply_fun (fun x => x^(3:ℝ))
      dsimp
      rw [← Real.rpow_mul h]
      simp
      exact Exercise_5_3_4_2_helper

    case inr h =>
      rw[if_neg h]
      apply_fun (fun x => x^(3:ℝ))
      dsimp
      push_neg at h
      have h': 0 < -(((2: ℝ) * x ^ (3: ℝ) - (3: ℝ) + (3:ℝ)) / (2: ℝ)) := by linarith
      have h': 0 ≤  -(((2: ℝ) * x ^ (3: ℝ) - (3: ℝ) + (3:ℝ)) / (2: ℝ)) := by exact Std.le_of_lt h'
      norm_cast
      rw [Odd.neg_pow (by use 1; simp)]
      rw [← Real.rpow_natCast]
      rw[← Real.rpow_mul ?_]
      · simp
      · rw [← Real.rpow_natCast]
        assumption
      exact Exercise_5_3_4_2_helper
  · funext x
    dsimp[g, f, cbrt]
    cases (Classical.em ((0: ℝ) ≤ (((x + (3: ℝ)) / (2: ℝ)))))
    case inl h =>
      rw[if_pos h]
      rw[← Real.rpow_mul h]
      simp
      field_simp
      simp
    case inr h =>
      rw[if_neg h]
      have h': 0 < -((x + (3: ℝ)) / (2: ℝ)) := by linarith
      have h': 0 ≤ -((x + (3: ℝ)) / (2: ℝ)) := by exact Std.le_of_lt h'
      norm_cast
      rw [Odd.neg_pow (by use 1; simp)]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul h']
      simp
      field_simp
      simp

theorem Exercise_5_3_5_1:
    let f: ℝ → {x: ℝ // x > 0} := fun x => ⟨(10: ℝ)^((2: ℝ) - x), by
      simp
      exact Real.rpow_pos_of_pos (by norm_num) (2 - x)
    ⟩
    Function.Injective f ∧ Function.Surjective f := by
  constructor
  ·
    intro x y hxy
    simp at hxy
    have : Real.log ((10: ℝ)^((2: ℝ) - x)) / Real.log 10 = Real.log ((10: ℝ)^((2: ℝ) - x))  / Real.log 10:= by rfl
    nth_rewrite 1 [hxy] at this
    rw[  Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)] at this
    field_simp at this
    simp at this
    linarith
  ·
    intro y
    exists (2 - ((Real.log y) / (Real.log 10)))
    apply Subtype.ext
    simp
    apply Real.rpow_logb
    · norm_num
    · norm_num
    · exact y.2

theorem Exercise_5_3_5_2:
    let f: ℝ → {x: ℝ // x > 0} := fun x => ⟨(10: ℝ)^((2: ℝ) - x), by
        simp
        exact Real.rpow_pos_of_pos (by norm_num) (2 - x)
    ⟩
    let g: {x: ℝ // x > 0} → ℝ := fun x => 2 - ((Real.log x.1) / (Real.log 10))
    (f ∘ g) = id ∧ (g ∘ f) = id := by
  constructor
  ·
    funext x
    apply Subtype.ext
    simp
    apply Real.rpow_logb
    · norm_num
    · norm_num
    · exact x.2
  · funext x
    simp
    rw[  Real.log_rpow (by norm_num)]
    field_simp
    simp

theorem Exercise_5_3_6_a:
    let f: {x : ℝ // x ≠ 2} → {x: ℝ // x ≠ 3} := fun x => ⟨(3 * x ) / (  x - 2), by
      intro h
      have: (x.1 - 2) ≠ 0 := by
        intro h
        have : x.1 = 2 := by linarith
        contradict this
        exact x.2

      field_simp at h
      have: 0 = 2 := by linarith
      contradict this
      norm_num
    ⟩
    Function.Injective f ∧ Function.Surjective f := by
  constructor
  ·
    intro x y hxy
    simp at hxy
    have: (x.1 - 2) ≠ 0 := by
      intro h
      have : x.1 = 2 := by linarith
      contradict this
      exact x.2
    field_simp at hxy
    have: (y.1 - 2) ≠ 0 := by
      intro h
      have : y.1 = 2 := by linarith
      contradict this
      exact y.2
    field_simp at hxy
    have : x.1 * (y.1 - 2) = x.1 * y.1 - 2 * x.1 := by linarith
    rw[this] at hxy
    have : (x.1 - 2) * y.1 = x.1 * y.1 - 2 * y.1 := by linarith
    rw[this] at hxy
    simp at hxy
    apply Subtype.ext
    linarith
  ·
    intro x
    exists ⟨ ((2 * x) / (x - 3)), by
      intro h
      have : x.1 - 3 ≠ 0 := by
        intro h
        have: x.1 = 3 := by linarith
        contradict this
        exact x.2
      field_simp at h
      have : 0 = 3 := by linarith
      contradict this
      norm_num
    ⟩
    apply Subtype.ext
    simp
    have : x.1 - 3 ≠ 0 := by
        intro h
        have: x.1 = 3 := by linarith
        contradict this
        exact x.2
    field_simp
    simp
    rw[mul_comm]

theorem Exercise_5_3_6_b:
    let f: {x : ℝ // x ≠ 2} → {x: ℝ // x ≠ 3} := fun x => ⟨(3 * x ) / (  x - 2), by
      intro h
      have: (x.1 - 2) ≠ 0 := by
        intro h
        have : x.1 = 2 := by linarith
        contradict this
        exact x.2

      field_simp at h
      have: 0 = 2 := by linarith
      contradict this
      norm_num
    ⟩
    let g : {x: ℝ // x ≠ 3} → {x : ℝ // x ≠ 2} := fun x => ⟨ (2 * x) / (x - 3), by
      intro h
      have : x.1 - 3 ≠ 0 := by
        intro h
        have: x.1 = 3 := by linarith
        contradict this
        exact x.2
      field_simp at h
      have : 0 = 3 := by linarith
      contradict this
      norm_num
    ⟩
    (f ∘ g) = id ∧ (g ∘ f) = id := by

  constructor
  ·
    funext x
    apply Subtype.ext
    simp
    have : x.1 - 3 ≠ 0 := by
          intro h
          have: x.1 = 3 := by linarith
          contradict this
          exact x.2
    field_simp
    simp
    rw[mul_comm]
  ·
    funext x
    apply Subtype.ext
    simp
    have: (x.1 - 2) ≠ 0 := by
          intro h
          have : x.1 = 2 := by linarith
          contradict this
          exact x.2
    field_simp
    simp
    rw[mul_comm]

theorem Exercise_5_3_7_a:
  let f: ℝ → ℝ := fun x => (x + 7) / 5
  let f₁: ℝ → ℝ := fun x => x + 7
  let f₂: ℝ → ℝ := fun x => x / 5
  f = f₂ ∘ f₁  := by
  funext x
  simp

theorem Exercise_5_3_7_b:
    let finv: ℝ → ℝ := fun x => 5 * x - 7
    let f₁inv : ℝ → ℝ := fun x => x - 7
    let f₂inv : ℝ → ℝ := fun x => x * 5
    finv = f₁inv ∘ f₂inv := by
  funext x
  simp
  rw[mul_comm]

theorem Exercise_5_3_8_a(A B: Type) (f: A → B) (g: B → A) (hg: graph g = inv (graph f)):
    f ∘ g = id := by
  funext x
  simp
  rw[← graph_def]
  have: graph f = inv (graph g) := by
    rw[hg, inv, inv]
    simp
  rw[this]
  rw[inv]
  simp
  rfl

theorem Exercise_5_3_8_b(A B: Type) (f: A → B) (g: B → A)
    (hg'': one_to_one g)
    (hg' : g ∘ f = id)
    (hg: graph g = inv (graph f)):
    f ∘ g = id := by
  funext y
  apply hg''
  simp
  have: g (f (g y)) = (g ∘ f) (g y) := by simp
  rw[this, hg']
  simp

theorem Exercise_5_3_9 (A B: Type) (f: A → B) (g: B → A)
    (h: f ∘ g = id): onto f := by
  intro y
  exists (g y)
  have: f (g y) = (f ∘ g) y := by simp
  rw[this, h]
  rfl

theorem Exercise_5_3_10 (A B: Type) (f: A → B) (g: B → A)
    (hfg: f ∘ g = id) (hgf: g ∘ f = id):
    graph g = inv (graph f) := by
  apply Set.ext
  intro ⟨b, a⟩
  constructor
  ·
    intro h
    simp[inv]
    have: (f ∘ g) b = (f ∘ g) b := by rfl
    nth_rewrite 2 [hfg] at this
    rw[graph_def] at h
    simp at this
    rw[h] at this
    rw[graph_def]
    assumption
  ·
    intro h
    simp[inv] at h
    have: (g ∘ f) a= (g ∘ f) a := by rfl
    nth_rewrite 2 [hgf] at this
    simp at this
    rw[graph_def] at h
    rw[h] at this
    rw[graph_def]
    assumption

theorem Exercise_5_3_11_a (A B: Type) (f: A → B) (g: B → A)
    (hf: one_to_one f) (hfg: f ∘ g = id):
    graph g = inv (graph f) := by
    apply Set.ext
    intro ⟨b, a⟩
    constructor
    ·
      intro h
      simp[inv]
      have : (f ∘ g) b = (f ∘ g) b := by rfl
      nth_rewrite 2 [hfg] at this
      simp at this
      rw[graph_def] at h
      rw[h] at this
      rw[graph_def]
      assumption
    ·
      intro h
      simp[inv] at h
      have: (f ∘ g) b = (f ∘ g) b := by rfl
      nth_rewrite 2 [hfg] at this
      simp at this
      have: f (g b) = f (a) := by
        rw[graph_def] at h
        rw[h, this]
      have  := hf (g b) a this
      rw[graph_def]
      assumption

theorem Exercise_5_3_11_b (A B: Type) (f: A → B) (g: B → A)
    (hf: onto f) (hfg: g ∘ f = id):
    graph g = inv (graph f) := by
  apply Set.ext
  intro ⟨b, a⟩
  constructor
  ·
    intro h
    simp[inv]
    have ⟨a', ha'⟩ := hf b
    rw[graph_def]
    have: (g ∘ f) a' = a := by
      simp
      rw[ha']
      rw[graph_def] at h
      assumption
    rw[hfg] at this
    simp at this
    rw[← this]
    assumption
  ·
    intro h
    simp[inv] at h
    have: ( g ∘ f) a =  (g ∘ f) a := by rfl
    nth_rewrite 2 [hfg] at this
    simp at this
    rw[graph_def] at h
    rw[h] at this
    rw[graph_def]
    assumption

theorem Exercise_5_3_11_c (A B: Type) (f: A → B) (g: B → A)
    (hfg : f ∘ g = id) (hngf: g ∘ f ≠ id):
    onto f ∧ ¬one_to_one f := by
  constructor
  ·
    intro b
    exists g b
    have: (f ∘ g) b = (f ∘ g) b := by simp
    nth_rewrite 2 [hfg] at this
    simp at this
    assumption
  ·
    intro hf
    contradict hngf
    funext a
    simp
    apply hf
    have: f (g (f a)) = (f ∘ g) (f a) := by simp
    rw[this, hfg]
    simp

noncomputable section

open Classical

theorem Exercise_5_3_12  {A B: Type} [Inhabited A] (f: A → B) (hF: one_to_one f):
    let B': Set B := Set.range f
    let finv: B → A := fun y : B =>
      if h : ∃ x, f x = y then Classical.choose h else default
    finv ∘ f = id ∧ (∀ b ∈ B', (f ∘ finv) b = b) := by
  constructor
  ·
    funext a
    simp
    apply hF
    have: ∃ (x : A), f x = f a  := by exists a
    exact Classical.choose_spec this
  ·
    intro b hb
    simp at hb
    have ⟨a, ha⟩ := hb
    simp[dif_pos hb]
    exact Classical.choose_spec hb


theorem Exercise_5_3_13_a (A B: Type) (f: A → B):
  let R : Setoid A := Setoid.mk (fun x y: A => f x = f y) (by
    constructor
    ·
      intro a
      rfl
    · intro x y hxy
      symm
      assumption
    ·
      intro x y z hxy hyz
      rw[hxy, ← hyz]
  )
  ∃ h: Quotient R → B, ∀ x : A, h (Quotient.mk R x) = f x := by
  intro R
  let h: Quotient R → B := Quotient.lift f (by
    intro a b h
    define at h
    rw[h]
  )
  exists h
  intro a
  simp[h]

theorem Exercise_5_3_13_b (A B: Type) (f: A → B) (hf: onto f):
  let R : Setoid A := Setoid.mk (fun x y: A => f x = f y) (by
    constructor
    ·
      intro a
      rfl
    · intro x y hxy
      symm
      assumption
    ·
      intro x y z hxy hyz
      rw[hxy, ← hyz]
  )
  let h: Quotient R → B := Quotient.lift f (by
    intro a b h
    define at h
    rw[h]
  )
  one_to_one h ∧ onto h := by
intro R h
constructor
·

  intro a1 a2 ha1ha2
  have ⟨a1', ha1'⟩  := Quotient.exists_rep a1
  have ⟨a2', ha2'⟩  := Quotient.exists_rep a2
  rw[← ha1', ← ha2']
  rw[← ha1', ← ha2'] at ha1ha2
  apply Quotient.sound
  define
  simp[h] at ha1ha2
  assumption
·
  intro b
  have ⟨a, ha⟩ := hf b
  exists Quotient.mk R a


theorem Exercise_5_3_13_c (A B: Type) [Inhabited A] (f: A → B) (hf: onto f):
  let R : Setoid A := Setoid.mk (fun x y: A => f x = f y) (by
    constructor
    ·
      intro a
      rfl
    · intro x y hxy
      symm
      assumption
    ·
      intro x y z hxy hyz
      rw[hxy, ← hyz]
  )
  let h: Quotient R → B := Quotient.lift f (by
    intro a b h
    define at h
    rw[h]
  )
  let hInv: B → Quotient R :=
    fun y : B =>
      if h : ∃ x, h x = y then Classical.choose h else Quotient.mk R default

  ∀ b: B, Quotient.lift (fun x: A=> {a: A | f a = f x}) (by
    intro a1 a2 ha1a2
    simp
    have: f a1 = f a2 := by
      define at ha1a2
      assumption
    rw[this]
  ) (hInv b) = {x: A | f x = b} := by
  intro R h hInv b
  simp[hInv]
  have ⟨a, ha⟩ := hf b
  have: ∃ (x : Quotient R), h x = b := by
    exists Quotient.mk R a
  rw[dif_pos this]
  have ⟨q, hq⟩ := this
  have ⟨a', ha'⟩  := Quotient.exists_rep (choose this)
  rw[← ha']
  simp
  have new := Classical.choose_spec this
  rw[← ha'] at new
  simp[h] at new
  rw[new]

theorem Exercise_5_3_13_d (A B: Type) [Inhabited A] (f: A → B) (g: B → A) (hf: onto f):
  let R : Setoid A := Setoid.mk (fun x y: A => f x = f y) (by
    constructor
    ·
      intro a
      rfl
    · intro x y hxy
      symm
      assumption
    ·
      intro x y z hxy hyz
      rw[hxy, ← hyz]
  )
  let h: Quotient R → B := Quotient.lift f (by
    intro a b h
    define at h
    rw[h]
  )
  let hInv: B → Quotient R :=
    fun y : B =>
      if h : ∃ x, h x = y then Classical.choose h else Quotient.mk R default
  (f ∘ g) = id ↔ ∀ b: B, g b ∈ (Quotient.lift (fun x: A=> {a: A | f a = f x}) (by
    intro a1 a2 ha1a2
    simp
    have: f a1 = f a2 := by
      define at ha1a2
      assumption
    rw[this]
  ) (hInv b) ) := by
intro R h hInv
constructor
· intro hfg b
  simp[hInv]
  have ⟨a, ha⟩ := hf b
  have:  ∃ (x : Quotient R), h x = b:= by
    exists Quotient.mk R a
  rw[dif_pos this]
  have ⟨a', ha'⟩  := Quotient.exists_rep (choose this)
  rw[← ha']
  simp
  have hkeep:= Classical.choose_spec this
  have new: f (g b) = (f ∘ g) b:= by simp
  rw[new, hfg]
  simp
  symm
  rw[← ha'] at hkeep
  simp[h] at hkeep
  assumption
· intro h'
  funext x
  simp
  have h' := h' x
  simp[hInv] at h'
  have ⟨a, ha⟩ := hf x
  have q: ∃ (x_1 : Quotient R), h x_1 = x := by exists Quotient.mk R a
  rw[dif_pos q] at h'
  have ⟨a', ha'⟩ := Quotient.exists_rep (choose q)
  rw[← ha'] at h'
  simp at h'
  have := Classical.choose_spec q
  simp[h] at this
  rw[← ha'] at this
  simp at this
  rw[h', ← this]

theorem Exercise_5_3_14_a (A B: Type) (f: A → B) (g: B → A) (hfg: f ∘ g = id):
    let A' : Set A := Set.range g
    ∀ x ∈ A', (g ∘ f) x = x := by
  intro A' x hx
  define at hx
  have ⟨b, hb⟩ := hx
  have : (f ∘ g) b =  (f ∘ g) b := by rfl
  nth_rw 2 [hfg] at this
  simp at this
  rw[hb] at this
  simp
  rw[this, hb]

theorem Exercise_5_3_14_b (A B: Type) [Inhabited A] (f: A → B) (b: B) (g: B → A) (hfg: f ∘ g = id):
    let A' : Set A := Set.range g
    let fres: A' → B := fun x => f x
    let fresInv: B → A' :=
    fun y : B =>
      if h1 : ∃ x : A', f x = y then Classical.choose h1 else ⟨g b, by
        define
        exists b
      ⟩
    one_to_one fres ∧ onto fres ∧  g = fun y => (fresInv y : A):= by
  intro A' fres fresInv
  have hinj : one_to_one fres := by
    intro x y hxy
    simp[fres] at hxy
    have ⟨b, hb⟩ := x.2
    have ⟨b', hb'⟩ := y.2
    have : (f ∘ g) b = (f ∘ g) b' := by
      simp
      rw[hb, hb']
      assumption
    rw[hfg] at this
    simp at this
    rw[this] at hb
    apply Subtype.ext
    rw[← hb, ← hb']

  constructor
  · exact hinj
  ·
    constructor
    ·
      intro y
      exists ⟨g y, by
        define
        exists y
      ⟩
      simp[fres]
      have : f (g y) = (f ∘ g) y := by rfl
      rw[this, hfg]
      simp
    ·
      funext b
      dsimp[fresInv]
      have q : ∃ x : A', f x = b := by
        exists ⟨g b, by
          exact ⟨b, rfl⟩
        ⟩
        have : f (g b) = (f ∘ g) b := by rfl
        rw [this, hfg]
        simp
      rw[dif_pos q ]
      define at hinj
      have fres1: fres ⟨(g b), by exists b⟩   = b := by
        simp[fres]
        have: f (g b) = (f ∘ g) b := by rfl
        rw[this]
        rw[hfg]
        simp

      have fres2 : fres (Classical.choose q) = b := by
        exact Classical.choose_spec q

      have fres3 : fres ⟨(g b), by exists b⟩  = fres (Classical.choose q) := by
        rw[fres1, fres2]
      have hinj1 := hinj ⟨(g b), by exists b⟩ (Classical.choose q) fres3
      exact congrArg Subtype.val hinj1

theorem Exercise_5_3_15:
    let B : Type := {x : ℝ // 0 ≤ x}
    let f: ℝ → B := fun x => ⟨x^2, by positivity⟩
    let g : B → ℝ := fun x => Real.sqrt x.val
    let fres : B → B := fun x => f x
    let fresInv: B → B :=
      fun y : B =>
        if h1 : ∃ x : B, f x = y then Classical.choose h1 else 0
    g = fun y => (fresInv y : ℝ) := by
  intro B f g fres fresInv
  funext x
  dsimp[fresInv]
  have q: ∃ (x_1 : B), f x_1 = x  := by
    exists ⟨Real.sqrt x, by positivity⟩
    simp
    dsimp[f]
    simp
    apply Subtype.ext
    simp
  change g x = ((if h1 : ∃ x_1 : B, f ↑x_1 = x then Classical.choose h1 else 0 : B) : ℝ)
  rw[dif_pos q]
  dsimp[g]
  have fresInj: one_to_one fres := by

    intro x y
    dsimp[fres, f]
    intro hxy
    have hval := congrArg Subtype.val hxy
    simp at hval
    assumption

  have fresInj2 := fresInj ⟨(Real.sqrt x), by exact Real.sqrt_nonneg ↑x⟩ (Classical.choose q)
  refine congrArg Subtype.val (fresInj2 ?_)
  have :=  Classical.choose_spec q
  dsimp[fres]
  conv_lhs =>
    dsimp [f]
  apply Subtype.ext
  simp
  symm
  assumption

theorem Exercise_5_3_16_a:
    let f: ℝ → ℝ := fun x => 4 * x - x^2
    let B := Set.range f
    {x : ℝ | x ≤ (4: ℝ)} = B := by
  ext x
  constructor
  ·
    intro hx
    simp at *
    exists ((4 + Real.sqrt (16 - 4 * x)) / 2)
    field_simp
    have hrad : 0 ≤ 16 - 4 * x := by
      nlinarith
    have hsqrt : (√(16 - 4 * x)) ^ 2 = 16 - 4 * x := by
      exact Real.sq_sqrt hrad
    nlinarith
  ·
    intro hx
    simp at *
    have ⟨y, hy⟩ := hx
    symm at hy
    rw[hy]
    have : 0 ≤ (y - 2) ^ 2 := by exact sq_nonneg (y - 2)
    nlinarith


theorem EXER (A: Type) [Inhabited A] (f: A → A) (hf: onto f) (hf': one_to_one f):
    let fInv := fun y : A =>
              if h1 : ∃ x : A, f x = y then Classical.choose h1 else default
    let fInvInv := fun y : A =>
              if h1 : ∃ x : A, fInv x = y then Classical.choose h1 else default
    fInvInv = f := by
    intro fInv fInvInv
    funext a
    dsimp[fInvInv]
    have q : ∃ (x : A), fInv x = a := by
      dsimp[fInv]
      exists (f a)
      have q2: ∃ (x : A), f x = f a  := by
        exists a
      rw[dif_pos q2]
      apply hf'
      exact Classical.choose_spec q2
    rw[dif_pos q]
    have quirk := Classical.choose_spec q
    have qurik1: f (fInv (choose q)) = f (fInv (choose q)) := by rfl
    nth_rewrite 1 [quirk] at qurik1
    rw[qurik1]
    have part :f (fInv (choose q)) = (f ∘ fInv) (choose q) := by rfl
    rw[part]
    have: f ∘ fInv = id := by
      funext y
      simp
      dsimp[fInv]
      have q: ∃ (x : A), f x = y := by
        have ⟨t, ht⟩ := hf y
        exists t
      rw[dif_pos q]
      exact Classical.choose_spec q
    rw[this]
    simp

theorem Exercise_5_3_16_b:
      let f: ℝ → ℝ := fun x => 4 * x - x^2
      let B := Set.range f
      let A': Type := {x : ℝ | 2 ≤ x}
      let fres : A' → B := fun x => ⟨f x, by exists x⟩
      let fresInv: B → A' :=
        fun y : B =>
          if h1 : ∃ x : A', fres x = y then Classical.choose h1 else ⟨(2: ℝ), by norm_num⟩
      let g : B → A' := fun y: B => ⟨(4 + Real.sqrt (16 - 4 * y)) / 2, by
        simp
        field_simp
        have : 2 ^ 2 = (4: ℝ) := by norm_num
        rw[this]
        simp
      ⟩
      one_to_one fres ∧ onto fres ∧ g = fresInv := by
  intro f B A' fres fresInv g
  have hf : one_to_one fres := by
    intro x y hxy
    dsimp[fres, f] at hxy
    simp at hxy
    apply_fun (fun x => (4 + Real.sqrt (16 - 4 * x)) / 2) at hxy
    field_simp at hxy
    have xtemp : (16 - 4 * x.1 * (4 - x.1)) = (2 * x.1 - 4)^ 2:= by nlinarith
    rw[xtemp] at hxy
    have xrad : 0 ≤ (2 * x.1 - 4) := by
      simp
      have: 2 ≤ x.1 := x.2
      linarith
    simp at hxy
    have := Real.sqrt_sq xrad
    rw[this] at hxy
    have ytemp : (16 - 4 * y.1 * (4 - y.1)) = (2 * y.1 - 4)^ 2:= by nlinarith
    rw[ytemp] at hxy
    have yrad : 0 ≤ (2 * y.1 - 4) := by
      simp
      have: 2 ≤ y.1 := y.2
      linarith
    simp at hxy
    have := Real.sqrt_sq yrad
    rw[this] at hxy
    field_simp at hxy
    apply Subtype.ext
    linarith

  constructor
  · exact hf
  ·
    constructor
    ·
      intro x
      exists ⟨ ((4 + Real.sqrt (16 - 4 * x)) / 2), by
        simp
        field_simp
        have : 2 ^ 2  = (4: ℝ) := by norm_num
        rw[this]
        simp
      ⟩
      simp[fres, f]
      apply Subtype.ext
      simp
      have hrad : (0: ℝ) ≤ 16 - 4 * x := by
        have : x ≤ (4: ℝ) := by
          have ⟨y, hy⟩ := x.2
          simp
          rw[← hy]
          dsimp[f]
          have : 0 ≤ (y - 2) ^ 2 := by exact sq_nonneg (y - 2)
          nlinarith
        nlinarith
      have hsqrt : (√(16 - 4 * x)) ^ 2 = 16 - 4 * x := by
        exact Real.sq_sqrt hrad
      nlinarith
    ·
      funext b
      dsimp[g, fresInv]
      apply Subtype.ext
      have q :  ∃ (x : A'), fres x = b := by
        dsimp[f]
        exists ⟨ ((4 + Real.sqrt (16 - 4 * b.1)) / 2), by
          simp
          field_simp
          have : 2 ^ 2  = (4: ℝ) := by norm_num
          rw[this]
          simp
        ⟩
        simp
        have hrad : (0: ℝ) ≤ 16 - 4 * b.1 := by
          have : b.1 ≤ (4: ℝ) := by
            have ⟨y, hy⟩ := b.2
            simp
            rw[← hy]
            dsimp[f]
            have : 0 ≤ (y - 2) ^ 2 := by exact sq_nonneg (y - 2)
            nlinarith
          nlinarith
        have hsqrt : (√(16 - 4 * b.1)) ^ 2 = 16 - 4 * b.1 := by
          exact Real.sq_sqrt hrad
        dsimp[fres, f]
        apply Subtype.ext
        simp
        nlinarith
      rw[dif_pos q]
      have q2 := Classical.choose_spec q
      simp
      have fresInj2 := hf ⟨((4 + √(16 - 4 * b)) / 2), by
        simp
        field_simp
        have : 2^2 = (4: ℝ) := by norm_num
        rw[this]
        simp
        ⟩ (Classical.choose q)
      refine congrArg Subtype.val (fresInj2 ?_)
      rw[q2]
      dsimp[fres, f]
      apply Subtype.ext
      simp
      have hrad : (0: ℝ) ≤ 16 - 4 * b := by
        have : b ≤ (4: ℝ) := by
          have ⟨y, hy⟩ := b.2
          simp
          rw[← hy]
          dsimp[f]
          have : 0 ≤ (y - 2) ^ 2 := by exact sq_nonneg (y - 2)
          nlinarith
        nlinarith
      have hsqrt : (√(16 - 4 * b)) ^ 2 = 16 - 4 * b := by
        exact Real.sq_sqrt hrad
      nlinarith

variable {A : Type*} [Inhabited A]

def inverse (f : A → A) : A → A := fun y : A ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem Exercise_5_3_17_a (A: Type) [Inhabited A]:
    let F : Type := A → A
    let P := {f: F | one_to_one f ∧ onto f}
    let R := {(f, g): F × F | ∃ h : F,
      h ∈ P ∧
      f = (inverse h) ∘ g ∘ h
    }
    equiv_rel (RelFromExt R) := by
  intro F P R
  define
  constructor
  ·
    intro f
    rw[RelFromExt]
    dsimp[R]
    exists id
    constructor
    ·
      define
      constructor
      ·
        intro x y hxy
        simp at hxy
        assumption
      ·
        intro y
        exists y
    ·
      symm
      funext x
      simp
      dsimp[inverse]
      have q : ∃ (x_1 : A), x_1 = f x := by
        exists f x
      rw[dif_pos q]
      exact Classical.choose_spec q
  ·
    constructor
    intro x y hxy
    rw[RelFromExt] at hxy
    dsimp[R] at hxy
    have ⟨g, ⟨hg1, hg2⟩ , hg'⟩ := hxy
    have hinvgg: ((inverse g) ∘ g) = id := by
      funext a
      simp
      dsimp[inverse]
      have q: ∃ (x : A), g x = g a  := by
        exists a
      rw[dif_pos q]
      apply_fun fun x => g x
      simp
      exact Classical.choose_spec q
    have hginvg: (g ∘ (inverse g)) = id := by
          funext x
          simp
          dsimp[inverse]
          have q :  ∃ (x_1 : A), g x_1 = x := by
            have ⟨t, ht⟩ := hg2 x
            exists t
          rw[dif_pos q]
          exact Classical.choose_spec q
    rw[RelFromExt]
    dsimp[R]
    exists (inverse g)
    constructor
    ·
      constructor
      ·
        intro a b hab
        apply_fun (fun x => g x) at hab
        have : g (inverse g a) = (g ∘ (inverse g)) a := by rfl
        rw[this] at hab
        have : g (inverse g b) = (g ∘ (inverse g)) b := by rfl
        rw[this] at hab
        rw[hginvg]at hab
        simp at hab
        assumption
      ·
        intro y
        exists (g y)
        have: inverse g (g y) = ((inverse g) ∘ g) y := by rfl
        rw[this]
        rw[hinvgg]
        simp
    ·
      rw[hg']
      have: inverse (inverse g) ∘ (inverse g ∘ y ∘ g) ∘ inverse g = (inverse (inverse g) ∘ inverse g) ∘ y ∘ (g ∘ inverse g) := by rfl
      rw[this]
      have: (inverse (inverse g) ∘ inverse g) = id := by
        have : inverse (inverse g) = g := by
          funext a
          change
            (if h : ∃ x : A, inverse g x = a then Classical.choose h else default) = g a
          have q:  ∃ x : A, inverse g x = a := by
            exists (g a)
            have: inverse g (g a) = ((inverse g) ∘ g) a := by rfl
            rw[this]
            rw[hinvgg]
            simp
          rw[dif_pos q]
          have test := Classical.choose_spec q
          apply_fun (fun x => g x) at test
          have : g (inverse g (choose q)) = (g ∘ inverse g) (choose q) := by rfl
          rw[this] at test
          rw[hginvg] at test
          simp at test
          assumption
        rw[this]
        exact hginvg
      rw[this]
      rw[hginvg]
      simp
    intro x y z hxy hyz
    rw[RelFromExt] at *
    dsimp[R] at *
    have ⟨f, ⟨hf1, hf2⟩ , hf'⟩ := hxy
    have ⟨g, ⟨hg1, hg2⟩ , hg'⟩ := hyz
    exists (g ∘ f)
    constructor
    ·
      constructor
      ·
        intro a b hab
        simp at hab
        have := hg1 ((f a)) ((f b)) hab
        have := hf1 a b this
        assumption
      ·
        intro c
        simp
        exists (inverse f (inverse g c))
        have: g (f (inverse f (inverse g c))) = g ((f ∘ inverse f) (inverse g c)) := by rfl
        rw[this]
        have: (f ∘ inverse f)  = id := by
          funext x
          simp
          dsimp[inverse]
          have q :  ∃ (x_1 : A), f x_1 = x := by
            have ⟨t, ht⟩ := hf2 x
            exists t
          rw[dif_pos q]
          exact Classical.choose_spec q
        rw[this]
        simp
        have: g (inverse g c) = (g ∘ inverse g) c := by rfl
        rw[this]
        have: (g ∘ inverse g)  = id := by
          funext x
          simp
          dsimp[inverse]
          have q :  ∃ (x_1 : A), g x_1 = x := by
            have ⟨t, ht⟩ := hg2 x
            exists t
          rw[dif_pos q]
          exact Classical.choose_spec q
        rw[this]
        simp
    ·
      calc
        x = inverse f ∘ y ∘ f := by assumption
        _ = inverse f ∘ (inverse g ∘ z ∘ g) ∘ f := by rw[hg']
        _ = (inverse f ∘ inverse g) ∘ z ∘ (g ∘ f) := by rfl
        _ = inverse (g ∘ f) ∘ z ∘ g ∘ f := by
            have : (inverse f ∘ inverse g) = inverse (g ∘ f) := by
              funext a
              simp
              change
                (if h : ∃ x, f x = inverse g a then Classical.choose h else default) = inverse (g ∘ f) a
              have q : ∃ x, f x = inverse g a:= by
                exists inverse f (inverse g a)
                have: f (inverse f (inverse g a))  = (f ∘ inverse f) (inverse g a) := by rfl
                rw[this]
                have : (f ∘ inverse f) = id := by
                  funext x
                  simp
                  dsimp[inverse]
                  have q :  ∃ (x_1 : A), f x_1 = x := by
                    have ⟨t, ht⟩ := hf2 x
                    exists t
                  rw[dif_pos q]
                  exact Classical.choose_spec q
                rw[this]
                simp
              rw[dif_pos q]
              have p := Classical.choose_spec q
              apply_fun fun x => f x
              simp
              rw[p]
              change (if h : ∃ (x : A), g x = a then choose h else default) = f (inverse (g ∘ f) a)
              have q2:  ∃ (x : A), g x = a  := by
                exists inverse g a
                have :  g (inverse g a) = (g ∘ inverse g) a := by rfl
                rw[this]
                have : (g ∘ inverse g) = id := by
                  funext x
                  simp
                  dsimp[inverse]
                  have q :  ∃ (x_1 : A), g x_1 = x := by
                    have ⟨t, ht⟩ := hg2 x
                    exists t
                  rw[dif_pos q]
                  exact Classical.choose_spec q
                rw[this]
                simp
              rw[dif_pos q2]
              have p2 := Classical.choose_spec q2
              apply_fun fun x => g x
              simp
              rw[p2]
              have: g (f (inverse (g ∘ f) a)) = ((g ∘ f) ∘ inverse (g ∘ f)) a := by rfl
              rw[this]
              have : ((g ∘ f) ∘ inverse (g ∘ f)) = id := by
                funext a
                simp
                dsimp[inverse]
                have q :  ∃ (x : A), g (f x) = a := by
                  exists inverse f (inverse g a)
                  have : g (f (inverse f (inverse g a))) = g ((f  ∘ inverse f) (inverse g a)) := by rfl
                  rw[this]
                  have: (f  ∘ inverse f) = id := by
                    funext x
                    simp
                    dsimp[inverse]
                    have q :  ∃ (x_1 : A), f x_1 = x := by
                      have ⟨t, ht⟩ := hf2 x
                      exists t
                    rw[dif_pos q]
                    exact Classical.choose_spec q
                  rw[this]
                  simp
                  have : g (inverse g a) = (g ∘ inverse g) a := by rfl
                  rw[this]
                  have: (g ∘ inverse g) = id := by
                    funext x
                    simp
                    dsimp[inverse]
                    have q :  ∃ (x_1 : A), g x_1 = x := by
                      have ⟨t, ht⟩ := hg2 x
                      exists t
                    rw[dif_pos q]
                    exact Classical.choose_spec q
                  rw[this]
                  simp
                rw[dif_pos q]
                exact Classical.choose_spec q
              rw[this]
              simp
            rw[this]


theorem Exercise_5_3_17_b (A: Type) (f g: A → A) [Inhabited A]:
    let F : Type := A → A
    let P := {f: F | one_to_one f ∧ onto f}
    let R := {(f, g): F × F | ∃ h : F,
      h ∈ P ∧
      f = (inverse h) ∘ g ∘ h
    }
    (RelFromExt R) f g → (RelFromExt R) (f ∘ f) (g ∘ g):= by
  intro F P R h
  rw[RelFromExt] at *
  simp[R] at *
  have ⟨h, ⟨hh1, hh2⟩ , hh'⟩ := h
  exists h
  constructor
  ·
    constructor
    · assumption
    · assumption
  ·
    calc
    f ∘ f = (inverse h ∘ g ∘ h) ∘ (inverse h ∘ g ∘ h) := by rw[hh']
    _ = (inverse h ∘ g ∘ (h ∘ inverse h) ∘ g ∘ h) := by rfl
    _ = (inverse h ∘ g  ∘ g ∘ h) := by
      have : (h ∘ inverse h) = id := by
        funext x
        simp
        dsimp[inverse]
        have q : ∃ (x_1 : A), h x_1 = x  := by
          have ⟨t, ht⟩ := hh2 x
          exists t
        rw[dif_pos q]
        exact Classical.choose_spec q
      rw[this]
      simp


theorem Exercise_5_3_17_c (A: Type) (f g: A → A) [Inhabited A]:
    let F : Type := A → A
    let P := {f: F | one_to_one f ∧ onto f}
    let R := {(f, g): F × F | ∃ h : F,
      h ∈ P ∧
      f = (inverse h) ∘ g ∘ h
    }
    (∃ a : A, f a = a) → (RelFromExt R) f g  → ∃ a : A, g a = a := by
  intro F P R hf hfg
  rw[RelFromExt] at *
  simp[R] at *
  have ⟨h, ⟨hh1, hh2⟩ , hh'⟩ := hfg
  have ⟨a, ha⟩ := hf
  exists h a
  rw[hh'] at ha
  apply_fun fun x => h x at ha
  have : h ((inverse h ∘ g ∘ h) a) = ((h ∘ inverse h) ∘ g ∘ h) a := by rfl
  rw[this] at ha
  have: (h ∘ inverse h) = id := by
    funext x
    simp
    dsimp[inverse]
    have q : ∃ (x_1 : A), h x_1 = x  := by
      have ⟨t, ht⟩ := hh2 x
      exists t
    rw[dif_pos q]
    exact Classical.choose_spec q
  rw[this] at ha
  simp at ha
  assumption

theorem Exercise_5_3_18 (A B C: Type) [Inhabited B] (f: A → C) (g: B → C)
    (hg: one_to_one g) (hg': onto g):
    ∃ h: A → B, g ∘ h = f := by
  let gInv := fun y : C ↦
      if h : ∃ x, g x = y then Classical.choose h else default
  exists (gInv ∘ f)
  have : g ∘ gInv ∘ f = (g ∘ gInv) ∘ f := by rfl
  rw[this]
  have :  g ∘ gInv = id := by
    funext x
    simp
    dsimp[gInv]
    have q: ∃ (x_1 : B), g x_1 = x := by
      have ⟨t, ht⟩ := hg' x
      exists t
    rw[dif_pos q]
    exact Classical.choose_spec q
  rw[this]
  simp
