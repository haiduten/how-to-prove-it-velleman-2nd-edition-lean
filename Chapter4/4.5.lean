import HTPILib.Chap4
namespace HTPI.Exercises


theorem Example_4_5_4 (A: Type) (R: BinRel A) (hA: equiv_rel R):
    partition (mod A R) := by
  rcases hA with ⟨refl, symm, trans⟩
  constructor
  rintro x
  use (equivClass R x)
  constructor
  use x
  exact refl x
  constructor
  rintro X hX Y hY XneY
  define
  by_contra h'
  apply XneY
  rcases h'  with ⟨p, hpX, hpY⟩
  rcases hX with ⟨m, hm⟩
  rcases hY with ⟨n, hn⟩
  rw[← hm] at hpX
  define at hpX
  rw[← hn] at hpY
  define at hpY
  apply Set.ext
  rintro x
  constructor
  rintro hx
  rw[← hm] at hx
  define at hx
  rw[← hn]
  define
  apply trans
  apply trans x m p hx (symm p m hpX)
  exact hpY
  rintro hxY
  rw[← hn] at hxY
  rw[← hm]
  define
  define at hxY
  apply trans
  exact hxY
  apply trans
  apply symm p n hpY
  exact hpX
  rintro X hX
  define at hX
  rcases hX with ⟨x, hx⟩
  rw[← hx]
  define
  push_neg
  use x
  define
  exact refl x

  theorem Example_4_5_5_1 (A: Type) (R: BinRel A) (hA: equiv_rel R):
      ∀ x : A, x ∈ equivClass R x := by
    rcases hA with ⟨refl, _, _⟩
    rintro x
    exact refl x

  theorem Example_4_5_5_2 (A: Type) (R: BinRel A) (hA: equiv_rel R):
      ∀ x y: A, y ∈ equivClass R x ↔ equivClass R y = equivClass R x := by
    rintro x y
    constructor
    rintro hyx
    define at hyx
    apply Set.ext
    rintro z
    constructor
    rintro hzy
    define at hzy
    exact hA.2.2 z y x hzy hyx
    rintro hzx
    exact hA.2.2 z x y hzx (hA.2.1 y x hyx)
    rintro h
    rw[← h]
    exact Example_4_5_5_1 A R hA y

  theorem Example_4_5_6 (A: Type) (F: Set (Set A)) (hF: partition F):
      ∃ R: BinRel A, equiv_rel R ∧ mod A R = F := by
    let R: Set (A × A) := {(x, y) : (A × A) | ∃ F': Set A, F' ∈ F ∧ x ∈ F' ∧ y ∈ F'}
    rcases hF with ⟨union, pairwise, nonempty⟩
    use RelFromExt R
    constructor
    constructor
    rintro x
    rw[RelFromExt]
    rcases union x with ⟨i, hi, hi'⟩
    use i
    constructor
    rintro x y hxy
    rcases hxy with ⟨i , hi, hi'⟩
    use i
    apply And.intro hi hi'.symm
    rintro x y z hxy hyz
    rcases hxy with ⟨I, hI, hI', hI''⟩
    rcases hyz with ⟨J, hJ, hJ', hJ''⟩
    have hieqJ: I = J := by
      by_contra h'
      apply pairwise I hI J hJ h'
      use y
      constructor
      exact hI''
      exact hJ'
    use I
    constructor
    exact hI
    constructor
    exact hI'
    rw[←hieqJ] at hJ''
    exact hJ''
    apply Set.ext
    rintro I
    constructor
    rintro hI
    rcases hI with ⟨x, hx⟩
    rw[equivClass] at hx
    simp[RelFromExt] at hx
    simp[R] at hx
    have h: ∃ F' ∈ F, {y : A | ∃ F' ∈ F, y ∈ F' ∧ x ∈ F'} = F' := by
      have h := union x
      rcases h with ⟨U, hU, hU'⟩
      use U
      constructor
      exact hU
      apply Set.ext
      rintro x'
      constructor
      rintro hx'
      define at hx'
      rcases hx' with ⟨V, hV, hV', hV''⟩
      have h: V = U := by
        by_contra h'
        apply pairwise V hV U hU h'
        use x
        constructor
        exact hV''
        exact hU'
      rw[← h]
      exact hV'
      rintro hx'U
      define
      use U
    rcases h with ⟨F', hF', hF''⟩
    rw[← hx, hF'']
    exact hF'
    rintro hIF
    have h:= nonempty I hIF
    rw[empty] at h
    push_neg at h
    rcases h with ⟨x, hx⟩
    rw[mod]
    define
    use x
    rw[equivClass]
    apply Set.ext
    rintro x'
    constructor
    rintro hx'
    define at hx'
    rcases hx' with ⟨J, hJ, hJ', hJ''⟩
    have h: I = J := by
      by_contra h'
      apply pairwise I hIF J hJ h'
      use x
      constructor
      exact hx
      exact hJ''
    rw[h]
    exact hJ'
    rintro hI
    define
    use I

  theorem Example_4_5_10 (R : ℤ → BinRel ℤ)
      (hR : ∀ m x y: ℤ, R m x y ↔ ∃ k : ℤ, x - y = k * m):
      ∀ m : ℤ, m > 0 → equiv_rel (R m) := by
    rintro m hm
    constructor
    rintro x
    rw[hR]
    use 0
    exact by ring
    constructor
    rintro x y hxy
    rw[hR] at hxy
    rcases hxy with ⟨k ,hk⟩
    rw[hR]
    use -1 * k
    rw[mul_assoc]
    rw[← hk]
    exact by ring
    rintro x y z hxy hyz
    rw[hR] at hxy
    rw[hR] at hyz
    rcases hxy with ⟨u, hu⟩
    rcases hyz with ⟨v, hv⟩
    rw[hR]
    use (u + v)
    rw[add_mul, ←hu, ←hv]
    exact by ring

  /-
  Exercise_4_5_1
  {(1), (2), (3)}
  {(1, 2, 3)}
  {(1, 2), (3)}
  {(1), (2, 3)}
  {(1, 3), (2)}
  -/

  /-
  Exercise_4_5_2
  {(1,1), (2, 2), (3, 3)}
  {(1, 1), (2, 2), (1, 2), (2, 1), (3, 3)}
  {(1, 1), (3, 3), (1, 3), (3, 1), (2, 2)}
  {(2, 2), (3, 3), (2, 3), (3, 2), (1, 1)}
  {(1, 1), (2, 2), (1, 2), (2, 1), (3, 3), (1, 3), (3, 1),(2, 3), (3, 2)}

  Exercise_4_5_3
  A and C are equivalence classes

  The equivalence classes for A are {{words that start with a}, {words that start with b}, ...}
  The equivalence classes for C are one letter words, 2 letter words, 3 letter words...

  Exercise_4_5_4
  B and C is an equivalence classes
  The equivalence classes for B set of
  {-3,-2, -1, 0, 1 ,2 , 3}
  {-3.5, -2.5, -1.5, 0.5 , 1.5, 2.5, 3.5}

  The equivalence classes for C
  {1/10 ,1 , 10 , 100}

  Exercise_4_5_5
  A is an equivalence relation. Equivalence class is lines with slope 1, lines with slope with slope 2, ...

  B is not. A line cannot be perpendicular to itself

  C is an equivalence relation. every line is in its own class except that y and x axis

  Exercise_4_5_6
  →
  take an arbitrary element of P/B call it X. Then there is an x such that X = [x]b. [x]b are people with same
  birthday as x. Call D' x's birthday. [x]b is equal to PD' and since D' ∈ D, pD' ∈ {Pd | d ∈ D} so X ∈ {Pd | d ∈ D}

  ←
  Take an arbitrary element of {Pd | d ∈ D} call it pd'. assume every day has a person born on it. Thus there is a person
  in pd'. Let's call him x. pd' is equal to [x]b. [x]b ∈ P \ B. so pd' ∈  P \ B

  Exercise_4_5_7

  Reflexive. The same triangle has the same angles
  Symmetry. A has same angles as B, B must have same angles as A
  Transitivity. If A has same angles as B and B has same angles as C, A and C must have same angles
  -/

  theorem Exercise_4_5_8 (A: Type) (F: Set (Set A)) (R: Set (A × A))
      (hF: partition F) (hR: ∀ x y: A, (x, y) ∈ R ↔ (x, y) ∈ {p: A × A | ∃ F' ∈ F, p ∈ (F' ×ˢ F')}):
      equiv_rel (RelFromExt R) := by
    rcases hF with ⟨total, pairwise, nonempty⟩
    constructor
    rintro x
    rw[RelFromExt, hR]
    define
    rcases total x with ⟨F', hF', hF''⟩
    use F'
    constructor
    use hF'
    constructor
    exact hF''
    exact hF''
    constructor
    rintro x y hxy
    simp[RelFromExt, hR]
    simp[RelFromExt, hR] at hxy
    rcases hxy with ⟨F', hF', hF'', hF'''⟩
    use F'
    rintro x y z hxy hyz
    simp[RelFromExt, hR]
    simp[RelFromExt, hR] at hxy
    simp[RelFromExt, hR] at hyz
    rcases hxy with ⟨F', hF', hF'', hF'''⟩
    rcases hyz with ⟨G', hG', hG'', hG'''⟩
    have h: F' = G' := by
      by_contra h'
      apply (pairwise F' hF' G' hG' h')
      use y
      constructor
      exact hF'''
      exact hG''
    rw[← h] at hG'''
    use F'

  theorem Exercise_4_5_9 (A: Type) (R S: BinRel A) (hR: equiv_rel R) (hS: equiv_rel S) (hRS: mod A  R = mod A  S): extension R = extension S := by
    apply Set.ext
    rintro ⟨m, n⟩
    rcases hS with ⟨reflS, symmS, transS⟩
    rcases hR with ⟨reflR, symmR, transR⟩
    constructor
    rintro hmn
    have h: ∃ X ∈ mod A R, m ∈ X ∧ n ∈ X := by
      use (equivClass R m)
      constructor
      use m
      constructor
      apply reflR
      exact symmR m n hmn
    rw[hRS] at h
    rcases h with ⟨F', hF', hF'', hF'''⟩
    rcases hF' with ⟨x, hx⟩
    simp[← hx] at hF''
    simp[← hx] at hF'''
    exact transS m x n hF'' (symmS  n x hF''')
    rintro hmn
    have h: ∃ X ∈ mod A S, m ∈ X ∧ n ∈ X := by
      use (equivClass S m)
      constructor
      use m
      constructor
      apply reflS
      exact symmS m n hmn
    rw[← hRS] at h
    rcases h with ⟨F', hF', hF'', hF'''⟩
    rcases hF' with ⟨x, hx⟩
    simp[← hx] at hF''
    simp[← hx] at hF'''
    exact transR m x n hF'' (symmR  n x hF''')

  theorem Exercise_4_5_10 (A: Type) (F: Set (Set A)) (R S: BinRel A)
      (hR: equiv_rel R) (hS: equiv_rel S) (hF: ∀ X : Set A, X ∈ F ↔ X ∈ mod A R)
      (hS': ∀ x y : A, (x, y) ∈ extension S ↔ (x, y) ∈ {p: A × A | ∃ F' ∈ F, p ∈ (F' ×ˢ F')}):
      extension S = extension R := by
    apply Set.ext
    rcases hR with ⟨reflR, symmR, transR⟩
    rintro ⟨m, n⟩
    constructor
    · -- →
      rintro hmn
      simp[hS', hF, mod, equivClass] at hmn
      rcases hmn with ⟨x, hx, hx'⟩
      exact transR m x n hx (symmR n x hx')
    · -- ←
      rintro hmn
      define at hmn
      simp[hS', hF, mod, equivClass]
      use n
      apply And.intro hmn (reflR n)

  theorem Exercise_4_5_11_a (R : ℤ → BinRel ℤ)
      (hR : ∀ m x y: ℤ, R m x y ↔ ∃ k : ℤ, x - y = k * m):
      ∀ m : ℤ, m > 0 → equiv_rel (R m) := by
    rintro m hm
    constructor
    rintro x
    rw[hR]
    use 0
    exact by ring
    constructor
    rintro x y hxy
    rw[hR] at hxy
    rcases hxy with ⟨k ,hk⟩
    rw[hR]
    use -1 * k
    rw[mul_assoc]
    rw[← hk]
    exact by ring
    rintro x y z hxy hyz
    rw[hR] at hxy
    rw[hR] at hyz
    rcases hxy with ⟨u, hu⟩
    rcases hyz with ⟨v, hv⟩
    rw[hR]
    use (u + v)
    rw[add_mul, ←hu, ←hv]
    exact by ring

/-
  Exercise_4_5_11_b
  {..., -2, 0, 2, 4, 6, 8, ....}
  {..., -1, 1, 3, 5, .....}
  There are two
  {---, -3, 0, 3, 6, 9, ....}
  {---, -2, 1, 4, 7, 10, ....}
  {---, -1, 2, 5, 8, 11, ....}
  There are three
  There are m classes for ---m
-/

theorem Exercise_4_5_12: ∀ n: ℤ, ∃ k: ℤ, n ^ 2 = 4 * k ∨ n ^ 2 - 1 = 4 * k := by
  rintro n
  have h: n % 2 = 0 ∨ n % 2 = 1 := Int.emod_two_eq n
  rcases h with h | h
  have h: 2 ∣ n := Int.dvd_of_emod_eq_zero h
  define at h
  rcases h with ⟨u, hu⟩
  use u ^ 2
  left
  symm
  calc 4 * u ^ 2
   _ = (2 * u) * (2 * u) := by ring
   _ = n ^ 2 := by rw[hu]; ring
  have h := Int.dvd_self_sub_of_emod_eq h
  define at h
  rcases h with ⟨u, hu⟩
  have hu: n = 2 * u  +1 := Int.sub_eq_iff_eq_add.mp hu
  use (u^2 + u)
  right
  rw[Int.sub_eq_iff_eq_add.mpr]
  symm
  calc 4 * (u ^ 2 + u) + 1
    _ = (2 * u + 1) * (2 * u + 1) := by ring
    _ = n ^2 := by rw[hu]; ring

theorem Exercise_4_5_13 (a a' b b' m: ℤ) (ha: ∃ k : ℤ, a - a' = k * m)
    (hb: ∃ k : ℤ, b - b' = k * m):
    (∃ k : ℤ, a + b - (a' + b') = k * m) ∧ ∃ k : ℤ, a * b - (a' * b')= k * m := by
  rcases ha with ⟨k, hk⟩
  rcases hb with ⟨l, hl⟩
  constructor
  use k + l
  symm
  calc (k + l) * m
    _ = k * m + l * m := by ring
    _ = (a - a') + (b - b') := by rw[←hk, ← hl]
    _ = a + b - (a' + b') := by ring
  use (k * b + l * a')
  symm
  calc (k * b + l * a') * m
    _ = (k * m * b + l * m * a') := by ring
    _ = ((a - a') * b + (b - b') * a') := by rw[←hk, ← hl]
    _ = a * b - a' * b' := by ring

theorem Exercise_4_5_14_a (A: Type) (R S: BinRel A) (B: Set A)
    (hR: equiv_rel R) (hS: ∀ x y : A, S x y ↔ x ∈ B ∧ y ∈ B ∧ R x y):
    equiv_rel_on B S := by
  rcases hR with ⟨refl, symm, trans⟩
  constructor
  rintro x hb
  rw[hS]
  constructor
  exact hb
  constructor
  exact hb
  exact refl x
  constructor
  rintro x y ⟨hbx, hby⟩ hxy
  rw[hS]
  constructor
  exact hby
  constructor
  exact hbx
  rw[hS] at hxy
  rcases hxy with ⟨_, _, hxy⟩
  exact symm x y hxy
  rintro x y z ⟨hbx, hby, hbz⟩ hSxy hSyz
  rw[hS]
  constructor
  exact hbx
  constructor
  exact hbz
  rw[hS] at hSxy
  rcases hSxy with ⟨_, _, hSxy⟩
  rw[hS] at hSyz
  rcases hSyz with ⟨_, _, hSyz⟩
  apply trans
  exact hSxy
  exact hSyz

theorem Exercise_4_5_14_b (A: Type) (R S: BinRel A) (B: Set A)
    (hR: equiv_rel R) (hS: ∀ x y : A, S x y ↔ x ∈ B ∧ y ∈ B ∧ R x y):
    ∀ x ∈ B, equivClass S x = equivClass R x ∩ B := by
  rcases hR with ⟨refl, symm, trans⟩
  rintro x hbx
  apply Set.ext
  rintro m
  constructor
  rintro hm
  simp[equivClass, hS] at hm
  rcases hm with ⟨_, hm', hm⟩
  simp[equivClass]
  constructor
  exact hm
  exact hm'
  rintro ⟨hm, hm'⟩
  simp[equivClass] at hm
  simp[equivClass, hS]
  constructor
  apply And.intro hm' hbx
  apply And.intro hm' hm

theorem Exericise_4_5_15_a (A: Type) (R: BinRel (Set A)) (B: Set A)
    (hR: ∀ X Y: (Set A), R X Y ↔ X ∆ Y ⊆ B):
    equiv_rel R := by
  constructor
  rintro X
  rw[hR]
  rintro A hA
  define at hA
  by_contra
  rcases hA with hA | hA
  rw[Set.diff_self] at hA
  apply hA
  rw[Set.diff_self] at hA
  apply hA
  constructor
  rintro X Y hXY
  simp[hR, symmDiff_def]
  simp[hR, symmDiff_def] at hXY
  symm
  exact hXY
  rintro X Y Z hXY hYZ
  simp[hR, symmDiff_def]
  simp[hR, symmDiff_def] at hXY
  simp[hR, symmDiff_def] at hYZ
  rcases hXY with ⟨hXY, hYX⟩
  rcases hYZ with ⟨hYZ, hZY⟩
  constructor
  rintro x ⟨hx, hx'⟩
  by_cases hy : x ∈ Y
  apply hYZ
  apply And.intro hy hx'
  apply hXY
  apply And.intro hx hy
  rintro a ⟨hZ, hX⟩
  by_cases hY: a ∈ Y
  apply hYX
  apply And.intro hY hX
  apply hZY
  apply And.intro hZ hY

theorem Exercise_4_5_15_b (A: Type) (R: BinRel (Set A)) (B: Set A)
    (hR: ∀ X Y: (Set A), R X Y ↔ X ∆ Y ⊆ B):
    ∀ X : Set A, ∃! Y : Set A, Y ∈ equivClass R X ∧ Y ∩ B = ∅  := by
  rintro X
  exists_unique
  use (X ∩ (Set.univ \ B))
  constructor
  simp[equivClass, hR, symmDiff_def]
  constructor
  rw [Set.diff_inter_distrib_right, Set.diff_self, Set.empty_inter]
  apply Set.empty_subset
  rintro x ⟨hx, hx'⟩
  define at hx'
  demorgan at hx'
  rcases hx' with hx' | hx'
  by_contra
  apply hx'
  exact trivial
  exact hx'
  rw[Set.inter_assoc, Set.diff_inter_self, Set.inter_empty]
  rintro Q P ⟨hQ, hQ''⟩  ⟨hP, hP''⟩
  simp[equivClass, hR, symmDiff] at hQ
  rcases hQ with ⟨hQ, hQ'⟩
  simp[equivClass, hR, symmDiff] at hP
  rcases hP with ⟨hP, hP'⟩
  apply Set.ext
  rintro x
  constructor
  rintro hx
  by_cases h: x ∉ B ∧ x ∈ X ∧ x ∈ P
  rcases h with ⟨_, _, h⟩
  exact h
  demorgan at h;
  have hxB : x ∉ B := by
    by_contra h'
    contradict hQ''
    push_neg
    use x
    constructor
    exact hx
    exact h'
  disj_syll h hxB
  demorgan at h
  have hxX: x ∈ X := by
    by_contra h'
    contradict hQ
    have hQ := hQ (And.intro hx h')
    contradict hxB
    exact hQ
  disj_syll h hxX
  have hP' := hP' (And.intro hxX h)
  contradict hxB
  exact hP'
  rintro hx
  by_cases h: x ∉ B ∧ x ∈ X ∧ x ∈ Q
  rcases h with ⟨_, _, h⟩
  exact h
  demorgan at h;
  have hxB : x ∉ B := by
    by_contra h'
    contradict hP''
    push_neg
    use x
    constructor
    exact hx
    exact h'
  disj_syll h hxB
  demorgan at h
  have hxX: x ∈ X := by
    by_contra h'
    contradict hP
    have hP := hP (And.intro hx h')
    contradict hxB
    exact hP
  disj_syll h hxX
  have hQ' := hQ' (And.intro hxX h)
  contradict hxB
  exact hQ'

theorem Exercise_4_5_16 (U: Type) (A B: Set U) (F: Set (Set U)) (G: Set (Set U))
      (hF': ⋃₀ F ⊆ A) (hG': ⋃₀ G ⊆ B)
      (hF: partition_on A F) (hG: partition_on B G) (hAB: A ∩ B = ∅):
      partition_on (A ∪ B) (F ∪ G) := by
  rcases hF with ⟨totalF, disjointF, nonemptyF⟩
  rcases hG with ⟨totalG, disjointG, nonemptyG⟩
  constructor
  rintro x (hx | hx)
  rcases (totalF x hx) with ⟨M, hM, hM'⟩
  use M
  constructor
  left
  exact hM
  exact hM'
  rcases (totalG x hx) with ⟨M, hM, hM'⟩
  use M
  constructor
  right
  exact hM
  exact hM'
  constructor
  rintro X (hX | hX) Y (hY | hY) XneqY
  exact disjointF X hX Y hY XneqY
  define
  push_neg
  rintro x
  have h: X ∩ Y = ∅ := by
    by_contra h'
    contradict hAB
    push_neg
    push_neg at h'
    rcases h' with ⟨u, hu, hu'⟩
    use u
    constructor
    apply hF'
    use X
    apply hG'
    use Y
  simp[h]
  have h: X ∩ Y = ∅ := by
    by_contra h'
    contradict hAB
    push_neg
    push_neg at h'
    rcases h' with ⟨u, hu, hu'⟩
    use u
    constructor
    apply hF'
    use Y
    apply hG'
    use X
  define
  push_neg
  rintro x
  simp[h]
  exact disjointG X hX Y hY XneqY
  rintro X (hX | hX)
  exact nonemptyF X hX
  exact nonemptyG X hX

theorem Exercise_4_5_17_a (U: Type) (A B: Set U) (R S: BinRel U)
    (hR': extension R ⊆ A ×ˢ A) (hS': extension S ⊆ B ×ˢ B)
    (hR: equiv_rel_on A R) (hS: equiv_rel_on B S) (hAB: A ∩ B = ∅):
    equiv_rel_on (A ∪ B) (RelFromExt (extension R ∪ extension S)) := by
  rcases hR with ⟨reflR, symmR, transR⟩
  rcases hS with ⟨reflS, symmS, transS⟩
  constructor
  rintro x (hx | hx)
  simp[RelFromExt, ext_def]
  left
  exact reflR x hx
  simp[RelFromExt, ext_def]
  right
  exact reflS x hx
  constructor
  rintro m n ⟨hm, hn⟩  (hnm | hnm)
  rcases (hR' hnm) with ⟨hmA, hnA⟩
  simp[RelFromExt, ext_def]
  simp[ext_def] at hnm
  left
  exact symmR m n (And.intro hmA hnA) hnm
  rcases (hS' hnm) with ⟨hmB, hnB⟩
  simp[RelFromExt, ext_def]
  simp[ext_def] at hnm
  right
  exact symmS m n (And.intro hmB hnB) hnm
  rintro x y z ⟨hx, hy, hz⟩ (hxy | hxy) (hyz | hyz)
  rcases (hR' hxy) with ⟨hx', hy'⟩
  rcases (hR' hyz) with ⟨_, hz'⟩
  left
  apply transR
  constructor
  exact hx'
  apply And.intro hy' hz'
  exact hxy
  exact hyz
  contradict hAB
  push_neg
  use y
  constructor
  exact (hR' hxy).2
  exact (hS' hyz).1
  right
  contradict hAB
  push_neg
  use y
  constructor
  exact (hR' hyz).1
  exact (hS' hxy).2
  right
  apply transS
  constructor
  exact (hS' hxy).1
  constructor
  exact (hS' hxy).2
  exact (hS' hyz).2
  exact hxy
  exact hyz

theorem Exercise_4_5_17_b (U: Type) (A B: Set U) (R S: BinRel U)
    (hR': extension R ⊆ A ×ˢ A) (hS': extension S ⊆ B ×ˢ B)
    (hR: equiv_rel_on A R) (hS: equiv_rel_on B S) (hAB: A ∩ B = ∅):
    (∀ x ∈ A, equivClass (RelFromExt (extension R ∪ extension S)) x = equivClass R x) ∧
    ∀ y ∈ B, equivClass (RelFromExt (extension R ∪ extension S)) y = equivClass S y := by
  rcases hR with ⟨reflR, symmR, transR⟩
  rcases hS with ⟨reflS, symmS, transS⟩
  constructor
  rintro x hx
  apply Set.ext
  rintro y
  constructor
  simp[equivClass, RelFromExt]
  rintro (hy | hy)
  exact hy
  contradict hAB
  push_neg
  use x
  constructor
  exact hx
  exact (hS' hy).2
  simp[equivClass, RelFromExt, ext_def]
  rintro hy
  left
  exact hy
  rintro x hx
  apply Set.ext
  rintro y
  constructor
  simp[equivClass, RelFromExt]
  rintro (hy | hy)
  contradict hAB
  push_neg
  use x
  constructor
  exact (hR' hy).2
  exact hx
  exact hy
  simp[equivClass, RelFromExt, ext_def]
  rintro hy
  right
  exact hy

theorem Exercise_4_5_17_c (U: Type) (A B: Set U) (R S: BinRel U)
    (hR': extension R ⊆ A ×ˢ A) (hS': extension S ⊆ B ×ˢ B)
    (hR: equiv_rel_on A R) (hS: equiv_rel_on B S) (hAB: A ∩ B = ∅):
    mod_on U (A ∪ B) (RelFromExt (extension R ∪ extension S))  = mod_on U A R ∪ mod_on U B S := by
  apply Set.ext
  rintro X
  constructor
  rintro hX
  rcases hX with ⟨x, ⟨(hX | hX), hX'⟩⟩
  left
  use x
  constructor
  exact hX
  rw[← hX']
  apply Set.ext
  rintro a
  constructor
  simp[equivClass, RelFromExt, ext_def]
  rintro ha
  left
  exact ha
  simp[equivClass, RelFromExt]
  rintro (ha | ha)
  exact ha
  contradict hAB
  push_neg
  use x
  constructor
  exact hX
  exact (hS' ha).2
  right
  use x
  constructor
  exact hX
  rw[← hX']
  apply Set.ext
  rintro a
  constructor
  simp[equivClass, RelFromExt]
  rintro ha
  right
  exact ha
  simp[equivClass, RelFromExt]
  rintro (ha | ha)
  contradict hAB
  push_neg
  use x
  constructor
  exact (hR' ha).2
  exact hX
  exact ha
  rintro (hX | hX)
  rcases hX with ⟨u, hu, hu'⟩
  use u
  constructor
  apply Or.inl hu
  rw[← hu']
  apply Set.ext
  rintro y
  constructor
  simp[equivClass, RelFromExt]
  rintro (hy | hy)
  exact hy
  contradict hAB
  push_neg
  use u
  constructor
  exact hu
  exact (hS' hy).2
  simp[equivClass, RelFromExt]
  rintro hy
  left
  exact hy
  rcases hX with ⟨u, hu, hu'⟩
  use u
  constructor
  apply Or.inr hu
  rw[← hu']
  apply Set.ext
  rintro y
  constructor
  simp[equivClass, RelFromExt]
  rintro (hy | hy)
  contradict hAB
  push_neg
  use u
  constructor
  exact (hR' hy).2
  exact hu
  exact hy
  simp[equivClass, RelFromExt]
  rintro hy
  right
  exact hy

theorem Exercise_4_5_18 (U: Type) (A: Set U) (F G FG: Set (Set U))
    (hF: partition F) (hG: partition G)
    (hFG: ∀ Z: Set U, Z ∈ FG ↔ Z ≠ ∅ ∧ ∃ X ∈ F, ∃ Y ∈ G, Z = X ∩ Y):
    partition FG := by
  rcases hF with ⟨allF, disjointF, emptyF⟩
  rcases hG with ⟨allG, disjointG, emptyG⟩
  constructor
  rintro x
  rcases (allF x) with ⟨XF, hXF, hXF'⟩
  rcases (allG x) with ⟨XG, hXG, hXG'⟩
  use (XF ∩ XG)
  constructor
  rw[hFG]
  constructor
  push_neg
  use x
  constructor
  exact hXF'
  exact hXG'
  use XF
  constructor
  exact hXF
  use XG
  constructor
  exact hXF'
  exact hXG'
  constructor
  rintro X hX Y hY hXNeqY
  rw[empty]
  by_contra h'
  rcases h' with ⟨u, huX, huY⟩
  contradict hXNeqY
  rw[hFG] at hX
  rw[hFG] at hY
  rcases hX.2 with ⟨F', hF', G', hG', hG''⟩
  rcases hY.2 with ⟨J', hJ', K', hK', hK''⟩
  rw[hG''] at huX
  rw[hK''] at huY
  rw[hG'']
  rw[hK'']
  have h1: F' = J' := by
    have h := disjointF F' hF' J' hJ'
    contrapos at h
    simp at h
    exact h u huX.1 huY.1
  have h2: G' = K' := by
    have h := disjointG G' hG' K' hK'
    contrapos at h
    simp at h
    exact h u huX.2 huY.2
  rw[h1, h2]
  rintro X hX
  by_contra h'
  rw[hFG] at hX
  contradict h'
  have hX := hX.1
  push_neg at hX
  rcases hX with ⟨p, hP⟩
  use p

/-
Exercise 4_5_19
{ℤ⁺, ℤ⁻, {0}, (ℝ \ ℤ)⁺, (ℝ \ ℤ)⁻}
-/

theorem Exercise_4_5_20_a (A: Type) (R S: BinRel A) (hR: equiv_rel R)
    (hS: equiv_rel S):
    equiv_rel (RelFromExt ((extension S) ∩ (extension R))) := by
  rcases hR with ⟨reflR, symmR, transR⟩
  rcases hS with ⟨reflS, symmS, transS⟩
  constructor
  rintro x
  simp[RelFromExt, ext_def]
  constructor
  exact reflS x
  exact reflR x
  constructor
  rintro x y hxy
  simp[RelFromExt, ext_def] at hxy
  rcases hxy with ⟨hxy, hxy'⟩
  simp[RelFromExt, ext_def]
  constructor
  exact symmS x y hxy
  exact symmR x y hxy'
  rintro x y z hxy hyz
  simp[RelFromExt, ext_def] at hxy
  simp[RelFromExt, ext_def] at hyz
  simp[RelFromExt, ext_def]
  rcases hxy with ⟨hxy, hxy'⟩
  rcases hyz with ⟨hyz, hyz'⟩
  constructor
  exact transS x y z hxy hyz
  exact transR x y z hxy' hyz'

theorem Exercise_4_5_20_b (A: Type) (R S: BinRel A) (hR: equiv_rel R)
    (hS: equiv_rel S):
    ∀ x : A, equivClass (RelFromExt ((extension S) ∩ (extension R))) x = equivClass R x ∩ equivClass S x := by
  rintro x
  apply Set.ext
  rintro a
  constructor
  simp [equivClass, RelFromExt, ext_def]
  rintro hSax hRax
  constructor
  exact hRax
  exact hSax
  simp [equivClass, RelFromExt, ext_def]
  rintro hRax hSax
  constructor
  exact hSax
  exact hRax

theorem Exercise_4_5_20_c (A: Type) (R S: BinRel A) (RS: Set (Set A)) (hR: equiv_rel R)
    (hS: equiv_rel S) (hRS: ∀ X: Set A, X ∈ RS ↔ X ≠ ∅ ∧ ∃ Y ∈ mod A R, ∃ Z ∈ mod A S, X = Y ∩ Z):
    mod A (RelFromExt ((extension S) ∩ (extension R))) = RS := by
    rcases hR with ⟨reflR, symmR, transR⟩
    rcases hS with ⟨reflS, symmS, transS⟩
    apply Set.ext
    rintro X
    constructor
    rintro hX
    simp[hRS]
    rcases hX with ⟨x , hx⟩
    simp[equivClass, RelFromExt, ext_def] at hx
    rw[← hx]
    constructor
    push_neg
    use x
    simp
    constructor
    exact reflS x
    exact reflR x
    use equivClass R x
    constructor
    simp[mod]
    use equivClass S x
    constructor
    simp[mod]
    apply Set.ext
    rintro a
    constructor
    rintro ha
    define at ha
    rcases ha with ⟨ha, ha'⟩
    simp [equivClass]
    constructor
    exact ha'
    exact ha
    simp[equivClass]
    rintro ha ha'
    constructor
    exact ha'
    exact ha
    rintro hRS'
    simp[hRS] at hRS'
    rcases hRS' with ⟨hRS, hRS'⟩
    rcases hRS' with ⟨P, hP, Q, hQ, neq⟩
    rcases hP with ⟨a, ha⟩
    rcases hQ with ⟨b, hb⟩
    push_neg at hRS
    rw[neq, ← ha, ← hb] at hRS
    rcases hRS with ⟨z, hz, hz'⟩
    use z
    simp[equivClass, RelFromExt, ext_def, neq, ← ha, ← hb]
    apply Set.ext
    rintro q
    constructor
    simp[equivClass] at hz
    simp[equivClass] at hz'
    rintro hq
    simp at hq
    rcases hq with ⟨hq, hq'⟩
    simp
    constructor
    exact transR q z a hq' hz
    exact transS q z b hq hz'
    simp
    rintro hq hq'
    simp[equivClass] at hz
    simp[equivClass] at hz'
    constructor
    exact transS q b z hq' (symmS z b hz')
    exact transR q a z hq (symmR z a hz)

theorem Exercise_4_5_21 (A B: Type) (F: Set (Set A)) (G: Set (Set B)) (hF: partition F)
    (hG: partition G):
    let FG: Set (Set (A × B)) := {Z : Set (A × B) | ∃ X ∈ F, ∃ Y ∈ G, (Z = X ×ˢ Y)};
    partition FG := by
  rcases hF with ⟨allF, disjointF, emptyF⟩
  rcases hG with ⟨allG, disjointG, emptyG⟩
  constructor
  rintro ⟨m , n⟩
  rcases (allF m) with ⟨M, hM, hM'⟩
  rcases (allG n) with ⟨N, hN, hN'⟩
  use (M ×ˢ N)
  constructor
  use M
  constructor
  exact hM
  use N
  constructor
  exact hM'
  exact hN'
  constructor
  rintro Z hZ Y hY
  rcases hZ with ⟨F', hF', G', hG', hF'G'⟩
  rcases hY with ⟨F'', hF'', G'', hG'', hF''G''⟩
  contrapos
  rintro h
  rcases h with ⟨⟨p, q⟩ , hpq, hpq'⟩
  rw[hF'G', hF''G'']
  rw[hF'G'] at hpq
  rw[hF''G''] at hpq'
  have hFirst: F' = F'' := by
    have h := disjointF F' hF' F'' hF''
    contrapos at h
    apply h
    use p
    constructor
    exact hpq.1
    exact hpq'.1
  have hSecond: G' = G'' := by
    have h := disjointG G' hG' G'' hG''
    contrapos at h
    apply h
    use q
    constructor
    exact hpq.2
    exact hpq'.2
  rw[hFirst, hSecond]
  rintro X hX
  rcases hX with ⟨F', hF', G', hG', hF'G'⟩
  rw[hF'G']
  define
  push_neg
  have hFirst := emptyF F' hF'
  define at hFirst
  push_neg at hFirst
  rcases hFirst with ⟨a, ha⟩
  have hSecond := emptyG G' hG'
  define at hSecond
  push_neg at hSecond
  rcases hSecond with ⟨b, hb⟩
  use (a, b)
  constructor
  exact ha
  exact hb

/-
Exercise 4_5_22
{(ℝ+, ℝ+), (ℝ-, ℝ-), (ℝ+, ℝ-), (ℝ-, ℝ+), (ℝ+, 0), (ℝ-, 0), (0, ℝ+), (0, ℝ-), (0,0)}
(ℝ+, ℝ+) = top right quadrant
(ℝ-, ℝ-) = bottom left quadrant
(ℝ+, ℝ-) = bottom right quadrant
(ℝ-, ℝ+) = top left quadrant
(ℝ+, 0) = right x axis
(ℝ-, 0) = left x axis
(0, ℝ+) = top y axis
(0, ℝ-) = bottom y axis
(0,0) = center
-/

theorem Exercise_4_5_23_a (A B: Type) (R: BinRel A) (S: BinRel B)
    (hR: equiv_rel R) (hS: equiv_rel S):
    let T := {((a, b), (a', b')): (A × B) × (A × B) | R a a' ∧ S b b'}
    equiv_rel (RelFromExt T) := by
  rcases hR with ⟨reflR, symmR, transR⟩
  rcases hS with ⟨reflS, symmS, transS⟩
  constructor
  rintro ⟨m , n⟩
  define
  constructor
  exact reflR m
  exact reflS n
  constructor
  rintro ⟨m , n⟩  ⟨m', n'⟩ hmn
  define at hmn
  define
  constructor
  exact symmR m m' hmn.1
  exact symmS n n' hmn.2
  rintro ⟨x, x'⟩ ⟨y, y'⟩ ⟨z, z'⟩ hxy hyz
  define
  define at hxy
  define at hyz
  constructor
  exact transR x y z hxy.1 hyz.1
  exact transS x' y' z' hxy.2 hyz.2

theorem Exercise_4_5_23_b (A B: Type) (R: BinRel A) (S: BinRel B) (a : A) (b : B)
    (hR: equiv_rel R) (hS: equiv_rel S):
    let T := {((a, b), (a', b')): (A × B) × (A × B) | R a a' ∧ S b b'}
    equivClass (RelFromExt T) (a, b)  = equivClass R a ×ˢ equivClass S b := by
  apply Set.ext
  rintro ⟨m, n⟩
  constructor
  rintro hmn
  rcases hmn with ⟨h, h'⟩
  constructor
  define
  exact h
  define
  exact h'
  rintro hmn
  simp[equivClass] at hmn
  define
  constructor
  exact hmn.1
  exact hmn.2

theorem Exercise_4_5_23_c (A B: Type) (R: BinRel A) (S: BinRel B)
    (hR: equiv_rel R) (hS: equiv_rel S):
    let T := {((a, b), (a', b')): (A × B) × (A × B) | R a a' ∧ S b b'}
    mod (A × B) (RelFromExt T) = {Z : Set (A × B) | ∃ X ∈ (mod A R), ∃ Y ∈ (mod B S), (Z = X ×ˢ Y)} := by
  apply Set.ext
  rintro X
  constructor
  rintro hX
  rcases hX with ⟨⟨a, b⟩, h⟩
  simp
  use (equivClass R a)
  constructor
  use a
  use (equivClass S b)
  constructor
  use b
  rw[← h]
  apply Set.ext
  rintro ⟨a', b'⟩
  constructor
  rintro ha'b'
  define at ha'b'
  constructor
  exact ha'b'.1
  exact ha'b'.2
  rintro ha'b'
  rcases ha'b' with ⟨ha'b'1, ha'b'2⟩
  define
  constructor
  exact ha'b'1
  exact ha'b'2
  rintro hX
  define at hX
  define
  rcases hX with ⟨A', hA', B', hB', hX ⟩
  rcases hA' with ⟨a', ha'⟩
  rcases hB' with ⟨b', hb'⟩
  use (a', b')
  rw[hX, ← ha', ← hb']
  apply Set.ext
  rintro ⟨m, n⟩
  constructor
  rintro hmn
  define at hmn
  constructor
  exact hmn.1
  exact hmn.2
  rintro hmn
  define at hmn
  define
  constructor
  exact hmn.1
  exact hmn.2

theorem Exercise_4_5_24_a (A: Type) (R S: BinRel A) (hS: equiv_rel S)
    (hCom: ∀ x y x' y' : A, S x x' → S y y' → (R x y ↔ R x' y')):
    ∃! T : Set ((Set A) × (Set A)), T ⊆ (mod A S ×ˢ mod A S) ∧  (∀ x y : A, (equivClass S x, equivClass S y) ∈ T ↔ R x y) := by
  rcases hS with ⟨reflS, symmS, transS⟩
  exists_unique
  use ({(X, Y) :  (Set A) × (Set A) | X ∈ mod A S ∧ Y ∈ mod A S ∧  ∀ x ∈ X, ∀ y ∈ Y, R x y})
  constructor
  rintro ⟨X, Y⟩ ⟨hXY, hXY', hXY''⟩
  constructor
  exact hXY
  exact hXY'
  rintro x y
  constructor
  rintro ⟨hxy, hxy', hxy''⟩
  exact hxy'' x (reflS x) y (reflS y)
  rintro hxy
  define
  constructor
  use x
  constructor
  use y
  rintro x' hx' y' hy'
  exact (hCom x' y' x y hx' hy').mpr hxy
  rintro T₁ T₂ ⟨hT₁, hT₁'⟩  ⟨hT₂, hT₂'⟩
  apply Set.ext
  rintro ⟨X, Y⟩
  constructor
  rintro hXY
  rcases hT₁ hXY with ⟨hX, hY⟩
  rcases hX with ⟨x, hx⟩
  rcases hY with ⟨y, hy⟩
  simp at hx
  simp at hy
  simp [← hx, ← hy]
  apply (hT₂' x y).mpr
  apply (hT₁' x y).mp
  rw[hx, hy]
  exact hXY
  rintro hXY
  rcases hT₂ hXY with ⟨hX, hY⟩
  rcases hX with ⟨x, hx⟩
  rcases hY with ⟨y, hy⟩
  simp at hx
  simp at hy
  simp [← hx, ← hy]
  apply (hT₁' x y).mpr
  apply (hT₂' x y).mp
  rw[hx, hy]
  exact hXY

theorem Exercise_4_5_24_b (A: Type) (T: BinRel (Set A)) (R S: BinRel A) (hS: equiv_rel S)
    (hT: extension T ⊆ ((mod A S) ×ˢ (mod A S))) (hT': ∀ x y : A, T (equivClass S x) (equivClass S x) ↔ R x y):
    ∀ x y x' y' : A, S x x' ∧ S y y' → (R x y ↔ R x' y') := by
  rcases hS with ⟨reflS, symmS, transS⟩
  rintro x y x' y' ⟨hSxx', hSyy'⟩
  constructor
  rintro hRxy
  have h := (hT' x y).mpr hRxy
  have h1: (equivClass S x) = (equivClass S x') := by
    apply Set.ext
    rintro a
    constructor
    rintro ha
    define at ha
    define
    exact transS a x x' ha hSxx'
    rintro ha
    define
    define at ha
    exact transS a x' x ha (symmS x x' hSxx')
  apply (hT' x' y').mp
  rw[h1] at h
  exact h
  rintro hRx'y'
  have h := (hT' x' y').mpr hRx'y'
  have h1: (equivClass S x') = (equivClass S x) := by
    apply Set.ext
    rintro a
    constructor
    rintro ha
    define at ha
    define
    exact transS a x' x ha (symmS x x' hSxx')
    rintro ha
    define
    define at ha
    exact transS a x x' ha hSxx'
  apply (hT' x y).mp
  rw[h1] at h
  exact h

theorem Exercise_4_5_25_a (A: Type) (R: BinRel A) (hReflR: reflexive R)
    (hTransR: transitive R): let S := (extension R) ∩ (inv (extension R))
    equiv_rel (RelFromExt S) := by
  constructor
  rintro x
  constructor
  exact hReflR x
  rw[inv]
  exact hReflR x
  constructor
  rintro x y ⟨hxy, hxy'⟩
  constructor
  exact hxy'
  exact hxy
  rintro x y z ⟨hxy, hxy'⟩ ⟨hyz, hyz'⟩
  constructor
  exact hTransR x y z hxy hyz
  exact hTransR z y x hyz' hxy'

theorem Exercise_4_5_25_b (A: Type) (R S: BinRel A) (hReflR: reflexive R)
    (hTransR: transitive R): let S := (extension R) ∩ (inv (extension R))
    let S := RelFromExt S
    ∃! T : Set ((Set A) × (Set A)), T ⊆ (mod A S ×ˢ mod A S) ∧
    (∀ x y : A, (equivClass S x, equivClass S y) ∈ T ↔ R x y) := by
  have g := Exercise_4_5_25_a A R hReflR hTransR
  simp at g
  apply Exercise_4_5_24_a A R (RelFromExt (extension R ∩ inv (extension R))) g
  rintro x y x' y' ⟨hSxx, hSxx'⟩ ⟨hSyy, hSyy'⟩
  constructor
  rintro hxy
  exact hTransR x' y y' (hTransR x' x y hSxx' hxy) hSyy
  rintro h
  apply hTransR x x' y hSxx (hTransR x' y' y h hSyy')

theorem Exercise_4_5_25_c (A: Type) (R S: BinRel A) (T: BinRel (Set A)) (hReflR: reflexive R)
    (hTransR: transitive R) (hS: S =  RelFromExt ((extension R) ∩ (inv (extension R))))
    (hT : extension T ⊆ (mod A S ×ˢ mod A S))
    (hT' : (∀ x y : A, T (equivClass S x) (equivClass S y) ↔ R x y)):
    partial_order_on (mod A S) T := by
  constructor
  rintro X hX
  rcases hX with ⟨x, hx⟩
  rw[← hx]
  apply (hT' x x).mpr
  exact hReflR x
  constructor
  rintro X Y Z ⟨hX, hY, hZ⟩ hXY hYZ
  rcases hX with ⟨x, hx⟩
  rcases hY with ⟨y, hy⟩
  rcases hZ with ⟨z, hz⟩
  rw[← hx, ← hz]
  rw[← hx, ← hy] at hXY
  rw[← hy, ← hz] at hYZ
  apply (hT' x z).mpr
  apply (hT' x y).mp at hXY
  apply (hT' y z).mp at hYZ
  exact hTransR x y z hXY hYZ
  rintro X Y ⟨hX, hY⟩ hXY hYX
  rcases hX with ⟨x, hx⟩
  rcases hY with ⟨y, hy⟩
  rw[← hx, ← hy]
  rw[← hx, ← hy] at hXY
  rw[← hy, ← hx] at hYX
  apply (hT' x y).mp at hXY
  apply (hT' y x).mp at hYX
  apply Set.ext
  rintro a
  constructor
  rintro ha
  rw[hS] at ha
  rcases ha with ⟨ha, ha'⟩
  rw[hS]
  constructor
  exact hTransR a x y ha hXY
  exact hTransR y x a hYX ha'
  rintro ha
  rw[hS] at ha
  rcases ha with ⟨ha, ha'⟩
  rw[hS]
  constructor
  exact hTransR a y x ha hYX
  exact hTransR x y a hXY ha'

theorem Exercise_4_5_26_a (A : Set (Set ℤ)) (I: Set ℤ) (R: Set (Set ℤ × Set ℤ)) (hI: I = {i: ℤ | i > 0 ∧ i ≤ 100})
    (hA: A = 𝒫 I) (hR: R = {(X, Y) :  Set ℤ × Set ℤ  | X ∈ A ∧ Y ∈ A ∧  Y.ncard ≥ X.ncard  } ):
    preorder_on A (RelFromExt R) := by
  constructor
  rintro X hX
  simp [RelFromExt , hR]
  exact hX
  rintro X Y Z ⟨hX, hY, hZ⟩
  simp[RelFromExt, hR]
  rintro hX hY hXY hY hZ hYZ
  constructor
  exact hX
  constructor
  exact hZ
  exact le_trans hXY hYZ

/-
Exercise 4_5_26_b
A / S = set of 1 element sets, set of 2 element sets, set of 3 element sets...
T = pairs of equivalence classes X Y, where an element of Y is at least as large
an element of X
A / S has 101 elements
T is a total order
-/

theorem Exercise_4_5_27_a (A: Type) (P: Set (Set (Set A)))
    (hP: P = {X | partition X})
    (R: Set (Set (Set A) × Set (Set A)))
    (hR: R = {(F, G): Set (Set A) × Set (Set A) | F ∈ P ∧ G ∈ P ∧  ∀ X ∈ F, ∃ Y ∈ G, X ⊆ Y}):
    partial_order_on P (RelFromExt R) := by
  constructor
  rintro L hL
  simp[RelFromExt, hR]
  constructor
  exact hL
  rintro X hX
  use X
  constructor
  rintro X Y Z ⟨hX, hY, hZ⟩ hXY hYZ
  simp[RelFromExt, hR]
  constructor
  exact hX
  constructor
  exact hZ
  simp[RelFromExt, hR] at hXY
  simp[RelFromExt, hR] at hYZ
  rcases hXY with ⟨_, _, hXY⟩
  rcases hYZ with ⟨_, _, hYZ⟩
  rintro Q hQ
  rcases hXY Q hQ with ⟨L, hL, hQL⟩
  rcases hYZ L hL with ⟨M, hM, hLM⟩
  use M
  constructor
  exact hM
  exact subset_trans hQL hLM
  rintro F G ⟨hF, hG⟩ hFG hGF
  simp[RelFromExt, hR] at hFG
  simp[RelFromExt, hR] at hGF
  rcases hFG with ⟨_, _, hFG⟩
  rcases hGF with ⟨_, _, hGF⟩
  apply Set.ext
  rintro L
  constructor
  rintro hL
  rcases hFG L hL with ⟨M, hM, hLM⟩
  rcases hGF M hM with ⟨N, hN, hMN⟩
  rw[hP] at hF
  define at hF
  rcases hF with ⟨_, hF, hF'⟩
  have h: L = N := by
    have hF := hF L hL N hN
    contrapos at hF
    have hF' := hF' L hL
    simp[empty] at hF'
    rcases hF' with ⟨s, hs⟩
    apply hF
    use s
    constructor
    exact hs
    have final: L ⊆ N :=  by
      apply subset_trans
      exact hLM
      exact hMN
    exact final hs
  have h': L = M := by
    rw[← h] at hMN
    apply Set.ext
    rintro x
    constructor
    rintro hx
    exact hLM hx
    rintro hx
    exact hMN hx
  rw[← h'] at hM
  exact hM
