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
  rintro x y z ⟨hx, hy, hz⟩ (hxy | hxy) hyz
  
