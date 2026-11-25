module

public import RBMTransitionEdge.Localized.Expansion.Counts
public import RBMTransitionEdge.Localized.Expansion.PkgShape

@[expose] public section

/-!
# The words of the derivative structures of the further expansion

The words of the derivative structures of (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression] in the proof of Lemma 5.5
[claim_estimate_remainder_terms], the words they come from, and the count (5.67) [eq:sumai].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The word of `𝒯.pkgStart` behind a word of a derivative structure of (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression]: every `𝒢_b Δ 𝒢_b` produced by
`∂𝒢 = -𝒢 Δ 𝒢` collapsed back to `𝒢_b`; a hit light weight `⟨(𝒢_b - 𝔐_b) E_y⟩` becomes `𝒢_b E_y`. -/
def pkgColl (w : List PkgLetter) : List PkgLetter :=
  w.foldr (fun x acc => match x, acc with
    | .lw (.res a), .ent _ _ :: .lw (.res b) :: t =>
      if a == b then .lw (.res a) :: t else x :: acc
    | _, _ => x :: acc) []

/-! ### Auxiliary facts: the collapse `pkgColl` -/

/-- The step of the right fold that defines `pkgColl`: `𝒢_b Δ 𝒢_b ↦ 𝒢_b` as in (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression]. -/
private def collStep (x : PkgLetter) (acc : List PkgLetter) : List PkgLetter :=
  match x, acc with
  | .lw (.res a), .ent _ _ :: .lw (.res b) :: t =>
    if a == b then .lw (.res a) :: t else x :: acc
  | _, _ => x :: acc

private theorem pkgColl_nil : pkgColl [] = [] := rfl

private theorem pkgColl_cons (x : PkgLetter) (w : List PkgLetter) :
    pkgColl (x :: w) = collStep x (pkgColl w) := rfl

private theorem pkgColl_append (X Z : List PkgLetter) :
    pkgColl (X ++ Z) = X.foldr collStep (pkgColl Z) := by
  change (X ++ Z).foldr collStep [] = X.foldr collStep (Z.foldr collStep [])
  rw [List.foldr_append]

/-- A step that finds no `Δ 𝒢` at the head of the accumulator only prepends. -/
private theorem collStep_of_head (x : PkgLetter) (acc : List PkgLetter)
    (h : ∀ (u v : ℕ) (b : Fin 2) (t : List PkgLetter), acc ≠ .ent u v :: .lw (.res b) :: t) :
    collStep x acc = x :: acc := by
  rcases x with ⟨y⟩ | ⟨u, v⟩
  · rcases y with a | _ | _ | _
    · rcases acc with _ | ⟨z, t⟩
      · rfl
      · rcases z with y | ⟨u, v⟩
        · rfl
        · rcases t with _ | ⟨z', t'⟩
          · rfl
          · rcases z' with y' | ⟨u', v'⟩
            · rcases y' with b | _ | _ | _
              · exact absurd rfl (h u v b t')
              all_goals rfl
            · rfl
    all_goals rfl
  · rfl

private theorem collStep_res (a : Fin 2) (acc : List PkgLetter) :
    ∃ acc', collStep (.lw (.res a)) acc = .lw (.res a) :: acc' := by
  rcases acc with _ | ⟨z, t⟩
  · exact ⟨_, rfl⟩
  · rcases z with y | ⟨u, v⟩
    · exact ⟨_, rfl⟩
    · rcases t with _ | ⟨z', t'⟩
      · exact ⟨_, rfl⟩
      · rcases z' with y' | ⟨u', v'⟩
        · rcases y' with b | _ | _ | _
          · by_cases hab : a = b
            · subst hab
              exact ⟨t', by simp [collStep]⟩
            · exact ⟨.ent u v :: .lw (.res b) :: t', by simp [collStep, hab]⟩
          all_goals exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩

/-- Inserting `Δ` at a resolvent, `𝒢_c ↦ 𝒢_c Δ 𝒢_c` as in `∂𝒢 = -𝒢 Δ 𝒢` of (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression], does not change `pkgColl`. -/
private theorem pkgColl_ins (X Y : List PkgLetter) (c : Fin 2) (u v : ℕ) :
    pkgColl (X ++ [.lw (.res c), .ent u v, .lw (.res c)] ++ Y) =
      pkgColl (X ++ .lw (.res c) :: Y) := by
  have key : pkgColl ([.lw (.res c), .ent u v, .lw (.res c)] ++ Y) =
      pkgColl (.lw (.res c) :: Y) := by
    obtain ⟨A', hA'⟩ := collStep_res c (pkgColl Y)
    simp only [List.cons_append, List.nil_append, pkgColl_cons]
    rw [hA']
    simp [collStep]
  calc pkgColl (X ++ [.lw (.res c), .ent u v, .lw (.res c)] ++ Y)
      = pkgColl (X ++ ([.lw (.res c), .ent u v, .lw (.res c)] ++ Y)) := by rw [List.append_assoc]
    _ = X.foldr collStep (pkgColl ([.lw (.res c), .ent u v, .lw (.res c)] ++ Y)) :=
        pkgColl_append _ _
    _ = X.foldr collStep (pkgColl (.lw (.res c) :: Y)) := by rw [key]
    _ = pkgColl (X ++ .lw (.res c) :: Y) := (pkgColl_append _ _).symm

private theorem pkgColl_free (w : List PkgLetter) (h : ∀ z ∈ w, PkgLetter.isEnt z = false) :
    pkgColl w = w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have h' : ∀ z ∈ w, PkgLetter.isEnt z = false := fun z hz => h z (List.mem_cons_of_mem _ hz)
    rw [pkgColl_cons, ih h']
    refine collStep_of_head _ _ ?_
    intro u v b t hw
    have := h' (.ent u v) (by rw [hw]; simp)
    simp [PkgLetter.isEnt] at this

private theorem pkgColl_snoc (W : List PkgLetter) (hW : ∀ z ∈ W, PkgLetter.isEnt z = false)
    (u v : ℕ) : pkgColl (W ++ [.ent u v]) = W ++ [.ent u v] := by
  induction W with
  | nil => rfl
  | cons x W ih =>
    have h' : ∀ z ∈ W, PkgLetter.isEnt z = false := fun z hz => hW z (List.mem_cons_of_mem _ hz)
    rw [List.cons_append, pkgColl_cons, ih h']
    refine collStep_of_head _ _ ?_
    intro u' v' b t hw
    cases W with
    | nil => simp at hw
    | cons z W' =>
      have := h' z (by simp)
      simp only [List.cons_append, List.cons.injEq] at hw
      rw [hw.1] at this
      simp [PkgLetter.isEnt] at this

private theorem pkgColl_weight (b : Fin 2) (y u v : ℕ) :
    pkgColl [.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)] =
      [.lw (.res b), .lw (.proj y)] := by
  simp [pkgColl_cons, pkgColl_nil, collStep]

private theorem split_at {α : Type*} (w : List α) (r : ℕ) (x : α) (h : w[r]? = some x) :
    w = w.take r ++ x :: w.drop (r + 1) := by
  obtain ⟨hr, rfl⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.getElem_cons_drop hr, List.take_append_drop]

/-- The terms of one derivative `PkgExpr.dent` of (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression], with the change of the fields: a resolvent
of a loop is doubled with a `Δ` in between, or a light weight becomes a new loop. -/
private theorem dent_cases' (R R' : PkgExpr) (u v : ℕ) (h : R' ∈ R.dent u v) :
    (∃ (ℓ : ℕ) (X Y : List PkgLetter) (a : Fin 2), R.loops[ℓ]? = some (X ++ .lw (.res a) :: Y) ∧
      R'.cf = -R.cf ∧ R'.nb = R.nb ∧ R'.weights = R.weights ∧
      R'.loops = R.loops.set ℓ (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y) ∧
      ((X ++ .lw (.res a) :: Y).any PkgLetter.isEnt = true → R'.dexp = R.dexp ∧ R'.S = R.S) ∧
      ((X ++ .lw (.res a) :: Y).any PkgLetter.isEnt = false →
        R'.dexp = R.dexp - 1 ∧ R'.S = R.S + 1)) ∨
    ∃ (j : ℕ) (b : Fin 2) (y : ℕ), R.weights[j]? = some (b, y) ∧
      R'.cf = -R.cf ∧ R'.nb = R.nb ∧ R'.dexp = R.dexp - 1 ∧ R'.S = R.S + 1 ∧
      R'.weights = R.weights.eraseIdx j ∧
      R'.loops = R.loops ++ [[.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)]] := by
  unfold PkgExpr.dent at h
  rcases List.mem_append.1 h with h | h
  · left
    obtain ⟨ℓ, -, h⟩ := List.mem_flatMap.1 h
    rcases hℓ : R.loops[ℓ]? with _ | w
    · simp [hℓ] at h
    · simp only [hℓ] at h
      obtain ⟨r, -, h⟩ := List.mem_filterMap.1 h
      split at h
      · rename_i a hr
        simp only [Option.some.injEq] at h
        have hw := split_at w r _ hr
        refine ⟨ℓ, w.take r, w.drop (r + 1), a, by rw [← hw]; exact hℓ, ?_⟩
        subst h
        refine ⟨rfl, rfl, rfl, rfl, fun hany => ?_, fun hany => ?_⟩
        · rw [← hw] at hany
          change (if (!w.any PkgLetter.isEnt) = true then R.dexp - 1 else R.dexp) = R.dexp ∧
            (if (!w.any PkgLetter.isEnt) = true then R.S + 1 else R.S) = R.S
          simp [hany]
        · rw [← hw] at hany
          change (if (!w.any PkgLetter.isEnt) = true then R.dexp - 1 else R.dexp) = R.dexp - 1 ∧
            (if (!w.any PkgLetter.isEnt) = true then R.S + 1 else R.S) = R.S + 1
          simp [hany]
      · simp at h
  · right
    obtain ⟨j, -, h⟩ := List.mem_filterMap.1 h
    split at h
    · rename_i b y hj
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨j, b, y, hj, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp at h

/-! ### Auxiliary facts: counts and invariants along one derivative -/

private theorem free_of_any' {l : List PkgLetter} (h : l.any PkgLetter.isEnt = false) :
    ∀ z ∈ l, PkgLetter.isEnt z = false := by
  intro z hz
  by_contra hne
  have : l.any PkgLetter.isEnt = true := List.any_eq_true.2 ⟨z, hz, by simpa using hne⟩
  rw [this] at h
  exact absurd h (by simp)

private theorem countP_ins_res (X Y : List PkgLetter) (a : Fin 2) (u v : ℕ) :
    (X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y).countP PkgLetter.isRes =
      (X ++ PkgLetter.lw (.res a) :: Y).countP PkgLetter.isRes + 1 := by
  simp [List.countP_append, List.countP_cons, PkgLetter.isRes]
  omega

private theorem countP_ins_ent (X Y : List PkgLetter) (a : Fin 2) (u v : ℕ) :
    (X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y).countP PkgLetter.isEnt =
      (X ++ PkgLetter.lw (.res a) :: Y).countP PkgLetter.isEnt + 1 := by
  simp [List.countP_append, List.countP_cons, PkgLetter.isEnt]
  omega

private theorem set_self' {α : Type*} : ∀ (l : List α) (i : ℕ) (x : α), l[i]? = some x →
    l.set i x = l
  | [], i, x, h => by simp at h
  | y :: l, 0, x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rfl
  | y :: l, i + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      simp [set_self' l i x h]

/-- Replacing the entry `w` at position `i` of a list changes the count of entries with a
property by the difference of the indicators. -/
private theorem countP_set' {α : Type*} (g : α → Bool) :
    ∀ (l : List α) (i : ℕ) (w x : α), l[i]? = some w →
      (l.set i x).countP g + (if g w = true then 1 else 0) =
        l.countP g + (if g x = true then 1 else 0)
  | [], i, w, x, h => by simp at h
  | y :: l, 0, w, x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, List.countP_cons]
      split_ifs <;> omega
  | y :: l, i + 1, w, x, h => by
      have := countP_set' g l i w x (by simpa using h)
      simp only [List.set_cons_succ, List.countP_cons]
      split_ifs at this ⊢ <;> omega

/-- The invariants of a derivative structure `R` of `T` after `k` derivatives, (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression] and (5.67) [eq:sumai]: the words behind its
loops, the counts per word, the words without `Δ`, the letters `Λ̃` of the first word, and the
coefficient. `R₀ = T.pkgStart`, `F₀` the letters `Λ̃` of its first word. -/
private structure WInv (T : LoopExpr) (R₀ : PkgExpr) (F₀ : List PkgLetter) (k : ℕ)
    (R : PkgExpr) : Prop where
  perm : ∃ hs : List (Fin 2 × ℕ), (R.weights ++ hs).Perm T.weights ∧
    R.loops.map pkgColl = R₀.loops ++ hs.map fun y => [.lw (.res y.1), .lw (.proj y.2)]
  cnt : ∀ w ∈ R.loops, w.countP PkgLetter.isRes + (pkgColl w).countP PkgLetter.isEnt =
    (pkgColl w).countP PkgLetter.isRes + w.countP PkgLetter.isEnt
  free : ∀ w ∈ R.loops, w.any PkgLetter.isEnt = false → ∃ w₀ ∈ T.loops, w = w₀.map PkgLetter.lw
  head : ∃ (W : List PkgLetter) (rest : List (List PkgLetter)),
    R.loops = W :: rest ∧ W.filter PkgLetter.isLam = F₀
  cf : R.cf = (-1) ^ k
  nb : R.nb = T.nb
  dS : R.dexp + R.S = T.dexp + T.S
  S : R.S = T.S + (R.loops.countP fun w =>
    w.any PkgLetter.isEnt && !(pkgColl w).any PkgLetter.isEnt)

private theorem WInv.step {T : LoopExpr} {R₀ : PkgExpr} {F₀ : List PkgLetter} {k : ℕ}
    {R R' : PkgExpr} (u v : ℕ) (hI : WInv T R₀ F₀ k R) (h : R' ∈ R.dent u v) :
    WInv T R₀ F₀ (k + 1) R' := by
  rcases dent_cases' R R' u v h with
    ⟨ℓ, X, Y, a, hℓ, hcf, hnb, hwt, hl, hent, hfree⟩ |
    ⟨j, b, y, hj, hcf, hnb, hdx, hS, hwt, hl⟩
  · have hmem : X ++ PkgLetter.lw (.res a) :: Y ∈ R.loops := List.mem_of_getElem? hℓ
    have hC := pkgColl_ins X Y a u v
    have hres := countP_ins_res X Y a u v
    have hentc := countP_ins_ent X Y a u v
    have hany2 : (X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y).any
        PkgLetter.isEnt = true := by
      simp [List.any_append, PkgLetter.isEnt]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨hs, hp, hm⟩ := hI.perm
      refine ⟨hs, by rw [hwt]; exact hp, ?_⟩
      have e : (R.loops.map pkgColl).set ℓ (pkgColl (X ++ PkgLetter.lw (.res a) :: Y)) =
          R.loops.map pkgColl :=
        set_self' _ ℓ _ (by rw [List.getElem?_map, hℓ]; rfl)
      rw [hl, List.map_set, hC, e]
      exact hm
    · intro w hw
      rw [hl] at hw
      rcases List.mem_or_eq_of_mem_set hw with hw | rfl
      · exact hI.cnt w hw
      · have := hI.cnt _ hmem
        rw [hC, hres, hentc]
        omega
    · intro w hw hany
      rw [hl] at hw
      rcases List.mem_or_eq_of_mem_set hw with hw | rfl
      · exact hI.free w hw hany
      · rw [hany2] at hany
        exact absurd hany (by simp)
    · obtain ⟨W, rest, hL, hF⟩ := hI.head
      cases ℓ with
      | zero =>
          rw [hL] at hℓ
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hℓ
          subst hℓ
          refine ⟨_, rest, by rw [hl, hL]; rfl, ?_⟩
          rw [← hF]
          simp [List.filter_append, PkgLetter.isLam]
      | succ m =>
          exact ⟨W, rest.set m _, by rw [hl, hL, List.set_cons_succ], hF⟩
    · rw [hcf, hI.cf, pow_succ]
      ring
    · rw [hnb]
      exact hI.nb
    · have := hI.dS
      by_cases hany : (X ++ PkgLetter.lw (.res a) :: Y).any PkgLetter.isEnt = true
      · obtain ⟨h1, h2⟩ := hent hany
        omega
      · have hany' : (X ++ PkgLetter.lw (.res a) :: Y).any PkgLetter.isEnt = false := by
          simpa using hany
        obtain ⟨h1, h2⟩ := hfree hany'
        omega
    · have hcs := countP_set' (fun w : List PkgLetter =>
        w.any PkgLetter.isEnt && !(pkgColl w).any PkgLetter.isEnt) R.loops ℓ _
        (X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y) hℓ
      have hS0 := hI.S
      rw [hl]
      by_cases hany : (X ++ PkgLetter.lw (.res a) :: Y).any PkgLetter.isEnt = true
      · obtain ⟨h1, h2⟩ := hent hany
        have e : (if ((X ++ PkgLetter.lw (.res a) :: Y).any PkgLetter.isEnt &&
            !(pkgColl (X ++ PkgLetter.lw (.res a) :: Y)).any PkgLetter.isEnt) = true
              then 1 else 0) = (if ((X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++
                Y).any PkgLetter.isEnt &&
            !(pkgColl (X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y)).any
              PkgLetter.isEnt) = true then 1 else 0) := by
          rw [hC, hany, hany2]
        omega
      · have hany' : (X ++ PkgLetter.lw (.res a) :: Y).any PkgLetter.isEnt = false := by
          simpa using hany
        obtain ⟨h1, h2⟩ := hfree hany'
        have e1 : ((X ++ PkgLetter.lw (.res a) :: Y).any PkgLetter.isEnt &&
            !(pkgColl (X ++ PkgLetter.lw (.res a) :: Y)).any PkgLetter.isEnt) = false := by
          rw [hany']
          rfl
        have e2 : ((X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y).any
              PkgLetter.isEnt &&
            !(pkgColl (X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y)).any
              PkgLetter.isEnt) = true := by
          rw [hany2, hC, pkgColl_free _ (free_of_any' hany')]
          rw [hany']
          rfl
        simp only [e1, e2] at hcs
        simp only [Bool.false_eq_true, ↓reduceIte] at hcs
        omega
  · obtain ⟨hs, hp, hm⟩ := hI.perm
    obtain ⟨hj', hjeq⟩ := List.getElem?_eq_some_iff.1 hj
    refine ⟨⟨hs ++ [(b, y)], ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hp1 := List.getElem_cons_eraseIdx_perm hj'
      rw [hjeq] at hp1
      rw [hwt]
      refine List.Perm.trans ?_ hp
      refine List.Perm.trans ?_ (hp1.append_right hs)
      rw [List.perm_iff_count]
      intro z
      simp [List.count_append, List.count_cons]
      omega
    · rw [hl, List.map_append, hm, List.map_cons, List.map_nil, pkgColl_weight]
      simp
    · intro w hw
      rw [hl, List.mem_append] at hw
      rcases hw with hw | hw
      · exact hI.cnt w hw
      · rw [List.mem_singleton] at hw
        subst hw
        simp [pkgColl_weight, List.countP_cons, PkgLetter.isRes, PkgLetter.isEnt]
    · intro w hw hany
      rw [hl, List.mem_append] at hw
      rcases hw with hw | hw
      · exact hI.free w hw hany
      · rw [List.mem_singleton] at hw
        subst hw
        simp [PkgLetter.isEnt] at hany
    · obtain ⟨W, rest, hL, hF⟩ := hI.head
      exact ⟨W, rest ++ [[.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)]],
        by rw [hl, hL]; rfl, hF⟩
    · rw [hcf, hI.cf, pow_succ]
      ring
    · rw [hnb]
      exact hI.nb
    · have := hI.dS
      omega
    · have hS0 := hI.S
      rw [hl, List.countP_append]
      simp [pkgColl_weight, PkgLetter.isEnt]
      omega

/-- `n` derivatives `PkgExpr.dent`, each adding one to the exponent of the sign. -/
private theorem WInv.iter {T : LoopExpr} {R₀ : PkgExpr} {F₀ : List PkgLetter} (u v : ℕ) :
    ∀ (n k : ℕ) (L : List PkgExpr), (∀ R ∈ L, WInv T R₀ F₀ k R) →
      ∀ R ∈ (fun L : List PkgExpr => L.flatMap fun R' => R'.dent u v)^[n] L,
        WInv T R₀ F₀ (k + n) R
  | 0, k, L, h => fun R hR => by simpa using h R hR
  | n + 1, k, L, h => fun R hR => by
      rw [Function.iterate_succ_apply'] at hR
      obtain ⟨R₁, hR₁, hR⟩ := List.mem_flatMap.1 hR
      exact (WInv.iter u v n k L h R₁ hR₁).step u v hR

/-! ### Auxiliary facts: the focus of a word -/

/-- The letter of a loop word is a resolvent. -/
private def PC_isResL (x : LoopLetter) : Bool :=
  match x with | .res _ => true | _ => false

/-- The letter of a loop word is a `Λ̃`. -/
private def isLamL (x : LoopLetter) : Bool :=
  match x with | .lamt _ => true | _ => false

/-- The letter of a loop word is not a `Λ̃`. -/
private def isNotLamL (x : LoopLetter) : Bool :=
  match x with | .lamt _ => false | _ => true

/-- The entry at position `m` of the loop word `w` is a resolvent. -/
private def ResAt (w : List LoopLetter) (m : ℕ) : Bool :=
  match w[m]? with | some (.res _) => true | _ => false

private theorem idx_mod (i n j m : ℕ) (hj : j < n) (hm : m < n)
    (h : (m = i - 1 - j ∧ j < i) ∨ (m = n + i - 1 - j ∧ i ≤ j)) : (i + n - 1 - j) % n = m := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · have : i + n - 1 - j = (i - 1 - j) + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hm]
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

private theorem mod_val (i n j : ℕ) (hi : i < n) (hj : j < n) :
    (i + n - 1 - j) % n = if j < i then i - 1 - j else n + i - 1 - j := by
  split_ifs with h
  · exact idx_mod i n j _ hj (by omega) (Or.inl ⟨rfl, h⟩)
  · exact idx_mod i n j _ hj (by omega) (Or.inr ⟨rfl, by omega⟩)

/-- The letters to the left of the entry at position `i` of a word, read leftwards, cyclically. -/
private theorem left_getElem? (w : List LoopLetter) (i j : ℕ) (hj : j + 1 < w.length) :
    (((w.rotate i).drop 1).reverse)[j]? = w[(i + w.length - 1 - j) % w.length]? := by
  have hlen : ((w.rotate i).drop 1).length = w.length - 1 := by simp
  rw [List.getElem?_reverse (by omega), hlen, List.getElem?_drop,
    List.getElem?_rotate (by omega)]
  have e : 1 + (w.length - 1 - 1 - j) + i = i + w.length - 1 - j := by omega
  rw [e]

/-- The first resolvent to the left of the entry `x` of a loop word `w` (cyclically), put in front
by the rotation of the focus (5.38) [explicit_cT]: if a resolvent occurs to the left of `x` before
any `Λ̃` (the term of `kk` of (5.34) [Gamma_Type_1]), then the letters between this resolvent and
`x` are not `Λ̃`. -/
private theorem rotate_left_lam (w : List LoopLetter) (x : LoopLetter) (hx : x ∈ w)
    (hxl : isLamL x = true) (a : Fin 2) (tl : List LoopLetter) (r : ℕ)
    (hr : (((List.range w.length).map fun j => (w.idxOf x + w.length - 1 - j) % w.length).find?
      (ResAt w)) = some r)
    (hrot : w.rotate r = .res a :: tl)
    (hk : 1 ≤ ((((w.rotate (w.idxOf x)).drop 1).reverse.takeWhile isNotLamL).countP PC_isResL)) :
    ∃ tl₀ tl₁ : List LoopLetter, tl = tl₀ ++ x :: tl₁ ∧ ∀ z ∈ tl₀, isLamL z = false := by
  set n := w.length with hn
  set i := w.idxOf x with hi_def
  have hi : i < n := List.idxOf_lt_length_iff.2 hx
  have hwi : w[i] = x := List.getElem_idxOf hi
  have hwi' : w[i]? = some x := by rw [List.getElem?_eq_getElem hi, hwi]
  rw [List.find?_eq_some_iff_getElem] at hr
  obtain ⟨hpr, k, hk', hkr, hbef⟩ := hr
  simp only [List.length_map, List.length_range] at hk'
  simp only [List.getElem_map, List.getElem_range] at hkr hbef
  have hrn : r < n := by
    rw [← hkr]; exact Nat.mod_lt _ (by omega)
  have hwr : ∃ a'', w[r]? = some (.res a'') := by
    unfold ResAt at hpr
    split at hpr
    · rename_i a'' h; exact ⟨a'', h⟩
    · simp at hpr
  obtain ⟨a'', hwr⟩ := hwr
  have hwr' : w[r] = .res a'' := by
    rw [List.getElem?_eq_getElem hrn] at hwr; exact Option.some.inj hwr
  have hnl : ∀ m (hm : m < n), (∃ j, j < k ∧ (i + n - 1 - j) % n = m) → isLamL w[m] = false := by
    rintro m hm ⟨j, hj, hjm⟩
    obtain ⟨R, hR⟩ : ∃ R, R = ((w.rotate i).drop 1).reverse := ⟨_, rfl⟩
    rw [← hR] at hk
    obtain ⟨e, heP, hres⟩ := List.countP_pos_iff.1 (show 0 < _ from hk)
    obtain ⟨j₀, hj₀P, hPj₀⟩ := List.mem_iff_getElem.1 heP
    have hD := List.takeWhile_append_dropWhile (p := isNotLamL) (l := R)
    have hRlen : R.length = n - 1 := by rw [hR]; simp [hn]
    have hlen := congrArg List.length hD
    rw [List.length_append] at hlen
    have hPR : ∀ j' (h1 : j' < (R.takeWhile isNotLamL).length),
        R[j']? = some (R.takeWhile isNotLamL)[j'] := by
      intro j' h1
      calc R[j']? = ((R.takeWhile isNotLamL) ++ (R.dropWhile isNotLamL))[j']? := by rw [hD]
        _ = (R.takeWhile isNotLamL)[j']? := List.getElem?_append_left h1
        _ = some (R.takeWhile isNotLamL)[j'] := List.getElem?_eq_getElem h1
    have hRw : ∀ j', j' + 1 < n → R[j']? = w[(i + n - 1 - j') % n]? := by
      intro j' hj'
      rw [hR]
      exact left_getElem? w i j' hj'
    have hj₀ : j₀ + 1 < n := by omega
    have hres₀ : ResAt w ((i + n - 1 - j₀) % n) = true := by
      have h1 := hPR j₀ hj₀P
      rw [hRw j₀ hj₀, hPj₀] at h1
      unfold ResAt
      rw [h1]
      cases e <;> simp_all [PC_isResL]
    have hkj : k ≤ j₀ := by
      by_contra hlt
      have := hbef j₀ (by omega)
      rw [hres₀] at this
      exact absurd this (by simp)
    have hjP : j < (R.takeWhile isNotLamL).length := by omega
    have h1 := hPR j hjP
    rw [hRw j (by omega), hjm, List.getElem?_eq_getElem hm] at h1
    have h2 : w[m] = (R.takeWhile isNotLamL)[j] := Option.some.inj h1
    have h3 := List.mem_takeWhile_imp (List.getElem_mem hjP)
    rw [← h2] at h3
    revert h3
    cases w[m] <;> simp [isNotLamL, isLamL]
  have hdrop : w.drop r = .res a'' :: w.drop (r + 1) := by
    rw [List.drop_eq_getElem_cons hrn, hwr']
  have htl : tl = w.drop (r + 1) ++ w.take r := by
    rw [List.rotate_eq_drop_append_take (by omega), hdrop] at hrot
    simpa using (List.cons.inj hrot).2.symm
  have hdi : w.drop i = x :: w.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hwi]
  have hrv := mod_val i n k hi hk'
  rw [hkr] at hrv
  by_cases hki : k < i
  · -- the resolvent is to the left of `x` in the word
    simp only [hki, ↓reduceIte] at hrv
    refine ⟨(w.drop (r + 1)).take (i - r - 1), w.drop (i + 1) ++ w.take r, ?_, ?_⟩
    · rw [htl]
      have e1 : w.drop (r + 1) = (w.drop (r + 1)).take (i - r - 1) ++ x :: w.drop (i + 1) := by
        conv_lhs => rw [← List.take_append_drop (i - r - 1) (w.drop (r + 1))]
        rw [List.drop_drop, show r + 1 + (i - r - 1) = i by omega, hdi]
      conv_lhs => rw [e1]
      simp
    · intro z hz
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hz
      simp only [List.length_take, List.length_drop, List.getElem_take, List.getElem_drop] at hm ⊢
      refine hnl _ (by omega) ⟨k - 1 - m, by omega, ?_⟩
      exact idx_mod i n _ _ (by omega) (by omega) (Or.inl ⟨by omega, by omega⟩)
  · -- the resolvent is to the right of `x`: the cycle passes through the end of the word
    simp only [hki, ↓reduceIte] at hrv
    have hri : i < r := by
      rcases Nat.lt_or_ge i r with h | h
      · exact h
      · exfalso
        have : r = i := by omega
        rw [this, hwi'] at hwr
        have hxx : x = .res a'' := Option.some.inj hwr
        rw [hxx] at hxl
        exact absurd hxl (by simp [isLamL])
    refine ⟨w.drop (r + 1) ++ w.take i, (w.drop (i + 1)).take (r - i - 1), ?_, ?_⟩
    · rw [htl]
      have e1 : w.take r = w.take i ++ x :: (w.drop (i + 1)).take (r - i - 1) := by
        have h1 : r = i + (r - i - 1 + 1) := by omega
        conv_lhs => rw [h1, List.take_add, hdi, List.take_succ_cons]
      conv_lhs => rw [e1]
      simp
    · intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hz
        simp only [List.length_drop, List.getElem_drop] at hm ⊢
        refine hnl _ (by omega) ⟨k - 1 - m, by omega, ?_⟩
        exact idx_mod i n _ _ (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩)
      · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hz
        simp only [List.length_take, List.getElem_take] at hm ⊢
        refine hnl _ (by omega) ⟨i - 1 - m, by omega, ?_⟩
        exact idx_mod i n _ _ (by omega) (by omega) (Or.inl ⟨by omega, by omega⟩)

/-- `Λ̃_o` occurs in one loop of `𝒯` only. -/
private theorem uniq_lam {T : LoopExpr} (hT : T.wf = true) (o : Fin 2) {w w₁ : List LoopLetter}
    (hw : w ∈ T.loops) (hw₁ : w₁ ∈ T.loops) (hc : w.contains (.lamt o) = true)
    (hc₁ : w₁.contains (.lamt o) = true) : w₁ = w := by
  unfold LoopExpr.wf at hT
  simp only [Bool.and_eq_true, beq_iff_eq] at hT
  obtain ⟨⟨⟨⟨h0, h1⟩, -⟩, -⟩, -⟩ := hT
  have hs : (T.loops.map fun w => w.count (.lamt o)).sum = 1 := by
    fin_cases o
    · exact h0
    · exact h1
  by_contra hne
  have hperm := List.perm_cons_erase hw
  have hs2 : (T.loops.map fun w => w.count (.lamt o)).sum =
      w.count (.lamt o) + ((T.loops.erase w).map fun w => w.count (.lamt o)).sum := by
    rw [(hperm.map _).sum_eq]
    simp
  have hmem : w₁ ∈ T.loops.erase w := (List.mem_erase_of_ne hne).2 hw₁
  have hle : w₁.count (.lamt o) ≤ ((T.loops.erase w).map fun w => w.count (.lamt o)).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hmem)
  have hpos : 0 < w.count (.lamt o) := List.count_pos_iff.2 (List.contains_iff_mem.1 hc)
  have hpos₁ : 0 < w₁.count (.lamt o) := List.count_pos_iff.2 (List.contains_iff_mem.1 hc₁)
  omega

/-- The focus of `T` (5.38) [explicit_cT]: the loop `w` of `Λ̃_o` is a permutation of `𝒢_a · tl`,
and `tl = tl₀ Λ̃_o tl₁` with no `Λ̃` in `tl₀`, since `1 ≤ k_o` (5.34) [Gamma_Type_1]. -/
private theorem focus_lam {T : LoopExpr} (hT : T.wf = true) {ℓ : ℕ} {a : Fin 2}
    {tl : List LoopLetter} (o : Fin 2) (ho : o = if 1 ≤ T.kk 0 then 0 else 1)
    (h : T.focus = some (ℓ, a, tl)) :
    ∃ (w tl₀ tl₁ : List LoopLetter), w ∈ T.loops ∧ w.contains (.lamt o) = true ∧
      w.Perm (.res a :: tl) ∧ tl = tl₀ ++ .lamt o :: tl₁ ∧ ∀ z ∈ tl₀, isLamL z = false := by
  unfold LoopExpr.focus at h
  dsimp only at h
  rw [← ho] at h
  split at h
  · cases h
  · rename_i w hw
    split at h
    · cases h
    · rename_i r hr
      split at h
      · rename_i a' tl' hrot
        split at h
        · rename_i hkk
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have hwm : w ∈ T.loops := List.mem_of_getElem? hw
          have hc : w.contains (.lamt o) = true := by
            obtain ⟨hlt, hwe⟩ := List.getElem?_eq_some_iff.1 hw
            have := List.findIdx_getElem (p := fun w : List LoopLetter => w.contains (.lamt o))
              (xs := T.loops) (w := hlt)
            rwa [hwe] at this
          have hx : LoopLetter.lamt o ∈ w := List.contains_iff_mem.1 hc
          have hperm : w.Perm (.res a' :: tl') := by
            rw [← hrot]; exact (List.rotate_perm w r).symm
          have hk1 : 1 ≤ ((((w.rotate (w.idxOf (.lamt o))).drop 1).reverse.takeWhile
              fun x => match x with | .lamt _ => false | _ => true).countP
              fun x => match x with | .res _ => true | _ => false) := by
            by_contra hlt
            have hz : T.kk o = 0 := by
              unfold LoopExpr.kk
              apply List.sum_eq_zero
              intro z hz
              obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hz
              by_cases hc' : w'.contains (.lamt o) = true
              · rw [uniq_lam hT o hwm hw' hc hc']
                simp only [hc, ↓reduceIte]
                exact Nat.lt_one_iff.1 (not_le.1 hlt)
              · simp only [hc', Bool.false_eq_true, ↓reduceIte]
            omega
          obtain ⟨tl₀, tl₁, he, hfree⟩ := rotate_left_lam w (.lamt o) hx rfl a' tl' r hr hrot hk1
          exact ⟨w, tl₀, tl₁, hwm, hc, hperm, he, hfree⟩
        · cases h
      · cases h

/-! ### Auxiliary facts: the packages of a word -/

private theorem isEnt_ent' (u v : ℕ) : PkgLetter.isEnt (.ent u v) = true := rfl

/-- A list with a letter `Δ` splits at its first one. -/
private theorem exists_first_ent' : ∀ w : List PkgLetter, w.any PkgLetter.isEnt = true →
    ∃ (P : List PkgLetter) (x y : ℕ) (Q : List PkgLetter),
      (∀ z ∈ P, PkgLetter.isEnt z = false) ∧ w = P ++ .ent x y :: Q
  | [], h => by simp at h
  | z :: w, h => by
      match z with
      | .ent x y => exact ⟨[], x, y, w, by simp, rfl⟩
      | .lw z' =>
          have h' : w.any PkgLetter.isEnt = true := by simpa [PkgLetter.isEnt] using h
          obtain ⟨P, x, y, Q, hP, hw⟩ := exists_first_ent' w h'
          refine ⟨.lw z' :: P, x, y, Q, ?_, by simp [hw]⟩
          intro t ht
          rcases List.mem_cons.1 ht with rfl | ht
          · rfl
          · exact hP t ht

private theorem findIdx_ent' (P Q : List PkgLetter) (u v : ℕ)
    (hP : ∀ y ∈ P, PkgLetter.isEnt y = false) :
    (P ++ .ent u v :: Q).findIdx PkgLetter.isEnt = P.length := by
  induction P with
  | nil => simp [List.findIdx_cons, isEnt_ent']
  | cons z P ih =>
      rw [List.cons_append, List.findIdx_cons, hP z (List.mem_cons_self)]
      simp [ih (fun y hy => hP y (List.mem_cons_of_mem _ hy))]

/-- The packages of a word cut at its first letter `Δ`: the pieces of the list read from just
after that `Δ`. -/
private theorem pkgSegs_first' (P Q : List PkgLetter) (u v : ℕ)
    (hP : ∀ y ∈ P, PkgLetter.isEnt y = false) :
    pkgSegs (P ++ .ent u v :: Q) = (Q ++ P).splitOnP PkgLetter.isEnt := by
  unfold pkgSegs
  have h1 : (P ++ .ent u v :: Q).any PkgLetter.isEnt = true := by simp [PkgLetter.isEnt]
  simp only [h1, ↓reduceIte, findIdx_ent' P Q u v hP]
  have h2 : (P ++ .ent u v :: Q).rotate (P.length + 1) = (Q ++ P) ++ [.ent u v] := by
    rw [List.rotate_eq_drop_append_take (by simp)]
    have e0 : P ++ .ent u v :: Q = (P ++ [.ent u v]) ++ Q := by simp
    have e1 : (P ++ .ent u v :: Q).drop (P.length + 1) = Q := by
      rw [e0]; exact List.drop_left' (by simp)
    have e2 : (P ++ .ent u v :: Q).take (P.length + 1) = P ++ [.ent u v] := by
      rw [e0]; exact List.take_left' (by simp)
    rw [e1, e2]; simp
  rw [h2, List.dropLast_concat]

/-- The number of pieces of a list cut at its letters `Δ`, and the number of resolvents in them. -/
private theorem splitOnP_counts : ∀ Z : List PkgLetter,
    (Z.splitOnP PkgLetter.isEnt).length = Z.countP PkgLetter.isEnt + 1 ∧
    ((Z.splitOnP PkgLetter.isEnt).map fun σ => σ.countP PkgLetter.isRes).sum =
      Z.countP PkgLetter.isRes
  | [] => by simp
  | x :: Z => by
      obtain ⟨h1, h2⟩ := splitOnP_counts Z
      by_cases hx : PkgLetter.isEnt x = true
      · have hr : PkgLetter.isRes x = false := by
          cases x with
          | lw y => simp [PkgLetter.isEnt] at hx
          | ent u v => rfl
        rw [List.splitOnP_cons_eq_ite_modifyHead]
        simp [hx, hr, h1, h2]
      · have hx' : PkgLetter.isEnt x = false := by simpa using hx
        rcases hS : Z.splitOnP PkgLetter.isEnt with _ | ⟨σ, L⟩
        · exact absurd hS (List.splitOnP_ne_nil _ _)
        · rw [hS] at h1 h2
          rw [List.splitOnP_cons_eq_ite_modifyHead, hS]
          simp [hx', List.countP_cons] at h1 h2 ⊢
          exact ⟨h1, by split_ifs <;> omega⟩

/-- The packages of a word with a letter `Δ`, as in (5.67) [eq:sumai]: their number is the number
of letters `Δ`, and their resolvents are those of the word. -/
private theorem pkgSegs_counts (w : List PkgLetter) (h : w.any PkgLetter.isEnt = true) :
    (pkgSegs w).length = w.countP PkgLetter.isEnt ∧
    ((pkgSegs w).map fun σ => σ.countP PkgLetter.isRes).sum = w.countP PkgLetter.isRes := by
  obtain ⟨P, x, y, Q, hP, rfl⟩ := exists_first_ent' w h
  rw [pkgSegs_first' P Q x y hP]
  obtain ⟨h1, h2⟩ := splitOnP_counts (Q ++ P)
  have hPc : P.countP PkgLetter.isEnt = 0 :=
    List.countP_eq_zero.2 (fun z hz => by simp [hP z hz])
  refine ⟨?_, ?_⟩
  · rw [h1]
    simp [List.countP_append, List.countP_cons, PkgLetter.isEnt, hPc]
  · rw [h2]
    simp [List.countP_append, PkgLetter.isRes]
    omega

/-! ### Auxiliary facts: the letters `Λ̃` of the first word -/

private theorem map_lw_free (l : List LoopLetter) :
    ∀ z ∈ l.map PkgLetter.lw, PkgLetter.isEnt z = false := by
  intro z hz
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hz
  rfl

/-- The letters `Λ̃` of the first word of `𝒯.pkgStart`: `Λ̃_o` first (no `Λ̃` before it in `tl`),
then those of `tl₁`. -/
private theorem filter_main (a o : Fin 2) (tl₀ tl₁ : List LoopLetter)
    (h₀ : ∀ z ∈ tl₀, isLamL z = false) :
    ((List.map PkgLetter.lw (LoopLetter.det a :: (tl₀ ++ LoopLetter.lamt o :: tl₁) ++
        [LoopLetter.res a])) ++ [PkgLetter.ent 1 0]).filter PkgLetter.isLam =
      PkgLetter.lw (.lamt o) :: (tl₁.map PkgLetter.lw).filter PkgLetter.isLam := by
  have h1 : (tl₀.map PkgLetter.lw).filter PkgLetter.isLam = [] := by
    rw [List.filter_eq_nil_iff]
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    have := h₀ y hy
    cases y <;> simp_all [PkgLetter.isLam, isLamL]
  simp [List.map_append, List.filter_append, List.filter_cons, h1, PkgLetter.isLam]

/-- A list whose letters `Λ̃` start with `x` splits at its first one. -/
private theorem first_lam (x : PkgLetter) (hx : PkgLetter.isLam x = true) :
    ∀ (W F : List PkgLetter), W.filter PkgLetter.isLam = x :: F →
      ∃ P S : List PkgLetter, W = P ++ x :: S ∧ (∀ z ∈ P, PkgLetter.isLam z = false) ∧
        S.filter PkgLetter.isLam = F
  | [], F, h => by simp at h
  | z :: W, F, h => by
      by_cases hz : PkgLetter.isLam z = true
      · rw [List.filter_cons_of_pos hz] at h
        obtain ⟨h1, h2⟩ := List.cons.inj h
        subst h1
        exact ⟨[], W, rfl, by simp, h2⟩
      · have hz' : PkgLetter.isLam z = false := by simpa using hz
        rw [List.filter_cons_of_neg hz] at h
        obtain ⟨P, S, rfl, hP, hS⟩ := first_lam x hx W F h
        refine ⟨z :: P, S, rfl, ?_, hS⟩
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hz'
        · exact hP y hy

/-- The words of the derivative structures of (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression] and the count (5.67) [eq:sumai]: the
first words of `𝓡` are the words of `𝒯.pkgStart` (the main word and the loops of `𝒯`) with
letters `Δ` inserted at resolvents, in their order; the further words are the hit light weights
`𝒢_b Δ 𝒢_b E_y` with letters `Δ` inserted, and the light weights of `𝓡` with them are those of
`𝒯`; each word has its resolvents before the derivatives plus one per inserted `Δ`, so the
resolvent counts `a_σ` of its packages sum to them plus the number of packages; a word without
`Δ` is a loop of `𝒯`; `Λ̃` other than `Λ̃_o` lies in the main word after `Λ̃_o` (Type I) or
in another word (Type II); the coefficient is `(-1)^{p+q} D^{dexp} N^{-S}` with one factor
`(DN)⁻¹` per hit loop or light weight. -/
theorem pkg_dwirt_words (T : LoopExpr) (hT : T.wf = true) (ℓ : ℕ) (a : Fin 2)
    (tl : List LoopLetter) (hf : T.focus = some (ℓ, a, tl)) (u v p q : ℕ) (R : PkgExpr)
    (hR : R ∈ T.pkgStart.dwirt u v p q) :
    (R.loops.take T.pkgStart.loops.length).map pkgColl = T.pkgStart.loops ∧
    (∃ hs : List (Fin 2 × ℕ), (R.weights ++ hs).Perm T.weights ∧
      (R.loops.drop T.pkgStart.loops.length).map pkgColl =
        hs.map fun y => [.lw (.res y.1), .lw (.proj y.2)]) ∧
    (∀ w ∈ R.loops, w.countP PkgLetter.isRes + (pkgColl w).countP PkgLetter.isEnt =
      (pkgColl w).countP PkgLetter.isRes + w.countP PkgLetter.isEnt) ∧
    (∀ w ∈ R.loops, w.any PkgLetter.isEnt = true →
      ((pkgSegs w).map fun σ => σ.countP PkgLetter.isRes).sum +
          (pkgColl w).countP PkgLetter.isEnt =
        (pkgColl w).countP PkgLetter.isRes + (pkgSegs w).length) ∧
    (∀ w ∈ R.loops, w.any PkgLetter.isEnt = false → ∃ w₀ ∈ T.loops, w = w₀.map PkgLetter.lw) ∧
    (T.typeI = true → ∃ w ∈ R.loops.head?,
      ((w.drop (w.idxOf (.lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1))) + 1)).contains
        (.lw (.lamt (if 1 ≤ T.kk 0 then 1 else 0)))) = true) ∧
    (T.typeI = false → ∀ w ∈ R.loops.head?,
      w.contains (.lw (.lamt (if 1 ≤ T.kk 0 then 1 else 0))) = false) ∧
    R.cf = (-1) ^ (p + q) ∧ R.nb = T.nb ∧ R.dexp + R.S = T.dexp + T.S ∧
    R.S = T.S + (R.loops.countP fun w =>
      w.any PkgLetter.isEnt && !(pkgColl w).any PkgLetter.isEnt) := by
  obtain ⟨o, o', hoo, ho, ho'⟩ : ∃ o o' : Fin 2, ((o = 0 ∧ o' = 1) ∨ (o = 1 ∧ o' = 0)) ∧
      o = (if 1 ≤ T.kk 0 then 0 else 1) ∧ o' = (if 1 ≤ T.kk 0 then 1 else 0) := by
    by_cases hc : 1 ≤ T.kk 0
    · exact ⟨0, 1, Or.inl ⟨rfl, rfl⟩, by simp [hc], by simp [hc]⟩
    · exact ⟨1, 0, Or.inr ⟨rfl, rfl⟩, by simp [hc], by simp [hc]⟩
  rw [← ho, ← ho']
  have hne : o ≠ o' := by rcases hoo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain ⟨w, tl₀, tl₁, hwT, hwc, hperm, he, hfree⟩ := focus_lam hT o ho hf
  subst he
  have hboth : T.typeI = true →
      ∃ w₁ ∈ T.loops, w₁.contains (.lamt o) = true ∧ w₁.contains (.lamt o') = true := by
    intro hty
    obtain ⟨w₁, hw₁, h⟩ := List.any_eq_true.1 hty
    refine ⟨w₁, hw₁, ?_⟩
    rcases hoo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using h
    · simpa [and_comm] using h
  have hnone : T.typeI = false → ∀ w₁ ∈ T.loops, w₁.contains (.lamt o) = true →
      w₁.contains (.lamt o') = false := by
    intro hty w₁ hw₁ hc
    have h := List.any_eq_false.1 hty w₁ hw₁
    rcases hoo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hc, Bool.true_and] at h
      exact Bool.eq_false_iff.2 h
    · rw [hc, Bool.and_true] at h
      exact Bool.eq_false_iff.2 h
  -- the loop `w` contains `Λ̃_{o'}` only in `tl₁`
  have hmem1 : w.contains (.lamt o') = true → LoopLetter.lamt o' ∈ tl₁ := by
    intro hc'
    have hm : LoopLetter.lamt o' ∈ w := List.contains_iff_mem.1 hc'
    rw [hperm.mem_iff] at hm
    rcases List.mem_cons.1 hm with h | h
    · cases h
    · rcases List.mem_append.1 h with h | h
      · have := hfree _ h
        simp [isLamL] at this
      · rcases List.mem_cons.1 h with h | h
        · exact absurd (LoopLetter.lamt.inj h).symm hne
        · exact h
  have hmem2 : LoopLetter.lamt o' ∈ tl₁ → w.contains (.lamt o') = true := by
    intro h
    refine List.contains_iff_mem.2 (hperm.mem_iff.2 ?_)
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  -- the start
  have hs : T.pkgStart = ⟨1, T.dexp, T.S, T.nb, T.weights,
      (((LoopLetter.det a :: (tl₀ ++ LoopLetter.lamt o :: tl₁) ++ [LoopLetter.res a]).map
        PkgLetter.lw) ++ [PkgLetter.ent 1 0]) ::
        (T.loops.eraseIdx ℓ).map fun w => w.map PkgLetter.lw⟩ := by
    unfold LoopExpr.pkgStart
    rw [hf]
  have hloops : T.pkgStart.loops = (((LoopLetter.det a :: (tl₀ ++ LoopLetter.lamt o :: tl₁) ++
      [LoopLetter.res a]).map PkgLetter.lw) ++ [PkgLetter.ent 1 0]) ::
        (T.loops.eraseIdx ℓ).map (fun w => w.map PkgLetter.lw) := by
    rw [hs]
  have hfix : ∀ w' ∈ T.pkgStart.loops, pkgColl w' = w' := by
    intro w' hw'
    rw [hloops] at hw'
    rcases List.mem_cons.1 hw' with rfl | hw'
    · exact pkgColl_snoc _ (map_lw_free _) 1 0
    · obtain ⟨w₀, -, rfl⟩ := List.mem_map.1 hw'
      exact pkgColl_free _ (map_lw_free _)
  have hg : ∀ w' ∈ T.pkgStart.loops,
      (w'.any PkgLetter.isEnt && !(pkgColl w').any PkgLetter.isEnt) = false := by
    intro w' hw'
    rw [hfix w' hw']
    cases w'.any PkgLetter.isEnt <;> simp
  have hbase : WInv T T.pkgStart
      ((((LoopLetter.det a :: (tl₀ ++ LoopLetter.lamt o :: tl₁) ++ [LoopLetter.res a]).map
        PkgLetter.lw) ++ [PkgLetter.ent 1 0]).filter PkgLetter.isLam) 0 T.pkgStart := by
    refine ⟨⟨[], ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs]
      simp
    · rw [List.map_nil, List.append_nil]
      exact (List.map_congr_left fun w' hw' => hfix w' hw').trans (List.map_id _)
    · intro w' hw'
      rw [hfix w' hw']
    · intro w' hw' hany
      rw [hloops] at hw'
      rcases List.mem_cons.1 hw' with rfl | hw'
      · simp [List.any_append, PkgLetter.isEnt] at hany
      · obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.1 hw'
        exact ⟨w₀, List.mem_of_mem_eraseIdx hw₀, rfl⟩
    · exact ⟨_, _, hloops, rfl⟩
    · rw [hs]
      simp
    · rw [hs]
    · rw [hs]
    · have hz : (T.pkgStart.loops.countP fun w' =>
          w'.any PkgLetter.isEnt && !(pkgColl w').any PkgLetter.isEnt) = 0 :=
        List.countP_eq_zero.2 fun w' hw' => by simp [hg w' hw']
      rw [hz, hs]
      simp
  unfold PkgExpr.dwirt at hR
  have h1 := WInv.iter (T := T) (R₀ := T.pkgStart) v u q 0 [T.pkgStart]
    (fun R hR => by rw [List.mem_singleton] at hR; subst hR; exact hbase)
  have hI := WInv.iter u v p (0 + q) _ h1 R hR
  obtain ⟨hs', hp, hm⟩ := hI.perm
  refine ⟨?_, ⟨hs', hp, ?_⟩, hI.cnt, ?_, hI.free, ?_, ?_, ?_, hI.nb, hI.dS, hI.S⟩
  · rw [List.map_take, hm]
    simp
  · rw [List.map_drop, hm]
    simp
  · intro w' hw' hany
    obtain ⟨hl, hsum⟩ := pkgSegs_counts w' hany
    rw [hl, hsum]
    exact hI.cnt w' hw'
  · intro hty
    obtain ⟨W, rest, hL, hF⟩ := hI.head
    obtain ⟨w₁, hw₁, hc₁, hc₁'⟩ := hboth hty
    rw [uniq_lam hT o hwT hw₁ hwc hc₁] at hc₁'
    have hmem := hmem1 hc₁'
    rw [filter_main a o tl₀ tl₁ hfree] at hF
    obtain ⟨P, S, hW, hP, hS⟩ := first_lam (.lw (.lamt o)) rfl W _ hF
    refine ⟨W, by rw [hL]; rfl, ?_⟩
    have hnotin : (PkgLetter.lw (.lamt o)) ∉ P := fun hm => by
      have := hP _ hm
      simp [PkgLetter.isLam] at this
    have hidx : W.idxOf (.lw (.lamt o)) = P.length := by
      rw [hW, List.idxOf_append_of_notMem hnotin]
      simp
    have hdrop : W.drop (P.length + 1) = S := by
      rw [hW, show P ++ PkgLetter.lw (.lamt o) :: S = (P ++ [PkgLetter.lw (.lamt o)]) ++ S by simp]
      exact List.drop_left' (by simp)
    rw [hidx, hdrop]
    have : PkgLetter.lw (.lamt o') ∈ S.filter PkgLetter.isLam := by
      rw [hS]
      exact List.mem_filter.2 ⟨List.mem_map_of_mem hmem, by simp [PkgLetter.isLam]⟩
    exact List.contains_iff_mem.2 (List.mem_filter.1 this).1
  · intro hty W' hW'
    obtain ⟨W, rest, hL, hF⟩ := hI.head
    rw [hL] at hW'
    have hWW : W = W' := Option.some.inj hW'
    subst hWW
    rw [filter_main a o tl₀ tl₁ hfree] at hF
    by_contra hne'
    have hcT : W.contains (.lw (.lamt o')) = true := by simpa using hne'
    have hmemW : PkgLetter.lw (.lamt o') ∈ W := List.contains_iff_mem.1 hcT
    have hmF : PkgLetter.lw (.lamt o') ∈ W.filter PkgLetter.isLam :=
      List.mem_filter.2 ⟨hmemW, by simp [PkgLetter.isLam]⟩
    rw [hF] at hmF
    rcases List.mem_cons.1 hmF with h | h
    · exact hne (LoopLetter.lamt.inj (PkgLetter.lw.inj h)).symm
    · obtain ⟨y, hy, hye⟩ := List.mem_map.1 (List.mem_filter.1 h).1
      have hy' : y = .lamt o' := PkgLetter.lw.inj hye
      subst hy'
      have := hmem2 hy
      rw [hnone hty w hwT hwc] at this
      exact absurd this (by simp)
  · rw [hI.cf]
    congr 1
    omega


end RBMTransitionEdge

end
