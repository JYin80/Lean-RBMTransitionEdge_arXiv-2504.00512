module

public import RBMTransitionEdge.Localized.Expansion.FOpts
public import RBMTransitionEdge.Localized.Expansion.PairG

@[expose] public section

/-!
# The rules of the further-class bound

One rule for every expression of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: the order of summation of the four labels, the roles of the entry
factors, the kinds of options each role tries in turn, and the assignment it builds; the pairings
it uses through `𝔐` and through `𝒢`; the conclusion `FRuleOK` that the rule lemmas prove and the
bridges assume; and the integer form of the row lemma.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- A default entry datum. -/
def FEnt.dflt : FEnt := (0, 0, [], ⟨0, 0, 0, 0, 0⟩, true)

/-- The lexicographic order on lists of naturals. -/
def fListLe : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => a < b || (a = b && fListLe s t)

/-- The label is inner (`i, j`: `2, 3`). -/
def fInnerL (l : ℕ) : Bool := 2 ≤ l

/-- The role of an entry in the patterns of the paper: `0` the `Λ̃`-half `P_Λ` (a letter `Λ̃` with
no resolvent between it and an inner label), `1` another entry with `Λ̃`, `2` an entry with
resolvents and one inner and one outer label (the half `W` and the outer pieces of the hit
packages), `3` every other entry. -/
def FEnt.role (d : FEnt) : ℕ :=
  if 2 ≤ d.2.2.1.length then
    (if (d.2.2.1.head? = some 0 && fInnerL d.1) || (d.2.2.1.getLast? = some 0 && fInnerL d.2.1)
     then 0 else 1)
  else if 1 ≤ d.2.2.1.sum && fInnerL d.1 != fInnerL d.2.1 then 2 else 3

/-- The kinds tried for an entry, in order (the first that fits the capacities and the order of
summation is taken; sup always fits). -/
def FEnt.prefs (d : FEnt) (leaf : Bool) : List FKind :=
  let nl := d.2.2.1.length - 1
  if d.1 = d.2.1 then
    (if nl = 2 then [.dbl true true, .isoX, .isoY] else if nl = 1 then [.isoX, .isoY] else []) ++
    (if 1 ≤ nl ∧ d.2.2.1.sum ≤ 1 then [.diag] else []) ++ [.sup]
  else if nl = 0 then
    (if fInnerL d.1 && !fInnerL d.2.1 then [.wardX]
     else if fInnerL d.2.1 && !fInnerL d.1 then [.wardY]
     else [.wardX, .wardY]) ++ [.sup]
  else if nl = 1 then
    (if leaf && d.2.2.1.sum = 0 then [.hs, .a590 true true, .a590 true false, .a590 false true]
     else [.hs]) ++
    (if d.2.2.1.head? = some 0 && d.2.2.1.getLast? = some 0 then
      (if fInnerL d.2.1 then [.isoY, .isoX] else [.isoX, .isoY])
     else [.isoX, .isoY] ++
       (if 1 ≤ d.2.2.1.getD 0 0 ∧ 1 ≤ d.2.2.1.getD 1 0 then [.plainX, .plainY] else [])) ++ [.sup]
  else
    [.dbl true true, .dbl true false, .dbl false true, .isoX, .isoY, .sup]

/-- The option of a kind fits: it is in the menu `os` of the entry (checked when `menu`; always
true by `fkind_mem`), the capacities stay `≤ 2`, and its order agrees with the ranks `rk`; with its
index in the menu (`0` when `menu` is false). -/
def fkindFit (menu : Bool) (rk : List ℕ) (cap : List ℕ) (d : FEnt) (os : List FOpt) (k : FKind) :
    Option (ℕ × FOpt) :=
  match fkindOpt d k with
  | none => none
  | some o =>
    let i := if menu then foptIdx os o else 0
    if (!menu || i < os.length) &&
        cap.getD d.1 0 + o.cx ≤ 2 && (d.1 = d.2.1 || cap.getD d.2.1 0 + o.cy ≤ 2) &&
        (o.ord != 1 || rk.getD d.1 0 < rk.getD d.2.1 0) &&
        (o.ord != -1 || rk.getD d.2.1 0 < rk.getD d.1 0) then some (i, o) else none

/-- The fixed ranks of the rules: `i, j` summed first, then `α, β`. -/
def frk : List ℕ := [2, 3, 0, 1]

/-- The order in which the rule treats the entries: by role, then by the data. -/
def FEnt.before (d e : FEnt) : Bool :=
  d.role < e.role || (d.role = e.role &&
    (e.2.2.1.sum < d.2.2.1.sum || (e.2.2.1.sum = d.2.2.1.sum &&
      (d.1 < e.1 || (d.1 = e.1 && (d.2.1 < e.2.1 || (d.2.1 = e.2.1 &&
        (d.2.2.1.length < e.2.2.1.length || (d.2.2.1.length = e.2.2.1.length &&
          fListLe d.2.2.1 e.2.2.1)))))))))

/-- The rule on the entries, with its state: in the order `FEnt.before`, each entry takes the
first kind of its list that fits (sup if none does); the result is the capacities used and, per
entry, its index, its option index and the option (the indices only when `menu`). -/
def fruleRun (menu : Bool) (E : List FEnt) (leaf : Bool) : List ℕ × List (ℕ × ℕ × Option FOpt) :=
  let ord := (List.range E.length).insertionSort fun s t =>
    (E.getD s FEnt.dflt).before (E.getD t FEnt.dflt) = true
  ord.foldl (fun (st : List ℕ × List (ℕ × ℕ × Option FOpt)) t =>
    let d := E.getD t FEnt.dflt
    let os := if menu then d.opts else []
    match (d.prefs leaf).findSome? (fkindFit menu frk st.1 d os) with
    | none => (st.1, (t, 0, fkindOpt d .sup) :: st.2)
    | some (i, o) =>
      let cap := st.1.set d.1 (st.1.getD d.1 0 + o.cx)
      let cap := if d.1 = d.2.1 then cap else cap.set d.2.1 (cap.getD d.2.1 0 + o.cy)
      (cap, (t, i, some o) :: st.2)) ([0, 0, 0, 0], [])

/-- The rule on the entries: the option indices of `fruleRun`, in the order of the entries. -/
def fruleE (E : List FEnt) (leaf : Bool) : List ℕ :=
  let res := fruleRun true E leaf
  (List.range E.length).map fun t => ((res.2.find? fun p => p.1 = t).map fun p => p.2.1).getD 0

/-- The rule of the inner nodes of Types I, II, III of the further expansion of Lemma 5.5
[claim_estimate_remainder_terms], on a factor list. -/
def frule (F : List FFac) : FAsg := ⟨frk, fruleE (F.filterMap FFac.entData) false⟩

/-- The rule of the terminal cases (i)–(iii) of Lemma 5.5 [claim_estimate_remainder_terms], on a
factor list. -/
def fruleLeaf (F : List FFac) : FAsg := ⟨frk, fruleE (F.filterMap FFac.entData) true⟩

/-- (W1j) The integer test of the three points of `fmono_row` at `ε_A = ε/2`: `12 λ = A + B ε` at
`ξ = -1/3`, `-ε/2`, `0`, and `A + B ε ≤ 24 ε` for every `ε ∈ (0, 1/3]`, with `Im m` to a
nonnegative power and total degree at least `2` in `‖A‖`. -/
def FMono.ok (m : FMono) : Bool :=
  decide (0 ≤ m.i) && decide (2 ≤ m.d + m.o) &&
  ([(6 * m.a - 2 * m.i + 4 * m.l + 20 + (if 2 ≤ m.d then 4 * ((m.d : ℤ) - 2) else 0),
      3 * m.i - 6 * m.l - (if 2 ≤ m.d then 6 * ((m.d : ℤ) - 2) else 0)),
    (6 * m.a + 6 * m.l + 12, 12 - 9 * m.l),
    (6 * m.a + 6 * m.l + 12, 3 * m.i - 6 * m.l - 6 * ((m.d : ℤ) + m.o - 2))].all fun p =>
      (decide (p.1 < 0) || (decide (p.1 = 0) && decide (p.2 ≤ 24))) && decide (3 * p.1 + p.2 ≤ 24))

/-- `FMono.ok` as a proposition: `Im m` to a nonnegative power, total degree at least `2` in
`‖A‖`, and the integer test at each of the three points, with `(d - 2)⁺` written as a truncated
difference. -/
private lemma FR_ok_iff (m : FMono) : m.ok = true ↔
    0 ≤ m.i ∧ 2 ≤ m.d + m.o ∧
    ((6 * m.a - 2 * m.i + 4 * m.l + 20 + 4 * ((m.d - 2 : ℕ) : ℤ) < 0 ∨
        (6 * m.a - 2 * m.i + 4 * m.l + 20 + 4 * ((m.d - 2 : ℕ) : ℤ) = 0 ∧
          3 * m.i - 6 * m.l - 6 * ((m.d - 2 : ℕ) : ℤ) ≤ 24)) ∧
      3 * (6 * m.a - 2 * m.i + 4 * m.l + 20 + 4 * ((m.d - 2 : ℕ) : ℤ)) +
        (3 * m.i - 6 * m.l - 6 * ((m.d - 2 : ℕ) : ℤ)) ≤ 24) ∧
    ((6 * m.a + 6 * m.l + 12 < 0 ∨ (6 * m.a + 6 * m.l + 12 = 0 ∧ 12 - 9 * m.l ≤ 24)) ∧
      3 * (6 * m.a + 6 * m.l + 12) + (12 - 9 * m.l) ≤ 24) ∧
    ((6 * m.a + 6 * m.l + 12 < 0 ∨
        (6 * m.a + 6 * m.l + 12 = 0 ∧ 3 * m.i - 6 * m.l - 6 * ((m.d : ℤ) + m.o - 2) ≤ 24)) ∧
      3 * (6 * m.a + 6 * m.l + 12) + (3 * m.i - 6 * m.l - 6 * ((m.d : ℤ) + m.o - 2)) ≤ 24) := by
  have e : (if 2 ≤ m.d then 4 * ((m.d : ℤ) - 2) else 0) = 4 * ((m.d - 2 : ℕ) : ℤ) ∧
      (if 2 ≤ m.d then 6 * ((m.d : ℤ) - 2) else 0) = 6 * ((m.d - 2 : ℕ) : ℤ) := by
    split_ifs <;> omega
  simp only [FMono.ok, e.1, e.2, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    exact ⟨h1, by exact_mod_cast h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h1, by exact_mod_cast h2⟩, h3, h4, h5⟩

/-- One pair `(A, B)` of the integer test gives `A + B ε ≤ 24 ε` for `ε ∈ (0, 1/3]`. -/
private lemma FR_pair (A B : ℤ) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 3)
    (h : (A < 0 ∨ (A = 0 ∧ B ≤ 24)) ∧ 3 * A + B ≤ 24) : (A : ℝ) + B * ε ≤ 24 * ε := by
  obtain ⟨h1 | ⟨h1, h1'⟩, h2⟩ := h
  · have hA : (A : ℝ) ≤ -1 := by exact_mod_cast (by omega : A ≤ -1)
    have h2' : 3 * (A : ℝ) + B ≤ 24 := by exact_mod_cast h2
    rcases le_or_gt (B : ℝ) 24 with hB | hB
    · nlinarith
    · nlinarith
  · subst h1
    have : (B : ℝ) ≤ 24 := by exact_mod_cast h1'
    simp only [Int.cast_zero, zero_add]
    nlinarith

/-- (W1j) The row lemma from the integer test, for every `ε_A` with `ε < 2 ε_A` (applied at
`min(ε_A, 1/3)`): a monomial that passes `FMono.ok` is at most `C N^{2ε} N^{-5/3} 𝔯(k)^{2/3}
‖A‖²_HS` under (2.8) [eq:condA2], the bound on `Im m` and `η = etaK`, as in the proof of Lemma 5.5
[claim_estimate_remainder_terms]. -/
theorem fmono_ok_row (D : ℕ) (hD : 2 ≤ D) (εA ε : ℝ) (hεA : 0 < εA) (hε : 0 < ε)
    (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (m : FMono) (hm : m.ok = true) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ 1 →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        m.evalR N ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε)
            (hsNorm A) (opNorm A) ≤
          C * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) := by
  rw [FR_ok_iff] at hm
  obtain ⟨hi, hdo, h1, h2, h3⟩ := hm
  have p1 := FR_pair _ _ ε hε hε'' h1
  have p2 := FR_pair _ _ ε hε hε'' h2
  have p3 := FR_pair _ _ ε hε hε'' h3
  push_cast at p1 p2 p3
  have hdo' : (2 : ℝ) ≤ m.d + m.o := by exact_mod_cast hdo
  have hD2 : (0 : ℝ) ≤ ((m.d - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min εA (1 / 3) := ⟨_, rfl⟩
  have ht0 : 0 < t := ht ▸ lt_min hεA (by norm_num)
  have ht1 : t ≤ 1 / 3 := ht ▸ min_le_right _ _
  have ht2 : t ≤ εA := ht ▸ min_le_left _ _
  have htε : ε / 2 < t := ht ▸ lt_min (by linarith) (by linarith)
  have e1 : m.lamR ε t (-(1 / 3)) ≤ 2 * ε := by
    unfold FMono.lamR
    have hmin : min 0 (-t - -(1 / 3 : ℝ)) = 0 := min_eq_left (by linarith)
    rw [hmin]
    split_ifs with hd
    · have hc : ((m.d - 2 : ℕ) : ℝ) = (m.d : ℝ) - 2 := by
        rw [Nat.cast_sub hd]; norm_num
      rw [hc] at p1 hD2
      nlinarith [mul_le_mul_of_nonneg_left (show 1 / 3 - t ≤ 1 / 3 - ε / 2 by linarith) hD2]
    · have hc : ((m.d - 2 : ℕ) : ℝ) = 0 := by
        rw [Nat.sub_eq_zero_of_le (by omega)]; norm_num
      rw [hc] at p1
      nlinarith
  have e2 : m.lamR ε t (-t) ≤ 2 * ε := by
    unfold FMono.lamR
    have hmin : min 0 (-t - -t) = 0 := by simp
    rw [hmin]
    have hb : (0 : ℝ) ≤ ((m.d - 2 : ℕ) : ℝ) * (4 - 6 * ε) :=
      mul_nonneg hD2 (by linarith)
    rcases le_or_gt 0 (24 - 6 * (m.i : ℝ) - 6 * m.l) with hβ | hβ
    · split_ifs <;> nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ (show t - 1 / 3 ≤ 0 by linarith)]
    · split_ifs <;> nlinarith [mul_pos_of_neg_of_neg hβ (show ε / 2 - t < 0 by linarith)]
  have e3 : m.lamR ε t 0 ≤ 2 * ε := by
    unfold FMono.lamR
    have hmin : min 0 (-t - 0) = -t := by
      rw [sub_zero]; exact min_eq_right (by linarith)
    rw [hmin]
    have hdt := mul_le_mul_of_nonneg_left (show ε / 2 ≤ t by linarith)
      (show (0 : ℝ) ≤ (m.d : ℝ) + (m.o : ℝ) - 2 by linarith)
    split_ifs <;> nlinarith
  obtain ⟨C, hC, hrow⟩ := fmono_row D hD t ε ht0 hε (by linarith) hε'' m hi hdo (2 * ε) e1 e2 e3
  refine ⟨C, hC, fun N hN A hA k hk hk2 hhs => hrow N hN A hA k hk hk2 (hhs.trans ?_)⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hrk : 0 ≤ rk D N k := by unfold rk; positivity
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (Real.rpow_nonneg hrk _)

/-- The pairing through `𝔐_a` of the rules: slot `a` enters only through one letter `𝔐_a`
(`onlyDet`), which lies in a word with `Δ`, and the other slot is not paired this way
first. -/
def PkgExpr.fpm (R : PkgExpr) (a : Fin 2) : Bool :=
  R.onlyDet a && (R.loops.all fun w => w.any PkgLetter.isEnt || !w.contains (.lw (.det a))) &&
    (a = 0 || !(R.onlyDet 0 && R.loops.all fun w => w.any PkgLetter.isEnt ||
      !w.contains (.lw (.det 0))))

/-- The pairing through `𝒢_a` of the rules: slot `a` enters only through one resolvent
(`onlyRes`), and the other slot is not paired this way first. -/
def PkgExpr.fpg (R : PkgExpr) (a : Fin 2) : Bool :=
  R.onlyRes a && (a = 0 || !R.onlyRes 0)

/-- The factor list of the rules: `ffacs` with the pairings `fpm` (`𝔐_a - 𝔐_aᴴ`) and every
resolvent of a slot of `fpg` doubled (`𝒢_a 𝒢_aᴴ`). -/
def PkgExpr.rfacs (R : PkgExpr) : List FFac :=
  (R.ffacs (fun _ => false) R.fpm).map fun f =>
    if R.fpg 0 then f.dupRes 0 else if R.fpg 1 then f.dupRes 1 else f

/-- The factor `η` of the pairing through a resolvent, `2 i η 𝒢 𝒢ᴴ` of (5.29) [expansion_of_im]. -/
def PkgExpr.rext (R : PkgExpr) : FMono :=
  ⟨0, 0, if R.fpg 0 || R.fpg 1 then -2 else 0, 0, 0⟩

/-- The conclusion of the rule lemmas for one structure `R'` and the doubled exponent `pre` of its
prefactor: the assignment `g` is valid for the factor list of the rules, and every monomial of its
bound times the prefactor passes the integer test of `fmono_row` at `λ₀ = 2ε`. -/
def FRuleOK (R' : PkgExpr) (pre : ℤ) (g : FAsg) : Prop :=
  fvalid R'.nb R'.rfacs g = true ∧
    ∀ m ∈ fboundM R'.rfacs g, ((m.mul ⟨pre, 0, 0, 0, 0⟩).mul R'.rext).ok = true

end RBMTransitionEdge

end
