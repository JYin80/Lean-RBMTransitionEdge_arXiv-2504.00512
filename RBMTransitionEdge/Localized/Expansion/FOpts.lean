module

public import RBMTransitionEdge.Localized.Expansion.FSlots
public import RBMTransitionEdge.Localized.Expansion.LabelCS
public import RBMTransitionEdge.Localized.Expansion.FRows
public import RBMTransitionEdge.Localized.Expansion.DetLoop
public import RBMTransitionEdge.Localized.Expansion.PkgSharp
public import RBMTransitionEdge.Localized.Expansion.Bound
public import RBMTransitionEdge.LocalLaw.MultiRes
import all RBMTransitionEdge.Localized.Expansion.PkgSharp
import all RBMTransitionEdge.Localized.Expansion.Bound
import all RBMTransitionEdge.LocalLaw.MultiRes
import all Init.Data.List.SplitOn.Basic

@[expose] public section

/-!
# The menu of the further-class bound

For each factor of an expression of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: the options of an entry (sup, a Ward row or column, the
Hilbert–Schmidt norm, the splits at `Λ̃`, (5.90) [eq:addoneLambda]) with their `ℓ²` uses, order and
size; an assignment of the label sum, its validity and its bound; the sizes of the loops and light
weights off a bad event; and the lemmas that compute the chosen options, the uses and the validity under append, the
bound by membership, sup and the kinds of the paper's patterns.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The size of one row (`l2 = false`: sup over the other index; `true`: `ℓ²`) of a half of an
entry with `nl` letters `Λ̃` and `r` resolvents. -/
def fhalf (nl r : ℕ) (l2 : Bool) : FMono :=
  if l2 then
    (if nl = 0 then (FMono.omega r).mul ⟨1, 0, 0, 0, 0⟩
     else (FMono.omega r).mul ⟨0, 0, 0, 1, nl - 1⟩)
  else (FMono.omega r).mul ⟨0, 0, 0, 0, nl⟩

/-- An option for an entry: `ℓ²` uses at its row label and at its column label, the order it needs
(`1`: row label first, `-1`: column label first, `0`: none), and its size (a sum of monomials). -/
structure FOpt where
  /-- The number of `ℓ²` uses at the row label (`0`, `1` or `2`). -/
  cx : ℕ
  /-- The number of `ℓ²` uses at the column label (`0`, `1` or `2`). -/
  cy : ℕ
  /-- The order the option needs: `1` row label first, `-1` column label first, `0` none. -/
  ord : ℤ
  /-- The size of the option, a sum of monomials. -/
  val : List FMono
  deriving Repr, Inhabited

/-- The labels `x, y` lie in one block of the sum (`α, β` or `i, j`). -/
def fsameBlk (x y : ℕ) : Bool := (x < 2 && y < 2) || (2 ≤ x && 2 ≤ y)

/-- The options of an entry with distinct labels `x ≠ y`, `parts` the resolvent counts between its
letters `Λ̃`, `ext` the size of its paired letters `𝔐 - 𝔐ᴴ` (`Im m` each), `det` its letters
`𝔐` are unpaired: the entry (isotropic (A.53) [entprodG]), a row or column (Ward), the
Hilbert–Schmidt norm ((A.55) [two_loop_estimate]), (5.90) [eq:addoneLambda] for a package with
one `Λ̃` and no resolvent in one block, the double split at both `Λ̃`, and the splits at one `Λ̃`
with each half in sup or `ℓ²`, isotropic when one half is deterministic. -/
def fopts2 (x y : ℕ) (parts : List ℕ) (ext : FMono) (det : Bool) : List FOpt :=
  let nl := parts.length - 1
  let r := parts.sum
  let iso : FMono := (FMono.psi r).mul ⟨0, 0, 0, 0, nl⟩
  let row : FMono := (FMono.omega r).mul ⟨0, 0, 0, 0, nl⟩
  let base : List FOpt :=
    [⟨0, 0, 0, [iso]⟩, ⟨1, 0, 1, [row]⟩, ⟨0, 1, -1, [row]⟩, ⟨1, 1, 0, [fhalf nl r true]⟩]
  let a590 : List FOpt := if nl = 1 && r = 0 && fsameBlk x y && det then
      [⟨0, 0, 0, [⟨0, 0, 0, 0, 2⟩, ⟨-2, 0, 0, 2, 0⟩]⟩,
       ⟨1, 0, 0, [⟨0, 0, 0, 1, 1⟩, ⟨-1, 0, 0, 2, 0⟩]⟩,
       ⟨0, 1, 0, [⟨0, 0, 0, 1, 1⟩, ⟨-1, 0, 0, 2, 0⟩]⟩,
       ⟨1, 1, 0, [⟨0, 0, 0, 2, 0⟩, ⟨0, 0, 0, 2, 0⟩]⟩] else []
  let dbl : List FOpt := if nl = 2 && parts.head? = some 0 && parts.getLast? = some 0 then
      [false, true].flatMap fun mx => [false, true].map fun my =>
        ⟨if mx then 1 else 0, if my then 1 else 0, 0,
          [(FMono.psi (parts.getD 1 0)).mul
            ⟨0, 0, 0, (if mx then 1 else 0) + (if my then 1 else 0),
              (if mx then 0 else 1) + (if my then 0 else 1)⟩]⟩ else []
  let splits : List FOpt := (List.range nl).flatMap fun k =>
    let rL := (parts.take (k + 1)).sum
    let rR := (parts.drop (k + 1)).sum
    [true, false].flatMap fun left =>
      let nL := if left then k + 1 else k
      let nR := nl - nL
      [false, true].flatMap fun mx => [false, true].flatMap fun my =>
        let plain : FOpt := ⟨if mx then 1 else 0, if my then 1 else 0, 0,
          [(fhalf nL rL mx).mul (fhalf nR rR my)]⟩
        let isoL : List FOpt := if rL = 0 then
          [⟨if mx then 1 else 0, if my then 1 else 0, if my then -1 else 0,
            [(fhalf nL 0 mx).mul ((if my then FMono.omega rR else FMono.psi rR).mul
              ⟨0, 0, 0, 0, nR⟩)]⟩] else []
        let isoR : List FOpt := if rR = 0 then
          [⟨if mx then 1 else 0, if my then 1 else 0, if mx then 1 else 0,
            [(fhalf nR 0 my).mul ((if mx then FMono.omega rL else FMono.psi rL).mul
              ⟨0, 0, 0, 0, nL⟩)]⟩] else []
        plain :: (isoL ++ isoR)
  (base ++ a590 ++ dbl ++ splits).map fun o => { o with val := o.val.map fun m => m.mul ext }

/-- The options of an entry: `fopts2` for distinct labels; for `x = y` (a function of one label)
the entry in sup, the Hilbert–Schmidt norm with one use, and the options of `fopts2` without an
order, with their uses added. -/
def fopts (x y : ℕ) (parts : List ℕ) (ext : FMono) (det : Bool) : List FOpt :=
  if x = y then
    let nl := parts.length - 1
    let r := parts.sum
    [⟨0, 0, 0, [((FMono.psi r).mul ⟨0, 0, 0, 0, nl⟩).mul ext]⟩,
      ⟨1, 0, 0, [(fhalf nl r true).mul ext]⟩] ++
    (((fopts2 x y parts ext det).drop 4).filterMap fun o =>
      if o.ord ≠ 0 then none else some ⟨o.cx + o.cy, 0, 0, o.val⟩)
  else fopts2 x y parts ext det

/-- The resolvent counts between the letters `Λ̃` of a factor word. -/
def FLet.parts (w : List FLet) : List ℕ :=
  (w.splitOnP fun x => x == .lamt).map fun s => s.countP fun x => match x with
    | .res _ _ => true
    | _ => false

/-- The data `(x, y, parts, ext, det)` of an entry factor. -/
def FFac.entData : FFac → Option (ℕ × ℕ × List ℕ × FMono × Bool)
  | .ent x y w => some (x, y, FLet.parts w,
      ⟨0, 2 * ((w.countP fun z => match z with | .det _ pr => pr | _ => false : ℕ) : ℤ), 0, 0, 0⟩,
      w.all fun z => match z with | .det _ pr => !pr | _ => true)
  | _ => none

/-- The size of a loop or a light weight: `(Nη)⁻¹` ((2.23) [eq:aver_local]); a loop without `Λ̃`,
(A.53) [entprodG]; one `Λ̃`: (A.54) [one_loop_estimate], or `⟨Λ²⟩` ((A.7)
[add_one_more_Lambda]) with `Im m` for `⟨𝔐_a Λ̃ 𝔐_b E_x⟩`, `a ≠ b` ((5.5)
[regular_estimate_localized_eigenvector]); two `Λ̃`: (A.55) [two_loop_estimate]. -/
def FFac.fixV : FFac → FMono
  | .ent _ _ _ => ⟨0, 0, 0, 0, 0⟩
  | .wt _ _ => ⟨-2, 0, 2, 0, 0⟩
  | .loop w =>
    let nl := w.countP (· == .lamt)
    let r := w.countP fun x => match x with | .res _ _ => true | _ => false
    let gain := (List.range w.length).any fun t => match w.rotate t with
      | [.det a _, .lamt, .det b _, .proj _] => a != b
      | _ => false
    if nl = 0 then FMono.psi r
    else if nl = 1 then
      (if r = 0 then (if gain then ⟨-2, 2, 0, 2, 0⟩ else ⟨-2, 0, 0, 2, 0⟩)
       else (FMono.psi r).mul ⟨-1, 0, 0, 1, 0⟩)
    else (if r = 0 then ⟨-2, 0, 0, 2, 0⟩ else (FMono.psi r).mul ⟨-2, 0, 0, 2, 0⟩)

/-- An assignment of the label sum: the rank of each label `0, 1, 2, 3` in the order of
summation, and one option for each entry factor, in the order of the factors. -/
structure FAsg where
  /-- The rank of each label `0, 1, 2, 3` in the order of summation. -/
  rk : List ℕ
  /-- The index of the option chosen for each entry factor, in the order of the factors. -/
  opt : List ℕ

/-- The entries of a factor list with their option. -/
def fchosen (F : List FFac) (g : FAsg) : List ((ℕ × ℕ × List ℕ × FMono × Bool) × Option FOpt) :=
  let E := F.filterMap FFac.entData
  (List.range E.length).filterMap fun t => match E[t]? with
    | some d => some (d, (fopts d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2)[g.opt.getD t 0]?)
    | none => none

/-- The `ℓ²` uses of label `l` by an assignment. -/
def fuses (F : List FFac) (g : FAsg) (l : ℕ) : ℕ :=
  ((fchosen F g).map fun c => match c.2 with
    | some o => (if c.1.1 = l then o.cx else 0) + (if c.1.2.1 = l ∧ c.1.1 ≠ l then o.cy else 0)
    | none => 0).sum

/-- An assignment is valid: labels below `4`, block indices below `nb`, one option per entry,
at most two `ℓ²` uses per label, the orders of the options compatible with the ranks, no paired
letter in a loop. -/
def fvalid (nb : ℕ) (F : List FFac) (g : FAsg) : Bool :=
  g.rk.length = 4 && g.opt.length = (F.filterMap FFac.entData).length &&
  (F.all fun f => match f with
    | .ent x y w => x < 4 && y < 4 && w.all fun z => match z with | .proj u => u < nb | _ => true
    | .loop w => w.all fun z => match z with
        | .proj u => u < nb
        | .det _ pr => !pr
        | _ => true
    | .wt _ u => u < nb) &&
  ((List.range 4).all fun l => fuses F g l ≤ 2) &&
  ((fchosen F g).all fun c => match c.2 with
    | none => false
    | some o => (o.ord != 1 || g.rk.getD c.1.1 0 < g.rk.getD c.1.2.1 0) &&
        (o.ord != -1 || g.rk.getD c.1.2.1 0 < g.rk.getD c.1.1 0))

/-- The bound of a valid assignment, as a sum of monomials: `N^{(2 - c_l)/2}` per label, the
sizes of the loops and light weights, and the sizes of the chosen options. -/
def fboundM (F : List FFac) (g : FAsg) : List FMono :=
  let lab : FMono := ⟨((List.range 4).map fun l => 2 - (fuses F g l : ℤ)).sum, 0, 0, 0, 0⟩
  let fix : FMono := F.foldl (fun m f => m.mul f.fixV) lab
  (fchosen F g).foldl (fun L c => match c.2 with
    | some o => L.flatMap fun p => o.val.map fun q => p.mul q
    | none => L) [fix]

/-- The norm that an option of `fopts` bounds, for a nonnegative function `f` of the row and the
column label of an entry: for distinct labels the mixed norm `fcsNorm` with the row label summed
first (`rowFirst`) or the column label first; for equal labels (a function of one label) the sup,
the `ℓ²` norm or the sum, for `0`, `1` or `2` uses. -/
def foptNorm {ι : Type*} [Fintype ι] (diag : Bool) (o : FOpt) (rowFirst : Bool)
    (f : ι → ι → ℝ) : ℝ :=
  if diag then
    (match o.cx with
     | 0 => ⨆ x, f x x
     | 1 => Real.sqrt (∑ x, f x x ^ 2)
     | _ => ∑ x, f x x)
  else if rowFirst then fcsNorm f (o.cx == 1) (o.cy == 1)
  else fcsNorm (fun y x => f x y) (o.cy == 1) (o.cx == 1)

open private PS_It PS_v PS_nr PS_Gr PS_b PS_Adm PS_fbw PS_fbl PS_fbt PS_slot PS_bnd PS_b_nonneg
  PS_psi_nonneg from RBMTransitionEdge.Localized.Expansion.PkgSharp
open private Bd_opNorm_E Bd_ntr_le Bd_prod_norm Bd_opNorm_one Bd_opNorm_sub Bd_avgSq_le
  Bd_avgSq_nonneg Bd_opNorm_nonneg from RBMTransitionEdge.Localized.Expansion.Bound
open private MultiRes_hs2_mul_left_le MultiRes_hsNorm_sq from RBMTransitionEdge.LocalLaw.MultiRes

/-! ### Monomials at the slots -/

private lemma FO_evalR_mul (m m' : FMono) (N : ℕ) (hN : 1 ≤ N) (M η hs op : ℝ) (hM : 0 < M)
    (hη : 0 < η) : (m.mul m').evalR N M η hs op = m.evalR N M η hs op * m'.evalR N M η hs op := by
  unfold FMono.evalR FMono.mul
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  push_cast
  rw [show ((m.a : ℝ) + m'.a) / 2 = (m.a : ℝ) / 2 + (m'.a : ℝ) / 2 by ring, Real.rpow_add hN0,
    show ((m.i : ℝ) + m'.i) / 2 = (m.i : ℝ) / 2 + (m'.i : ℝ) / 2 by ring, Real.rpow_add hM,
    show -((m.l : ℝ) + m'.l) / 2 = -(m.l : ℝ) / 2 + -(m'.l : ℝ) / 2 by ring, Real.rpow_add hη,
    pow_add, pow_add]
  ring

private lemma FO_evalR_nonneg (m : FMono) (N : ℕ) {M η hs op : ℝ} (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hhs : 0 ≤ hs) (hop : 0 ≤ op) : 0 ≤ m.evalR N M η hs op :=
  mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg hM _)) (Real.rpow_nonneg hη _)) (pow_nonneg hhs _)) (pow_nonneg hop _)

private lemma FO_ev_psi (N : ℕ) (M η hs op : ℝ) (hη : 0 ≤ η) (r : ℕ) :
    (FMono.psi r).evalR N M η hs op = pkgPsi η M r := by
  unfold FMono.psi pkgPsi
  split_ifs with h
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp only [FMono.evalR, Nat.add_sub_cancel, pow_zero, mul_one]
    have e1 : -(((2 * (((s + 1 : ℕ) : ℤ) - 1)) : ℤ) : ℝ) / 2 = -(s : ℝ) := by push_cast; ring
    rw [e1, Real.rpow_neg hη, Real.rpow_natCast]
    norm_num
    ring
  · simp [FMono.evalR, show r - 1 = 0 by omega]

private lemma FO_ev_wt (N : ℕ) (M η hs op : ℝ) :
    (⟨-2, 0, 2, 0, 0⟩ : FMono).evalR N M η hs op = (N : ℝ)⁻¹ * η⁻¹ := by
  simp only [FMono.evalR]
  norm_num [Real.rpow_neg_one]

private lemma FO_ev_hs2 (N : ℕ) (M η hs op : ℝ) :
    (⟨-2, 0, 0, 2, 0⟩ : FMono).evalR N M η hs op = (N : ℝ)⁻¹ * hs ^ 2 := by
  simp only [FMono.evalR]
  norm_num [Real.rpow_neg_one]

private lemma FO_ev_hs2m (N : ℕ) (M η hs op : ℝ) :
    (⟨-2, 2, 0, 2, 0⟩ : FMono).evalR N M η hs op = (N : ℝ)⁻¹ * M * hs ^ 2 := by
  simp only [FMono.evalR]
  norm_num [Real.rpow_neg_one]

private lemma FO_ev_hs1 (N : ℕ) (M η hs op : ℝ) :
    (⟨-1, 0, 0, 1, 0⟩ : FMono).evalR N M η hs op = (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs := by
  simp only [FMono.evalR]
  norm_num

/-! ### The good event of a loop or a light weight -/

/-- The bound `‖f‖ ≤ Cst N^τ m` of a factor off an event of probability `≤ N^{-D'}`, at the slots
of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law], `m` evaluated at the bound on `Im m`, `η`, `‖A‖_HS`,
`‖A‖`. -/
private def FO_Good (D nb : ℕ) (δA εA ε : ℝ) (C : ℕ → ℝ) (f : FFac) (m : FMono) (τ D' Cst : ℝ)
    (N : ℕ) : Prop :=
  ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
  ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
  ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
  hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
  ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
      ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
  ∀ (ι : Fin nb → Fin D) (κ : ℕ → Idx D N), ∃ bad : Set (Idx D N → Idx D N → ℂ),
    μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧ ∀ h, h ∉ bad →
      ‖f.val e ι κ h‖ ≤ Cst * (N : ℝ) ^ τ * m.evalR N
        ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε)
        (hsNorm A) (opNorm A)

/-- The constant of `FO_Good` is absorbed by `N^{τ'/2}` for `N` large. -/
private lemma FO_absorb (D nb : ℕ) (δA εA ε : ℝ) (C : ℕ → ℝ) (f : FFac) (τ' D' : ℝ)
    (hτ' : 0 < τ') (h : ∃ Cst : ℝ, ∃ N₁ : ℕ, ∀ N, N₁ ≤ N →
      FO_Good D nb δA εA ε C f f.fixV (τ' / 2) D' Cst N) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
      ∀ (ι : Fin nb → Fin D) (κ : ℕ → Idx D N),
        μ {h | (N : ℝ) ^ τ' * f.fixV.evalR N
            ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε)
            (hsNorm A) (opNorm A) < ‖f.val e ι κ h‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  obtain ⟨Cst, N₁, hN₁⟩ := h
  have hev : ∀ᶠ N : ℕ in atTop, Cst ≤ (N : ℝ) ^ (τ' / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < τ' / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop Cst
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max N₁ (max N₂ 1), fun N hN μ hμ A hA k hk hkN hhs e he ι κ => ?_⟩
  obtain ⟨bad, hbad, hb⟩ := hN₁ N (le_of_max_le_left hN) μ hμ A hA k hk hkN hhs e he ι κ
  refine le_trans (measure_mono fun h hh => ?_) hbad
  by_contra hnot
  have h1 := hb h hnot
  have hC := hN₂ N (le_trans (le_max_left _ _) (le_of_max_le_right hN))
  simp only [Set.mem_ofPred_eq] at hh
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) (le_of_max_le_right hN)
  have hrk : (0 : ℝ) ≤ rk D N k := by unfold rk; positivity
  have hMb : 0 ≤ (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Real.rpow_nonneg hrk _)
  have hη : 0 ≤ etaK D N k ε :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Real.rpow_nonneg hrk _)
  have hV : 0 ≤ f.fixV.evalR N ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ))
      (etaK D N k ε) (hsNorm A) (opNorm A) :=
    FO_evalR_nonneg _ _ hMb hη (Real.sqrt_nonneg _) (Bd_opNorm_nonneg A)
  have hsplit : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
    rw [← Real.rpow_add (by linarith)]
    ring_nf
  have hN2 : 0 ≤ (N : ℝ) ^ (τ' / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [hsplit] at hh
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hN2) hV
  linarith

/-! ### The slots -/

/-- The facts at the slots used by the bounds of the loops: the hypotheses of Lemma A.4
[lemma_necessary_estimates], `Im z_a = η`, the bound on `Im m_a`, the norms of `𝔐_a` and `Λ̃`,
and the Hilbert–Schmidt norms. -/
private lemma FO_facts (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) :
    ∃ c₀ K CU : ℝ, 0 < c₀ ∧ 2 ≤ K ∧ 1 ≤ CU ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        PS_Adm D N δA (ε / 2) c₀ K e ∧ e.A = A ∧ 1 ≤ N ∧
        (∀ a, (e.z a).im = etaK D N k ε) ∧ 0 < etaK D N k ε ∧
        0 < (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ) ∧
        (∀ a, (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im ≤
          CU * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ))) ∧
        (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im ≤ 1 ∧
        (∀ a, opNorm (e.M a) ≤ K) ∧ opNorm e.Lt ≤ 2 * K ∧
        hsNorm e.Lt ≤ K * hsNorm A ∧ hsNorm (lam D N e.A) ≤ K * hsNorm A ∧
        avgSq (lam D N e.A) ≤ K * (hsNorm A ^ 2 / N) := by
  obtain ⟨c₀, K, hc₀, hK2, -, N₁, hslot⟩ := PS_slot D hD δA εA ε hδA hεA hε hε' hε'' C 1
  obtain ⟨CU, hCU, N₂, hCUb⟩ := pkg_slot_im D hD δA εA ε hδA hεA hε hε' hε''
  refine ⟨c₀, K, max CU 1, hc₀, hK2, le_max_right _ _, max N₁ N₂,
    fun N hN μ hμ A hA k hk hkN hhs e he => ?_⟩
  obtain ⟨hctx, hM, -, havg, heA⟩ := hslot N (le_of_max_le_left hN) μ hμ A hA k hk hkN hhs e he
  obtain ⟨hadm, heta, -, hm1, -, -, hsLt, hslam, -, -, -, -, hN1⟩ :=
    hctx e.M hM (fun _ => 1) (fun _ => Bd_opNorm_one)
  have hCU' := hCUb N (le_of_max_le_right hN) A hA k hk hkN hhs e he
  have hη : 0 < etaK D N k ε := heta 0 ▸ (hadm.2.2.2.1 0).2.1
  have hrk : (1 : ℝ) ≤ rk D N k := by
    unfold rk
    exact_mod_cast (show 1 ≤ min k (D * N + 1 - k) by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hMb : 0 < (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ) :=
    mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos (by linarith) _)
  have hLt : opNorm e.Lt ≤ 2 * K := by
    obtain ⟨-, hA2, -, -, hδ⟩ := hadm
    have hl : opNorm (lam D N e.A) ≤ 1 / 10 := (opNorm_lam_le D N e.A).trans (by linarith)
    have hav := Bd_avgSq_le (lam D N e.A)
    have h1 := Bd_opNorm_one (ι := Idx D N)
    have h0 := Bd_opNorm_nonneg (lam D N e.A)
    unfold LoopEnv.Lt
    refine (Bd_opNorm_sub _ _).trans ?_
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hd : |e.δ| ≤ K * (1 / 100) := hδ.trans (mul_le_mul_of_nonneg_left (by nlinarith)
      (by linarith))
    nlinarith [abs_nonneg e.δ, Bd_opNorm_nonneg (1 : Matrix (Idx D N) (Idx D N) ℂ)]
  refine ⟨hadm, heA, hN1, heta, hη, hMb, fun a => (hCU' a).2.trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hMb.le), hm1, hM, hLt, heA ▸ hsLt,
    heA ▸ hslam, heA ▸ havg⟩

/-! ### The light weights: (2.23) -/

private lemma FO_wt_good (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (a : Fin 2) (u : ℕ)
    (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) (hD' : 0 < D') :
    ∃ Cst : ℝ, ∃ N₁ : ℕ, ∀ N, N₁ ≤ N →
      FO_Good D nb δA εA ε C (.wt a u) (FFac.wt a u).fixV (τ' / 2) D' Cst N := by
  obtain ⟨c₀, Kδ, -, -, N₁, hadm⟩ := loop_env_admissible D hD δA εA ε hδA hεA hε hε' hε''
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (fb_weight D (by omega) δA (ε / 2) 1 hδA
    (by positivity) le_rfl C (τ' / 2) (by positivity) D' hD')
  refine ⟨1, max N₁ N₂, fun N hN μ hμ A hA k hk hkN hhs e he ι κ => ?_⟩
  obtain ⟨-, hc, hz, -⟩ := hadm N (le_of_max_le_left hN) A hA k hk hkN hhs e he
  have heA : e.A = A := by
    rcases he with ⟨s, rfl⟩ | ⟨t, -, s, rfl⟩ <;> rfl
  obtain ⟨bad, hbad, hb⟩ := hN₂ N (le_of_max_le_right hN) μ hμ e (heA ▸ hA) hc
    (fun a => (hz a).1) a (e.E ι u) (Bd_opNorm_E e ι u)
  refine ⟨bad, hbad, fun h hh => ?_⟩
  refine (hb h hh).trans (le_of_eq ?_)
  rw [abs_of_pos (hz a).2.1, (hz a).2.2.1]
  change _ = 1 * (N : ℝ) ^ (τ' / 2) * (⟨-2, 0, 2, 0, 0⟩ : FMono).evalR N _ _ _ _
  rw [FO_ev_wt]
  field_simp

/-! ### The loops: (A.53)–(A.55), (A.7) -/

/-- The letter is a resolvent. -/
private def FO_isRes : FLet → Bool
  | .res _ _ => true
  | _ => false

/-- The gain pattern of `FFac.fixV`: `⟨𝔐_a Λ̃ 𝔐_b E_x⟩` up to rotation, `a ≠ b`. -/
private def FO_gain (w : List FLet) : Bool :=
  (List.range w.length).any fun t => match w.rotate t with
    | [.det a _, .lamt, .det b _, .proj _] => a != b
    | _ => false

private lemma FO_fixV_loop (w : List FLet) : (FFac.loop w).fixV =
    (if w.countP (· == .lamt) = 0 then FMono.psi (w.countP FO_isRes)
    else if w.countP (· == .lamt) = 1 then
      (if w.countP FO_isRes = 0 then (if FO_gain w then ⟨-2, 2, 0, 2, 0⟩ else ⟨-2, 0, 0, 2, 0⟩)
       else (FMono.psi (w.countP FO_isRes)).mul ⟨-1, 0, 0, 1, 0⟩)
    else (if w.countP FO_isRes = 0 then ⟨-2, 0, 0, 2, 0⟩
      else (FMono.psi (w.countP FO_isRes)).mul ⟨-2, 0, 0, 2, 0⟩)) := rfl

/-- A factor letter as a factor of a product of Lemma A.4 [lemma_necessary_estimates]. -/
private def FO_it {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D) :
    FLet → PS_It (Idx D N)
  | .res a f => .inl (a, f)
  | z => .inr (FLet.mat e ι 0 z)

private lemma FO_v {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (l : List FLet) :
    PS_v (PS_Gr e h) (l.map (FO_it e ι)) = (l.map (FLet.mat e ι h)).prod := by
  unfold PS_v
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun z _ => ?_
  cases z <;> rfl

private lemma FO_nr {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D) (l : List FLet) :
    PS_nr (l.map (FO_it e ι)) = l.countP FO_isRes := by
  unfold PS_nr
  rw [List.countP_map]
  congr 1
  funext z
  cases z <;> rfl

private lemma FO_it_det {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D) (K₀ : ℝ)
    (hK : 1 ≤ K₀) (hM : ∀ a, opNorm (e.M a) ≤ K₀) (hL : opNorm e.Lt ≤ K₀) (l : List FLet)
    (hl : ∀ a pr, FLet.det a pr ∈ l → pr = false) :
    ∀ B, Sum.inr B ∈ l.map (FO_it e ι) → opNorm B ≤ K₀ := by
  intro B hB
  obtain ⟨z, hz, hzB⟩ := List.mem_map.1 hB
  cases z with
  | res a f => cases hzB
  | det a pr =>
    obtain rfl := hl a pr hz
    cases hzB
    exact hM a
  | proj x =>
    cases hzB
    exact (Bd_opNorm_E e ι x).trans hK
  | lamt =>
    cases hzB
    exact hL

private lemma FO_mat_le {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (K₀ : ℝ) (hK : 1 ≤ K₀) (hM : ∀ a, opNorm (e.M a) ≤ K₀)
    (hL : opNorm e.Lt ≤ K₀) (l : List FLet) (hl : ∀ a pr, FLet.det a pr ∈ l → pr = false)
    (hr : l.countP FO_isRes = 0) : opNorm (l.map (FLet.mat e ι h)).prod ≤ K₀ ^ l.length := by
  refine Bd_prod_norm l _ K₀ hK fun z hz => ?_
  cases z with
  | res a f =>
    have := List.countP_eq_zero.1 hr _ hz
    simp [FO_isRes] at this
  | det a pr =>
    obtain rfl := hl a pr hz
    exact hM a
  | proj x => exact (Bd_opNorm_E e ι x).trans hK
  | lamt => exact hL

private lemma FO_split1 (w : List FLet) (h : 1 ≤ w.countP (· == FLet.lamt)) :
    ∃ P Q : List FLet, w = P ++ FLet.lamt :: Q := by
  obtain ⟨z, hz, hz'⟩ := List.countP_pos_iff.1 h
  have : z = FLet.lamt := by simpa using hz'
  exact List.append_of_mem (this ▸ hz)

private lemma FO_split2 (w : List FLet) (h : 2 ≤ w.countP (· == FLet.lamt)) :
    ∃ X Y Z : List FLet, w = X ++ FLet.lamt :: (Y ++ FLet.lamt :: Z) := by
  obtain ⟨P, T, rfl⟩ := FO_split1 w (by omega)
  simp only [List.countP_append, List.countP_cons, beq_self_eq_true, ↓reduceIte] at h
  by_cases hT : 1 ≤ T.countP (· == FLet.lamt)
  · obtain ⟨Y, Z, rfl⟩ := FO_split1 T hT
    exact ⟨P, Y, Z, rfl⟩
  · obtain ⟨X, Y, rfl⟩ := FO_split1 P (by omega)
    exact ⟨X, Y, T, by simp⟩

/-- `|tr (A B)| ≤ ‖A‖_HS ‖B‖_HS`. -/
private lemma FO_trace_cs {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) :
    ‖(A * B).trace‖ ≤ hsNorm A * hsNorm B := by
  have h1 : (A * B).trace = ∑ p : ι × ι, A p.1 p.2 * B p.2 p.1 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Fintype.sum_prod_type]
  have h2 : hsNorm A = Real.sqrt (∑ p : ι × ι, ‖A p.1 p.2‖ ^ 2) := by
    unfold hsNorm
    rw [Fintype.sum_prod_type]
  have h3 : hsNorm B = Real.sqrt (∑ p : ι × ι, ‖B p.2 p.1‖ ^ 2) := by
    unfold hsNorm
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [h1, h2, h3]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- `‖U L‖_HS ≤ ‖U‖ ‖L‖_HS`. -/
private lemma FO_hs_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (U L : Matrix ι ι ℂ) :
    hsNorm (U * L) ≤ opNorm U * hsNorm L := by
  have h := MultiRes_hs2_mul_left_le U L
  rw [← MultiRes_hsNorm_sq, ← MultiRes_hsNorm_sq, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _)
    (mul_nonneg (Bd_opNorm_nonneg U) (Real.sqrt_nonneg _)) two_ne_zero).1 h

/-- The deterministic two-`Λ̃` loop: `|⟨U L V L⟩| ≤ ‖U‖ ‖V‖ ‖L‖²_HS / n`. -/
private lemma FO_tr_cs {ι : Type*} [Fintype ι] [DecidableEq ι] (U V L : Matrix ι ι ℂ) :
    ‖ntr (U * L * V * L)‖ ≤ (Fintype.card ι : ℝ)⁻¹ * (opNorm U * opNorm V * hsNorm L ^ 2) := by
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast, show U * L * V * L = (U * L) * (V * L) by
    simp only [Matrix.mul_assoc]]
  refine mul_le_mul_of_nonneg_left ((FO_trace_cs _ _).trans ?_) (by positivity)
  have h1 := FO_hs_mul U L
  have h2 := FO_hs_mul V L
  have h0 : 0 ≤ hsNorm (U * L) := Real.sqrt_nonneg _
  have h0' : 0 ≤ hsNorm (V * L) := Real.sqrt_nonneg _
  calc hsNorm (U * L) * hsNorm (V * L) ≤ (opNorm U * hsNorm L) * (opNorm V * hsNorm L) :=
        mul_le_mul h1 h2 h0' (mul_nonneg (Bd_opNorm_nonneg U) (Real.sqrt_nonneg _))
    _ = opNorm U * opNorm V * hsNorm L ^ 2 := by ring

/-- A loop without a resolvent and without `Λ̃`: a product of bounded deterministic letters. -/
private lemma FO_loop_a (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (w : List FLet)
    (hw : ∀ a pr, FLet.det a pr ∈ w → pr = false) (hr0 : w.countP FO_isRes = 0)
    (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) :
    ∃ Cst : ℝ, ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → FO_Good D nb δA εA ε C (.loop w)
      (FMono.psi (w.countP FO_isRes)) (τ' / 2) D' Cst N := by
  obtain ⟨c₀, K, CU, -, hK2, -, N₁, hfac⟩ := FO_facts D hD δA εA ε hδA hεA hε hε' hε'' C
  refine ⟨(2 * K) ^ w.length, N₁, fun N hN μ hμ A hA k hk hkN hhs e he ι κ => ?_⟩
  obtain ⟨-, -, hN1, -, hη, -, -, -, hM, hLt, -, -, -⟩ := hfac N hN μ hμ A hA k hk hkN hhs e he
  refine ⟨∅, by simp, fun h _ => ?_⟩
  rw [hr0, FO_ev_psi _ _ _ _ _ hη.le]
  have hp : pkgPsi (etaK D N k ε) ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ))
      0 = 1 := by
    simp [pkgPsi]
  rw [hp, mul_one]
  have hNτ : (1 : ℝ) ≤ (N : ℝ) ^ (τ' / 2) :=
    Real.one_le_rpow (by exact_mod_cast hN1) (by positivity)
  have h1 := (Bd_ntr_le _).trans (FO_mat_le e ι h (2 * K) (by linarith)
    (fun a => (hM a).trans (by linarith)) hLt w hw hr0)
  calc ‖FFac.val e ι κ h (.loop w)‖ ≤ (2 * K) ^ w.length := h1
    _ ≤ (2 * K) ^ w.length * (N : ℝ) ^ (τ' / 2) :=
        le_mul_of_one_le_right (by positivity) hNτ

/-- A loop with resolvents and without `Λ̃`: (A.53) [entprodG] averaged. -/
private lemma FO_loop_b (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (w : List FLet)
    (hw : ∀ a pr, FLet.det a pr ∈ w → pr = false) (hr : 1 ≤ w.countP FO_isRes)
    (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) (hD' : 0 < D') :
    ∃ Cst : ℝ, ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → FO_Good D nb δA εA ε C (.loop w)
      (FMono.psi (w.countP FO_isRes)) (τ' / 2) D' Cst N := by
  obtain ⟨c₀, K, CU, hc₀, hK2, hCU, N₁, hfac⟩ := FO_facts D hD δA εA ε hδA hεA hε hε' hε'' C
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.1 (PS_fbw D hD δA (ε / 2) c₀ (2 * K) hδA
    (by positivity) hc₀ (by linarith) C w.length (w.countP FO_isRes) hr (τ' / 2) (by positivity)
    D' hD')
  refine ⟨((2 * K) ^ w.length) ^ (w.countP FO_isRes + 1) * CU, max N₁ N₃,
    fun N hN μ hμ A hA k hk hkN hhs e he ι κ => ?_⟩
  obtain ⟨hadm, -, -, heta, hη, hMb, hCU', -, hM, hLt, -, -, -⟩ :=
    hfac N (le_of_max_le_left hN) μ hμ A hA k hk hkN hhs e he
  have hdet := FO_it_det e ι (2 * K) (by linarith) (fun a => (hM a).trans (by linarith)) hLt w hw
  refine ⟨_, (hN₃ N (le_of_max_le_right hN) μ hμ K e hadm (w.map (FO_it e ι)) (FO_nr e ι w)
    (by simp) hdet).1, fun h hh => ?_⟩
  simp only [Set.mem_ofPred_eq, not_lt, FO_v] at hh
  rw [FO_ev_psi _ _ _ _ _ hη.le]
  have hb := PS_bnd hη heta hCU hCU' (w.countP FO_isRes)
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ (τ' / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h2 : (0 : ℝ) ≤ ((2 * K) ^ w.length) ^ (w.countP FO_isRes + 1) := by
    have : (0 : ℝ) ≤ 2 * K := by linarith
    positivity
  refine hh.trans ?_
  calc (N : ℝ) ^ (τ' / 2) * (((2 * K) ^ w.length) ^ (w.countP FO_isRes + 1) *
        PS_b e (w.countP FO_isRes))
      ≤ (N : ℝ) ^ (τ' / 2) * (((2 * K) ^ w.length) ^ (w.countP FO_isRes + 1) *
        (CU * pkgPsi (etaK D N k ε) ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ))
          (w.countP FO_isRes))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb h2) h0
    _ = _ := by ring

/-- A factor letter as a letter of a loop. -/
private def FO_ll : FLet → LoopLetter
  | .res a _ => .res a
  | .det a _ => .det a
  | .proj x => .proj x
  | .lamt => .lamt 0

/-- A loop with one `Λ̃` and no resolvent: (A.7) [add_one_more_Lambda], with the gain of (5.5)
[regular_estimate_localized_eigenvector]. -/
private lemma FO_loop_c (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (w : List FLet)
    (hw : ∀ a pr, FLet.det a pr ∈ w → pr = false) (hl1 : w.countP (· == FLet.lamt) = 1)
    (hr0 : w.countP FO_isRes = 0) (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) :
    ∃ Cst : ℝ, ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → FO_Good D nb δA εA ε C (.loop w)
      (if FO_gain w then ⟨-2, 2, 0, 2, 0⟩ else ⟨-2, 0, 0, 2, 0⟩) (τ' / 2) D' Cst N := by
  have hc1 : (w.map FO_ll).countP (fun x => match x with | .lamt _ => true | _ => false) = 1 := by
    rw [List.countP_map, ← hl1]
    congr 1
    funext z
    cases z <;> rfl
  have hc0 : (w.map FO_ll).countP (fun x => match x with | .res _ => true | _ => false) = 0 := by
    rw [List.countP_map, ← hr0]
    congr 1
    funext z
    cases z <;> rfl
  obtain ⟨K₂, hK₂, N₃, hlam⟩ := pkg_lam0_bound D hD δA εA ε hδA hεA hε hε' hε'' (w.map FO_ll)
    hc1 hc0
  have hgain : FO_gain w = true → pkgGainLoop ((w.map FO_ll).map PkgLetter.lw) = true := by
    intro hg
    unfold FO_gain at hg
    unfold pkgGainLoop
    rw [List.any_eq_true] at hg ⊢
    obtain ⟨t, ht, hmt⟩ := hg
    refine ⟨t, by simpa using ht, ?_⟩
    rw [List.map_map, ← List.map_rotate]
    generalize w.rotate t = l at hmt ⊢
    rcases l with _ | ⟨z1, _ | ⟨z2, _ | ⟨z3, _ | ⟨z4, _ | ⟨z5, l⟩⟩⟩⟩⟩ <;>
      (try cases z1) <;> (try cases z2) <;> (try cases z3) <;> (try cases z4) <;> exact hmt
  obtain ⟨c₀, K, CU, -, hK2, hCU, N₁, hfac⟩ := FO_facts D hD δA εA ε hδA hεA hε hε' hε'' C
  refine ⟨K₂ * K * CU, max N₁ N₃, fun N hN μ hμ A hA k hk hkN hhs e he ι κ => ?_⟩
  obtain ⟨-, heA, hN1, -, -, hMb, hCU', hm1, -, -, -, -, havg⟩ :=
    hfac N (le_of_max_le_left hN) μ hμ A hA k hk hkN hhs e he
  refine ⟨∅, by simp, fun h _ => ?_⟩
  have hmat : loopWordMat (e.G h) e.M (e.E ι) e.Lt (w.map FO_ll) =
      (w.map (FLet.mat e ι h)).prod := by
    unfold loopWordMat
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun z hz => ?_
    cases z with
    | res a f =>
      have := List.countP_eq_zero.1 hr0 _ hz
      simp [FO_isRes] at this
    | det a pr =>
      obtain rfl := hw a pr hz
      rfl
    | proj x => rfl
    | lamt => rfl
  have hb := hlam N (le_of_max_le_right hN) A hA k hk hkN hhs e he nb ι h
  rw [hmat] at hb
  have hav0 : 0 ≤ avgSq (lam D N e.A) := Bd_avgSq_nonneg _ (lam_isHermitian D N _)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNτ : (1 : ℝ) ≤ (N : ℝ) ^ (τ' / 2) :=
    Real.one_le_rpow (by exact_mod_cast hN1) (by positivity)
  have hK0 : 0 < K := by linarith
  have hCU0 : 0 < CU := by linarith
  have hs0 : 0 ≤ hsNorm A ^ 2 / N := by positivity
  set Mb := (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)
  set m₁ := (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im
  change ‖ntr (w.map (FLet.mat e ι h)).prod‖ ≤ _
  refine hb.trans ?_
  by_cases hg : FO_gain w = true
  · rw [ite_eq_left hg, ite_eq_left (hgain hg), FO_ev_hs2m]
    have h1 : m₁ * avgSq (lam D N e.A) ≤ (CU * Mb) * (K * (hsNorm A ^ 2 / N)) :=
      mul_le_mul (hCU' 1) havg hav0 (by positivity)
    have h2 : 0 ≤ K₂ * K * CU * ((N : ℝ)⁻¹ * Mb * hsNorm A ^ 2) := by positivity
    calc K₂ * (m₁ * avgSq (lam D N e.A)) ≤ K₂ * ((CU * Mb) * (K * (hsNorm A ^ 2 / N))) :=
          mul_le_mul_of_nonneg_left h1 hK₂.le
      _ = K₂ * K * CU * ((N : ℝ)⁻¹ * Mb * hsNorm A ^ 2) * 1 := by ring
      _ ≤ K₂ * K * CU * ((N : ℝ)⁻¹ * Mb * hsNorm A ^ 2) * (N : ℝ) ^ (τ' / 2) :=
          mul_le_mul_of_nonneg_left hNτ h2
      _ = _ := by ring
  · rw [ite_eq_right hg, FO_ev_hs2]
    have hg1 : (if pkgGainLoop ((w.map FO_ll).map PkgLetter.lw) then m₁ else 1) ≤ 1 := by
      split_ifs
      · exact hm1
      · exact le_rfl
    have h1 : (if pkgGainLoop ((w.map FO_ll).map PkgLetter.lw) then m₁ else 1) *
        avgSq (lam D N e.A) ≤ 1 * (K * (hsNorm A ^ 2 / N)) :=
      (mul_le_mul_of_nonneg_right hg1 hav0).trans (by nlinarith)
    have h2 : 0 ≤ K₂ * K * ((N : ℝ)⁻¹ * hsNorm A ^ 2) := by positivity
    calc K₂ * ((if pkgGainLoop ((w.map FO_ll).map PkgLetter.lw) then m₁ else 1) *
          avgSq (lam D N e.A)) ≤ K₂ * (1 * (K * (hsNorm A ^ 2 / N))) :=
          mul_le_mul_of_nonneg_left h1 hK₂.le
      _ = K₂ * K * ((N : ℝ)⁻¹ * hsNorm A ^ 2) * 1 * 1 := by ring
      _ ≤ K₂ * K * ((N : ℝ)⁻¹ * hsNorm A ^ 2) * CU * (N : ℝ) ^ (τ' / 2) := by
          gcongr
      _ = _ := by ring

/-- A loop with one `Λ̃` and resolvents: (A.54) [one_loop_estimate]. -/
private lemma FO_loop_d (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (w : List FLet)
    (hw : ∀ a pr, FLet.det a pr ∈ w → pr = false) (hl : 1 ≤ w.countP (· == FLet.lamt))
    (hr : 1 ≤ w.countP FO_isRes) (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) (hD' : 0 < D') :
    ∃ Cst : ℝ, ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → FO_Good D nb δA εA ε C (.loop w)
      ((FMono.psi (w.countP FO_isRes)).mul ⟨-1, 0, 0, 1, 0⟩) (τ' / 2) D' Cst N := by
  obtain ⟨P, Q, hPQ⟩ := FO_split1 w hl
  have hrQP : (Q ++ P).countP FO_isRes = w.countP FO_isRes := by
    rw [hPQ]
    simp only [List.countP_append, List.countP_cons, FO_isRes]
    simp
    omega
  have hlen : (Q ++ P).length ≤ w.length := by
    rw [hPQ]
    simp only [List.length_append, List.length_cons]
    omega
  have hwQP : ∀ a pr, FLet.det a pr ∈ Q ++ P → pr = false := fun a pr hm =>
    hw a pr (by rw [hPQ]; simp only [List.mem_append, List.mem_cons] at hm ⊢; tauto)
  obtain ⟨c₀, K, CU, hc₀, hK2, hCU, N₁, hfac⟩ := FO_facts D hD δA εA ε hδA hεA hε hε' hε'' C
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.1 (PS_fbl D hD δA (ε / 2) c₀ (2 * K) K hδA
    (by positivity) hc₀ (by linarith) C w.length (w.countP FO_isRes) hr (τ' / 2)
    (by positivity) D' hD')
  refine ⟨(max ((2 * K) ^ w.length) K) ^ (w.countP FO_isRes + 1) * K * CU, max N₁ N₃,
    fun N hN μ hμ A hA k hk hkN hhs e he ι κ => ?_⟩
  obtain ⟨hadm, -, hN1, heta, hη, hMb, hCU', -, hM, hLt, -, hslam, -⟩ :=
    hfac N (le_of_max_le_left hN) μ hμ A hA k hk hkN hhs e he
  have hdet := FO_it_det e ι (2 * K) (by linarith) (fun a => (hM a).trans (by linarith)) hLt
    (Q ++ P) hwQP
  refine ⟨_, hN₃ N (le_of_max_le_right hN) μ hμ e hadm ((Q ++ P).map (FO_it e ι))
    (by rw [FO_nr, hrQP]) (by simpa using hlen) hdet, fun h hh => ?_⟩
  simp only [Set.mem_ofPred_eq, not_lt, FO_v] at hh
  have hval : FFac.val e ι κ h (.loop w) = ntr (((Q ++ P).map (FLet.mat e ι h)).prod * e.Lt) := by
    change ntr (w.map (FLet.mat e ι h)).prod = _
    rw [hPQ]
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    unfold ntr
    congr 1
    rw [show FLet.mat e ι h FLet.lamt = e.Lt from rfl, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc]
  rw [hval]
  refine hh.trans ?_
  rw [FO_evalR_mul _ _ N hN1 _ _ _ _ hMb hη, FO_ev_psi _ _ _ _ _ hη.le, FO_ev_hs1]
  have hb := PS_bnd hη heta hCU hCU' (w.countP FO_isRes)
  have hb0 := PS_b_nonneg hadm (w.countP FO_isRes)
  have hψ := PS_psi_nonneg hη hMb.le (w.countP FO_isRes)
  have hK0 : 0 < K := by linarith
  have hs0 : 0 ≤ hsNorm A := Real.sqrt_nonneg _
  have hsl0 : 0 ≤ hsNorm (lam D N e.A) := Real.sqrt_nonneg _
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ (τ' / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hn : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hx : (0 : ℝ) ≤ (max ((2 * K) ^ w.length) K) ^ (w.countP FO_isRes + 1) := by positivity
  calc (N : ℝ) ^ (τ' / 2) * ((max ((2 * K) ^ w.length) K) ^ (w.countP FO_isRes + 1) *
        ((N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm (lam D N e.A) * PS_b e (w.countP FO_isRes)))
      ≤ (N : ℝ) ^ (τ' / 2) * ((max ((2 * K) ^ w.length) K) ^ (w.countP FO_isRes + 1) *
        ((N : ℝ) ^ (-(1 / 2 : ℝ)) * (K * hsNorm A) *
          (CU * pkgPsi (etaK D N k ε) ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ))
            (w.countP FO_isRes)))) := by
        gcongr
    _ = _ := by ring

/-- A loop with two `Λ̃` or more and no resolvent: `|⟨U Λ̃ V Λ̃⟩| ≤ ‖U‖ ‖V‖ ⟨|Λ̃|²⟩`. -/
private lemma FO_loop_e (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (w : List FLet)
    (hw : ∀ a pr, FLet.det a pr ∈ w → pr = false) (hl : 2 ≤ w.countP (· == FLet.lamt))
    (hr0 : w.countP FO_isRes = 0) (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) :
    ∃ Cst : ℝ, ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → FO_Good D nb δA εA ε C (.loop w)
      ⟨-2, 0, 0, 2, 0⟩ (τ' / 2) D' Cst N := by
  obtain ⟨X, Y, Z, hXYZ⟩ := FO_split2 w hl
  have hr0' := List.countP_eq_zero.1 hr0
  have hr1 : (Z ++ X).countP FO_isRes = 0 ∧ Y.countP FO_isRes = 0 := by
    refine ⟨List.countP_eq_zero.2 fun z hz => hr0' z ?_,
      List.countP_eq_zero.2 fun z hz => hr0' z ?_⟩
    · rw [hXYZ]
      simp only [List.mem_append, List.mem_cons] at hz ⊢
      tauto
    · rw [hXYZ]
      simp only [List.mem_append, List.mem_cons] at hz ⊢
      tauto
  have hw1 : ∀ a pr, FLet.det a pr ∈ Z ++ X → pr = false := fun a pr hm =>
    hw a pr (by rw [hXYZ]; simp only [List.mem_append, List.mem_cons] at hm ⊢; tauto)
  have hw2 : ∀ a pr, FLet.det a pr ∈ Y → pr = false := fun a pr hm =>
    hw a pr (by rw [hXYZ]; simp only [List.mem_append, List.mem_cons] at hm ⊢; tauto)
  obtain ⟨c₀, K, CU, -, hK2, -, N₁, hfac⟩ := FO_facts D hD δA εA ε hδA hεA hε hε' hε'' C
  refine ⟨(2 * K) ^ (Z ++ X).length * (2 * K) ^ Y.length * K ^ 2, N₁,
    fun N hN μ hμ A hA k hk hkN hhs e he ι κ => ?_⟩
  obtain ⟨-, -, hN1, -, -, -, -, -, hM, hLt, hsLt, -, -⟩ := hfac N hN μ hμ A hA k hk hkN hhs e he
  refine ⟨∅, by simp, fun h _ => ?_⟩
  have hval : FFac.val e ι κ h (.loop w) = ntr (((Z ++ X).map (FLet.mat e ι h)).prod * e.Lt *
      (Y.map (FLet.mat e ι h)).prod * e.Lt) := by
    change ntr (w.map (FLet.mat e ι h)).prod = _
    rw [hXYZ]
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons,
      show FLet.mat e ι h FLet.lamt = e.Lt from rfl]
    unfold ntr
    congr 1
    simp only [← Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc]
  rw [hval, FO_ev_hs2]
  refine (FO_tr_cs _ _ _).trans ?_
  have hU := FO_mat_le e ι h (2 * K) (by linarith) (fun a => (hM a).trans (by linarith)) hLt
    (Z ++ X) hw1 hr1.1
  have hV := FO_mat_le e ι h (2 * K) (by linarith) (fun a => (hM a).trans (by linarith)) hLt
    Y hw2 hr1.2
  have hK0 : 0 < K := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNτ : (1 : ℝ) ≤ (N : ℝ) ^ (τ' / 2) :=
    Real.one_le_rpow (by exact_mod_cast hN1) (by positivity)
  have hcard : (Fintype.card (Idx D N) : ℝ)⁻¹ ≤ (N : ℝ)⁻¹ := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    exact inv_anti₀ hN0 (by nlinarith)
  have hL2 : hsNorm e.Lt ^ 2 ≤ (K * hsNorm A) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsLt 2
  have hs0 : 0 ≤ hsNorm A := Real.sqrt_nonneg _
  have hc0 : 0 ≤ (Fintype.card (Idx D N) : ℝ)⁻¹ := by positivity
  have hUV : opNorm ((Z ++ X).map (FLet.mat e ι h)).prod * opNorm (Y.map (FLet.mat e ι h)).prod *
      hsNorm e.Lt ^ 2 ≤ (2 * K) ^ (Z ++ X).length * (2 * K) ^ Y.length * (K * hsNorm A) ^ 2 :=
    mul_le_mul (mul_le_mul hU hV (Bd_opNorm_nonneg _) (by positivity)) hL2 (by positivity)
      (by positivity)
  have hP : 0 ≤ (2 * K) ^ (Z ++ X).length * (2 * K) ^ Y.length * (K * hsNorm A) ^ 2 := by
    positivity
  calc (Fintype.card (Idx D N) : ℝ)⁻¹ * (opNorm ((Z ++ X).map (FLet.mat e ι h)).prod *
        opNorm (Y.map (FLet.mat e ι h)).prod * hsNorm e.Lt ^ 2)
      ≤ (N : ℝ)⁻¹ * ((2 * K) ^ (Z ++ X).length * (2 * K) ^ Y.length * (K * hsNorm A) ^ 2) :=
        mul_le_mul hcard hUV (mul_nonneg (mul_nonneg (Bd_opNorm_nonneg _) (Bd_opNorm_nonneg _))
          (sq_nonneg _)) (by positivity)
    _ = (2 * K) ^ (Z ++ X).length * (2 * K) ^ Y.length * K ^ 2 *
        ((N : ℝ)⁻¹ * hsNorm A ^ 2) * 1 := by ring
    _ ≤ (2 * K) ^ (Z ++ X).length * (2 * K) ^ Y.length * K ^ 2 *
        ((N : ℝ)⁻¹ * hsNorm A ^ 2) * (N : ℝ) ^ (τ' / 2) :=
        mul_le_mul_of_nonneg_left hNτ (by positivity)
    _ = _ := by ring

/-- A loop with two `Λ̃` or more and resolvents: (A.55) [two_loop_estimate], the other `Λ̃` as
bounded deterministic letters. -/
private lemma FO_loop_f (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (w : List FLet)
    (hw : ∀ a pr, FLet.det a pr ∈ w → pr = false) (hl : 2 ≤ w.countP (· == FLet.lamt))
    (hr : 1 ≤ w.countP FO_isRes) (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) (hD' : 0 < D') :
    ∃ Cst : ℝ, ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → FO_Good D nb δA εA ε C (.loop w)
      ((FMono.psi (w.countP FO_isRes)).mul ⟨-2, 0, 0, 2, 0⟩) (τ' / 2) D' Cst N := by
  obtain ⟨X, Y, Z, hXYZ⟩ := FO_split2 w hl
  have hr12 : (Z ++ X).countP FO_isRes + Y.countP FO_isRes = w.countP FO_isRes := by
    rw [hXYZ]
    simp only [List.countP_append, List.countP_cons]
    simp [FO_isRes]
    omega
  have hlen1 : (Z ++ X).length ≤ w.length := by
    rw [hXYZ]
    simp only [List.length_append, List.length_cons]
    omega
  have hlen2 : Y.length ≤ w.length := by
    rw [hXYZ]
    simp only [List.length_append, List.length_cons]
    omega
  have hw1 : ∀ a pr, FLet.det a pr ∈ Z ++ X → pr = false := fun a pr hm =>
    hw a pr (by rw [hXYZ]; simp only [List.mem_append, List.mem_cons] at hm ⊢; tauto)
  have hw2 : ∀ a pr, FLet.det a pr ∈ Y → pr = false := fun a pr hm =>
    hw a pr (by rw [hXYZ]; simp only [List.mem_append, List.mem_cons] at hm ⊢; tauto)
  obtain ⟨c₀, K, CU, hc₀, hK2, hCU, N₁, hfac⟩ := FO_facts D hD δA εA ε hδA hεA hε hε' hε'' C
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.1 (PS_fbt D hD δA (ε / 2) c₀ (2 * K) K hδA
    (by positivity) hc₀ (by linarith) C w.length ((Z ++ X).countP FO_isRes)
    (Y.countP FO_isRes) (by omega) (τ' / 2) (by positivity) D' hD')
  refine ⟨(max ((2 * K) ^ w.length) K) ^ (w.countP FO_isRes + 2) * K ^ 2 * CU, max N₁ N₃,
    fun N hN μ hμ A hA k hk hkN hhs e he ι κ => ?_⟩
  obtain ⟨hadm, -, hN1, heta, hη, hMb, hCU', -, hM, hLt, -, hslam, -⟩ :=
    hfac N (le_of_max_le_left hN) μ hμ A hA k hk hkN hhs e he
  have hd1 := FO_it_det e ι (2 * K) (by linarith) (fun a => (hM a).trans (by linarith)) hLt
    (Z ++ X) hw1
  have hd2 := FO_it_det e ι (2 * K) (by linarith) (fun a => (hM a).trans (by linarith)) hLt Y hw2
  refine ⟨_, hN₃ N (le_of_max_le_right hN) μ hμ e hadm ((Z ++ X).map (FO_it e ι))
    (Y.map (FO_it e ι)) (FO_nr e ι _) (FO_nr e ι _) (by simpa using hlen1) (by simpa using hlen2)
    hd1 hd2, fun h hh => ?_⟩
  simp only [Set.mem_ofPred_eq, not_lt, FO_v, hr12] at hh
  have hval : FFac.val e ι κ h (.loop w) = ntr (((Z ++ X).map (FLet.mat e ι h)).prod * e.Lt *
      (Y.map (FLet.mat e ι h)).prod * e.Lt) := by
    change ntr (w.map (FLet.mat e ι h)).prod = _
    rw [hXYZ]
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons,
      show FLet.mat e ι h FLet.lamt = e.Lt from rfl]
    unfold ntr
    congr 1
    simp only [← Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc]
  rw [hval]
  refine hh.trans ?_
  rw [FO_evalR_mul _ _ N hN1 _ _ _ _ hMb hη, FO_ev_psi _ _ _ _ _ hη.le, FO_ev_hs2]
  have hb := PS_bnd hη heta hCU hCU' (w.countP FO_isRes)
  have hb0 := PS_b_nonneg hadm (w.countP FO_isRes)
  have hψ := PS_psi_nonneg hη hMb.le (w.countP FO_isRes)
  have hK0 : 0 < K := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hs0 : 0 ≤ hsNorm A := Real.sqrt_nonneg _
  have hsl0 : 0 ≤ hsNorm (lam D N e.A) := Real.sqrt_nonneg _
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ (τ' / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hx : (0 : ℝ) ≤ (max ((2 * K) ^ w.length) K) ^ (w.countP FO_isRes + 2) := by positivity
  have hl2 : hsNorm (lam D N e.A) ^ 2 / N ≤ (K * hsNorm A) ^ 2 / N :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hsl0 hslam 2) hN0.le
  calc (N : ℝ) ^ (τ' / 2) * ((max ((2 * K) ^ w.length) K) ^ (w.countP FO_isRes + 2) *
        (hsNorm (lam D N e.A) ^ 2 / N * PS_b e (w.countP FO_isRes)))
      ≤ (N : ℝ) ^ (τ' / 2) * ((max ((2 * K) ^ w.length) K) ^ (w.countP FO_isRes + 2) *
        ((K * hsNorm A) ^ 2 / N *
          (CU * pkgPsi (etaK D N k ε) ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ))
            (w.countP FO_isRes)))) := by
        gcongr
    _ = _ := by ring

/-- A loop: the six cases of `FFac.fixV`. -/
private lemma FO_loop_good (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (w : List FLet)
    (hw : ∀ a pr, FLet.det a pr ∈ w → pr = false) (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ)
    (hD' : 0 < D') :
    ∃ Cst : ℝ, ∃ N₁ : ℕ, ∀ N, N₁ ≤ N →
      FO_Good D nb δA εA ε C (.loop w) (FFac.loop w).fixV (τ' / 2) D' Cst N := by
  rw [FO_fixV_loop]
  by_cases hl0 : w.countP (· == FLet.lamt) = 0
  · rw [ite_eq_left hl0]
    by_cases hr0 : w.countP FO_isRes = 0
    · exact FO_loop_a D hD δA εA ε hδA hεA hε hε' hε'' C nb w hw hr0 τ' hτ' D'
    · exact FO_loop_b D hD δA εA ε hδA hεA hε hε' hε'' C nb w hw (by omega) τ' hτ' D' hD'
  · rw [ite_eq_right hl0]
    by_cases hl1 : w.countP (· == FLet.lamt) = 1
    · rw [ite_eq_left hl1]
      by_cases hr0 : w.countP FO_isRes = 0
      · rw [ite_eq_left hr0]
        exact FO_loop_c D hD δA εA ε hδA hεA hε hε' hε'' C nb w hw hl1 hr0 τ' hτ' D'
      · rw [ite_eq_right hr0]
        exact FO_loop_d D hD δA εA ε hδA hεA hε hε' hε'' C nb w hw (by omega) (by omega) τ' hτ'
          D' hD'
    · rw [ite_eq_right hl1]
      by_cases hr0 : w.countP FO_isRes = 0
      · rw [ite_eq_left hr0]
        exact FO_loop_e D hD δA εA ε hδA hεA hε hε' hε'' C nb w hw (by omega) hr0 τ' hτ' D'
      · rw [ite_eq_right hr0]
        exact FO_loop_f D hD δA εA ε hδA hεA hε hε' hε'' C nb w hw (by omega) (by omega) τ' hτ'
          D' hD'

/-- The sizes of the loops and light weights in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: at the slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law]
and 5.4 [lemma_localized_eigenvalue_local_law], outside an event of probability `≤ N^{-D'}`, a
factor that is not an entry is at most `N^{τ'}` times `fixV` ((2.23) [eq:aver_local], (A.53)
[entprodG]–(A.55) [two_loop_estimate], (A.7) [add_one_more_Lambda], (5.5)
[regular_estimate_localized_eigenvector]). -/
theorem pkg_ffix_good (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (f : FFac)
    (hf : fvalid nb [f] ⟨[0, 1, 2, 3], []⟩ = true) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
      ∀ (ι : Fin nb → Fin D) (κ : ℕ → Idx D N),
        μ {h | (N : ℝ) ^ τ' * f.fixV.evalR N
            ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε)
            (hsNorm A) (opNorm A) < ‖f.val e ι κ h‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  refine FO_absorb D nb δA εA ε C f τ' D' hτ' ?_
  cases f with
  | ent x y w => simp [fvalid, FFac.entData] at hf
  | wt a u => exact FO_wt_good D hD δA εA ε hδA hεA hε hε' hε'' C nb a u τ' hτ' D' hD'
  | loop w =>
    have hw : ∀ a pr, FLet.det a pr ∈ w → pr = false := by
      intro a pr hm
      unfold fvalid at hf
      simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] at hf
      have h2 := List.all_eq_true.1 hf.1.1.2 _ hm
      simpa using h2
    exact FO_loop_good D hD δA εA ε hδA hεA hε hε' hε'' C nb w hw τ' hτ' D' hD'

/-- The data `(x, y, parts, ext, det)` of an entry factor. -/
abbrev FEnt := ℕ × ℕ × List ℕ × FMono × Bool

/-- The index of an option of a menu given by its fields (`os.length` if it is not there). -/
def foptIdx (os : List FOpt) (o : FOpt) : ℕ :=
  os.findIdx fun o' => o'.cx == o.cx && o'.cy == o.cy && o'.ord == o.ord && o'.val == o.val

/-- The options of the paper's patterns, as kinds: the entry in sup (isotropic), a Ward row
(`ℓ²` at the row label, summed first) or column, the Hilbert–Schmidt norm, the split at the first
`Λ̃` with the deterministic side in `ℓ²` at the row label and the other side in sup (`isoX`), the
same at the last `Λ̃` and the column label (`isoY`), the plain split at one `Λ̃` with `ℓ²` at the
row (`plainX`) or the column label (`plainY`), the double split with `ℓ²` or sup at each label,
(5.90) with `ℓ²` or sup at each label, and the one-use `ℓ²` norm of a diagonal entry. -/
inductive FKind
  | sup | wardX | wardY | hs | isoX | isoY | plainX | plainY | dbl (mx my : Bool)
  | a590 (mx my : Bool) | diag
  deriving DecidableEq, Repr

/-- The option of a kind for an entry with data `d`, by its fields (`none`: the kind does not
apply to the entry). -/
def fkindOpt (d : FEnt) : FKind → Option FOpt
  | .sup => some ⟨0, 0, 0, [((FMono.psi d.2.2.1.sum).mul ⟨0, 0, 0, 0, d.2.2.1.length - 1⟩).mul
      d.2.2.2.1]⟩
  | .wardX => if d.1 = d.2.1 then none else
      some ⟨1, 0, 1, [((FMono.omega d.2.2.1.sum).mul ⟨0, 0, 0, 0, d.2.2.1.length - 1⟩).mul
        d.2.2.2.1]⟩
  | .wardY => if d.1 = d.2.1 then none else
      some ⟨0, 1, -1, [((FMono.omega d.2.2.1.sum).mul ⟨0, 0, 0, 0, d.2.2.1.length - 1⟩).mul
        d.2.2.2.1]⟩
  | .hs => if d.1 = d.2.1 then none else
      some ⟨1, 1, 0, [(fhalf (d.2.2.1.length - 1) d.2.2.1.sum true).mul d.2.2.2.1]⟩
  | .diag => if d.1 = d.2.1 then
      some ⟨1, 0, 0, [(fhalf (d.2.2.1.length - 1) d.2.2.1.sum true).mul d.2.2.2.1]⟩ else none
  | .isoX =>
      let nl := d.2.2.1.length - 1
      if 1 ≤ nl ∧ d.2.2.1.head? = some 0 then
        let o : FOpt := ⟨1, 0, 0, [((fhalf 1 0 true).mul ((FMono.psi (d.2.2.1.drop 1).sum).mul
          ⟨0, 0, 0, 0, nl - 1⟩)).mul d.2.2.2.1]⟩
        if d.1 = d.2.1 then some ⟨o.cx + o.cy, 0, 0, o.val⟩ else some o
      else none
  | .isoY =>
      let nl := d.2.2.1.length - 1
      if 1 ≤ nl ∧ d.2.2.1.getLast? = some 0 then
        let o : FOpt := ⟨0, 1, 0, [((fhalf 1 0 true).mul ((FMono.psi (d.2.2.1.take nl).sum).mul
          ⟨0, 0, 0, 0, nl - 1⟩)).mul d.2.2.2.1]⟩
        if d.1 = d.2.1 then some ⟨o.cx + o.cy, 0, 0, o.val⟩ else some o
      else none
  | .plainX =>
      if d.2.2.1.length = 2 then
        let o : FOpt := ⟨1, 0, 0, [((fhalf 1 (d.2.2.1.getD 0 0) true).mul
          (fhalf 0 (d.2.2.1.getD 1 0) false)).mul d.2.2.2.1]⟩
        if d.1 = d.2.1 then some ⟨o.cx + o.cy, 0, 0, o.val⟩ else some o
      else none
  | .plainY =>
      if d.2.2.1.length = 2 then
        let o : FOpt := ⟨0, 1, 0, [((fhalf 0 (d.2.2.1.getD 0 0) false).mul
          (fhalf 1 (d.2.2.1.getD 1 0) true)).mul d.2.2.2.1]⟩
        if d.1 = d.2.1 then some ⟨o.cx + o.cy, 0, 0, o.val⟩ else some o
      else none
  | .dbl mx my =>
      if ¬ (d.2.2.1.length = 3 ∧ d.2.2.1.head? = some 0 ∧ d.2.2.1.getLast? = some 0) then none else
      let o : FOpt := ⟨if mx then 1 else 0, if my then 1 else 0, 0,
        [((FMono.psi (d.2.2.1.getD 1 0)).mul ⟨0, 0, 0,
          (if mx then 1 else 0) + (if my then 1 else 0),
          (if mx then 0 else 1) + (if my then 0 else 1)⟩).mul d.2.2.2.1]⟩
      if d.1 = d.2.1 then some ⟨o.cx + o.cy, 0, 0, o.val⟩ else some o
  | .a590 mx my =>
      if ¬ (d.2.2.1.length = 2 ∧ d.2.2.1.sum = 0 ∧ fsameBlk d.1 d.2.1 = true ∧ d.2.2.2.2 = true)
      then none else
      let v : List FMono := if mx && my then [⟨0, 0, 0, 2, 0⟩, ⟨0, 0, 0, 2, 0⟩]
        else if mx || my then [⟨0, 0, 0, 1, 1⟩, ⟨-1, 0, 0, 2, 0⟩]
        else [⟨0, 0, 0, 0, 2⟩, ⟨-2, 0, 0, 2, 0⟩]
      let o : FOpt := ⟨if mx then 1 else 0, if my then 1 else 0, 0, v.map fun m => m.mul d.2.2.2.1⟩
      if d.1 = d.2.1 then some ⟨o.cx + o.cy, 0, 0, o.val⟩ else some o

/-- The menu of an entry. -/
def FEnt.opts (d : FEnt) : List FOpt := fopts d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2

/-- The product of a list of monomials. -/
def FMono.prodL (L : List FMono) : FMono := L.foldl FMono.mul ⟨0, 0, 0, 0, 0⟩

/-- The conditions of `fvalid` other than the capacities: four ranks, one option index per entry,
labels below `4`, block indices below `nb`, no paired letter in a loop, every chosen option in the
menu, and the orders of the chosen options compatible with the ranks. -/
def fvalidL (nb : ℕ) (F : List FFac) (g : FAsg) : Bool :=
  g.rk.length = 4 && g.opt.length = (F.filterMap FFac.entData).length &&
  (F.all fun f => match f with
    | .ent x y w => x < 4 && y < 4 && w.all fun z => match z with | .proj u => u < nb | _ => true
    | .loop w => w.all fun z => match z with
        | .proj u => u < nb
        | .det _ pr => !pr
        | _ => true
    | .wt _ u => u < nb) &&
  ((fchosen F g).all fun c => match c.2 with
    | none => false
    | some o => (o.ord != 1 || g.rk.getD c.1.1 0 < g.rk.getD c.1.2.1 0) &&
        (o.ord != -1 || g.rk.getD c.1.2.1 0 < g.rk.getD c.1.1 0))

/-- A factor with every resolvent flag set to `false`. -/
def FFac.unflag : FFac → FFac
  | .ent x y w => .ent x y (w.map fun z => match z with | .res a _ => .res a false | z => z)
  | .loop w => .loop (w.map fun z => match z with | .res a _ => .res a false | z => z)
  | .wt a x => .wt a x

/-! ### Products of monomials and the fold of the bound -/

private lemma FO_mul_assoc (p q r : FMono) : (p.mul q).mul r = p.mul (q.mul r) := by
  simp only [FMono.mul, FMono.mk.injEq]
  omega

private lemma FO_mul_one (p : FMono) : p.mul ⟨0, 0, 0, 0, 0⟩ = p := by
  cases p
  simp [FMono.mul]

private lemma FO_one_mul (p : FMono) : (⟨0, 0, 0, 0, 0⟩ : FMono).mul p = p := by
  cases p
  simp [FMono.mul]

/-- A left fold of products is its start times the product of the list. -/
private lemma FO_foldl_mul : ∀ (L : List FMono) (a : FMono),
    L.foldl FMono.mul a = a.mul (FMono.prodL L)
  | [], a => by simp [FMono.prodL, FO_mul_one]
  | x :: L, a => by
    change L.foldl FMono.mul (a.mul x) = a.mul (L.foldl FMono.mul ((⟨0, 0, 0, 0, 0⟩ : FMono).mul x))
    rw [FO_foldl_mul L (a.mul x), FO_foldl_mul L, FO_one_mul, FO_mul_assoc]

private lemma FO_prodL_nil : FMono.prodL [] = ⟨0, 0, 0, 0, 0⟩ := rfl

private lemma FO_prodL_cons (x : FMono) (L : List FMono) :
    FMono.prodL (x :: L) = x.mul (FMono.prodL L) := by
  change L.foldl FMono.mul ((⟨0, 0, 0, 0, 0⟩ : FMono).mul x) = _
  rw [FO_foldl_mul, FO_one_mul]

/-- The fold of the sizes of the loops and light weights. -/
private lemma FO_fix (F : List FFac) (a : FMono) :
    F.foldl (fun m f => m.mul f.fixV) a = a.mul (FMono.prodL (F.map FFac.fixV)) := by
  rw [← FO_foldl_mul, List.foldl_map]

/-- One step of the fold of `fboundM`. -/
private def FO_step (L : List FMono) (c : FEnt × Option FOpt) : List FMono :=
  match c.2 with
  | some o => L.flatMap fun p => o.val.map fun q => p.mul q
  | none => L

/-- The label monomial of `fboundM`. -/
private def FO_lab (F : List FFac) (g : FAsg) : FMono :=
  ⟨((List.range 4).map fun l => 2 - (fuses F g l : ℤ)).sum, 0, 0, 0, 0⟩

private lemma FO_fboundM (F : List FFac) (g : FAsg) :
    fboundM F g = (fchosen F g).foldl FO_step
      [(FO_lab F g).mul (FMono.prodL (F.map FFac.fixV))] := by
  rw [← FO_fix]
  rfl

private lemma FO_step_some (L : List FMono) (c : FEnt × Option FOpt) (o : FOpt)
    (hc : c.2 = some o) (m : FMono) :
    m ∈ FO_step L c ↔ ∃ p ∈ L, ∃ v ∈ o.val, m = p.mul v := by
  simp only [FO_step, hc, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨p, hp, v, hv, rfl⟩
    exact ⟨p, hp, v, hv, rfl⟩
  · rintro ⟨p, hp, v, hv, rfl⟩
    exact ⟨p, hp, v, hv, rfl⟩

/-- The members of the fold when every option is chosen: one monomial of each option. -/
private lemma FO_fold_mem₂ : ∀ (C : List (FEnt × Option FOpt)) (L : List FMono) (m : FMono),
    (∀ c ∈ C, c.2.isSome = true) →
    (m ∈ C.foldl FO_step L ↔ ∃ p ∈ L, ∃ qs : List FMono,
      List.Forall₂ (fun c q => ∃ o, c.2 = some o ∧ q ∈ o.val) C qs ∧ m = p.mul (FMono.prodL qs))
  | [], L, m, _ => by
    simp only [List.foldl_nil, List.forall₂_nil_left_iff, exists_eq_left, FO_prodL_nil,
      FO_mul_one]
    constructor
    · intro h
      exact ⟨m, h, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp
  | c :: C, L, m, hC => by
    obtain ⟨o, hc⟩ := Option.isSome_iff_exists.1 (hC c List.mem_cons_self)
    simp only [List.foldl_cons]
    rw [FO_fold_mem₂ C (FO_step L c) m fun c' hc' => hC c' (List.mem_cons_of_mem _ hc')]
    simp only [List.forall₂_cons_left_iff]
    constructor
    · rintro ⟨p', hp', qs, hqs, rfl⟩
      obtain ⟨p, hp, v, hv, rfl⟩ := (FO_step_some L c o hc p').1 hp'
      refine ⟨p, hp, v :: qs, ⟨v, qs, ⟨o, hc, hv⟩, hqs, rfl⟩, ?_⟩
      rw [FO_prodL_cons, FO_mul_assoc]
    · rintro ⟨p, hp, _, ⟨v, qs, ⟨o', hc', hv⟩, hqs, rfl⟩, rfl⟩
      rw [hc] at hc'
      cases hc'
      refine ⟨p.mul v, (FO_step_some L c o hc _).2 ⟨p, hp, v, hv, rfl⟩, qs, hqs, ?_⟩
      rw [FO_prodL_cons, FO_mul_assoc]

/-! ### The chosen options as an indexed map -/

private lemma FO_rfm {α β : Type*} : ∀ (E : List α) (φ : ℕ → α → β),
    (List.range E.length).filterMap (fun t => (E[t]?).map (φ t)) = E.mapIdx φ
  | [], φ => by simp
  | d :: E, φ => by
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map,
      List.mapIdx_cons]
    simp only [List.getElem?_cons_zero, Option.map_some, Function.comp_def,
      List.getElem?_cons_succ]
    rw [← FO_rfm E (fun t d => φ (t + 1) d)]

private lemma FO_fchosen (F : List FFac) (g : FAsg) :
    fchosen F g = (F.filterMap FFac.entData).mapIdx fun t d =>
      (d, (FEnt.opts d)[g.opt.getD t 0]?) := by
  unfold fchosen
  dsimp only
  rw [← FO_rfm]
  refine List.filterMap_congr fun t _ => ?_
  split <;> simp_all [FEnt.opts]

private lemma FO_fchosen_single (f : FFac) (d : FEnt) (hd : f.entData = some d) (rk : List ℕ)
    (i : ℕ) : fchosen [f] ⟨rk, [i]⟩ = [(d, (FEnt.opts d)[i]?)] := by
  rw [FO_fchosen]
  simp [hd]

private lemma FO_fchosen_nil (F : List FFac) (hF : F.filterMap FFac.entData = []) (g : FAsg) :
    fchosen F g = [] := by
  rw [FO_fchosen, hF]
  rfl

/-- (W1a) The entry data: an entry has data, a loop or a light weight has none. -/
theorem fentData_ent (x y : ℕ) (w : List FLet) :
    (FFac.ent x y w).entData = some (x, y, FLet.parts w,
      ⟨0, 2 * ((w.countP fun z => match z with | .det _ pr => pr | _ => false : ℕ) : ℤ), 0, 0, 0⟩,
      w.all fun z => match z with | .det _ pr => !pr | _ => true) ∧
    (FFac.loop w).entData = none ∧ ∀ a : Fin 2, (FFac.wt a x).entData = none := by
  exact ⟨rfl, rfl, fun _ => rfl⟩

/-- (W1b) `fchosen` under append: the options of `F₁` are the first `|E(F₁)|` indices. -/
theorem fchosen_append (F₁ F₂ : List FFac) (rk o₁ o₂ : List ℕ)
    (h : o₁.length = (F₁.filterMap FFac.entData).length) :
    fchosen (F₁ ++ F₂) ⟨rk, o₁ ++ o₂⟩ = fchosen F₁ ⟨rk, o₁⟩ ++ fchosen F₂ ⟨rk, o₂⟩ := by
  rw [FO_fchosen, FO_fchosen, FO_fchosen, List.filterMap_append, List.mapIdx_append]
  congr 1
  · rw [List.mapIdx_eq_mapIdx_iff]
    intro i hi
    simp only
    rw [List.getD_append _ _ _ _ (h ▸ hi)]
  · congr 1
    funext i d
    simp only
    rw [List.getD_append_right _ _ _ _ (by omega), h, Nat.add_sub_cancel]

/-- (W1c) The uses of a label add up under append. -/
theorem fuses_append (F₁ F₂ : List FFac) (rk o₁ o₂ : List ℕ)
    (h : o₁.length = (F₁.filterMap FFac.entData).length) (l : ℕ) :
    fuses (F₁ ++ F₂) ⟨rk, o₁ ++ o₂⟩ l = fuses F₁ ⟨rk, o₁⟩ l + fuses F₂ ⟨rk, o₂⟩ l := by
  unfold fuses
  rw [fchosen_append F₁ F₂ rk o₁ o₂ h, List.map_append, List.sum_append]

/-- (W1c) The uses of one entry with the option `o` of its menu: `cx` at its row label, `cy` at
its column label if the two differ. -/
theorem fuses_ent (x y : ℕ) (w : List FLet) (rk : List ℕ) (i : ℕ) (o : FOpt)
    (ho : (fopts x y (FLet.parts w)
      ⟨0, 2 * ((w.countP fun z => match z with | .det _ pr => pr | _ => false : ℕ) : ℤ), 0, 0, 0⟩
      (w.all fun z => match z with | .det _ pr => !pr | _ => true))[i]? = some o) (l : ℕ) :
    fuses [.ent x y w] ⟨rk, [i]⟩ l =
      (if x = l then o.cx else 0) + (if y = l ∧ x ≠ l then o.cy else 0) := by
  unfold fuses
  rw [FO_fchosen_single _ _ rfl]
  simp only [FEnt.opts]
  rw [ho]
  simp

/-- (W1c) A loop or a light weight uses no label. -/
theorem fuses_fix (f : FFac) (hf : f.entData = none) (rk : List ℕ) (l : ℕ) :
    fuses [f] ⟨rk, []⟩ l = 0 := by
  unfold fuses
  rw [FO_fchosen_nil [f] (by simp [hf])]
  rfl

/-- (W1d) `fvalid` is its local part `fvalidL` and the capacities. -/
theorem fvalid_eq (nb : ℕ) (F : List FFac) (g : FAsg) :
    fvalid nb F g = (fvalidL nb F g && (List.range 4).all fun l => decide (fuses F g l ≤ 2)) := by
  unfold fvalid fvalidL
  exact Bool.and_right_comm _ _ _

/-- (W1d) The local part of `fvalid` under append. -/
theorem fvalidL_append (nb : ℕ) (F₁ F₂ : List FFac) (rk o₁ o₂ : List ℕ)
    (h : o₁.length = (F₁.filterMap FFac.entData).length) :
    fvalidL nb (F₁ ++ F₂) ⟨rk, o₁ ++ o₂⟩ = (fvalidL nb F₁ ⟨rk, o₁⟩ && fvalidL nb F₂ ⟨rk, o₂⟩) := by
  unfold fvalidL
  rw [fchosen_append F₁ F₂ rk o₁ o₂ h]
  simp only [List.filterMap_append, List.length_append, List.all_append]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩
    exact ⟨⟨⟨⟨h1, h⟩, h3⟩, h5⟩, ⟨⟨h1, by omega⟩, h4⟩, h6⟩
  · rintro ⟨⟨⟨⟨h1, _⟩, h3⟩, h5⟩, ⟨⟨_, h2⟩, h4⟩, h6⟩
    exact ⟨⟨⟨h1, by omega⟩, h3, h4⟩, h5, h6⟩

/-- (W1e) The monomials of the bound by membership: the label monomial times the sizes of the loops
and the light weights times one monomial of each chosen option. -/
theorem fboundM_mem (F : List FFac) (g : FAsg) (hg : ∀ c ∈ fchosen F g, c.2.isSome = true)
    (m : FMono) :
    m ∈ fboundM F g ↔ ∃ qs : List FMono,
      List.Forall₂ (fun c q => ∃ o, c.2 = some o ∧ q ∈ o.val) (fchosen F g) qs ∧
      m = ((⟨((List.range 4).map fun l => 2 - (fuses F g l : ℤ)).sum, 0, 0, 0, 0⟩ : FMono).mul
        (FMono.prodL (F.map FFac.fixV))).mul (FMono.prodL qs) := by
  rw [FO_fboundM, FO_fold_mem₂ _ _ _ hg]
  simp only [List.mem_singleton, exists_eq_left]
  rfl

/-- (W1f) The option sup is the first of every menu. -/
theorem fopts_sup (x y : ℕ) (parts : List ℕ) (ext : FMono) (det : Bool) :
    (fopts x y parts ext det)[0]? =
      some ⟨0, 0, 0, [((FMono.psi parts.sum).mul ⟨0, 0, 0, 0, parts.length - 1⟩).mul ext]⟩ := by
  unfold fopts
  split_ifs
  · rfl
  · rfl

/-- (W1g) An option of a menu given by its fields is found by `foptIdx`. -/
theorem foptIdx_mem (os : List FOpt) (o : FOpt) (h : o ∈ os) : os[foptIdx os o]? = some o := by
  unfold foptIdx
  have hex : ∃ x ∈ os, (x.cx == o.cx && x.cy == o.cy && x.ord == o.ord && x.val == o.val) = true :=
    ⟨o, h, by simp⟩
  have hlt := List.findIdx_lt_length_of_exists hex
  rw [List.getElem?_eq_getElem hlt]
  have hp := List.findIdx_getElem (w := hlt)
  generalize os[List.findIdx _ os] = o' at hp ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
  cases o'
  cases o
  simp_all

/-! ### The menu as a list -/

/-- An option with every monomial multiplied by `ext`. -/
private def FO_ext (ext : FMono) (o : FOpt) : FOpt := { o with val := o.val.map fun m => m.mul ext }

/-- The options of `fopts2` from the split at the `(k+1)`-th `Λ̃`, before `ext`. -/
private def FO_spl (P : List ℕ) (k : ℕ) (left mx my : Bool) : List FOpt :=
  let rL := (P.take (k + 1)).sum
  let rR := (P.drop (k + 1)).sum
  let nL := if left then k + 1 else k
  let nR := P.length - 1 - nL
  let plain : FOpt := ⟨if mx then 1 else 0, if my then 1 else 0, 0,
    [(fhalf nL rL mx).mul (fhalf nR rR my)]⟩
  let isoL : List FOpt := if rL = 0 then
    [⟨if mx then 1 else 0, if my then 1 else 0, if my then -1 else 0,
      [(fhalf nL 0 mx).mul ((if my then FMono.omega rR else FMono.psi rR).mul
        ⟨0, 0, 0, 0, nR⟩)]⟩] else []
  let isoR : List FOpt := if rR = 0 then
    [⟨if mx then 1 else 0, if my then 1 else 0, if mx then 1 else 0,
      [(fhalf nR 0 my).mul ((if mx then FMono.omega rL else FMono.psi rL).mul
        ⟨0, 0, 0, 0, nL⟩)]⟩] else []
  plain :: (isoL ++ isoR)

/-- The options of `fopts2` after the four basic ones, before `ext`. -/
private def FO_rest (x y : ℕ) (P : List ℕ) (det : Bool) : List FOpt :=
  let nl := P.length - 1
  let r := P.sum
  let a590 : List FOpt := if nl = 1 && r = 0 && fsameBlk x y && det then
      [⟨0, 0, 0, [⟨0, 0, 0, 0, 2⟩, ⟨-2, 0, 0, 2, 0⟩]⟩,
       ⟨1, 0, 0, [⟨0, 0, 0, 1, 1⟩, ⟨-1, 0, 0, 2, 0⟩]⟩,
       ⟨0, 1, 0, [⟨0, 0, 0, 1, 1⟩, ⟨-1, 0, 0, 2, 0⟩]⟩,
       ⟨1, 1, 0, [⟨0, 0, 0, 2, 0⟩, ⟨0, 0, 0, 2, 0⟩]⟩] else []
  let dbl : List FOpt := if nl = 2 && P.head? = some 0 && P.getLast? = some 0 then
      [false, true].flatMap fun mx => [false, true].map fun my =>
        ⟨if mx then 1 else 0, if my then 1 else 0, 0,
          [(FMono.psi (P.getD 1 0)).mul
            ⟨0, 0, 0, (if mx then 1 else 0) + (if my then 1 else 0),
              (if mx then 0 else 1) + (if my then 0 else 1)⟩]⟩ else []
  a590 ++ dbl ++ (List.range nl).flatMap fun k => [true, false].flatMap fun left =>
    [false, true].flatMap fun mx => [false, true].flatMap fun my => FO_spl P k left mx my

private lemma FO_fopts2 (x y : ℕ) (P : List ℕ) (ext : FMono) (det : Bool) :
    fopts2 x y P ext det = (([⟨0, 0, 0, [(FMono.psi P.sum).mul ⟨0, 0, 0, 0, P.length - 1⟩]⟩,
      ⟨1, 0, 1, [(FMono.omega P.sum).mul ⟨0, 0, 0, 0, P.length - 1⟩]⟩,
      ⟨0, 1, -1, [(FMono.omega P.sum).mul ⟨0, 0, 0, 0, P.length - 1⟩]⟩,
      ⟨1, 1, 0, [fhalf (P.length - 1) P.sum true]⟩] : List FOpt) ++ FO_rest x y P det).map
        (FO_ext ext) :=
  rfl

private lemma FO_mem_ne {x y : ℕ} (hxy : x ≠ y) (P : List ℕ) (ext : FMono) (det : Bool)
    {o₀ : FOpt} (h : o₀ ∈ (([⟨0, 0, 0, [(FMono.psi P.sum).mul ⟨0, 0, 0, 0, P.length - 1⟩]⟩,
      ⟨1, 0, 1, [(FMono.omega P.sum).mul ⟨0, 0, 0, 0, P.length - 1⟩]⟩,
      ⟨0, 1, -1, [(FMono.omega P.sum).mul ⟨0, 0, 0, 0, P.length - 1⟩]⟩,
      ⟨1, 1, 0, [fhalf (P.length - 1) P.sum true]⟩] : List FOpt) ++ FO_rest x y P det)) :
    FO_ext ext o₀ ∈ fopts x y P ext det := by
  unfold fopts
  rw [ite_eq_right hxy, FO_fopts2]
  exact List.mem_map_of_mem h

private lemma FO_mem_eq (x : ℕ) (P : List ℕ) (ext : FMono) (det : Bool) {o₀ : FOpt}
    (h : o₀ ∈ FO_rest x x P det) (h0 : o₀.ord = 0) :
    (⟨o₀.cx + o₀.cy, 0, 0, (FO_ext ext o₀).val⟩ : FOpt) ∈ fopts x x P ext det := by
  unfold fopts
  rw [ite_eq_left rfl]
  dsimp only
  apply List.mem_append_right
  rw [List.mem_filterMap]
  refine ⟨FO_ext ext o₀, ?_, ?_⟩
  · have hd : ∀ (a b c e : FOpt) (l : List FOpt), List.drop 4 ([a, b, c, e] ++ l) = l :=
      fun _ _ _ _ _ => rfl
    rw [FO_fopts2, ← List.map_drop, hd]
    exact List.mem_map_of_mem h
  · simp [FO_ext, h0]

private lemma FO_mem_spl (x y : ℕ) (P : List ℕ) (det : Bool) {k : ℕ} (hk : k < P.length - 1)
    (left mx my : Bool) {o : FOpt} (h : o ∈ FO_spl P k left mx my) : o ∈ FO_rest x y P det := by
  unfold FO_rest
  dsimp only
  refine List.mem_append_right _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩)
  refine List.mem_flatMap.2 ⟨left, by cases left <;> simp, ?_⟩
  refine List.mem_flatMap.2 ⟨mx, by cases mx <;> simp, ?_⟩
  exact List.mem_flatMap.2 ⟨my, by cases my <;> simp, h⟩

private lemma FO_spl_plain (P : List ℕ) (k : ℕ) (left mx my : Bool) :
    (⟨if mx then 1 else 0, if my then 1 else 0, 0,
      [(fhalf (if left then k + 1 else k) (P.take (k + 1)).sum mx).mul
        (fhalf (P.length - 1 - (if left then k + 1 else k)) (P.drop (k + 1)).sum my)]⟩ : FOpt) ∈
      FO_spl P k left mx my :=
  List.mem_cons_self

private lemma FO_spl_isoL (P : List ℕ) (k : ℕ) (left mx my : Bool) (h : (P.take (k + 1)).sum = 0) :
    (⟨if mx then 1 else 0, if my then 1 else 0, if my then -1 else 0,
      [(fhalf (if left then k + 1 else k) 0 mx).mul
        ((if my then FMono.omega (P.drop (k + 1)).sum else FMono.psi (P.drop (k + 1)).sum).mul
          ⟨0, 0, 0, 0, P.length - 1 - (if left then k + 1 else k)⟩)]⟩ : FOpt) ∈
      FO_spl P k left mx my := by
  unfold FO_spl
  dsimp only
  rw [ite_eq_left h]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self)

private lemma FO_spl_isoR (P : List ℕ) (k : ℕ) (left mx my : Bool) (h : (P.drop (k + 1)).sum = 0) :
    (⟨if mx then 1 else 0, if my then 1 else 0, if mx then 1 else 0,
      [(fhalf (P.length - 1 - (if left then k + 1 else k)) 0 my).mul
        ((if mx then FMono.omega (P.take (k + 1)).sum else FMono.psi (P.take (k + 1)).sum).mul
          ⟨0, 0, 0, 0, if left then k + 1 else k⟩)]⟩ : FOpt) ∈
      FO_spl P k left mx my := by
  unfold FO_spl
  dsimp only
  rw [ite_eq_left h]
  exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)

private lemma FO_dbl_mem (x y : ℕ) (P : List ℕ) (det : Bool)
    (hc : (P.length - 1 = 2 && P.head? = some 0 && P.getLast? = some 0) = true) (mx my : Bool) :
    (⟨if mx then 1 else 0, if my then 1 else 0, 0,
      [(FMono.psi (P.getD 1 0)).mul ⟨0, 0, 0, (if mx then 1 else 0) + (if my then 1 else 0),
        (if mx then 0 else 1) + (if my then 0 else 1)⟩]⟩ : FOpt) ∈ FO_rest x y P det := by
  unfold FO_rest
  dsimp only
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  rw [ite_eq_left hc]
  exact List.mem_flatMap.2 ⟨mx, by cases mx <;> simp,
    List.mem_map.2 ⟨my, by cases my <;> simp, rfl⟩⟩

private lemma FO_a590_mem (x y : ℕ) (P : List ℕ) (det : Bool)
    (hc : (P.length - 1 = 1 && P.sum = 0 && fsameBlk x y && det) = true) (mx my : Bool) :
    (⟨if mx then 1 else 0, if my then 1 else 0, 0,
      (if mx && my then [⟨0, 0, 0, 2, 0⟩, ⟨0, 0, 0, 2, 0⟩]
        else if mx || my then [⟨0, 0, 0, 1, 1⟩, ⟨-1, 0, 0, 2, 0⟩]
        else [⟨0, 0, 0, 0, 2⟩, ⟨-2, 0, 0, 2, 0⟩])⟩ : FOpt) ∈ FO_rest x y P det := by
  unfold FO_rest
  dsimp only
  refine List.mem_append_left _ (List.mem_append_left _ ?_)
  rw [ite_eq_left hc]
  cases mx <;> cases my <;> simp

/-- (W1g) The options of the rules are members of the menu, given by their fields: sup, the Ward
row and column, the Hilbert–Schmidt norm, the splits at the first and the last `Λ̃` with the
deterministic side in `ℓ²`, the plain splits at one `Λ̃`, the double split, (5.90)
[eq:addoneLambda], the one-use norm of a diagonal entry, and the conversions of a diagonal entry. -/
theorem fkind_mem (d : FEnt) (k : FKind) (o : FOpt) (h : fkindOpt d k = some o) : o ∈ d.opts := by
  obtain ⟨x, y, P, ext, det⟩ := d
  change o ∈ fopts x y P ext det
  cases k with
  | sup =>
    simp only [fkindOpt, Option.some.injEq] at h
    subst h
    exact List.mem_of_getElem? (fopts_sup x y P ext det)
  | wardX =>
    simp only [fkindOpt] at h
    split_ifs at h with hxy
    cases h
    exact FO_mem_ne hxy P ext det
      (o₀ := ⟨1, 0, 1, [(FMono.omega P.sum).mul ⟨0, 0, 0, 0, P.length - 1⟩]⟩)
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
  | wardY =>
    simp only [fkindOpt] at h
    split_ifs at h with hxy
    cases h
    exact FO_mem_ne hxy P ext det
      (o₀ := ⟨0, 1, -1, [(FMono.omega P.sum).mul ⟨0, 0, 0, 0, P.length - 1⟩]⟩)
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  | hs =>
    simp only [fkindOpt] at h
    split_ifs at h with hxy
    cases h
    exact FO_mem_ne hxy P ext det (o₀ := ⟨1, 1, 0, [fhalf (P.length - 1) P.sum true]⟩)
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))
  | diag =>
    simp only [fkindOpt] at h
    split_ifs at h with hxy
    cases h
    subst hxy
    unfold fopts
    rw [ite_eq_left rfl]
    exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
  | isoX =>
    unfold fkindOpt at h
    dsimp only at h
    by_cases h1 : 1 ≤ P.length - 1 ∧ P.head? = some 0
    · obtain ⟨hnl, hP0⟩ := h1
      have hrL : (P.take (0 + 1)).sum = 0 := by
        obtain ⟨Q, rfl⟩ := List.head?_eq_some_iff.1 hP0
        simp
      have hm := FO_mem_spl x y P det (k := 0) (by omega) true true false
        (FO_spl_isoL P 0 true true false hrL)
      rw [ite_eq_left ⟨hnl, hP0⟩] at h
      by_cases hxy : x = y
      · rw [ite_eq_left hxy] at h
        cases h
        subst hxy
        exact FO_mem_eq x P ext det hm rfl
      · rw [ite_eq_right hxy] at h
        cases h
        exact FO_mem_ne hxy P ext det (List.mem_append_right _ hm)
    · rw [ite_eq_right h1] at h
      cases h
  | isoY =>
    unfold fkindOpt at h
    dsimp only at h
    by_cases h1 : 1 ≤ P.length - 1 ∧ P.getLast? = some 0
    · obtain ⟨hnl, hP0⟩ := h1
      have e1 : P.length - 1 - 1 + 1 = P.length - 1 := by omega
      have e2 : P.length - 1 - (P.length - 1 - 1) = 1 := by omega
      have hrR : (P.drop (P.length - 1 - 1 + 1)).sum = 0 := by
        obtain ⟨Q, rfl⟩ := List.getLast?_eq_some_iff.1 hP0
        rw [e1]
        simp
      have hm := FO_mem_spl x y P det (k := P.length - 1 - 1) (by omega) false false true
        (FO_spl_isoR P (P.length - 1 - 1) false false true hrR)
      simp only [Bool.false_eq_true, ↓reduceIte, e1, e2] at hm
      rw [ite_eq_left ⟨hnl, hP0⟩] at h
      by_cases hxy : x = y
      · rw [ite_eq_left hxy] at h
        cases h
        subst hxy
        exact FO_mem_eq x P ext det hm rfl
      · rw [ite_eq_right hxy] at h
        cases h
        exact FO_mem_ne hxy P ext det (List.mem_append_right _ hm)
    · rw [ite_eq_right h1] at h
      cases h
  | plainX =>
    unfold fkindOpt at h
    dsimp only at h
    by_cases h1 : P.length = 2
    · rw [ite_eq_left h1] at h
      obtain ⟨p0, p1, rfl⟩ : ∃ p0 p1, P = [p0, p1] := by
        rcases P with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, Q⟩⟩⟩ <;> simp at h1
        exact ⟨p0, p1, rfl⟩
      have hm := FO_mem_spl x y [p0, p1] det (k := 0) (by simp) true true false
        (FO_spl_plain [p0, p1] 0 true true false)
      by_cases hxy : x = y
      · rw [ite_eq_left hxy] at h
        cases h
        subst hxy
        exact FO_mem_eq x _ ext det hm rfl
      · rw [ite_eq_right hxy] at h
        cases h
        exact FO_mem_ne hxy _ ext det (List.mem_append_right _ hm)
    · rw [ite_eq_right h1] at h
      cases h
  | plainY =>
    unfold fkindOpt at h
    dsimp only at h
    by_cases h1 : P.length = 2
    · rw [ite_eq_left h1] at h
      obtain ⟨p0, p1, rfl⟩ : ∃ p0 p1, P = [p0, p1] := by
        rcases P with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, Q⟩⟩⟩ <;> simp at h1
        exact ⟨p0, p1, rfl⟩
      have hm := FO_mem_spl x y [p0, p1] det (k := 0) (by simp) false false true
        (FO_spl_plain [p0, p1] 0 false false true)
      by_cases hxy : x = y
      · rw [ite_eq_left hxy] at h
        cases h
        subst hxy
        exact FO_mem_eq x _ ext det hm rfl
      · rw [ite_eq_right hxy] at h
        cases h
        exact FO_mem_ne hxy _ ext det (List.mem_append_right _ hm)
    · rw [ite_eq_right h1] at h
      cases h
  | dbl mx my =>
    unfold fkindOpt at h
    dsimp only at h
    by_cases h1 : P.length = 3 ∧ P.head? = some 0 ∧ P.getLast? = some 0
    · rw [ite_eq_right (not_not_intro h1)] at h
      obtain ⟨a, rfl⟩ : ∃ a, P = [0, a, 0] := by
        rcases P with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, Q⟩⟩⟩⟩
        · simp at h1
        · simp at h1
        · simp at h1
        · obtain ⟨rfl, rfl⟩ : p0 = 0 ∧ p2 = 0 := by simpa using h1
          exact ⟨p1, rfl⟩
        · simp at h1
      have hm := FO_dbl_mem x y [0, a, 0] det (by simp) mx my
      by_cases hxy : x = y
      · rw [ite_eq_left hxy] at h
        cases h
        subst hxy
        exact FO_mem_eq x _ ext det hm rfl
      · rw [ite_eq_right hxy] at h
        cases h
        exact FO_mem_ne hxy _ ext det (List.mem_append_right _ hm)
    · rw [ite_eq_left h1] at h
      cases h
  | a590 mx my =>
    unfold fkindOpt at h
    dsimp only at h
    by_cases h1 : P.length = 2 ∧ P.sum = 0 ∧ fsameBlk x y = true ∧ det = true
    · rw [ite_eq_right (not_not_intro h1)] at h
      obtain ⟨hl, hs, hb, rfl⟩ := h1
      obtain rfl : P = [0, 0] := by
        rcases P with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, Q⟩⟩⟩
        · simp at hl
        · simp at hl
        · obtain ⟨rfl, rfl⟩ : p0 = 0 ∧ p1 = 0 := by simpa using hs
          rfl
        · simp at hl
      have hm := FO_a590_mem x y [0, 0] true (by simp [hb]) mx my
      by_cases hxy : x = y
      · rw [ite_eq_left hxy] at h
        cases h
        subst hxy
        exact FO_mem_eq x _ ext true hm rfl
      · rw [ite_eq_right hxy] at h
        cases h
        exact FO_mem_ne hxy _ ext true (List.mem_append_right _ hm)
    · rw [ite_eq_left h1] at h
      cases h

/-! ### The resolvent flags -/

/-- A letter with the flag of a resolvent set to `false`. -/
private def FO_uf (z : FLet) : FLet :=
  match z with
  | .res a _ => .res a false
  | z => z

private lemma FO_unflag_ent (x y : ℕ) (w : List FLet) :
    FFac.unflag (.ent x y w) = .ent x y (w.map FO_uf) := rfl

private lemma FO_unflag_loop (w : List FLet) :
    FFac.unflag (.loop w) = .loop (w.map FO_uf) := rfl

private lemma FO_splitOnP_map {α : Type*} (p : α → Bool) (f : α → α) (hp : ∀ z, p (f z) = p z) :
    ∀ l : List α, (l.map f).splitOnP p = (l.splitOnP p).map (List.map f)
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.splitOnP_cons_eq_ite_modifyHead, List.splitOnP_cons_eq_ite_modifyHead,
      hp, FO_splitOnP_map p f hp l]
    split_ifs
    · rfl
    · cases l.splitOnP p <;> rfl

private lemma FO_comp_uf (p : FLet → Bool) (hp : ∀ z, p (FO_uf z) = p z) : p ∘ FO_uf = p :=
  funext hp

private lemma FO_parts_uf (w : List FLet) : FLet.parts (w.map FO_uf) = FLet.parts w := by
  unfold FLet.parts
  rw [FO_splitOnP_map _ _ (fun z => by cases z <;> rfl), List.map_map]
  congr 1
  funext t
  simp only [Function.comp_apply, List.countP_map]
  congr 1
  funext z
  cases z <;> rfl

private lemma FO_comp_unflag (p : FFac → Bool) (hp : ∀ f, p f.unflag = p f) :
    p ∘ FFac.unflag = p :=
  funext hp

private lemma FO_entData_uf (f : FFac) : f.unflag.entData = f.entData := by
  cases f with
  | ent x y w =>
    rw [FO_unflag_ent]
    simp only [FFac.entData, FO_parts_uf, List.countP_map, List.all_map]
    rw [FO_comp_uf, FO_comp_uf] <;> (intro z; cases z <;> rfl)
  | loop w => rfl
  | wt a x => rfl

private lemma FO_fixV_uf (f : FFac) : f.unflag.fixV = f.fixV := by
  cases f with
  | ent x y w => rfl
  | wt a x => rfl
  | loop w =>
    rw [FO_unflag_loop]
    simp only [FFac.fixV, List.length_map, List.countP_map, ← List.map_rotate]
    have h1 : ((fun x => x == FLet.lamt) ∘ FO_uf) = fun x => x == FLet.lamt := by
      funext z
      cases z <;> rfl
    have h2 : ((fun x => match x with
        | FLet.res _ _ => true
        | _ => false) ∘ FO_uf) = fun x => match x with
        | FLet.res _ _ => true
        | _ => false := by
      funext z
      cases z <;> rfl
    erw [h1, h2]
    congr 6
    funext t
    rcases w.rotate t with _ | ⟨z1, _ | ⟨z2, _ | ⟨z3, _ | ⟨z4, _ | ⟨z5, l⟩⟩⟩⟩⟩ <;>
      (try cases z1) <;> (try cases z2) <;> (try cases z3) <;> (try cases z4) <;> rfl

/-- (W1h) `fvalid` and `fboundM` do not see the resolvent flags. -/
theorem fvalid_unflag (nb : ℕ) (F F' : List FFac) (h : F.map FFac.unflag = F'.map FFac.unflag)
    (g : FAsg) : fvalid nb F g = fvalid nb F' g ∧ fboundM F g = fboundM F' g := by
  have key : ∀ G : List FFac, fvalid nb (G.map FFac.unflag) g = fvalid nb G g ∧
      fboundM (G.map FFac.unflag) g = fboundM G g := by
    intro G
    have hE : (G.map FFac.unflag).filterMap FFac.entData = G.filterMap FFac.entData := by
      rw [List.filterMap_map]
      congr 1
      funext f
      exact FO_entData_uf f
    have hC : fchosen (G.map FFac.unflag) g = fchosen G g := by
      rw [FO_fchosen, FO_fchosen, hE]
    have hU : ∀ l, fuses (G.map FFac.unflag) g l = fuses G g l := by
      intro l
      unfold fuses
      rw [hC]
    refine ⟨?_, ?_⟩
    · unfold fvalid
      rw [hE, hC]
      simp only [hU, List.all_map]
      rw [FO_comp_unflag]
      intro f
      cases f with
      | ent x y w =>
        rw [FO_unflag_ent]
        dsimp only
        rw [List.all_map, FO_comp_uf]
        intro z
        cases z <;> rfl
      | loop w =>
        rw [FO_unflag_loop]
        dsimp only
        rw [List.all_map, FO_comp_uf]
        intro z
        cases z <;> rfl
      | wt a x => rfl
    · rw [FO_fboundM, FO_fboundM, hC, List.map_map]
      have : FFac.fixV ∘ FFac.unflag = FFac.fixV := funext FO_fixV_uf
      rw [this]
      simp only [FO_lab, hU]
  obtain ⟨h1, h2⟩ := key F
  obtain ⟨h3, h4⟩ := key F'
  rw [← h1, ← h3, h, ← h2, ← h4, h]
  exact ⟨rfl, rfl⟩

/-- (W1h) The factor lists of the four flags agree up to the flags. -/
theorem ffacs_unflag (R : PkgExpr) (s s' pr : Fin 2 → Bool) :
    (R.ffacs s pr).map FFac.unflag = (R.ffacs s' pr).map FFac.unflag := by
  have hl : ∀ σ : List PkgLetter, (σ.filterMap (PkgLetter.flet s pr)).map FO_uf =
      (σ.filterMap (PkgLetter.flet s' pr)).map FO_uf := by
    intro σ
    rw [List.map_filterMap, List.map_filterMap]
    congr 1
    funext z
    rcases z with ((a | a | x | o) | ⟨u, v⟩) <;> rfl
  unfold PkgExpr.ffacs
  rw [List.map_append, List.map_append, List.map_flatMap, List.map_flatMap]
  congr 1
  congr 1
  funext w
  dsimp only
  split_ifs
  · rw [List.map_filterMap, List.map_filterMap]
    congr 1
    funext t
    generalize (List.filterMap _ (w.rotate (List.findIdx PkgLetter.isEnt w))) = E
    rcases (pkgSegs w)[t]? with _ | σ
    · rfl
    rcases E[t]? with _ | e₀
    · rfl
    rcases E[(t + 1) % E.length]? with _ | e₁
    · rfl
    simp only [Option.map_some, FO_unflag_ent, hl]
  · simp only [List.map_cons, List.map_nil, FO_unflag_loop, hl]

/-- (W1i) The value of a product of monomials is the product of the values. -/
theorem fmono_evalR_mul (m m' : FMono) (N : ℕ) (hN : 1 ≤ N) (M η hs op : ℝ) (hM : 0 < M)
    (hη : 0 < η) : (m.mul m').evalR N M η hs op = m.evalR N M η hs op * m'.evalR N M η hs op := by
  unfold FMono.evalR FMono.mul
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  push_cast
  rw [show ((m.a : ℝ) + m'.a) / 2 = (m.a : ℝ) / 2 + (m'.a : ℝ) / 2 by ring, Real.rpow_add hN0,
    show ((m.i : ℝ) + m'.i) / 2 = (m.i : ℝ) / 2 + (m'.i : ℝ) / 2 by ring, Real.rpow_add hM,
    show -((m.l : ℝ) + m'.l) / 2 = -(m.l : ℝ) / 2 + -(m'.l : ℝ) / 2 by ring, Real.rpow_add hη,
    pow_add, pow_add]
  ring

end RBMTransitionEdge

end
