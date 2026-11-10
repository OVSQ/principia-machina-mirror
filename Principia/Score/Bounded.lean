import Principia.Sponsor
import Principia.ValueBound

/-!
# The reliability score's numbers within the bound on an exact value

The score's functions, the Beta layer's mean and interval and the user score's evidence,
computed as `Principia.Score`, `Principia.Beta` and `Principia.Sponsor` compute them, each
step that forms an exact value from a request's numbers checked first against the bound on
an exact value's size (`Principia.ValueBound`) and refused "exact value too large" when it
could cross it: the sums, products and quotients of the quota, the score's interval, the
update, the cuts, the inquiry and the inheritance; and the sums of rational multiples of
powers of 2 that weigh the events (`PowSum`), each coefficient checked as it is formed, a
power `2^n` held to `|n| < 65,536`. An event aged by many half-lives, whose weight
`2^(-age / HALF-LIFE)` has more bits than the bound allows, is so refused, where an
unchecked computation would try to form it.

Each function, when it answers, answers what the plain function does (the theorems
`..._ok` below), so the plain functions' theorems hold of every answer given. The checks
are made in v1's order of computation, after v1's own checks of the arguments, so a request
v1 refused is refused with v1's word.

Not checked here: values formed from counts alone (a rank's percentiles and cut, the peer
activity, a position), which hold a few dozen bits; and the working values of the Beta
layer's bounds, which are rounded to the precision in hand at each step. The Beta layer's
exact inputs, the shapes and the points, are held to a measured size by the Calculator
before they reach it.
-/

namespace Principia.Score.Bounded

open Principia.Canonical
open Principia.Beta
open Principia.ValueBound (Bounded tooLarge maxBits mulFits divFits addFits)

/-! ## Checks -/

/-- Refused for the bound unless `c` holds. -/
def fits (c : Bool) : Bounded Unit := if c then .ok () else .error tooLarge

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

theorem fits_bind {β : Type} {c : Bool} {f : Unit → Bounded β} {r : β}
    (h : (fits c >>= f) = .ok r) : f () = .ok r := by
  obtain ⟨u, -, h⟩ := bind_ok h
  exact h

theorem pure_ok {α : Type} {a r : α} (h : (pure a : Bounded α) = .ok r) : r = a := by
  cases h; rfl

/-- A check followed by a plain value, when it answers, answers that value. -/
theorem fits_pure {α : Type} {c : Bool} {a r : α}
    (h : (fits c >>= fun _ => (pure a : Bounded α)) = .ok r) : r = a :=
  pure_ok (fits_bind h)

/-- A checked left fold, when it answers, is the plain fold. -/
theorem foldlM_ok {α β : Type} (fB : β → α → Bounded β) (f : β → α → β)
    (hf : ∀ b a r, fB b a = .ok r → r = f b a) :
    ∀ (l : List α) (b r : β), l.foldlM fB b = .ok r → r = l.foldl f b
  | [], b, r, h => by simp only [List.foldlM_nil] at h; cases h; rfl
  | a :: l, b, r, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨b', hb', h⟩ := bind_ok h
    rw [List.foldl_cons, ← hf b a b' hb']
    exact foldlM_ok fB f hf l b' r h

/-- A checked map, when it answers, is the plain map. -/
theorem mapM_ok {α β : Type} (fB : α → Bounded β) (f : α → β)
    (hf : ∀ a r, fB a = .ok r → r = f a) :
    ∀ (l : List α) (r : List β), l.mapM fB = .ok r → r = l.map f
  | [], r, h => by simp only [List.mapM_nil] at h; cases h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    cases h
    rw [List.map_cons, hf a b hb, mapM_ok fB f hf l bs hbs]

/-- One step of a checked fold that may stop: nothing more once it has stopped. -/
def optStep {α β : Type} (fB : β → α → Bounded (Option β)) (o : Option β) (a : α) :
    Bounded (Option β) :=
  match o with
  | none => pure none
  | some b => fB b a

/-- A checked fold that may stop (`none`), when it answers, is the plain fold in `Option`. -/
theorem foldlM_option_ok {α β : Type} (fB : β → α → Bounded (Option β)) (f : β → α → Option β)
    (hf : ∀ b a r, fB b a = .ok r → r = f b a) :
    ∀ (l : List α) (o r : Option β), l.foldlM (optStep fB) o = .ok r →
      r = o.bind fun b => l.foldlM f b
  | [], o, r, h => by
    simp only [List.foldlM_nil] at h; cases h
    cases o <;> rfl
  | a :: l, o, r, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨o', ho', h⟩ := bind_ok h
    have ih := foldlM_option_ok fB f hf l o' r h
    cases o with
    | none =>
      cases ho'
      rw [ih]; rfl
    | some b =>
      rw [hf b a o' ho'] at ih
      rw [ih]
      simp only [Option.bind_some, List.foldlM_cons]
      rfl

/-! ## Sums of rational multiples of powers of 2 -/

namespace PowSum

open Principia.Score.PowSum (split)

/-- `2^n` within the bound: `|n| + 1` bits above or below the fraction line. -/
def powFits (n : Int) : Bool := n.natAbs < maxBits

/-- `split e` within the bound: `e - ⌊e⌋` and `2^⌊e⌋`. -/
def splitFits (e : Rat) : Bool := addFits e (e.floor : Rat) && powFits e.floor

/-- `PowSum.insertTerm`, the sum of two coefficients of one power checked first. -/
def insertTerm (f c : Rat) : List (Rat × Rat) → Bounded (List (Rat × Rat))
  | [] => .ok (if c = 0 then [] else [(f, c)])
  | (g, d) :: rest =>
    if f < g then .ok (if c = 0 then (g, d) :: rest else (f, c) :: (g, d) :: rest)
    else if f = g then do
      fits (addFits c d)
      .ok (if c + d = 0 then rest else (g, c + d) :: rest)
    else do
      let r ← insertTerm f c rest
      .ok ((g, d) :: r)

theorem insertTerm_ok (f c : Rat) :
    ∀ (l r : List (Rat × Rat)), insertTerm f c l = .ok r → r = Score.PowSum.insertTerm f c l
  | [], r, h => by
    unfold insertTerm at h; cases h; rfl
  | (g, d) :: rest, r, h => by
    unfold insertTerm at h
    unfold Score.PowSum.insertTerm
    by_cases h1 : f < g
    · rw [ite_eq_left h1] at h ⊢; cases h; rfl
    · rw [ite_eq_right h1] at h ⊢
      by_cases h2 : f = g
      · rw [ite_eq_left h2] at h ⊢
        have h := fits_bind h
        cases h; rfl
      · rw [ite_eq_right h2] at h ⊢
        obtain ⟨r', hr', h⟩ := bind_ok h
        cases h
        rw [insertTerm_ok f c rest r' hr']

/-- The sum, each coefficient's sum checked. -/
def add (x y : Score.PowSum) : Bounded Score.PowSum := do
  let ts ← y.terms.foldlM (fun acc t => insertTerm t.1 t.2 acc) x.terms
  pure ⟨ts⟩

theorem add_ok {x y r : Score.PowSum} (h : add x y = .ok r) : r = Score.PowSum.add x y := by
  unfold add at h
  obtain ⟨ts, hts, h⟩ := bind_ok h
  cases h
  unfold Score.PowSum.add
  rw [foldlM_ok (fun acc t => insertTerm t.1 t.2 acc)
    (fun acc t => Score.PowSum.insertTerm t.1 t.2 acc)
    (fun b a r h => insertTerm_ok a.1 a.2 b r h) y.terms x.terms ts hts]

/-- A rational multiple, each product checked. -/
def scale (q : Rat) (x : Score.PowSum) : Bounded Score.PowSum := do
  fits (q == 0 || x.terms.all fun t => mulFits q t.2)
  pure (Score.PowSum.scale q x)

theorem scale_ok {q : Rat} {x r : Score.PowSum} (h : scale q x = .ok r) :
    r = Score.PowSum.scale q x := by
  unfold scale at h
  exact fits_pure h

/-- The difference. -/
def sub (x y : Score.PowSum) : Bounded Score.PowSum := do add x (← scale (-1) y)

theorem sub_ok {x y r : Score.PowSum} (h : sub x y = .ok r) : r = Score.PowSum.sub x y := by
  unfold sub at h
  obtain ⟨y', hy', h⟩ := bind_ok h
  rw [add_ok h, scale_ok hy']
  rfl

/-- `2^e`, its whole part checked. -/
def pow2 (e : Rat) : Bounded Score.PowSum := do
  fits (splitFits e)
  pure (Score.PowSum.pow2 e)

theorem pow2_ok {e : Rat} {r : Score.PowSum} (h : pow2 e = .ok r) : r = Score.PowSum.pow2 e := by
  unfold pow2 at h
  exact fits_pure h

/-- One term of `mulPow2`, checked: `c · 2^(f + e)`, added to the sum so far. -/
def mulPow2Step (e : Rat) (acc : Score.PowSum) (t : Rat × Rat) : Bounded Score.PowSum := do
  fits (addFits t.1 e && splitFits (t.1 + e) && mulFits t.2 (split (t.1 + e)).2)
  add acc ⟨[((split (t.1 + e)).1, t.2 * (split (t.1 + e)).2)]⟩

/-- The product with `2^e`, each value checked. -/
def mulPow2 (e : Rat) (x : Score.PowSum) : Bounded Score.PowSum :=
  x.terms.foldlM (mulPow2Step e) Score.PowSum.zero

theorem mulPow2_ok {e : Rat} {x r : Score.PowSum} (h : mulPow2 e x = .ok r) :
    r = Score.PowSum.mulPow2 e x := by
  unfold mulPow2 at h
  unfold Score.PowSum.mulPow2
  rw [foldlM_ok (mulPow2Step e)
    (fun acc t => let (g, k) := split (t.1 + e); Score.PowSum.add acc ⟨[(g, t.2 * k)]⟩)
    (fun b a r h => by
      unfold mulPow2Step at h
      rw [add_ok (fits_bind h)])
    x.terms Score.PowSum.zero r h]

/-- The quotient `u / v` can be formed: its rational, or the multiple of `v` it is
compared with. -/
def ratioFits (u v : Score.PowSum) : Bool :=
  match u.isRat?, v.isRat? with
  | some a, some b => divFits a b
  | _, _ =>
    match u.terms, v.terms with
    | (f, c) :: _, (g, d) :: _ =>
      divFits c d && (f != g || v.terms.all fun t => mulFits (c / d) t.2)
    | _, _ => true

/-- `PowSum.ratio`, its exact values checked first. -/
def ratio (u v : Score.PowSum) : Bounded Quantity := do
  fits (ratioFits u v)
  pure (Score.PowSum.ratio u v)

theorem ratio_ok {u v : Score.PowSum} {r : Quantity} (h : ratio u v = .ok r) :
    r = Score.PowSum.ratio u v := by
  unfold ratio at h
  exact fits_pure h

/-- `PowSum.clip01`, the difference with 1 it compares checked first. -/
def clip01 (x : Score.PowSum) : Bounded (Option Score.PowSum) := do
  let _ ← sub x (Score.PowSum.ofRat 1)
  pure x.clip01

theorem clip01_ok {x : Score.PowSum} {r : Option Score.PowSum} (h : clip01 x = .ok r) :
    r = x.clip01 := by
  unfold clip01 at h
  obtain ⟨_, -, h⟩ := bind_ok h
  exact pure_ok h

end PowSum

/-! ## diversity_quota -/

/-- `Score.quotaOf`, each value checked. -/
def quotaOf (window : List (Option String × Rat)) (counterpart : String) (g cMax : Rat) :
    Bounded Quota := do
  let w ← window.foldlM (fun s e => ValueBound.add s e.2) 0
  let wc ← window.foldlM (fun s e => if e.1 == some counterpart then ValueBound.add s e.2 else pure s) 0
  let wg ← ValueBound.add w g
  let c ← ValueBound.mul cMax wg
  let d ← ValueBound.sub c wc
  let r ← ValueBound.div d g
  let adm ← ValueBound.mul g (clip r 0 1)
  pure ⟨clip r 0 1, w, wc, adm⟩

theorem quotaOf_ok {window : List (Option String × Rat)} {cp : String} {g cMax : Rat} {r : Quota}
    (h : quotaOf window cp g cMax = .ok r) : r = Score.quotaOf window cp g cMax := by
  unfold quotaOf at h
  obtain ⟨w, hw, h⟩ := bind_ok h
  obtain ⟨wc, hwc, h⟩ := bind_ok h
  obtain ⟨wg, hwg, h⟩ := bind_ok h
  obtain ⟨c, hc, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨q, hq, h⟩ := bind_ok h
  obtain ⟨adm, hadm, h⟩ := bind_ok h
  cases h
  have hw' := foldlM_ok (fun s e => ValueBound.add s e.2) (fun s e => s + e.2)
    (fun _ _ _ h => ValueBound.add_ok h) window 0 w hw
  have hwc' := foldlM_ok
    (fun s e => if e.1 == some cp then ValueBound.add s e.2 else pure s)
    (fun s e => if e.1 == some cp then s + e.2 else s)
    (fun b a r h => by
      try dsimp only at h ⊢
      split at h
      · rw [ite_eq_left (by assumption)]; exact ValueBound.add_ok h
      · rw [ite_eq_right (by assumption)]; exact pure_ok h)
    window 0 wc hwc
  rw [ValueBound.mul_ok hadm, ValueBound.div_ok hq, ValueBound.sub_ok hd, ValueBound.mul_ok hc,
    ValueBound.add_ok hwg, hw', hwc']
  rfl

/-- v1 `diversity_quota`, within the bound. -/
def diversityQuota (window counterpart g cMax : Canonical.Value) : Except String Quota := do
  let (entries, cp, gf, cm) ← quotaArgs window counterpart g cMax
  quotaOf entries cp gf cm

theorem diversityQuota_ok {w c g m : Canonical.Value} {r : Quota}
    (h : diversityQuota w c g m = .ok r) : Score.diversityQuota w c g m = .ok r := by
  unfold diversityQuota at h
  unfold Score.diversityQuota
  obtain ⟨⟨e, cp, gf, cm⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  rw [ha]
  exact congrArg Except.ok (quotaOf_ok h).symm

/-! ## evidence and pad_weight -/

/-- `Score.aged`, each value checked. -/
def aged (halfLife w : Rat) (age : Nat) : Bounded Score.PowSum := do
  let e ← ValueBound.div (-(age : Rat)) halfLife
  PowSum.scale w (← PowSum.pow2 e)

theorem aged_ok {halfLife w : Rat} {age : Nat} {r : Score.PowSum}
    (h : aged halfLife w age = .ok r) : r = Score.aged halfLife w age := by
  unfold aged at h
  obtain ⟨e, he, h⟩ := bind_ok h
  obtain ⟨p, hp, h⟩ := bind_ok h
  rw [PowSum.scale_ok h, PowSum.pow2_ok hp, ValueBound.div_ok he]
  rfl

/-- `Score.idleFactor`, each value checked. -/
def idleFactor (days tIdle : Rat) : Bounded Rat :=
  if tIdle < days then do
    let d ← ValueBound.sub days tIdle
    let q ← ValueBound.div d tIdle
    let s ← ValueBound.add 1 q
    ValueBound.div 1 s
  else pure 1

theorem idleFactor_ok {days tIdle r : Rat} (h : idleFactor days tIdle = .ok r) :
    r = Score.idleFactor days tIdle := by
  unfold idleFactor at h
  unfold Score.idleFactor
  split at h
  · rw [ite_eq_left (by assumption)]
    obtain ⟨d, hd, h⟩ := bind_ok h
    obtain ⟨q, hq, h⟩ := bind_ok h
    obtain ⟨s, hs, h⟩ := bind_ok h
    rw [ValueBound.div_ok h, ValueBound.add_ok hs, ValueBound.div_ok hq, ValueBound.sub_ok hd]
  · rw [ite_eq_right (by assumption)]; exact pure_ok h

/-- The sum of the aged weights of one side's events. -/
def sideSum (events : List EvidenceEvent) (s : Side) (halfLife : Rat) : Bounded Score.PowSum :=
  events.foldlM (fun acc e => if e.side == s then do PowSum.add acc (← aged halfLife e.weight e.age)
    else pure acc) Score.PowSum.zero

theorem sideSum_ok {events : List EvidenceEvent} {s : Side} {halfLife : Rat} {r : Score.PowSum}
    (h : sideSum events s halfLife = .ok r) :
    r = events.foldl (fun acc e =>
      if e.side == s then Score.PowSum.add acc (Score.aged halfLife e.weight e.age) else acc)
      Score.PowSum.zero := by
  unfold sideSum at h
  exact foldlM_ok _ _ (fun b a r h => by
    try dsimp only at h ⊢
    split at h
    · rw [ite_eq_left (by assumption)]
      obtain ⟨w, hw, h⟩ := bind_ok h
      rw [PowSum.add_ok h, aged_ok hw]
    · rw [ite_eq_right (by assumption)]; exact pure_ok h) events _ r h

/-- `Score.evidenceOf`, each value checked, with the shapes `a0 + F` and `b0 + A` it hands
the Beta layer. -/
def evidenceOf (events : List EvidenceEvent) (days : Rat) (p : Prior) :
    Bounded (Evidence × Score.PowSum × Score.PowSum) := do
  let fs ← sideSum events .supporting p.halfLife
  let as ← sideSum events .opposing p.halfLife
  let factor ← idleFactor days p.tIdle
  let f ← PowSum.scale factor fs
  let a ← PowSum.scale factor as
  let sa ← PowSum.add (Score.PowSum.ofRat p.a0) f
  let sb ← PowSum.add (Score.PowSum.ofRat p.b0) a
  let ab ← PowSum.add sa sb
  let e ← PowSum.ratio sa ab
  let (lo, hi) := interval sa.toQuantity sb.toQuantity (95 / 100)
  pure (⟨f, a, (events.filter (!·.pad)).length, e, lo, hi, factor⟩, sa, sb)

theorem evidenceOf_ok {events : List EvidenceEvent} {days : Rat} {p : Prior} {r : Evidence}
    {sa sb : Score.PowSum} (h : evidenceOf events days p = .ok (r, sa, sb)) :
    r = Score.evidenceOf events days p := by
  unfold evidenceOf at h
  obtain ⟨fs, hfs, h⟩ := bind_ok h
  obtain ⟨as, has, h⟩ := bind_ok h
  obtain ⟨factor, hfactor, h⟩ := bind_ok h
  obtain ⟨f, hf, h⟩ := bind_ok h
  obtain ⟨a, ha, h⟩ := bind_ok h
  obtain ⟨sa', hsa, h⟩ := bind_ok h
  obtain ⟨sb', hsb, h⟩ := bind_ok h
  obtain ⟨ab, hab, h⟩ := bind_ok h
  obtain ⟨e, he, h⟩ := bind_ok h
  cases h
  rw [PowSum.ratio_ok he, PowSum.add_ok hab, PowSum.add_ok hsa, PowSum.add_ok hsb,
    PowSum.scale_ok hf, PowSum.scale_ok ha, idleFactor_ok hfactor, sideSum_ok hfs,
    sideSum_ok has]
  rfl

/-- v1 `evidence`, within the bound, with the shapes it hands the Beta layer. -/
def evidence (events idle params : Canonical.Value) :
    Except String (Evidence × Score.PowSum × Score.PowSum) := do
  let (evs, days, p) ← evidenceArgs events idle params
  evidenceOf evs days p

theorem evidence_ok {e i p : Canonical.Value} {r : Evidence} {sa sb : Score.PowSum}
    (h : evidence e i p = .ok (r, sa, sb)) : Score.evidence e i p = .ok r := by
  unfold evidence at h
  unfold Score.evidence
  obtain ⟨⟨evs, days, pr⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  rw [ha]
  exact congrArg Except.ok (evidenceOf_ok h).symm

/-- v1 `pad_weight`, within the bound. -/
def padWeight (p age params : Canonical.Value) : Except String Score.PowSum := do
  let (p, a, hl) ← padWeightArgs p age params
  aged hl p a

theorem padWeight_ok {p a ps : Canonical.Value} {r : Score.PowSum}
    (h : padWeight p a ps = .ok r) : Score.padWeight p a ps = .ok r := by
  unfold padWeight at h
  unfold Score.padWeight
  obtain ⟨⟨pn, an, hl⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  rw [ha]
  exact congrArg Except.ok (aged_ok h).symm

/-! ## score_interval, rank, prime_select -/

/-- `Score.scoreIntervalOf`, each value checked. -/
def scoreIntervalOf (s e lo hi : Rat) : Bounded (Rat × Rat) := do
  let d1 ← ValueBound.sub e lo
  let x ← ValueBound.sub s d1
  let d2 ← ValueBound.sub hi e
  let y ← ValueBound.add s d2
  pure (clip x 0 1, clip y 0 1)

theorem scoreIntervalOf_ok {s e lo hi : Rat} {r : Rat × Rat}
    (h : scoreIntervalOf s e lo hi = .ok r) : r = Score.scoreIntervalOf s e lo hi := by
  unfold scoreIntervalOf at h
  obtain ⟨d1, hd1, h⟩ := bind_ok h
  obtain ⟨x, hx, h⟩ := bind_ok h
  obtain ⟨d2, hd2, h⟩ := bind_ok h
  obtain ⟨y, hy, h⟩ := bind_ok h
  cases h
  rw [ValueBound.sub_ok hx, ValueBound.sub_ok hd1, ValueBound.add_ok hy, ValueBound.sub_ok hd2]
  rfl

/-- v1 `score_interval`, within the bound. -/
def scoreInterval (s e lo hi : Canonical.Value) : Except String (Rat × Rat) := do
  let (s, e, l, h) ← intervalArgs s e lo hi
  scoreIntervalOf s e l h

theorem scoreInterval_ok {s e lo hi : Canonical.Value} {r : Rat × Rat}
    (h : scoreInterval s e lo hi = .ok r) : Score.scoreInterval s e lo hi = .ok r := by
  unfold scoreInterval at h
  unfold Score.scoreInterval
  obtain ⟨⟨s', e', l', h'⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  rw [ha]
  exact congrArg Except.ok (scoreIntervalOf_ok h).symm

/-- The values RANK and the Prime's order form from the accounts' numbers: each width
`S_hi - S_lo`, and the tier's `fraction × N`. -/
def accountsFit (accounts : List Account) (fraction : Rat) : Bool :=
  accounts.all (fun a => addFits a.hi a.lo) &&
    mulFits fraction ((accounts.filter (·.active)).length : Rat)

/-- v1 `rank`, within the bound. -/
def rank (accounts params : Canonical.Value) : Except String Rank := do
  let (acc, on, fraction) ← rankArgs accounts params
  fits (accountsFit acc fraction)
  pure (rankOf acc on fraction)

theorem rank_ok {a p : Canonical.Value} {r : Rank} (h : rank a p = .ok r) :
    Score.rank a p = .ok r := by
  unfold rank at h
  unfold Score.rank
  obtain ⟨⟨acc, on, fraction⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  rw [ha]
  exact congrArg Except.ok (fits_pure h).symm

/-- v1 `prime_select`, within the bound. -/
def primeSelect (accounts override params : Canonical.Value) :
    Except String (Option String × PrimeReason) := do
  let (acc, ov, overtake, on, fraction) ← primeArgs accounts override params
  fits (accountsFit acc fraction)
  pure (primeOf acc ov overtake on fraction)

theorem primeSelect_ok {a o p : Canonical.Value} {r : Option String × PrimeReason}
    (h : primeSelect a o p = .ok r) : Score.primeSelect a o p = .ok r := by
  unfold primeSelect at h
  unfold Score.primeSelect
  obtain ⟨⟨acc, ov, overtake, on, fraction⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  rw [ha]
  exact congrArg Except.ok (fits_pure h).symm

/-! ## score_update -/

/-- `Score.updateOf`, each value checked. -/
def updateOf (role : UpdateRole) (s e sp a : Rat) (u : UpdateParams) : Bounded Update :=
  if role == .prime || role == .userPrime then do
    let d ← ValueBound.sub u.ceiling sp
    let k1 ← ValueBound.mul u.kBase d
    let k2 ← ValueBound.mul k1 a
    let k ← ValueBound.mul k2 u.eps
    let st ← ValueBound.mul k d
    let x ← ValueBound.add sp (boundStep st u.deltaMax).1
    pure ⟨clip x 0 u.ceiling, u.ceiling, k, (boundStep st u.deltaMax).1,
      (boundStep st u.deltaMax).2⟩
  else do
    let t0 := if e < u.ceiling then e else u.ceiling
    let t := if !u.overtake && sp < t0 then sp else t0
    let d ← ValueBound.sub sp s
    let q ← ValueBound.div d sp
    let k1 ← ValueBound.mul u.kBase q
    let k2 ← ValueBound.mul k1 a
    let dt ← ValueBound.sub t s
    let st ← ValueBound.mul (clip k2 u.kMin u.kMax) dt
    let x ← ValueBound.add s (boundStep st u.deltaMax).1
    pure ⟨clip x 0 u.ceiling, t, clip k2 u.kMin u.kMax, (boundStep st u.deltaMax).1,
      (boundStep st u.deltaMax).2⟩

theorem updateOf_ok {role : UpdateRole} {s e sp a : Rat} {u : UpdateParams} {r : Update}
    (h : updateOf role s e sp a u = .ok r) : r = Score.updateOf role s e sp a u := by
  unfold updateOf at h
  unfold Score.updateOf
  split at h
  · rw [ite_eq_left (by assumption)]
    obtain ⟨d, hd, h⟩ := bind_ok h
    obtain ⟨k1, hk1, h⟩ := bind_ok h
    obtain ⟨k2, hk2, h⟩ := bind_ok h
    obtain ⟨k, hk, h⟩ := bind_ok h
    obtain ⟨st, hst, h⟩ := bind_ok h
    obtain ⟨x, hx, h⟩ := bind_ok h
    cases h
    rw [ValueBound.add_ok hx, ValueBound.mul_ok hst, ValueBound.mul_ok hk, ValueBound.mul_ok hk2,
      ValueBound.mul_ok hk1, ValueBound.sub_ok hd]
  · rw [ite_eq_right (by assumption)]
    obtain ⟨d, hd, h⟩ := bind_ok h
    obtain ⟨q, hq, h⟩ := bind_ok h
    obtain ⟨k1, hk1, h⟩ := bind_ok h
    obtain ⟨k2, hk2, h⟩ := bind_ok h
    obtain ⟨dt, hdt, h⟩ := bind_ok h
    obtain ⟨st, hst, h⟩ := bind_ok h
    obtain ⟨x, hx, h⟩ := bind_ok h
    cases h
    rw [ValueBound.add_ok hx, ValueBound.mul_ok hst, ValueBound.sub_ok hdt, ValueBound.mul_ok hk2,
      ValueBound.mul_ok hk1, ValueBound.div_ok hq, ValueBound.sub_ok hd]

/-- v1 `score_update`, within the bound. -/
def scoreUpdate (role s e sp a params : Canonical.Value) : Except String Update := do
  let (r, s, e, sp, a, u) ← updateArgs role s e sp a params
  updateOf r s e sp a u

theorem scoreUpdate_ok {role s e sp a p : Canonical.Value} {r : Update}
    (h : scoreUpdate role s e sp a p = .ok r) : Score.scoreUpdate role s e sp a p = .ok r := by
  unfold scoreUpdate at h
  unfold Score.scoreUpdate
  obtain ⟨⟨r', s', e', sp', a', u⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  rw [ha]
  exact congrArg Except.ok (updateOf_ok h).symm

/-! ## violation_cut, inquire, inherit, sponsor_cut -/

/-- `Score.cutOf`, each value checked. -/
def cutOf (s m : Rat) : Bounded Rat := do ValueBound.mul s (← ValueBound.sub 1 m)

theorem cutOf_ok {s m r : Rat} (h : cutOf s m = .ok r) : r = Score.cutOf s m := by
  unfold cutOf at h
  obtain ⟨d, hd, h⟩ := bind_ok h
  rw [ValueBound.mul_ok h, ValueBound.sub_ok hd]
  rfl

/-- v1 `violation_cut`, within the bound. -/
def violationCut (s mClass standing params : Canonical.Value) : Except String Cut := do
  let (s, m, aInc) ← cutArgs s mClass standing params
  pure ⟨← cutOf s m, m, aInc⟩

theorem violationCut_ok {s mc st p : Canonical.Value} {r : Cut}
    (h : violationCut s mc st p = .ok r) : Score.violationCut s mc st p = .ok r := by
  unfold violationCut at h
  unfold Score.violationCut
  obtain ⟨⟨s', m, aInc⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨c, hc, h⟩ := bind_ok h
  cases h
  rw [ha, cutOf_ok hc]
  rfl

/-- `Score.inquiryCost`, its product checked. -/
def inquiryCost (k' : Nat) (wI : Rat) : Bounded (Option Rat) :=
  if 1023 < k' - 1 then pure none else do pure (some (← ValueBound.mul wI ((2 : Rat) ^ (k' - 1))))

theorem inquiryCost_ok {k' : Nat} {wI : Rat} {r : Option Rat} (h : inquiryCost k' wI = .ok r) :
    r = Score.inquiryCost k' wI := by
  unfold inquiryCost at h
  unfold Score.inquiryCost
  split at h
  · rw [ite_eq_left (by assumption)]; exact pure_ok h
  · rw [ite_eq_right (by assumption)]
    obtain ⟨c, hc, h⟩ := bind_ok h
    rw [pure_ok h, ValueBound.mul_ok hc]

/-- `Score.afterCost`, its difference checked. -/
def afterCost (s : Rat) : Option Rat → Bounded Rat
  | none => pure 0
  | some c => do
    let d ← ValueBound.sub s c
    pure (if d < 0 then 0 else d)

theorem afterCost_ok {s r : Rat} {c : Option Rat} (h : afterCost s c = .ok r) :
    r = Score.afterCost s c := by
  cases c with
  | none => exact pure_ok h
  | some c =>
    unfold afterCost at h
    obtain ⟨d, hd, h⟩ := bind_ok h
    rw [pure_ok h, ValueBound.sub_ok hd]
    rfl

/-- `Score.inquireOf`, each value checked. -/
def inquireOf (last : Option Nat) (k block : Nat) (s wI : Rat) (cool : Nat) : Bounded Inquiry := do
  let inside := match last with
    | some l => decide (block - l < cool)
    | none => false
  let k' := if inside then k + 1 else 1
  let c ← inquiryCost k' wI
  let after ← afterCost s c
  pure ⟨c, after, k', inside, block⟩

theorem inquireOf_ok {last : Option Nat} {k block : Nat} {s wI : Rat} {cool : Nat} {r : Inquiry}
    (h : inquireOf last k block s wI cool = .ok r) : r = Score.inquireOf last k block s wI cool := by
  unfold inquireOf at h
  obtain ⟨c, hc, h⟩ := bind_ok h
  obtain ⟨after, hafter, h⟩ := bind_ok h
  cases h
  rw [afterCost_ok hafter, inquiryCost_ok hc]
  rfl

/-- v1 `inquire`, within the bound. -/
def inquire (state block s params : Canonical.Value) : Except String Inquiry := do
  let (last, k, b, s, wI, cool) ← inquireArgs state block s params
  inquireOf last k b s wI cool

theorem inquire_ok {st b s p : Canonical.Value} {r : Inquiry} (h : inquire st b s p = .ok r) :
    Score.inquire st b s p = .ok r := by
  unfold inquire at h
  unfold Score.inquire
  obtain ⟨⟨last, k, bl, s', wI, cool⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  rw [ha]
  exact congrArg Except.ok (inquireOf_ok h).symm

/-- v1 `inherit`, within the bound: the inherited `fraction × F_old` checked. -/
def inherit (fOld facts params : Canonical.Value) : Except String (Rat × Rat × Bool) := do
  let (f, c, sa, si, cause, on, fraction, start) ← inheritArgs fOld facts params
  let (fNew, valid) := inheritOf f c sa si cause on fraction
  fits (!valid || mulFits fraction f)
  pure (fNew, start, valid)

theorem inherit_ok {f fa p : Canonical.Value} {r : Rat × Rat × Bool}
    (h : inherit f fa p = .ok r) : Score.inherit f fa p = .ok r := by
  unfold inherit at h
  unfold Score.inherit
  obtain ⟨⟨f', c, sa, si, cause, on, fraction, start⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  rw [ha]
  exact congrArg Except.ok (fits_pure h).symm

/-- `Score.sponsorCutOf`, each value checked. -/
def sponsorCutOf (s m cut : Rat) : Bounded Rat := do
  let mc ← ValueBound.mul m cut
  ValueBound.mul s (← ValueBound.sub 1 mc)

theorem sponsorCutOf_ok {s m cut r : Rat} (h : sponsorCutOf s m cut = .ok r) :
    r = Score.sponsorCutOf s m cut := by
  unfold sponsorCutOf at h
  obtain ⟨mc, hmc, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  rw [ValueBound.mul_ok h, ValueBound.sub_ok hd, ValueBound.mul_ok hmc]
  rfl

/-- v1 `sponsor_cut`, within the bound. -/
def sponsorCut (s mClass params : Canonical.Value) : Except String Rat := do
  let (s, m, cut) ← sponsorCutArgs s mClass params
  sponsorCutOf s m cut

theorem sponsorCut_ok {s mc p : Canonical.Value} {r : Rat} (h : sponsorCut s mc p = .ok r) :
    Score.sponsorCut s mc p = .ok r := by
  unfold sponsorCut at h
  unfold Score.sponsorCut
  obtain ⟨⟨s', m, cut⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  rw [ha]
  exact congrArg Except.ok (sponsorCutOf_ok h).symm

/-! ## user_aggregate -/

/-- `Score.quotaPow`, each value checked. -/
def quotaPow (window : List (Option String × Score.PowSum)) (counterpart : String) (g cMax : Rat) :
    Bounded (Option Score.PowSum) := do
  let w ← window.foldlM (fun s x => PowSum.add s x.2) Score.PowSum.zero
  let wc ← window.foldlM
    (fun s x => if x.1 == some counterpart then PowSum.add s x.2 else pure s) Score.PowSum.zero
  let wg ← PowSum.add w (Score.PowSum.ofRat g)
  let sc ← PowSum.scale cMax wg
  let d ← PowSum.sub sc wc
  let ig ← ValueBound.div 1 g
  PowSum.clip01 (← PowSum.scale ig d)

theorem quotaPow_ok {window : List (Option String × Score.PowSum)} {cp : String} {g cMax : Rat}
    {r : Option Score.PowSum} (h : quotaPow window cp g cMax = .ok r) :
    r = Score.quotaPow window cp g cMax := by
  unfold quotaPow at h
  obtain ⟨w, hw, h⟩ := bind_ok h
  obtain ⟨wc, hwc, h⟩ := bind_ok h
  obtain ⟨wg, hwg, h⟩ := bind_ok h
  obtain ⟨sc, hsc, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨ig, hig, h⟩ := bind_ok h
  obtain ⟨v, hv, h⟩ := bind_ok h
  have hw' := foldlM_ok (fun (s : Score.PowSum) (x : Option String × Score.PowSum) =>
      PowSum.add s x.2) (fun s x => Score.PowSum.add s x.2)
    (fun _ _ _ h => PowSum.add_ok h) window _ w hw
  have hwc' := foldlM_ok
    (fun (s : Score.PowSum) (x : Option String × Score.PowSum) =>
      if x.1 == some cp then PowSum.add s x.2 else pure s)
    (fun s x => if x.1 == some cp then Score.PowSum.add s x.2 else s)
    (fun b a r h => by
      try dsimp only at h ⊢
      split at h
      · rw [ite_eq_left (by assumption)]; exact PowSum.add_ok h
      · rw [ite_eq_right (by assumption)]; exact pure_ok h) _ _ wc hwc
  rw [PowSum.clip01_ok h, PowSum.scale_ok hv, ValueBound.div_ok hig, PowSum.sub_ok hd,
    PowSum.scale_ok hsc, PowSum.add_ok hwg, hw', hwc']
  rfl

/-- `Score.poolWeight`, each value checked. -/
def poolWeight (admitted : List (Nat × Option String × Score.PowSum)) (e : PooledEvent)
    (sponsor : String) (halfLife cMax : Rat) : Bounded (Option Score.PowSum) :=
  if e.side == .opposing then pure (some (Score.PowSum.ofRat e.base))
  else if e.counterpart.isSome && e.counterpartSponsor == some sponsor then
    pure (some Score.PowSum.zero)
  else match e.counterpart with
    | none => pure (some (Score.PowSum.ofRat e.base))
    | some cp =>
      if e.base = 0 then pure (some (Score.PowSum.ofRat e.base))
      else do
        let window ← (admitted.filter fun x => ((x.1 - e.age : Nat) : Rat) ≤ halfLife).mapM
          fun x => do
            let ex ← ValueBound.div (-((x.1 - e.age : Nat) : Rat)) halfLife
            pure (x.2.1, ← PowSum.mulPow2 ex x.2.2)
        match ← quotaPow window cp e.base cMax with
        | none => pure none
        | some q => pure (some (← PowSum.scale e.base q))

theorem poolWeight_ok {admitted : List (Nat × Option String × Score.PowSum)} {e : PooledEvent}
    {sponsor : String} {halfLife cMax : Rat} {r : Option Score.PowSum}
    (h : poolWeight admitted e sponsor halfLife cMax = .ok r) :
    r = Score.poolWeight admitted e sponsor halfLife cMax := by
  unfold poolWeight at h
  unfold Score.poolWeight
  split at h
  · rw [ite_eq_left (by assumption)]; exact pure_ok h
  · rw [ite_eq_right (by assumption)]
    split at h
    · rw [ite_eq_left (by assumption)]; exact pure_ok h
    · rw [ite_eq_right (by assumption)]
      split at h
      · rename_i hc; rw [hc]; exact pure_ok h
      · rename_i cp hc
        rw [hc]
        dsimp only
        split at h
        · rw [ite_eq_left (by assumption)]; exact pure_ok h
        · rw [ite_eq_right (by assumption)]
          obtain ⟨window, hwin, h⟩ := bind_ok h
          obtain ⟨q, hq, h⟩ := bind_ok h
          have hwin' := mapM_ok _
            (fun x : Nat × Option String × Score.PowSum =>
              (x.2.1, Score.PowSum.mulPow2 (-((x.1 - e.age : Nat) : Rat) / halfLife) x.2.2))
            (fun x r h => by
              obtain ⟨ex, hex, h⟩ := bind_ok h
              obtain ⟨m, hm, h⟩ := bind_ok h
              rw [pure_ok h, PowSum.mulPow2_ok hm, ValueBound.div_ok hex]) _ window hwin
          subst hwin'
          rw [← quotaPow_ok hq]
          cases q with
          | none => exact pure_ok h
          | some q =>
            obtain ⟨s, hs, h⟩ := bind_ok h
            rw [pure_ok h, PowSum.scale_ok hs]
            rfl

/-- `Score.poolStep`, each value checked. -/
def poolStep (sponsor : String) (halfLife cMax : Rat)
    (st : List (Nat × Option String × Score.PowSum) × List UserEvent) (e : PooledEvent) :
    Bounded (Option (List (Nat × Option String × Score.PowSum) × List UserEvent)) := do
  match ← poolWeight st.1 e sponsor halfLife cMax with
  | none => pure none
  | some w =>
    pure (some ((if e.side == .supporting then st.1 ++ [(e.age, e.counterpart, w)] else st.1),
      st.2 ++ [⟨e.side, w, e.age⟩]))

theorem poolStep_ok {sponsor : String} {halfLife cMax : Rat}
    {st : List (Nat × Option String × Score.PowSum) × List UserEvent} {e : PooledEvent}
    {r : Option (List (Nat × Option String × Score.PowSum) × List UserEvent)}
    (h : poolStep sponsor halfLife cMax st e = .ok r) :
    r = Score.poolStep sponsor halfLife cMax st e := by
  unfold poolStep at h
  unfold Score.poolStep
  obtain ⟨w, hw, h⟩ := bind_ok h
  rw [← poolWeight_ok hw]
  cases w with
  | none => exact pure_ok h
  | some w => rw [pure_ok h]; rfl

/-- `Score.poolOf`, each value checked. -/
def poolOf (pool : List PooledEvent) (sponsor : String) (halfLife cMax : Rat) :
    Bounded (Option (List UserEvent)) := do
  let r ← (sortBy landingOrder pool).foldlM (optStep (poolStep sponsor halfLife cMax))
    (some ([], []))
  pure (r.map (·.2))

theorem poolOf_ok {pool : List PooledEvent} {sponsor : String} {halfLife cMax : Rat}
    {r : Option (List UserEvent)} (h : poolOf pool sponsor halfLife cMax = .ok r) :
    r = Score.poolOf pool sponsor halfLife cMax := by
  unfold poolOf at h
  obtain ⟨o, ho, h⟩ := bind_ok h
  rw [pure_ok h]
  unfold Score.poolOf
  rw [foldlM_option_ok (poolStep sponsor halfLife cMax) (Score.poolStep sponsor halfLife cMax)
    (fun _ _ _ h => poolStep_ok h) _ _ o ho]
  simp only [Option.bind_some]
  cases (sortBy landingOrder pool).foldlM (Score.poolStep sponsor halfLife cMax) ([], []) <;> rfl

theorem mapError_ok {ε ε' α : Type} {x : Except ε α} {f : ε → ε'} {a : α}
    (h : x.mapError f = .ok a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok b => cases h; rfl

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-- v1 `user_aggregate`, within the bound. -/
def userAggregate (agents sponsor params : Canonical.Value) : Except Stop Aggregate := do
  let (sp, hl, cm, certified, pool) ← (readAgents agents sponsor params).mapError .refused
  if certified = 0 then return .none
  match ← (poolOf pool sp hl cm).mapError .refused with
  | some evs => return .pooled evs
  | none => throw .unsettled

theorem userAggregate_ok {a s p : Canonical.Value} {r : Aggregate}
    (h : userAggregate a s p = .ok r) : Score.userAggregate a s p = .ok r := by
  unfold userAggregate at h
  unfold Score.userAggregate
  obtain ⟨⟨sp, hl, cm, certified, pool⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  rw [ha, ok_bind]
  dsimp only at h ⊢
  split at h
  · rw [ite_eq_left (by assumption)]; exact h
  · rw [ite_eq_right (by assumption)]
    obtain ⟨o, ho, h⟩ := bind_ok h
    rw [← poolOf_ok (mapError_ok ho)]
    exact h

/-! ## user_score_evidence -/

/-- The user's evidence, its sums of aged weights checked: `Sponsor.posteriorOf`, with the
shapes it hands the Beta layer. -/
def posteriorOf (events : List Sponsor.Weighed) (a0 b0 halfLife : Rat) :
    Bounded (Sponsor.Posterior × Score.PowSum × Score.PowSum) := do
  let side (s : Side) : Bounded Score.PowSum :=
    (events.filter (·.side == some s)).foldlM (fun acc x => do
      PowSum.add acc (← PowSum.mulPow2 (← ValueBound.div (-(x.age : Rat)) halfLife) x.weight))
      Score.PowSum.zero
  let f ← side .supporting
  let a ← side .opposing
  let sa ← PowSum.add (Score.PowSum.ofRat a0) f
  let sb ← PowSum.add (Score.PowSum.ofRat b0) a
  let ab ← PowSum.add sa sb
  let e ← PowSum.ratio sa ab
  let (lo, hi) := interval sa.toQuantity sb.toQuantity (95 / 100)
  pure (⟨f, a, Sponsor.counted events, e, lo, hi⟩, sa, sb)

theorem posteriorOf_ok {events : List Sponsor.Weighed} {a0 b0 halfLife : Rat}
    {r : Sponsor.Posterior} {sa sb : Score.PowSum}
    (h : posteriorOf events a0 b0 halfLife = .ok (r, sa, sb)) :
    r = Sponsor.posteriorOf events a0 b0 halfLife := by
  have side_ok : ∀ (s : Side) (x : Score.PowSum),
      (events.filter (·.side == some s)).foldlM (fun acc x => do
        PowSum.add acc (← PowSum.mulPow2 (← ValueBound.div (-(x.age : Rat)) halfLife) x.weight))
        Score.PowSum.zero = .ok x → x = Sponsor.sideSum events s halfLife := by
    intro s x hx
    unfold Sponsor.sideSum
    exact foldlM_ok _ _ (fun b a r h => by
      obtain ⟨ex, hex, h⟩ := bind_ok h
      obtain ⟨m, hm, h⟩ := bind_ok h
      rw [PowSum.add_ok h, PowSum.mulPow2_ok hm, ValueBound.div_ok hex]
      rfl) _ _ x hx
  unfold posteriorOf at h
  obtain ⟨f, hf, h⟩ := bind_ok h
  obtain ⟨a, ha, h⟩ := bind_ok h
  obtain ⟨sa', hsa, h⟩ := bind_ok h
  obtain ⟨sb', hsb, h⟩ := bind_ok h
  obtain ⟨ab, hab, h⟩ := bind_ok h
  obtain ⟨e, he, h⟩ := bind_ok h
  cases h
  rw [PowSum.ratio_ok he, PowSum.add_ok hab, PowSum.add_ok hsa, PowSum.add_ok hsb,
    side_ok _ f hf, side_ok _ a ha]
  rfl

/-- v1's call of `tpc_sponsor.user_evidence` on the score's input, as
`Sponsor.evidenceOfInput` makes it, its sums checked. -/
def evidenceOfInput (input : SponsorInput) :
    Except String (Sponsor.Posterior × Score.PowSum × Score.PowSum) := do
  let gw ← Sponsor.readWeights input.gC Sponsor.forKinds
  let hw ← Sponsor.readWeights input.hC Sponsor.againstKinds
  let (a0, b0, hl) ← Sponsor.readPriorOf (some input.a0) (some input.b0) (some input.halfLife)
  let agents := input.agentEvents.map fun e =>
    ((Canonical.Value.str "AGENT", Canonical.Value.str (WireWord.toWire e.side),
      (some (some e.weight) : Sponsor.WeightIn)), e.age)
  let conduct := input.conduct.map fun (k, r, age) => ((k, r, (none : Sponsor.WeightIn)), age)
  let ws ← (agents ++ conduct).mapM fun ((k, r, w), age) => do
    let (side, w) ← Sponsor.weigh (Sponsor.weightTable gw hw) k r w
    return (⟨side, w, age⟩ : Sponsor.Weighed)
  posteriorOf ws a0 b0 hl

theorem evidenceOfInput_ok {input : SponsorInput} {r : Sponsor.Posterior} {sa sb : Score.PowSum}
    (h : evidenceOfInput input = .ok (r, sa, sb)) : Sponsor.evidenceOfInput input = .ok r := by
  unfold evidenceOfInput at h
  unfold Sponsor.evidenceOfInput
  obtain ⟨gw, hgw, h⟩ := bind_ok h
  obtain ⟨hw, hhw, h⟩ := bind_ok h
  obtain ⟨⟨a0, b0, hl⟩, hp, h⟩ := bind_ok h
  obtain ⟨ws, hws, h⟩ := bind_ok h
  rw [hgw, hhw, hp]
  simp only [bind, Except.bind] at hws ⊢
  rw [hws]
  exact congrArg Except.ok (posteriorOf_ok h).symm

/-- v1 `user_score_evidence`, within the bound, up to its call of `tpc_sponsor.user_evidence`. -/
def userScoreEvidence (agents conduct sponsor params : Canonical.Value) :
    Except Stop UserEvidence := do
  match ← userAggregate agents sponsor params with
  | .none => return .none
  | .pooled evs => return .sponsor (← (sponsorInputOf evs conduct params).mapError Stop.refused)

theorem userScoreEvidence_ok {a c s p : Canonical.Value} {r : UserEvidence}
    (h : userScoreEvidence a c s p = .ok r) : Score.userScoreEvidence a c s p = .ok r := by
  unfold userScoreEvidence at h
  unfold Score.userScoreEvidence
  obtain ⟨agg, hagg, h⟩ := bind_ok h
  rw [userAggregate_ok hagg]
  exact h

/-- v1 `tpc_score.user_score_evidence`, whole, within the bound, with the shapes the user
evidence hands the Beta layer: NONE (`none`), or the user evidence. -/
def scoreUserEvidence (agents conduct sponsor params : Canonical.Value) :
    Except Stop (Option (Sponsor.Posterior × Score.PowSum × Score.PowSum)) := do
  match ← userScoreEvidence agents conduct sponsor params with
  | .none => return none
  | .sponsor input => some <$> (evidenceOfInput input).mapError Stop.refused

theorem scoreUserEvidence_ok {a c s p : Canonical.Value} {r : Sponsor.Posterior}
    {sa sb : Score.PowSum} (h : scoreUserEvidence a c s p = .ok (some (r, sa, sb))) :
    Sponsor.scoreUserEvidence a c s p = .ok (some r) := by
  unfold scoreUserEvidence at h
  unfold Sponsor.scoreUserEvidence
  obtain ⟨u, hu, h⟩ := bind_ok h
  rw [userScoreEvidence_ok hu, ok_bind]
  cases u with
  | none => cases h
  | sponsor input =>
    dsimp only at h ⊢
    cases hi : evidenceOfInput input with
    | error e => rw [hi] at h; cases h
    | ok x =>
      rw [hi] at h
      obtain ⟨r', sa', sb'⟩ := x
      cases h
      rw [evidenceOfInput_ok hi]
      rfl

/-! ## The Beta layer's mean and interval -/

/-- `Beta.mean`, each value checked. -/
def mean (a b : Rat) : Bounded Rat := do ValueBound.div a (← ValueBound.add a b)

theorem mean_ok {a b r : Rat} (h : mean a b = .ok r) : r = Beta.mean a b := by
  unfold mean at h
  obtain ⟨s, hs, h⟩ := bind_ok h
  rw [ValueBound.div_ok h, ValueBound.add_ok hs]
  rfl

/-- v1 `beta_mean`, within the bound. -/
def betaMean (a b : Canonical.Value) : Except String Rat := do
  let (a, b) ← betaMeanArgs a b
  mean a b

theorem betaMean_ok {a b : Canonical.Value} {r : Rat} (h : betaMean a b = .ok r) :
    Beta.betaMean a b = .ok r := by
  unfold betaMean at h
  unfold Beta.betaMean
  obtain ⟨⟨a', b'⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  rw [ha]
  exact congrArg Except.ok (mean_ok h).symm

/-- `Beta.interval`, its tails `(1 - level) / 2` and `1 - (1 - level) / 2` checked. -/
def interval (a b : Quantity) (level : Rat) : Bounded (Quantity × Quantity) := do
  let alpha ← ValueBound.div (← ValueBound.sub 1 level) 2
  let upper ← ValueBound.sub 1 alpha
  pure (quantile a b alpha, quantile a b upper)

theorem interval_ok {a b : Quantity} {level : Rat} {r : Quantity × Quantity}
    (h : interval a b level = .ok r) : r = Beta.interval a b level := by
  unfold interval at h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨alpha, halpha, h⟩ := bind_ok h
  obtain ⟨upper, hupper, h⟩ := bind_ok h
  rw [pure_ok h, ValueBound.sub_ok hupper, ValueBound.div_ok halpha, ValueBound.sub_ok hd]
  rfl

/-- v1 `beta_interval`, within the bound. -/
def betaInterval (a b level : Canonical.Value) : Except String (Quantity × Quantity) := do
  let (a, b, l) ← betaIntervalArgs a b level
  interval (.exact a) (.exact b) l

end Principia.Score.Bounded
