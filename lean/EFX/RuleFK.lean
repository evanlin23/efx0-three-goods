import EFX.K4C4AB
import EFX.C4min
import EFX.RuleF

/-!
# The counting lemmas of rule F (`k4/rulef.md` §2, §3, §6; ledger K4.RF.K.LEAN)

(module docstring: to be completed)
-/

set_option autoImplicit false

namespace EFX
namespace LB4R

open LB4
open LB (mem_bundle nodup_bundle length_le_one length_le_of_subset)

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Definitions (`k4/rulef.md` §2) -/

/-- **`N^K`**: the needs with the owner's replaced by `N_o^K = {g ∈ N_o : v_o(g) > v_o(B_o ∪ K)}`.
`B_o ∪ K` is `EFX.C4min.ownerBundle goods base o (¬K)` (the goods of `B_o`, and the junk goods of `K`). -/
def needsK (v : A → G → Nat) (goods : List G) (base : G → Option A) (N : A → G → Prop) (o : A) (K : G → Bool) :
    A → G → Prop :=
  fun i g => if i = o then N i g ∧ value v o (C4min.ownerBundle goods base o (fun h => !K h)) < v o g else N i g

/-- **`x ∈ E`**: `x` is a listed agent other than the owner `o`, threatened by `W_o = B_o ∪ J` with its base. -/
def InE (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (o x : A) : Prop :=
  x ∈ agents ∧ x ≠ o ∧ Threatened v x (Wl goods s o) (baseOf goods s.base x)

/-- **The service condition of Lemma K′** for the agent `x` with slot goods `G_x` and kept-out set `D_x`:
`D_x ⊆ J ∖ K`, `G_x ⊆ J ∖ (K ∪ D_x)` without repetitions, `G_x = ∅` unless `x ∉ F^K` and `|G_x| ≤ 2 − |B_x|`, and
not threatened(x, W_o ∖ (D_x ∪ G_x), B_x ∪ G_x). -/
def Serves (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (N : A → G → Prop) (o : A)
    (K : G → Bool) (x : A) (Gx Dx : List G) : Prop :=
  (∀ g ∈ Dx, g ∈ LB4.junk goods s.base ∧ K g = false) ∧
  (∀ g ∈ Gx, g ∈ LB4.junk goods s.base ∧ K g = false ∧ g ∉ Dx) ∧ Gx.Nodup ∧
  (Gx = [] ∨ (¬ Frozen agents goods s.base (needsK v goods s.base N o K) x ∧
    Gx.length + (baseOf goods s.base x).length ≤ 2)) ∧
  ¬ Threatened v x ((Wl goods s o).filter (fun g => g ∉ Dx ∧ g ∉ Gx)) (baseOf goods s.base x ++ Gx)

/-- **A service of the agents of `E` satisfying `T`** (Lemma K′'s K′-service when `T` holds for everyone): every such
agent is served (`Serves`), and the slot goods of distinct such agents are distinct. -/
structure ServiceOn (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (N : A → G → Prop)
    (o : A) (K : G → Bool) (T : A → Prop) (Gs Ds : A → List G) : Prop where
  serves : ∀ x, T x → InE v agents goods s o x → Serves v agents goods s N o K x (Gs x) (Ds x)
  disj : ∀ x y g, T x → T y → InE v agents goods s o x → InE v agents goods s o y → g ∈ Gs x → g ∈ Gs y → x = y

/-- **Lemma K's separated options**: every served agent uses a slot good alone (`G_x = {g}`, `D_x = ∅`: option (s))
or no slot good (`G_x = ∅`: option (r)). -/
def Separated (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (o : A) (T : A → Prop)
    (Gs Ds : A → List G) : Prop :=
  ∀ x, T x → InE v agents goods s o x → Gs x = [] ∨ ∃ g, Gs x = [g] ∧ Ds x = []

/-- A good used by the service for an agent of `E` satisfying `T`. -/
def UsedOn (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (o : A) (T : A → Prop)
    (Gs Ds : A → List G) (g : G) : Prop :=
  ∃ x, T x ∧ InE v agents goods s o x ∧ (g ∈ Gs x ∨ g ∈ Ds x)

open Classical in
/-- **The size of a service** on the agents satisfying `T`: `|⋃ G_x ∪ ⋃ D_x|`, the number of goods used. -/
noncomputable def sizeOn (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (o : A)
    (T : A → Prop) (Gs Ds : A → List G) : Nat :=
  goods.countP (fun g => decide (UsedOn v agents goods s o T Gs Ds g))

/-- **`κ^K`**: the slot places `2 − |B_x|` of the agents `x ≠ o` outside `F^K` (`EFX.LB4.otherSlots` with `N^K`). -/
noncomputable def kappaK (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (N : A → G → Prop)
    (o : A) (K : G → Bool) : Nat :=
  otherSlots agents goods s.base (needsK v goods s.base N o K) o

/-- **Lemma K's deficit of `(o, K)` is at most `d`**: some K-service (separated options) has size at most
`κ^K + d`. -/
def KDefLE (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (N : A → G → Prop) (o : A)
    (K : G → Bool) (d : Int) : Prop :=
  ∃ Gs Ds : A → List G, ServiceOn v agents goods s N o K (fun _ => True) Gs Ds ∧
    Separated v agents goods s o (fun _ => True) Gs Ds ∧
    (sizeOn v agents goods s o (fun _ => True) Gs Ds : Int) - kappaK v agents goods s N o K ≤ d

/-- **Lemma K′'s deficit of `(o, K)` is at most `d`**: some K′-service has size at most `κ^K + d`. -/
def KPDefLE (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (N : A → G → Prop) (o : A)
    (K : G → Bool) (d : Int) : Prop :=
  ∃ Gs Ds : A → List G, ServiceOn v agents goods s N o K (fun _ => True) Gs Ds ∧
    (sizeOn v agents goods s o (fun _ => True) Gs Ds : Int) - kappaK v agents goods s N o K ≤ d

/-! ## Basic facts -/

section basic
variable {v : A → G → Nat} {agents : List A} {goods : List G} {s : LState A G} {N : A → G → Prop} {o : A}
  {K : G → Bool}

/-- The two options of Lemma K are the separated shapes of `Serves`: **(s)** a slot good `g ∈ J ∖ K`, with
`x ∉ F^K`, `|B_x| ≤ 1` and not threatened(x, W_o ∖ {g}, B_x ∪ {g}). -/
theorem serves_slot_iff {x : A} {g : G} :
    Serves v agents goods s N o K x [g] [] ↔
      g ∈ LB4.junk goods s.base ∧ K g = false ∧ ¬ Frozen agents goods s.base (needsK v goods s.base N o K) x ∧
        (baseOf goods s.base x).length ≤ 1 ∧
        ¬ Threatened v x ((Wl goods s o).filter (fun h => h ≠ g)) (baseOf goods s.base x ++ [g]) := by
  have e : (Wl goods s o).filter (fun h => decide (h ∉ ([] : List G) ∧ h ∉ [g])) =
      (Wl goods s o).filter (fun h => decide (h ≠ g)) :=
    List.filter_congr fun h _ => by simp
  unfold Serves
  rw [e]
  constructor
  · rintro ⟨-, hG, -, hF, hT⟩
    obtain ⟨hJ, hK, -⟩ := hG g (by simp)
    rcases hF with hF | ⟨hF, hl⟩
    · cases hF
    · exact ⟨hJ, hK, hF, by simp at hl; omega, hT⟩
  · rintro ⟨hJ, hK, hF, hl, hT⟩
    exact ⟨by simp, fun h hh => by simp at hh; subst hh; exact ⟨hJ, hK, by simp⟩, by simp,
      Or.inr ⟨hF, by simp; omega⟩, hT⟩

/-- **(r)** a kept-out set `D ⊆ J ∖ K` with not threatened(x, W_o ∖ D, B_x). -/
theorem serves_keep_iff {x : A} {D : List G} :
    Serves v agents goods s N o K x [] D ↔
      (∀ g ∈ D, g ∈ LB4.junk goods s.base ∧ K g = false) ∧
        ¬ Threatened v x ((Wl goods s o).filter (fun h => h ∉ D)) (baseOf goods s.base x) := by
  have e : (Wl goods s o).filter (fun h => decide (h ∉ D ∧ h ∉ ([] : List G))) =
      (Wl goods s o).filter (fun h => decide (h ∉ D)) :=
    List.filter_congr fun h _ => by simp
  unfold Serves
  rw [e, List.append_nil]
  constructor
  · rintro ⟨hD, -, -, -, hT⟩; exact ⟨hD, hT⟩
  · rintro ⟨hD, hT⟩; exact ⟨hD, by simp, by simp, Or.inl rfl, hT⟩

omit [DecidableEq G] in
/-- `B_o ∪ K` lists the goods of `B_o` and the junk goods of `K`. -/
theorem mem_keptBundle {K : G → Bool} {base : G → Option A} {g : G} :
    g ∈ C4min.ownerBundle goods base o (fun h => !K h) ↔ g ∈ goods ∧ (base g = some o ∨ (base g = none ∧ K g = true)) := by
  simp [C4min.ownerBundle]

omit [DecidableEq G] in
/-- `N_o^K ⊆ N_o`, and the other agents' needs are unchanged: `NA^K ⊆ NA`. -/
theorem needsK_le {i : A} {g : G} (h : needsK v goods s.base N o K i g) : N i g := by
  unfold needsK at h
  split at h
  · exact h.1
  · exact h

omit [DecidableEq G] in
theorem NA_needsK_le {g : G} (h : NA agents (needsK v goods s.base N o K) g) : NA agents N g := by
  obtain ⟨i, hi, hN⟩ := h
  exact ⟨i, hi, needsK_le hN⟩

omit [DecidableEq G] in
/-- `F^K ⊆ F`. -/
theorem frozen_of_frozenK {x : A} (h : Frozen agents goods s.base (needsK v goods s.base N o K) x) :
    Frozen agents goods s.base N x := by
  obtain ⟨y, hy, hna⟩ := h
  exact ⟨y, hy, NA_needsK_le hna⟩

omit [DecidableEq A] in
/-- Not threatened, from a value bound: if `v_x(L) ≤ v_x(H)`, then `x` holding `H` is not threatened by `L`. -/
theorem not_threatened_of_value_le {x : A} {L H : List G} (h : value v x L ≤ value v x H) :
    ¬ Threatened v x L H := by
  rintro ⟨g, -, hlt⟩
  have := value_sublist v x (List.erase_sublist (l := L) (a := g))
  omega

end basic


/-! ## List counting -/

section lists

omit [DecidableEq A] [DecidableEq G] in
theorem countP_split {α : Type} (p q : α → Bool) :
    ∀ l : List α, l.countP p = l.countP (fun a => p a && q a) + l.countP (fun a => p a && !q a)
  | [] => by simp
  | a :: l => by
    have ih := countP_split p q l
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

omit [DecidableEq A] in
/-- A list without repetitions inside `goods` is counted by `goods.countP (· ∈ L)`. -/
theorem countP_mem_eq_length {goods L : List G} (hgd : goods.Nodup) (hL : L.Nodup) (hsub : ∀ g ∈ L, g ∈ goods) :
    goods.countP (fun g => decide (g ∈ L)) = L.length := by
  rw [List.countP_eq_length_filter]
  apply Nat.le_antisymm
  · exact length_le_of_subset (hgd.filter _) fun g hg => by simpa using (List.mem_filter.mp hg).2
  · exact length_le_of_subset hL fun g hg => List.mem_filter.mpr ⟨hsub g hg, by simpa using hg⟩

omit [DecidableEq A] [DecidableEq G] in
theorem sum_map_add {α : Type} (f g : α → Nat) :
    ∀ l : List α, (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_add f g l]; omega

omit [DecidableEq A] [DecidableEq G] in
theorem countP_le_of_imp {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = true → q a = true) → l.countP p ≤ l.countP q
  | [], _ => by simp
  | a :: l, h => by
    have ih := countP_le_of_imp (l := l) fun b hb => h b (by simp [hb])
    have ha := h a (by simp)
    simp only [List.countP_cons]
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

omit [DecidableEq A] in
/-- At most one good beyond those of `p`: `countP q ≤ countP p + 1` when every good of `q` but `a` is a good of `p`. -/
theorem countP_le_add_one {goods : List G} (hgd : goods.Nodup) {p q : G → Bool} {a : G}
    (h : ∀ g ∈ goods, q g = true → p g = true ∨ g = a) : goods.countP q ≤ goods.countP p + 1 := by
  have h1 : goods.countP q ≤ goods.countP (fun g => p g || decide (g = a)) :=
    countP_le_of_imp fun g hg hq => by
      rcases h g hg hq with h' | h' <;> simp [h']
  have h2 : goods.countP (fun g => p g || decide (g = a)) ≤ goods.countP p + goods.countP (fun g => decide (g = a)) := by
    clear h h1
    induction goods with
    | nil => simp
    | cons b l ih =>
      have := ih (List.nodup_cons.mp hgd).2
      simp only [List.countP_cons]
      cases p b <;> by_cases hb : b = a <;> simp [hb] <;> omega
  have h3 : goods.countP (fun g => decide (g = a)) ≤ 1 := by
    rw [List.countP_eq_length_filter]
    exact length_le_one (hgd.filter _) fun g hg => by simpa using (List.mem_filter.mp hg).2
  omega

end lists

/-! ## Lemma K′, "if": the completion of Lemma K's proof -/

section completion
variable {v : A → G → Nat} {agents : List A} {goods : List G} {s : LState A G} {N : A → G → Prop} {o : A}
  {K : G → Bool} {Gs Ds : A → List G}

open Classical in
/-- The agent of `E` whose slot good `g` is (the first in `agents`). -/
noncomputable def slotOf (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (o : A)
    (Gs : A → List G) (g : G) : Option A :=
  agents.find? (fun x => decide (InE v agents goods s o x ∧ g ∈ Gs x))

open Classical in
/-- The slot places left to `x` once its own slot goods are placed: none for the owner and the agents of `F^K`. -/
noncomputable def room (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (N : A → G → Prop)
    (o : A) (K : G → Bool) (Gs : A → List G) (x : A) : Nat :=
  if x = o ∨ Frozen agents goods s.base (needsK v goods s.base N o K) x then 0
  else 2 - (baseOf goods s.base x).length - (if InE v agents goods s o x then (Gs x).length else 0)

open Classical in
/-- The goods of the kept-out sets that are no slot good (`H ∖ G`), to be placed into unused places. -/
noncomputable def restList (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (o : A)
    (Gs Ds : A → List G) : List G :=
  goods.filter (fun g => decide (UsedOn v agents goods s o (fun _ => True) Gs Ds g ∧
    slotOf v agents goods s o Gs g = none))

open Classical in
/-- **The completion of Lemma K's proof**: base goods to their agents, each slot good to its agent, the other goods
of `C = G ∪ H` into the unused places in the order of `agents` (`EFX.LB.fill`), and the rest of the junk to `o`. -/
noncomputable def svcX (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (N : A → G → Prop)
    (o : A) (K : G → Bool) (Gs Ds : A → List G) (g : G) : A :=
  match s.base g with
  | some i => i
  | none =>
    match slotOf v agents goods s o Gs g with
    | some x => x
    | none =>
      if UsedOn v agents goods s o (fun _ => True) Gs Ds g then
        (LB.fill (room v agents goods s N o K Gs) agents (restList v agents goods s o Gs Ds) g).getD o
      else o

theorem slotOf_some {g : G} {x : A} (h : slotOf v agents goods s o Gs g = some x) :
    x ∈ agents ∧ InE v agents goods s o x ∧ g ∈ Gs x := by
  classical
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [decide_eq_true_eq] at h2
  exact ⟨h1, h2⟩

theorem slotOf_of_mem (hσ : ServiceOn v agents goods s N o K (fun _ => True) Gs Ds) {g : G} {x : A}
    (hx : InE v agents goods s o x) (hg : g ∈ Gs x) : slotOf v agents goods s o Gs g = some x := by
  classical
  cases hf : slotOf v agents goods s o Gs g with
  | none =>
    unfold slotOf at hf
    have := List.find?_eq_none.mp hf x hx.1
    simp only [decide_eq_true_eq, not_and] at this
    exact absurd hg (this hx)
  | some y =>
    obtain ⟨-, hy, hgy⟩ := slotOf_some hf
    rw [hσ.disj y x g trivial trivial hy hx hgy hg]

/-- **Lemma K′, "if"** (`k4/rulef.md` §2, Remark 5, and the proof of Lemma K). Let `(s.base, N)` be a valid
pre-allocation (needs in the Definition's sense, (V1), (V2)), every base good with a listed agent, `o` a listed agent
that is not frozen, every base other than `B_o` of at most two goods. If some K′-service has size at most `κ^K`, then
`svcX` is a sound completion with owner `o` (the owner's needs from its bundle, (OC₄)): an EFX₀ allocation in which
frozen agents hold exactly their bases and only `X_o` may have more than two goods (`EFX.LB4.Valid.sound_ownerNeeds`). -/
theorem lemmaK'_if (hag : agents.Nodup) (hgd : goods.Nodup)
    (hmem : ∀ g ∈ goods, ∀ i, s.base g = some i → i ∈ agents)
    (hNd : ∀ i ∈ agents, Needs v goods s.base N i) (hV : Valid agents goods s.base N)
    (ho : o ∈ agents) (hoF : ¬ Frozen agents goods s.base N o)
    (h2 : ∀ i ∈ agents, i ≠ o → (baseOf goods s.base i).length ≤ 2)
    (hσ : ServiceOn v agents goods s N o K (fun _ => True) Gs Ds)
    (hsize : sizeOn v agents goods s o (fun _ => True) Gs Ds ≤ kappaK v agents goods s N o K) :
    SoundCompletion v agents goods s.base N (some o) (svcX v agents goods s N o K Gs Ds) := by
  classical
  -- notation
  have hS : ∀ x, InE v agents goods s o x → Serves v agents goods s N o K x (Gs x) (Ds x) :=
    fun x hx => hσ.serves x trivial hx
  have hGJ : ∀ x, InE v agents goods s o x → ∀ g ∈ Gs x, g ∈ goods ∧ s.base g = none := fun x hx g hg =>
    mem_junk.mp ((hS x hx).2.1 g hg).1
  have hDJ : ∀ x, InE v agents goods s o x → ∀ g ∈ Ds x, g ∈ goods ∧ s.base g = none := fun x hx g hg =>
    mem_junk.mp ((hS x hx).1 g hg).1
  -- the slot goods of an agent of `F^K` (or of `o`) are none, and fit its places otherwise
  have hGF : ∀ x, InE v agents goods s o x → Frozen agents goods s.base (needsK v goods s.base N o K) x → Gs x = [] :=
    fun x hx hF => ((hS x hx).2.2.2.1).resolve_right fun h => h.1 hF
  have hroom : ∀ x ∈ agents, room v agents goods s N o K Gs x + (if InE v agents goods s o x then (Gs x).length else 0) =
      (if x = o ∨ Frozen agents goods s.base (needsK v goods s.base N o K) x then 0
        else 2 - (baseOf goods s.base x).length) := by
    intro x hxa
    unfold room
    by_cases hc : x = o ∨ Frozen agents goods s.base (needsK v goods s.base N o K) x
    · simp only [hc, ↓reduceIte, Nat.zero_add]
      by_cases hx : InE v agents goods s o x
      · rcases hc with hc | hc
        · exact absurd hc hx.2.1
        · simp [hx, hGF x hx hc]
      · simp [hx]
    · simp only [hc, ↓reduceIte]
      have hxo : x ≠ o := fun e => hc (Or.inl e)
      have := h2 x hxa hxo
      by_cases hx : InE v agents goods s o x
      · simp only [hx, ↓reduceIte]
        rcases (hS x hx).2.2.2.1 with h0 | ⟨-, hl⟩
        · rw [h0]; simp
        · omega
      · simp [hx]
  -- the slot goods are counted by `slotOf`
  have hslotcount : (agents.map (fun x => if InE v agents goods s o x then (Gs x).length else 0)).sum =
      goods.countP (fun g => decide (slotOf v agents goods s o Gs g ≠ none)) := by
    have e1 : agents.map (fun x => if InE v agents goods s o x then (Gs x).length else 0) =
        agents.map (fun x => goods.countP (fun g => decide (slotOf v agents goods s o Gs g = some x))) := by
      apply List.map_congr_left
      intro x _
      by_cases hx : InE v agents goods s o x
      · simp only [hx, ↓reduceIte]
        rw [← countP_mem_eq_length hgd (hS x hx).2.2.1 fun g hg => (hGJ x hx g hg).1]
        apply List.countP_congr
        intro g _
        simp only [decide_eq_true_eq]
        exact ⟨fun h => slotOf_of_mem hσ hx h, fun h => (slotOf_some h).2.2⟩
      · simp only [hx, ↓reduceIte]
        symm
        apply List.countP_eq_zero.mpr
        intro g _ h
        simp only [decide_eq_true_eq] at h
        exact hx (slotOf_some h).2.1
    rw [e1, sum_countP_comm (fun x g => decide (slotOf v agents goods s o Gs g = some x)) agents goods,
      countP_eq_sum]
    congr 1
    apply List.map_congr_left
    intro g _
    rw [countP_base agents hag (b := slotOf v agents goods s o Gs g) fun k hk => (slotOf_some hk).1]
    by_cases h : slotOf v agents goods s o Gs g = none <;> simp [h]
  -- the size splits into the slot goods and the rest
  have hsplit : sizeOn v agents goods s o (fun _ => True) Gs Ds =
      goods.countP (fun g => decide (slotOf v agents goods s o Gs g ≠ none)) +
        (restList v agents goods s o Gs Ds).length := by
    unfold sizeOn restList
    rw [countP_split _ (fun g => decide (slotOf v agents goods s o Gs g ≠ none)), ← List.countP_eq_length_filter]
    congr 1
    · apply List.countP_congr
      intro g _
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp h
        obtain ⟨-, hxE, hgx⟩ := slotOf_some hx
        exact ⟨x, trivial, hxE, Or.inl hgx⟩
    · apply List.countP_congr
      intro g _
      simp
  have hfit : (restList v agents goods s o Gs Ds).length ≤ (agents.map (room v agents goods s N o K Gs)).sum := by
    have hk : kappaK v agents goods s N o K = (agents.map (room v agents goods s N o K Gs)).sum +
        (agents.map (fun x => if InE v agents goods s o x then (Gs x).length else 0)).sum := by
      unfold kappaK otherSlots
      rw [← sum_map_add]
      congr 1
      exact List.map_congr_left fun x hx => (hroom x hx).symm
    omega
  -- the allocation
  obtain ⟨X, hX⟩ : ∃ X, X = svcX v agents goods s N o K Gs Ds := ⟨_, rfl⟩
  rw [← hX]
  have hXb : ∀ g ∈ goods, ∀ i, s.base g = some i → X g = i := fun g _ i hb => by
    simp [hX, svcX, hb]
  have hXs : ∀ g x, s.base g = none → slotOf v agents goods s o Gs g = some x → X g = x := fun g x hb hs => by
    simp [hX, svcX, hb, hs]
  have hXo : ∀ g, s.base g = none → slotOf v agents goods s o Gs g = none →
      ¬ UsedOn v agents goods s o (fun _ => True) Gs Ds g → X g = o := fun g hb hs hU => by
    simp [hX, svcX, hb, hs, hU]
  have hXf : ∀ g ∈ goods, s.base g = none → slotOf v agents goods s o Gs g = none →
      UsedOn v agents goods s o (fun _ => True) Gs Ds g →
      ∃ j, LB.fill (room v agents goods s N o K Gs) agents (restList v agents goods s o Gs Ds) g = some j ∧
        X g = j ∧ j ∈ agents ∧ 0 < room v agents goods s N o K Gs j := by
    intro g hg hb hs hU
    have hgR : g ∈ restList v agents goods s o Gs Ds := List.mem_filter.mpr ⟨hg, by simp [hU, hs]⟩
    obtain ⟨j, hj⟩ := LB.fill_cover hgR hfit
    obtain ⟨hja, -, hjp⟩ := LB.fill_some hj
    exact ⟨j, hj, by simp [hX, svcX, hb, hs, hU, hj], hja, hjp⟩
  have hroom_pos : ∀ j, 0 < room v agents goods s N o K Gs j →
      j ≠ o ∧ ¬ Frozen agents goods s.base (needsK v goods s.base N o K) j := by
    intro j hj
    unfold room at hj
    by_cases hc : j = o ∨ Frozen agents goods s.base (needsK v goods s.base N o K) j
    · simp [hc] at hj
    · exact ⟨fun e => hc (Or.inl e), fun h => hc (Or.inr h)⟩
  -- the goods of `X_o`: in `W`, and none used
  have hXoW : ∀ g ∈ goods, X g = o → (s.base g = none ∨ s.base g = some o) := by
    intro g hg hXg
    cases hb : s.base g with
    | none => exact Or.inl rfl
    | some i => rw [hXb g hg i hb] at hXg; exact Or.inr (by rw [hXg])
  have hXoU : ∀ g ∈ goods, X g = o → ¬ UsedOn v agents goods s o (fun _ => True) Gs Ds g := by
    rintro g hg hXg ⟨x, -, hxE, hgx⟩
    have hb : s.base g = none := by
      rcases hgx with h | h
      · exact (hGJ x hxE g h).2
      · exact (hDJ x hxE g h).2
    cases hs : slotOf v agents goods s o Gs g with
    | some y =>
      rw [hXs g y hb hs] at hXg
      exact (slotOf_some hs).2.1.2.1 hXg
    | none =>
      obtain ⟨j, -, hXj, -, hpos⟩ := hXf g hg hb hs ⟨x, trivial, hxE, hgx⟩
      rw [hXj] at hXg
      exact (hroom_pos j hpos).1 hXg
  -- the owner's needs from its bundle shrink to `N^K`: `X_o ⊇ B_o ∪ K`
  have hON : ∀ i ∈ agents, ∀ g, ownerNeeds v goods X N (some o) i g → needsK v goods s.base N o K i g := by
    intro i hi g hN
    by_cases hio : i = o
    · subst hio
      simp only [ownerNeeds, ↓reduceIte] at hN
      obtain ⟨hg, hXg, hlt⟩ := hN
      simp only [needsK, ↓reduceIte]
      refine ⟨(hNd i hi).of_bundle hXb g hg hXg hlt, Nat.lt_of_le_of_lt ?_ hlt⟩
      apply value_le_of_subset i ((hgd.filter _))
      intro h hh
      obtain ⟨hhg, hhb⟩ := mem_keptBundle.mp hh
      refine mem_bundle.mpr ⟨hhg, ?_⟩
      rcases hhb with hb | ⟨hb, hK⟩
      · exact hXb h hhg i hb
      · -- a kept good is used by nobody
        have hU : ¬ UsedOn v agents goods s i (fun _ => True) Gs Ds h := by
          rintro ⟨x, -, hxE, hgx⟩
          rcases hgx with h' | h'
          · have := ((hS x hxE).2.1 h h').2.1; rw [hK] at this; cases this
          · have := ((hS x hxE).1 h h').2; rw [hK] at this; cases this
        have hs : slotOf v agents goods s i Gs h = none := by
          cases hs : slotOf v agents goods s i Gs h with
          | none => rfl
          | some y =>
            obtain ⟨-, hyE, hhy⟩ := slotOf_some hs
            exact absurd ⟨y, trivial, hyE, Or.inl hhy⟩ hU
        exact hXo h hb hs hU
    · have : ownerNeeds v goods X N (some o) i g = N i g := by
        simp [ownerNeeds, show some o ≠ some i from fun e => hio (Option.some.inj e).symm]
      rw [this] at hN
      simp only [needsK, hio, ↓reduceIte]
      exact hN
  have hFK : ∀ j, Frozen agents goods s.base (ownerNeeds v goods X N (some o)) j →
      Frozen agents goods s.base (needsK v goods s.base N o K) j := fun j ⟨y, hy, i, hi, hN⟩ =>
    ⟨y, hy, i, hi, hON i hi y hN⟩
  -- the junk of an agent other than `o`: its slot goods and goods placed by `fill`
  have hjunk : ∀ j, j ≠ o → ∀ g ∈ junkOf goods s.base X j,
      (InE v agents goods s o j ∧ g ∈ Gs j) ∨
        (slotOf v agents goods s o Gs g = none ∧
          LB.fill (room v agents goods s N o K Gs) agents (restList v agents goods s o Gs Ds) g = some j ∧
          0 < room v agents goods s N o K Gs j) := by
    intro j hjo g hgJ
    obtain ⟨hg, hXg, hb⟩ := mem_junkOf.mp hgJ
    cases hs : slotOf v agents goods s o Gs g with
    | some x =>
      rw [hXs g x hb hs] at hXg; subst hXg
      exact Or.inl ⟨(slotOf_some hs).2.1, (slotOf_some hs).2.2⟩
    | none =>
      by_cases hU : UsedOn v agents goods s o (fun _ => True) Gs Ds g
      · obtain ⟨j', hj', hXj', -, hpos⟩ := hXf g hg hb hs hU
        rw [hXj'] at hXg; subst hXg
        exact Or.inr ⟨rfl, hj', hpos⟩
      · exact absurd ((hXo g hb hs hU).symm.trans hXg) (Ne.symm hjo)
  have hC : Completion agents goods s.base (ownerNeeds v goods X N (some o)) (some o) X := by
    refine ⟨fun g hg => ?_, hXb, fun w hw => ?_, fun j hj hjo hF => ?_, fun j hj hjo _ => ?_⟩
    · cases hb : s.base g with
      | some i => rw [hXb g hg i hb]; exact hmem g hg i hb
      | none =>
        cases hs : slotOf v agents goods s o Gs g with
        | some x => rw [hXs g x hb hs]; exact (slotOf_some hs).1
        | none =>
          by_cases hU : UsedOn v agents goods s o (fun _ => True) Gs Ds g
          · obtain ⟨j, -, hXj, hj, -⟩ := hXf g hg hb hs hU
            rw [hXj]; exact hj
          · rw [hXo g hb hs hU]; exact ho
    · cases hw
      exact ⟨ho, fun hF => hoF (frozen_of_frozenK (hFK o hF))⟩
    · have hjo' : j ≠ o := fun e => hjo (by rw [e])
      have hFj := hFK j hF
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro g hgJ
      rcases hjunk j hjo' g hgJ with ⟨hjE, hgj⟩ | ⟨-, -, hpos⟩
      · rw [hGF j hjE hFj] at hgj; simp at hgj
      · exact (hroom_pos j hpos).2 hFj
    · have hjo' : j ≠ o := fun e => hjo (by rw [e])
      have hB2 := h2 j hj hjo'
      -- `C_j ⊆ G'_j ∪ (the goods `fill` places with `j`)`
      have hlen : (junkOf goods s.base X j).length ≤ (if InE v agents goods s o j then (Gs j).length else 0) +
          room v agents goods s N o K Gs j := by
        have hnd : (junkOf goods s.base X j).Nodup := (nodup_bundle hgd X j).filter _
        rw [List.length_eq_countP_add_countP (fun g => decide (slotOf v agents goods s o Gs g = none))]
        have hA : (junkOf goods s.base X j).countP (fun g => decide (slotOf v agents goods s o Gs g = none)) ≤
            room v agents goods s N o K Gs j := by
          rw [List.countP_eq_length_filter]
          refine LB.fill_count (rest := restList v agents goods s o Gs Ds) hag (hnd.filter _) fun g hg => ?_
          obtain ⟨hgJ, hgs⟩ := List.mem_filter.mp hg
          simp only [decide_eq_true_eq] at hgs
          rcases hjunk j hjo' g hgJ with ⟨hjE, hgj⟩ | ⟨-, hf, -⟩
          · rw [slotOf_of_mem hσ hjE hgj] at hgs; cases hgs
          · exact hf
        have hB : (junkOf goods s.base X j).countP
            (fun g => decide (¬ (decide (slotOf v agents goods s o Gs g = none)) = true)) ≤
            (if InE v agents goods s o j then (Gs j).length else 0) := by
          rw [List.countP_eq_length_filter]
          by_cases hjE : InE v agents goods s o j
          · simp only [hjE, ↓reduceIte]
            refine length_le_of_subset (hnd.filter _) fun g hg => ?_
            obtain ⟨hgJ, hgs⟩ := List.mem_filter.mp hg
            rcases hjunk j hjo' g hgJ with ⟨-, hgj⟩ | ⟨hs, -, -⟩
            · exact hgj
            · simp [hs] at hgs
          · simp only [hjE, ↓reduceIte, Nat.le_zero, List.length_eq_zero_iff]
            refine List.eq_nil_iff_forall_not_mem.mpr fun g hg => ?_
            obtain ⟨hgJ, hgs⟩ := List.mem_filter.mp hg
            rcases hjunk j hjo' g hgJ with ⟨hjE', -⟩ | ⟨hs, -, -⟩
            · exact hjE hjE'
            · simp [hs] at hgs
        omega
      have hr := hroom j hj
      by_cases hc : j = o ∨ Frozen agents goods s.base (needsK v goods s.base N o K) j
      · simp only [hc, ↓reduceIte] at hr
        omega
      · simp only [hc, ↓reduceIte] at hr
        omega
  -- (OC₄)
  have hoc : OC v agents goods X (some o) := by
    intro w hw j hj hjw h hh
    cases hw
    refine Nat.le_of_not_lt fun hlt => ?_
    have hT : Threatened v j (bundle goods X o) (bundle goods X j) := ⟨h, hh, hlt⟩
    by_cases hjE : InE v agents goods s o j
    · -- served: `X_o ⊆ W_o ∖ (D_j ∪ G_j)` and `B_j ∪ G_j ⊆ X_j`
      have hsub : (bundle goods X o).Sublist ((Wl goods s o).filter (fun g => g ∉ Ds j ∧ g ∉ Gs j)) := by
        unfold Wl
        rw [List.filter_filter]
        refine filter_sublist_of_imp fun g hg hXg => ?_
        have hXg : X g = o := by simpa using hXg
        have hU := hXoU g hg hXg
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨fun hd => hU ⟨j, trivial, hjE, Or.inr hd⟩, fun hd => hU ⟨j, trivial, hjE, Or.inl hd⟩⟩,
          hXoW g hg hXg⟩
      have hval : value v j (baseOf goods s.base j ++ Gs j) ≤ value v j (bundle goods X j) := by
        refine value_le_of_subset j ?_ fun g hg => ?_
        · refine List.nodup_append.mpr ⟨hgd.filter _, (hS j hjE).2.2.1, fun a ha b hb e => ?_⟩
          subst e
          have := (mem_baseOf.mp ha).2
          rw [(hGJ j hjE a hb).2] at this; cases this
        · rcases List.mem_append.mp hg with hg | hg
          · obtain ⟨hgg, hb⟩ := mem_baseOf.mp hg
            exact mem_bundle.mpr ⟨hgg, hXb g hgg j hb⟩
          · obtain ⟨hgg, hb⟩ := hGJ j hjE g hg
            exact mem_bundle.mpr ⟨hgg, hXs g j hb (slotOf_of_mem hσ hjE hg)⟩
      exact (hS j hjE).2.2.2.2 (hT.mono hsub hval)
    · -- not threatened by `W_o ⊇ X_o`
      have hsub : (bundle goods X o).Sublist (Wl goods s o) :=
        filter_sublist_of_imp fun g hg hXg => by
          have := hXoW g hg (by simpa using hXg)
          simpa using this
      exact hjE ⟨hj, hjw, hT.mono hsub (value_baseOf_le hXb j)⟩
  exact ⟨fun i hi _ => hNd i hi, hV.toOwnerNeeds hXb hNd, hC, hoc⟩

end completion


/-! ## Lemma K′, "only if", and the statements of Lemmas K and K′ -/

section exact
variable {v : A → G → Nat} {agents : List A} {goods : List G} {s : LState A G} {N : A → G → Prop} {o : A}

/-- **Lemma K′, "only if"** (`k4/rulef.md` §2, Remark 5). If `X` is a completion with owner `o`, the owner's needs
taken from its bundle, that satisfies (OC₄), then `K := J ∩ X_o`, `G_x := X_x ∖ B_x` and `D_x := (J ∖ X_o) ∖ G_x`
form a K′-service of size at most `κ^K`. Only the needs of the Definition are used (no validity). -/
theorem lemmaK'_onlyIf (hag : agents.Nodup) (hgd : goods.Nodup) (hNd : ∀ i ∈ agents, Needs v goods s.base N i)
    {X : G → A} (hC : Completion agents goods s.base (ownerNeeds v goods X N (some o)) (some o) X)
    (hoc : OC v agents goods X (some o)) :
    ∃ (K : G → Bool) (Gs Ds : A → List G), ServiceOn v agents goods s N o K (fun _ => True) Gs Ds ∧
      sizeOn v agents goods s o (fun _ => True) Gs Ds ≤ kappaK v agents goods s N o K := by
  classical
  have ho := (hC.owner o rfl).1
  refine ⟨fun g => decide (s.base g = none ∧ X g = o), fun x => junkOf goods s.base X x,
    fun x => (LB4.junk goods s.base).filter (fun g => X g ≠ o ∧ X g ≠ x), ?_⟩
  -- `B_o ∪ K = X_o`, so `N^K` is the owner's needs from its bundle
  have hKB : C4min.ownerBundle goods s.base o (fun h => !decide (s.base h = none ∧ X h = o)) = bundle goods X o := by
    unfold C4min.ownerBundle bundle
    apply List.filter_congr
    intro g hg
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.not_eq_false']
    cases hb : s.base g with
    | none => simp
    | some i =>
      have := hC.onBase g hg i hb
      simp only [Option.some.injEq, reduceCtorEq, false_and, or_false]
      exact ⟨fun h => h ▸ this, fun h => this.symm.trans h⟩
  have hNK : needsK v goods s.base N o (fun g => decide (s.base g = none ∧ X g = o)) =
      ownerNeeds v goods X N (some o) := by
    funext i g
    by_cases hio : i = o
    · subst hio
      simp only [needsK, ownerNeeds, ↓reduceIte, hKB]
      apply propext
      constructor
      · rintro ⟨hN, hlt⟩
        obtain ⟨hg, -, -⟩ := (hNd i ho).upper g hN
        refine ⟨hg, fun hXg => ?_, hlt⟩
        have := le_value_of_mem v i (mem_bundle.mpr ⟨hg, hXg⟩)
        omega
      · rintro ⟨hg, hXg, hlt⟩
        exact ⟨(hNd i ho).of_bundle hC.onBase g hg hXg hlt, hlt⟩
    · have : some o ≠ some i := fun e => hio (Option.some.inj e).symm
      simp [needsK, ownerNeeds, hio, this]
  refine ⟨⟨fun x _ hxE => ?_, fun x y g _ _ _ _ hgx hgy => ?_⟩, ?_⟩
  · obtain ⟨hx, hxo, -⟩ := hxE
    have hxo' : some o ≠ some x := fun e => hxo (Option.some.inj e).symm
    refine ⟨fun g hg => ?_, fun g hg => ?_, (nodup_bundle hgd X x).filter _, ?_, ?_⟩
    · obtain ⟨hgJ, hgX⟩ := List.mem_filter.mp hg
      simp only [decide_eq_true_eq] at hgX
      exact ⟨hgJ, by simp [hgX.1]⟩
    · obtain ⟨hgg, hXg, hb⟩ := mem_junkOf.mp hg
      refine ⟨mem_junk.mpr ⟨hgg, hb⟩, by simp [hXg, hxo], fun hd => ?_⟩
      have := (List.mem_filter.mp hd).2
      simp only [decide_eq_true_eq] at this
      exact this.2 hXg
    · rw [hNK]
      by_cases hF : Frozen agents goods s.base (ownerNeeds v goods X N (some o)) x
      · exact Or.inl (hC.frozen x hx hxo' hF)
      · exact Or.inr ⟨hF, hC.free x hx hxo' hF⟩
    · -- `W_o ∖ (D_x ∪ G_x) = X_o` and `X_x ⊆ B_x ∪ G_x`
      have hL : (Wl goods s o).filter (fun g => g ∉ (LB4.junk goods s.base).filter (fun g => X g ≠ o ∧ X g ≠ x) ∧
          g ∉ junkOf goods s.base X x) = bundle goods X o := by
        unfold Wl bundle
        rw [List.filter_filter]
        apply List.filter_congr
        intro g hg
        rw [Bool.eq_iff_iff]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨hD, hJ⟩, hW⟩
          refine Classical.byContradiction fun hXo => ?_
          rcases hW with hb | hb
          · by_cases hXx : X g = x
            · exact hJ (mem_junkOf.mpr ⟨hg, hXx, hb⟩)
            · exact hD (List.mem_filter.mpr ⟨mem_junk.mpr ⟨hg, hb⟩, by simp [hXo, hXx]⟩)
          · exact hXo (hC.onBase g hg o hb)
        · intro hXo
          refine ⟨⟨fun hd => ?_, fun hj => ?_⟩, ?_⟩
          · have := (List.mem_filter.mp hd).2
            simp only [decide_eq_true_eq] at this
            exact this.1 hXo
          · exact hxo ((mem_junkOf.mp hj).2.1.symm.trans hXo)
          · cases hb : s.base g with
            | none => exact Or.inl rfl
            | some i => exact Or.inr (by rw [← hXo, hC.onBase g hg i hb])
      have hval : value v x (bundle goods X x) ≤ value v x (baseOf goods s.base x ++ junkOf goods s.base X x) := by
        refine value_le_of_subset x (nodup_bundle hgd X x) fun g hg => ?_
        obtain ⟨hgg, hXg⟩ := mem_bundle.mp hg
        cases hb : s.base g with
        | none => exact List.mem_append_right _ (mem_junkOf.mpr ⟨hgg, hXg, hb⟩)
        | some i =>
          have := hC.onBase g hgg i hb
          rw [hXg] at this; subst this
          exact List.mem_append_left _ (mem_baseOf.mpr ⟨hgg, hb⟩)
      rw [hL]
      rintro ⟨h, hh, hlt⟩
      have := hoc o rfl x hx hxo h hh
      omega
  · obtain ⟨-, hXx, -⟩ := mem_junkOf.mp hgx
    obtain ⟨-, hXy, -⟩ := mem_junkOf.mp hgy
    exact hXx.symm.trans hXy
  · -- the goods used are junk outside `X_o`, which fill the places of the other agents
    have h1 : sizeOn v agents goods s o (fun _ => True) (fun x => junkOf goods s.base X x)
        (fun x => (LB4.junk goods s.base).filter (fun g => X g ≠ o ∧ X g ≠ x)) ≤
        goods.countP (fun g => decide (s.base g = none ∧ X g ≠ o)) := by
      unfold sizeOn
      refine countP_le_of_imp fun g _ hU => ?_
      simp only [decide_eq_true_eq] at hU ⊢
      obtain ⟨x, -, hxE, hgx⟩ := hU
      rcases hgx with hgx | hgx
      · obtain ⟨-, hXg, hb⟩ := mem_junkOf.mp hgx
        exact ⟨hb, by rw [hXg]; exact hxE.2.1⟩
      · obtain ⟨hgJ, hgX⟩ := List.mem_filter.mp hgx
        simp only [decide_eq_true_eq] at hgX
        exact ⟨(mem_junk.mp hgJ).2, hgX.1⟩
    have h2 : goods.countP (fun g => decide (s.base g = none ∧ X g ≠ o)) =
        (agents.map (fun j => if j = o then 0 else (junkOf goods s.base X j).length)).sum := by
      have hJ := hC.junk_length hag
      rw [sum_split (fun j => (junkOf goods s.base X j).length) hag ho] at hJ
      have hJo : (junkOf goods s.base X o).length = goods.countP (fun g => decide (s.base g = none ∧ X g = o)) := by
        unfold junkOf bundle
        rw [List.filter_filter, ← List.countP_eq_length_filter]
        apply List.countP_congr
        intro g _
        simp [And.comm]
      have hsp := countP_split (fun g => decide (s.base g = none)) (fun g => decide (X g = o)) goods
      have e1 : goods.countP (fun g => decide (s.base g = none) && decide (X g = o)) =
          goods.countP (fun g => decide (s.base g = none ∧ X g = o)) :=
        List.countP_congr fun g _ => by simp
      have e2 : goods.countP (fun g => decide (s.base g = none) && !decide (X g = o)) =
          goods.countP (fun g => decide (s.base g = none ∧ X g ≠ o)) :=
        List.countP_congr fun g _ => by simp
      have e3 : (LB4.junk goods s.base).length = goods.countP (fun g => decide (s.base g = none)) := by
        rw [LB4.junk, List.countP_eq_length_filter]
      omega
    have h3 : (agents.map (fun j => if j = o then 0 else (junkOf goods s.base X j).length)).sum ≤
        kappaK v agents goods s N o (fun g => decide (s.base g = none ∧ X g = o)) := by
      unfold kappaK otherSlots
      rw [hNK]
      refine sum_le_sum_of_le _ _ agents fun j hj => ?_
      by_cases hjo : j = o
      · simp [hjo]
      · have hjo' : some o ≠ some j := fun e => hjo (Option.some.inj e).symm
        by_cases hF : Frozen agents goods s.base (ownerNeeds v goods X N (some o)) j
        · simp [hjo, hF, hC.frozen j hj hjo' hF]
        · have := hC.free j hj hjo' hF
          simp only [hjo, ↓reduceIte, hF, or_self]
          omega
    omega

/-- **Lemma K′** (`k4/rulef.md` §2, Remark 5): for a valid pre-allocation whose bases belong to listed agents and an
owner `o` that is not frozen, every other base of at most two goods, `P` has a completion with owner `o`, the owner's
needs from its bundle, satisfying (OC₄), **if and only if** some `K` and some K′-service have size at most `κ^K`
(Lemma K′'s deficit of `(o, K)` is at most 0). -/
theorem lemmaK' (hag : agents.Nodup) (hgd : goods.Nodup)
    (hmem : ∀ g ∈ goods, ∀ i, s.base g = some i → i ∈ agents)
    (hNd : ∀ i ∈ agents, Needs v goods s.base N i) (hV : Valid agents goods s.base N)
    (ho : o ∈ agents) (hoF : ¬ Frozen agents goods s.base N o)
    (h2 : ∀ i ∈ agents, i ≠ o → (baseOf goods s.base i).length ≤ 2) :
    (∃ X, Completion agents goods s.base (ownerNeeds v goods X N (some o)) (some o) X ∧ OC v agents goods X (some o)) ↔
      ∃ K, KPDefLE v agents goods s N o K 0 := by
  constructor
  · rintro ⟨X, hC, hoc⟩
    obtain ⟨K, Gs, Ds, hσ, hle⟩ := lemmaK'_onlyIf hag hgd hNd hC hoc
    exact ⟨K, Gs, Ds, hσ, by omega⟩
  · rintro ⟨K, Gs, Ds, hσ, hle⟩
    have := lemmaK'_if hag hgd hmem hNd hV ho hoF h2 hσ (by omega)
    exact ⟨_, this.completion, this.oc⟩

/-- **Lemma K** (`k4/rulef.md` §2): if the deficit of `(o, K)` is at most 0 (a K-service with the options (s), (r)
of size at most `κ^K`), `P` has a sound completion with owner `o` (the owner's needs from its bundle, (OC₄)); it is
EFX₀, frozen agents hold exactly their bases, and only `X_o` may have more than two goods. -/
theorem lemmaK (hag : agents.Nodup) (hgd : goods.Nodup)
    (hmem : ∀ g ∈ goods, ∀ i, s.base g = some i → i ∈ agents)
    (hNd : ∀ i ∈ agents, Needs v goods s.base N i) (hV : Valid agents goods s.base N)
    (ho : o ∈ agents) (hoF : ¬ Frozen agents goods s.base N o)
    (h2 : ∀ i ∈ agents, i ≠ o → (baseOf goods s.base i).length ≤ 2) {K : G → Bool}
    (h : KDefLE v agents goods s N o K 0) :
    ∃ X, SoundCompletion v agents goods s.base N (some o) X ∧ EFX0L v agents goods X ∧
      (∀ j ∈ agents, j ≠ o → (bundle goods X j).length ≤ 2) ∧
      (∀ j ∈ agents, j ≠ o → Frozen agents goods s.base (ownerNeeds v goods X N (some o)) j →
        ∀ g ∈ goods, X g = j → s.base g = some j) := by
  obtain ⟨Gs, Ds, hσ, -, hle⟩ := h
  have hS := lemmaK'_if hag hgd hmem hNd hV ho hoF h2 hσ (by omega)
  obtain ⟨hE, hlen⟩ := Valid.sound_ownerNeeds hgd hS.needs hS.valid hS.completion hS.oc
  refine ⟨_, hS, hE, fun j hj hjo => hlen j hj (fun e => hjo (Option.some.inj e).symm), fun j hj hjo hF =>
    hS.completion.frozen_base j hj (fun e => hjo (Option.some.inj e).symm) hF⟩

/-- A K-service is a K′-service: Lemma K's deficit bounds Lemma K′'s. -/
theorem KPDefLE_of_KDefLE {K : G → Bool} {d : Int} (h : KDefLE v agents goods s N o K d) :
    KPDefLE v agents goods s N o K d := by
  obtain ⟨Gs, Ds, hσ, -, hle⟩ := h
  exact ⟨Gs, Ds, hσ, hle⟩

/-! ### For the states of LB₄ʳ: outputs -/

/-- **Lemma K′ for a state of LB₄ʳ** (`EFX.LB4R.Inv`, needs `needsOf`): if `ω ≥ 1` or some base has three or more
goods, LB₄ʳ's owner step has an output with owner `o` (`EFX.LB4R.Output`) iff some `K` has Lemma K′ deficit ≤ 0. -/
theorem output_iff_lemmaK' (hag : agents.Nodup) (hgd : goods.Nodup) (hI : Inv v agents goods s)
    (hmem : ∀ g ∈ goods, ∀ i, s.base g = some i → i ∈ agents)
    (ho : o ∈ agents) (hoF : ¬ Frozen agents goods s.base (needsOf v goods s) o)
    (h2 : ∀ i ∈ agents, i ≠ o → (baseOf goods s.base i).length ≤ 2)
    (hω : (∀ i ∈ agents, (baseOf goods s.base i).length ≤ 2) → 0 < omega v agents goods s) :
    (∃ X, Output v agents goods s (some o) X) ↔ ∃ K, KPDefLE v agents goods s (needsOf v goods s) o K 0 := by
  rw [← lemmaK' hag hgd hmem hI.needs hI.valid ho hoF h2]
  constructor
  · rintro ⟨X, hC, hoc, -⟩
    exact ⟨X, hC, hoc⟩
  · rintro ⟨X, hC, hoc⟩
    refine ⟨X, hC, hoc, fun hall => ⟨fun h => (by cases h), fun hle => ?_⟩⟩
    have := hω hall
    omega

/-- **Lemma K for a state of LB₄ʳ**: with deficit ≤ 0 and `ω ≥ 1` (or a base of three or more goods), LB₄ʳ's owner
step has an output with owner `o`. -/
theorem output_of_lemmaK (hag : agents.Nodup) (hgd : goods.Nodup) (hI : Inv v agents goods s)
    (hmem : ∀ g ∈ goods, ∀ i, s.base g = some i → i ∈ agents)
    (ho : o ∈ agents) (hoF : ¬ Frozen agents goods s.base (needsOf v goods s) o)
    (h2 : ∀ i ∈ agents, i ≠ o → (baseOf goods s.base i).length ≤ 2)
    (hω : (∀ i ∈ agents, (baseOf goods s.base i).length ≤ 2) → 0 < omega v agents goods s) {K : G → Bool}
    (h : KDefLE v agents goods s (needsOf v goods s) o K 0) : ∃ X, Output v agents goods s (some o) X :=
  (output_iff_lemmaK' hag hgd hI hmem ho hoF h2 hω).mpr ⟨K, KPDefLE_of_KDefLE h⟩

/-- **`ω ≤ 0`** (`EFX.LB4.complete_none_exists`): when every base has at most two goods and `ω ≤ 0`, LB₄ʳ's owner
step has an output without owner. -/
theorem output_none_of_omega (hag : agents.Nodup) (hgd : goods.Nodup) (hI : Inv v agents goods s)
    (hmem : ∀ g ∈ goods, ∀ i, s.base g = some i → i ∈ agents)
    (hall : ∀ i ∈ agents, (baseOf goods s.base i).length ≤ 2) (hω : omega v agents goods s ≤ 0) (d : A) :
    ∃ X, Output v agents goods s none X := by
  have hC := complete_none_exists (N := needsOf v goods s) hag hgd hmem hall hω d
  exact ⟨_, hC.toOwnerNeeds hI.needs, (fun w hw => by cases hw), fun _ => ⟨fun _ => hω, fun _ => rfl⟩⟩

end exact

/-! ## Lemma S: free exposed agents cost nothing (`k4/rulef.md` §6, Step 2) -/

section lemmaS
variable {v : A → G → Nat} {agents : List A} {goods : List G} {s : LState A G} {N : A → G → Prop} {o : A}

/-- **Free** (`k4/rulef.md` §6): unmarked, not frozen, and a base of one good. -/
def Free (agents : List A) (goods : List G) (s : LState A G) (N : A → G → Prop) (x : A) : Prop :=
  ¬ s.marked x ∧ ¬ Frozen agents goods s.base N x ∧ (baseOf goods s.base x).length = 1

open Classical in
/-- **`κ₀`**: the slot places of the free agents other than `o` that are not in `E`. -/
noncomputable def kappa0 (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (N : A → G → Prop)
    (o : A) : Nat :=
  (agents.map (fun x => if x ≠ o ∧ Free agents goods s N x ∧ ¬ InE v agents goods s o x then
    2 - (baseOf goods s.base x).length else 0)).sum

open Classical in
/-- The number of free agents of `E`. -/
noncomputable def nFreeE (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (N : A → G → Prop)
    (o : A) : Nat :=
  agents.countP (fun x => decide (InE v agents goods s o x ∧ Free agents goods s N x))

omit [DecidableEq A] [DecidableEq G] in
theorem value_le_of_length_le_one {x : A} {c : Nat} {L : List G} (hL : L.length ≤ 1) (h : ∀ g ∈ L, v x g ≤ c) :
    value v x L ≤ c := by
  match L, hL with
  | [], _ => simp
  | [g], _ => simpa using h g (by simp)

omit [DecidableEq G] in
/-- `W ∩ NA = ∅` (`k4/rulef.md` §3, §6): the junk by (V1), `B_o` since `o` is not frozen and has at most one good. -/
theorem W_not_NA (hV : Valid agents goods s.base N) (hoF : ¬ Frozen agents goods s.base N o)
    (hB1 : (baseOf goods s.base o).length ≤ 1) {g : G} (hg : g ∈ Wl goods s o) : ¬ NA agents N g := by
  intro hna
  obtain ⟨hgg, hb⟩ := mem_Wl.mp hg
  rcases hb with hb | hb
  · exact hV.v1 g (mem_junk.mpr ⟨hgg, hb⟩) hna
  · have hgB : g ∈ baseOf goods s.base o := mem_baseOf.mpr ⟨hgg, hb⟩
    have : baseOf goods s.base o = [g] := by
      match h : baseOf goods s.base o, hB1 with
      | [], _ => rw [h] at hgB; simp at hgB
      | [y], _ => rw [h] at hgB; simp at hgB; rw [hgB]
    exact hoF ⟨g, this, hna⟩

/-- **One free agent of `E`** (the proof of Lemma S): whatever the goods `U` used so far, a free agent `x ∈ E` can be
served (K = ∅) by a slot good outside `U`, or by a kept-out set of which at most one good `a` is outside `U`. -/
theorem serve_free (hgd : goods.Nodup) (hNd : ∀ i ∈ agents, Needs v goods s.base N i)
    (hV : Valid agents goods s.base N) (hoF : ¬ Frozen agents goods s.base N o)
    (hB1 : (baseOf goods s.base o).length ≤ 1) (h4 : ∀ x ∈ agents, (relevant v x goods).length ≤ 4)
    {x : A} (hxE : InE v agents goods s o x) (hxF : Free agents goods s N x) (U : G → Prop) :
    ∃ (Gx Dx : List G) (a : G), Serves v agents goods s N o (fun _ => false) x Gx Dx ∧
      (Gx = [] ∨ ∃ g, Gx = [g] ∧ Dx = []) ∧ (∀ g ∈ Gx, ¬ U g) ∧ (∀ g, g ∈ Gx ∨ g ∈ Dx → U g ∨ g = a) := by
  classical
  obtain ⟨hxa, hxo, hthr⟩ := hxE
  obtain ⟨-, hxF', hB⟩ := hxF
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hB
  have hyg : y ∈ goods := (mem_baseOf.mp (by rw [hy]; simp : y ∈ baseOf goods s.base x)).1
  have hyb : s.base y = some x := (mem_baseOf.mp (by rw [hy]; simp : y ∈ baseOf goods s.base x)).2
  -- the goods of `W` are worth at most the pick `y` to `x`, and `y ∉ W`
  have hle : ∀ g ∈ Wl goods s o, v x g ≤ v x y := by
    intro g hg
    refine Nat.le_of_not_lt fun hlt => W_not_NA hV hoF hB1 hg ⟨x, hxa, (hNd x hxa).lower g (mem_Wl.mp hg).1 ?_ ?_⟩
    · intro hb
      rcases (mem_Wl.mp hg).2 with h | h <;> rw [hb] at h <;> simp at h
      exact hxo h
    · rw [hy]; simpa using hlt
  have hyW : y ∉ Wl goods s o := fun h => by
    rcases (mem_Wl.mp h).2 with h' | h' <;> rw [hyb] at h' <;> simp at h'
    exact hxo h'
  -- `L = R_x ∩ W`
  obtain ⟨L, hL⟩ : ∃ L, L = relevant v x (Wl goods s o) := ⟨_, rfl⟩
  have hLnd : L.Nodup := by rw [hL]; exact (hgd.filter _).filter _
  have hmemL : ∀ g, g ∈ L ↔ g ∈ Wl goods s o ∧ 0 < v x g := fun g => by
    rw [hL]; simp [relevant]
  -- `y` is relevant (else nothing in `W` is worth anything and `x` is not threatened)
  have hypos : 0 < v x y := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    obtain ⟨h, -, hlt⟩ := hthr
    have h1 := value_sublist v x (List.erase_sublist (l := Wl goods s o) (a := h))
    rw [← value_relevant v x (Wl goods s o)] at h1
    have h2 : relevant v x (Wl goods s o) = [] := List.eq_nil_iff_forall_not_mem.mpr fun g hg => by
      obtain ⟨hgW, hpos⟩ := (hmemL g).mp (hL ▸ hg)
      have := hle g hgW; omega
    rw [h2] at h1
    simp at h1; omega
  have hLlen : L.length ≤ 3 := by
    have hyR : y ∈ relevant v x goods := List.mem_filter.mpr ⟨hyg, by simpa using hypos⟩
    have := length_le_of_subset hLnd (T := (relevant v x goods).erase y) fun g hg => by
      obtain ⟨hgW, hpos⟩ := (hmemL g).mp hg
      refine (List.mem_erase_of_ne fun (e : g = y) => hyW (e ▸ hgW)).mpr ?_
      exact List.mem_filter.mpr ⟨(mem_Wl.mp hgW).1, by simpa using hpos⟩
    rw [List.length_erase_of_mem hyR] at this
    have := h4 x hxa
    omega
  -- at most one good of `L` is not junk: it is in `B_o`
  have hnj : (L.filter (fun g => s.base g ≠ none)).length ≤ 1 := by
    refine Nat.le_trans (length_le_of_subset (hLnd.filter _) fun g hg => ?_) hB1
    obtain ⟨hgL, hgb⟩ := List.mem_filter.mp hg
    simp only [ne_eq, decide_eq_true_eq] at hgb
    obtain ⟨hgW, -⟩ := (hmemL g).mp hgL
    obtain ⟨hgg, hb⟩ := mem_Wl.mp hgW
    exact mem_baseOf.mpr ⟨hgg, hb.resolve_left hgb⟩
  have hFK : ¬ Frozen agents goods s.base (needsK v goods s.base N o (fun _ => false)) x :=
    fun h => hxF' (frozen_of_frozenK h)
  by_cases hA : ∃ g₁ ∈ L, ∃ g₂ ∈ L, g₁ ≠ g₂ ∧ s.base g₁ = none ∧ s.base g₂ = none ∧ ¬ U g₁ ∧ ¬ U g₂ ∧
      v x g₂ ≤ v x g₁
  · -- two junk goods of `L` outside `U`: the larger is a slot good
    obtain ⟨g₁, hg₁, g₂, hg₂, h12, hb₁, hb₂, hU₁, -, hv⟩ := hA
    refine ⟨[g₁], [], g₁, serves_slot_iff.mpr ⟨mem_junk.mpr ⟨(mem_Wl.mp ((hmemL g₁).mp hg₁).1).1, hb₁⟩, rfl,
      hFK, by omega, not_threatened_of_value_le ?_⟩, Or.inr ⟨g₁, rfl, rfl⟩, by simpa using hU₁,
      fun g hg => by simp at hg; exact Or.inr hg⟩
    have hg₂' : g₂ ∈ L.erase g₁ := (List.mem_erase_of_ne (Ne.symm h12)).mpr hg₂
    have e1 : value v x ((Wl goods s o).filter (fun h => h ≠ g₁)) ≤ value v x (L.erase g₁) := by
      rw [← value_relevant v x ((Wl goods s o).filter (fun h => h ≠ g₁))]
      refine value_le_of_subset x (((hgd.filter _).filter _).filter _) fun g hg => ?_
      obtain ⟨hgf, hpos⟩ := List.mem_filter.mp hg
      obtain ⟨hgW, hne⟩ := List.mem_filter.mp hgf
      simp only [ne_eq, decide_eq_true_eq] at hne hpos
      exact (List.mem_erase_of_ne hne).mpr ((hmemL g).mpr ⟨hgW, hpos⟩)
    have e2 := LB4.value_erase (v := v) (i := x) hg₂'
    have e3 : value v x ((L.erase g₁).erase g₂) ≤ v x y := by
      refine value_le_of_length_le_one ?_ fun g hg => hle g ((hmemL g).mp
        (List.mem_of_mem_erase (List.mem_of_mem_erase hg))).1
      rw [List.length_erase_of_mem hg₂', List.length_erase_of_mem hg₁]
      omega
    rw [hy]
    simp only [List.cons_append, List.nil_append, value_cons, value_nil, Nat.add_zero]
    omega
  · -- otherwise keep out the junk goods of `L`: at most one of them is outside `U`
    have hD : ∀ g ∈ L.filter (fun g => s.base g = none), g ∈ LB4.junk goods s.base ∧ (fun _ => false) g = false :=
      fun g hg => by
        obtain ⟨hgL, hb⟩ := List.mem_filter.mp hg
        simp only [decide_eq_true_eq] at hb
        exact ⟨mem_junk.mpr ⟨(mem_Wl.mp ((hmemL g).mp hgL).1).1, hb⟩, rfl⟩
    have hT : ¬ Threatened v x ((Wl goods s o).filter (fun h => h ∉ L.filter (fun g => s.base g = none)))
        (baseOf goods s.base x) := by
      refine not_threatened_of_value_le ?_
      rw [← value_relevant v x ((Wl goods s o).filter (fun h => h ∉ L.filter (fun g => s.base g = none))), hy]
      simp only [value_cons, value_nil, Nat.add_zero]
      have := value_le_of_subset (v := v) x (L₂ := L.filter (fun g => s.base g ≠ none))
        (L₁ := relevant v x ((Wl goods s o).filter (fun h => h ∉ L.filter (fun g => s.base g = none))))
        (((hgd.filter _).filter _).filter _) fun g hg => by
          obtain ⟨hgf, hpos⟩ := List.mem_filter.mp hg
          obtain ⟨hgW, hnD⟩ := List.mem_filter.mp hgf
          have hpos : 0 < v x g := by simpa using hpos
          have hnD : g ∉ L.filter (fun g => s.base g = none) := fun hm => by
            simp only [decide_eq_true_eq] at hnD
            exact hnD hm
          have hgL := (hmemL g).mpr ⟨hgW, hpos⟩
          refine List.mem_filter.mpr ⟨hgL, ?_⟩
          simp only [ne_eq, decide_eq_true_eq]
          exact fun hb => hnD (List.mem_filter.mpr ⟨hgL, by simpa using hb⟩)
      have := value_le_of_length_le_one hnj (x := x) (c := v x y) fun g hg =>
        hle g ((hmemL g).mp (List.mem_filter.mp hg).1).1
      omega
    by_cases hout : ∃ a ∈ L.filter (fun g => s.base g = none), ¬ U a
    · obtain ⟨a, ha, hUa⟩ := hout
      refine ⟨[], L.filter (fun g => s.base g = none), a, serves_keep_iff.mpr ⟨hD, hT⟩, Or.inl rfl, by simp,
        fun g hg => ?_⟩
      replace hg : g ∈ L.filter (fun g => s.base g = none) := hg.resolve_left List.not_mem_nil
      refine Classical.byContradiction fun hno => ?_
      simp only [not_or] at hno
      obtain ⟨hUg, hga⟩ := hno
      obtain ⟨hgL, hgb⟩ := List.mem_filter.mp hg
      obtain ⟨haL, hab⟩ := List.mem_filter.mp ha
      simp only [decide_eq_true_eq] at hgb hab
      rcases Nat.le_total (v x a) (v x g) with h | h
      · exact hA ⟨g, hgL, a, haL, hga, hgb, hab, hUg, hUa, h⟩
      · exact hA ⟨a, haL, g, hgL, Ne.symm hga, hab, hgb, hUa, hUg, h⟩
    · refine ⟨[], L.filter (fun g => s.base g = none), y, serves_keep_iff.mpr ⟨hD, hT⟩, Or.inl rfl, by simp,
        fun g hg => ?_⟩
      replace hg : g ∈ L.filter (fun g => s.base g = none) := hg.resolve_left List.not_mem_nil
      exact Or.inl (Classical.byContradiction fun h => hout ⟨g, hg, h⟩)

/-! ### Changing the agents served -/

theorem ServiceOn.mono {K : G → Bool} {T T' : A → Prop} {Gs Ds : A → List G}
    (h : ServiceOn v agents goods s N o K T Gs Ds) (hT : ∀ x, InE v agents goods s o x → T' x → T x) :
    ServiceOn v agents goods s N o K T' Gs Ds :=
  ⟨fun x hx hxE => h.serves x (hT x hxE hx) hxE,
    fun x y g hx hy hxE hyE => h.disj x y g (hT x hxE hx) (hT y hyE hy) hxE hyE⟩

theorem Separated.mono {T T' : A → Prop} {Gs Ds : A → List G} (h : Separated v agents goods s o T Gs Ds)
    (hT : ∀ x, InE v agents goods s o x → T' x → T x) : Separated v agents goods s o T' Gs Ds :=
  fun x hx hxE => h x (hT x hxE hx) hxE

theorem sizeOn_congr {T T' : A → Prop} {Gs Ds : A → List G}
    (hT : ∀ x, InE v agents goods s o x → (T x ↔ T' x)) :
    sizeOn v agents goods s o T Gs Ds = sizeOn v agents goods s o T' Gs Ds := by
  classical
  unfold sizeOn
  apply List.countP_congr
  intro g _
  simp only [decide_eq_true_eq]
  exact ⟨fun ⟨x, hx, hxE, h⟩ => ⟨x, (hT x hxE).mp hx, hxE, h⟩, fun ⟨x, hx, hxE, h⟩ => ⟨x, (hT x hxE).mpr hx, hxE, h⟩⟩

/-- The extension of Lemma S, one free agent of `E` at a time (the list `xs` of the agents still to serve). -/
theorem lemmaS_aux (hgd : goods.Nodup) (hNd : ∀ i ∈ agents, Needs v goods s.base N i)
    (hV : Valid agents goods s.base N) (hoF : ¬ Frozen agents goods s.base N o)
    (hB1 : (baseOf goods s.base o).length ≤ 1) (h4 : ∀ x ∈ agents, (relevant v x goods).length ≤ 4) :
    ∀ xs : List A, xs.Nodup → (∀ x ∈ xs, InE v agents goods s o x ∧ Free agents goods s N x) →
    ∀ Gs Ds : A → List G, ServiceOn v agents goods s N o (fun _ => false) (fun x => x ∉ xs) Gs Ds →
      Separated v agents goods s o (fun x => x ∉ xs) Gs Ds →
      ∃ Gs' Ds' : A → List G, ServiceOn v agents goods s N o (fun _ => false) (fun _ => True) Gs' Ds' ∧
        Separated v agents goods s o (fun _ => True) Gs' Ds' ∧ (∀ x, x ∉ xs → Gs' x = Gs x ∧ Ds' x = Ds x) ∧
        sizeOn v agents goods s o (fun _ => True) Gs' Ds' ≤ sizeOn v agents goods s o (fun x => x ∉ xs) Gs Ds + xs.length
  | [], _, _, Gs, Ds, hσ, hsep => by
    refine ⟨Gs, Ds, hσ.mono fun x _ _ => List.not_mem_nil, hsep.mono fun x _ _ => List.not_mem_nil,
      fun _ _ => ⟨rfl, rfl⟩, ?_⟩
    rw [sizeOn_congr (T' := fun x => x ∉ ([] : List A)) fun x _ => ⟨fun _ => List.not_mem_nil, fun _ => trivial⟩]
    simp
  | x :: xs, hnd, hxs, Gs, Ds, hσ, hsep => by
    classical
    obtain ⟨hxn, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨hxE, hxF⟩ := hxs x (by simp)
    obtain ⟨Gx, Dx, a, hS, hsepx, hGU, hUa⟩ :=
      serve_free hgd hNd hV hoF hB1 h4 hxE hxF (UsedOn v agents goods s o (fun y => y ∉ x :: xs) Gs Ds)
    -- serve `x`
    let Gs₁ : A → List G := fun y => if y = x then Gx else Gs y
    let Ds₁ : A → List G := fun y => if y = x then Dx else Ds y
    have hσ₁ : ServiceOn v agents goods s N o (fun _ => false) (fun y => y ∉ xs) Gs₁ Ds₁ := by
      refine ⟨fun y hy hyE => ?_, fun y z g hy hz hyE hzE hgy hgz => ?_⟩
      · by_cases hyx : y = x
        · subst hyx; simpa [Gs₁, Ds₁] using hS
        · have : y ∉ x :: xs := by simp [hyx, hy]
          simpa [Gs₁, Ds₁, hyx] using hσ.serves y this hyE
      · by_cases hyx : y = x <;> by_cases hzx : z = x
        · rw [hyx, hzx]
        · subst hyx
          have hz' : z ∉ y :: xs := by simp [hzx, hz]
          simp only [Gs₁, ↓reduceIte, hzx] at hgy hgz
          exact absurd ⟨z, hz', hzE, Or.inl hgz⟩ (hGU g hgy)
        · subst hzx
          have hy' : y ∉ z :: xs := by simp [hyx, hy]
          simp only [Gs₁, ↓reduceIte, hyx] at hgy hgz
          exact absurd ⟨y, hy', hyE, Or.inl hgy⟩ (hGU g hgz)
        · simp only [Gs₁, hyx, hzx, ↓reduceIte] at hgy hgz
          exact hσ.disj y z g (by simp [hyx, hy]) (by simp [hzx, hz]) hyE hzE hgy hgz
    have hsep₁ : Separated v agents goods s o (fun y => y ∉ xs) Gs₁ Ds₁ := by
      intro y hy hyE
      by_cases hyx : y = x
      · subst hyx; simpa [Gs₁, Ds₁] using hsepx
      · simpa [Gs₁, Ds₁, hyx] using hsep y (by simp [hyx, hy]) hyE
    have hsize₁ : sizeOn v agents goods s o (fun y => y ∉ xs) Gs₁ Ds₁ ≤
        sizeOn v agents goods s o (fun y => y ∉ x :: xs) Gs Ds + 1 := by
      unfold sizeOn
      refine countP_le_add_one hgd (a := a) fun g _ hU => ?_
      simp only [decide_eq_true_eq] at hU ⊢
      obtain ⟨y, hy, hyE, hgy⟩ := hU
      by_cases hyx : y = x
      · subst hyx
        simp only [Gs₁, Ds₁, ↓reduceIte] at hgy
        exact hUa g hgy
      · simp only [Gs₁, Ds₁, hyx, ↓reduceIte] at hgy
        exact Or.inl ⟨y, by simp [hyx, hy], hyE, hgy⟩
    obtain ⟨Gs', Ds', hσ', hsep', hagree, hsize'⟩ :=
      lemmaS_aux hgd hNd hV hoF hB1 h4 xs hnd' (fun y hy => hxs y (by simp [hy])) Gs₁ Ds₁ hσ₁ hsep₁
    refine ⟨Gs', Ds', hσ', hsep', fun y hy => ?_, ?_⟩
    · have hyx : y ≠ x := fun e => hy (by simp [e])
      have hy' : y ∉ xs := fun h => hy (by simp [h])
      obtain ⟨h1, h2⟩ := hagree y hy'
      simp only [Gs₁, Ds₁, hyx, ↓reduceIte] at h1 h2
      exact ⟨h1, h2⟩
    · simp only [List.length_cons]
      omega

/-- **Lemma S, the extension** (`k4/rulef.md` §6): let `(s.base, N)` be a valid pre-allocation in which every listed
agent values at most four goods, and `o` an agent that is not frozen with `|B_o| ≤ 1`. A ∅-service (separated
options) of the agents of `E` that are not free extends, unchanged on them, to a ∅-service of all of `E` whose size
exceeds the given one by at most the number of free agents of `E`. -/
theorem lemmaS_extend (hag : agents.Nodup) (hgd : goods.Nodup) (hNd : ∀ i ∈ agents, Needs v goods s.base N i)
    (hV : Valid agents goods s.base N) (hoF : ¬ Frozen agents goods s.base N o)
    (hB1 : (baseOf goods s.base o).length ≤ 1) (h4 : ∀ x ∈ agents, (relevant v x goods).length ≤ 4)
    {Gs Ds : A → List G}
    (hσ : ServiceOn v agents goods s N o (fun _ => false) (fun x => ¬ Free agents goods s N x) Gs Ds)
    (hsep : Separated v agents goods s o (fun x => ¬ Free agents goods s N x) Gs Ds) :
    ∃ Gs' Ds' : A → List G, ServiceOn v agents goods s N o (fun _ => false) (fun _ => True) Gs' Ds' ∧
      Separated v agents goods s o (fun _ => True) Gs' Ds' ∧
      (∀ x, ¬ Free agents goods s N x → Gs' x = Gs x ∧ Ds' x = Ds x) ∧
      sizeOn v agents goods s o (fun _ => True) Gs' Ds' ≤
        sizeOn v agents goods s o (fun x => ¬ Free agents goods s N x) Gs Ds + nFreeE v agents goods s N o := by
  classical
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = agents.filter (fun x => decide (InE v agents goods s o x ∧ Free agents goods s N x)) :=
    ⟨_, rfl⟩
  have hmemxs : ∀ x, InE v agents goods s o x → (x ∉ xs ↔ ¬ Free agents goods s N x) := fun x hxE => by
    rw [hxs]; simp [List.mem_filter, hxE, hxE.1]
  have hfree : ∀ x, ¬ Free agents goods s N x → x ∉ xs := fun x hx hm => by
    rw [hxs] at hm
    have := (List.mem_filter.mp hm).2
    simp only [decide_eq_true_eq] at this
    exact hx this.2
  have hxsnd : xs.Nodup := by rw [hxs]; exact hag.filter _
  have hxsP : ∀ x ∈ xs, InE v agents goods s o x ∧ Free agents goods s N x := fun x hx => by
    rw [hxs] at hx; simpa using (List.mem_filter.mp hx).2
  obtain ⟨Gs', Ds', hσ', hsep', hagree, hsize⟩ := lemmaS_aux hgd hNd hV hoF hB1 h4 xs hxsnd hxsP Gs Ds
    (hσ.mono fun x hxE hx => (hmemxs x hxE).mp hx) (hsep.mono fun x hxE hx => (hmemxs x hxE).mp hx)
  refine ⟨Gs', Ds', hσ', hsep', fun x hx => hagree x (hfree x hx), ?_⟩
  rw [sizeOn_congr (T' := fun x => x ∉ xs) fun x hxE => (hmemxs x hxE).symm, nFreeE, List.countP_eq_length_filter,
    ← hxs]
  exact hsize

/-- **Lemma S** (`k4/rulef.md` §6, Step 2): with the hypotheses of `lemmaS_extend`, if a ∅-service of the agents of
`E` that are not free has size `|σ|`, the deficit of `(o, ∅)` is at most `|σ| − κ₀` (`κ₀` the slot places of the free
agents other than `o` that are not in `E`). -/
theorem lemmaS (hag : agents.Nodup) (hgd : goods.Nodup) (hNd : ∀ i ∈ agents, Needs v goods s.base N i)
    (hV : Valid agents goods s.base N) (hoF : ¬ Frozen agents goods s.base N o)
    (hB1 : (baseOf goods s.base o).length ≤ 1) (h4 : ∀ x ∈ agents, (relevant v x goods).length ≤ 4)
    {Gs Ds : A → List G}
    (hσ : ServiceOn v agents goods s N o (fun _ => false) (fun x => ¬ Free agents goods s N x) Gs Ds)
    (hsep : Separated v agents goods s o (fun x => ¬ Free agents goods s N x) Gs Ds) :
    KDefLE v agents goods s N o (fun _ => false)
      ((sizeOn v agents goods s o (fun x => ¬ Free agents goods s N x) Gs Ds : Int) - kappa0 v agents goods s N o) := by
  classical
  obtain ⟨Gs', Ds', hσ', hsep', -, hsize⟩ := lemmaS_extend hag hgd hNd hV hoF hB1 h4 hσ hsep
  refine ⟨Gs', Ds', hσ', hsep', ?_⟩
  --  counts  and one place for every free agent of 
  have hk : kappa0 v agents goods s N o + nFreeE v agents goods s N o ≤
      kappaK v agents goods s N o (fun _ => false) := by
    unfold kappa0 kappaK otherSlots nFreeE
    rw [countP_eq_sum, ← sum_map_add]
    refine sum_le_sum_of_le _ _ agents fun x _ => ?_
    by_cases hxo : x = o
    · simp only [hxo]
      have : ¬ InE v agents goods s o o := fun h => h.2.1 rfl
      simp [this]
    · by_cases hF : Free agents goods s N x
      · have hFK : ¬ Frozen agents goods s.base (needsK v goods s.base N o (fun _ => false)) x :=
          fun h => hF.2.1 (frozen_of_frozenK h)
        have hB := hF.2.2
        by_cases hE : InE v agents goods s o x <;> simp [hxo, hF, hFK, hE, hB]
      · simp [hF]
  omega

end lemmaS

end LB4R
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB4R.serves_slot_iff
#print axioms EFX.LB4R.serves_keep_iff
#print axioms EFX.LB4R.frozen_of_frozenK
#print axioms EFX.LB4R.slotOf_of_mem
#print axioms EFX.LB4R.lemmaK'_if
#print axioms EFX.LB4R.lemmaK'_onlyIf
#print axioms EFX.LB4R.lemmaK'
#print axioms EFX.LB4R.lemmaK
#print axioms EFX.LB4R.KPDefLE_of_KDefLE
#print axioms EFX.LB4R.output_iff_lemmaK'
#print axioms EFX.LB4R.output_of_lemmaK
#print axioms EFX.LB4R.output_none_of_omega
#print axioms EFX.LB4R.W_not_NA
#print axioms EFX.LB4R.serve_free
#print axioms EFX.LB4R.lemmaS_aux
#print axioms EFX.LB4R.lemmaS_extend
#print axioms EFX.LB4R.lemmaS
