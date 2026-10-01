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

end LB4R
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB4R.serves_slot_iff
#print axioms EFX.LB4R.serves_keep_iff
#print axioms EFX.LB4R.frozen_of_frozenK
#print axioms EFX.LB4R.slotOf_of_mem
#print axioms EFX.LB4R.lemmaK'_if
