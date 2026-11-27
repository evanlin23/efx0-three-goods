import EFX.RecS
import EFX.Lift1

/-!
# Theorem U: one truly dangerous agent (`k4/oc1max_multi.md` §3)

Theorem U (K4.MULTI.U, `proof/k4-oc1max-multi`; refereed CORRECT). Let `Y` be a perfect start with strict values,
`P = (k = x₀, …, x_t = z)` a *longest* canonical chain from `k` (each `x_i` wants `Y_{x_{i−1}}`, the head `z` is
unfrozen at the picks), and `H₀` a set of junk goods improving for `k`. Suppose that the junk `J` threatens no agent
other than `k` and `z` at its pick value (this is `D_T ⊆ {k}` together with `E_J ⊆ {z}`), and that if `J` threatens
`z` at its pick value, then `z` is unfrozen after `P`. Then the state `B′` after `P` has an S\* completion owned by
`k` (`thmU`), so OC₁ holds at `Y` (`thmU_oc1`).

The proof follows the note through Lemma M (`EFX.OC1Max.sStar_of_slotMatching`) with owner `k` and kept-out set
`H = {Y_z}`, so that the owner's set is `J`:
- (G1), (G2) at `B′` (Lemma D-red 1): every other base has at most one good; every junk good of `B′` is unwanted.
- (H1) and the exposed holders: values only rise along `P`, so by the hypothesis `J` threatens nobody other than
  `z` at its value after `P`.
- The receiver of `Y_z`: `z` itself if it is unfrozen after `P` (admissible by the count of Lemma KEEP,
  `v_z(J ∩ R_z) ≤ 2 p_z < v_z(a) + p_z`, from `|R_z| ≤ 4`); otherwise a wanter `w` of `z`'s new good `a`, which is
  off `P`, unfrozen at the picks (else walking up from `w` gives a longer canonical chain), and unfrozen after `P`.
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

open LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## (A) Order facts -/

omit [DecidableEq A] in
theorem before_irrefl {l : List A} (hnd : l.Nodup) {a : A} : ¬ Before l a a := fun h => before_asymm hnd h h

omit [DecidableEq A] in
theorem before_trans : ∀ {l : List A}, l.Nodup → ∀ {a b c : A}, Before l a b → Before l b c → Before l a c
  | [], _, _, _, _, h, _ => h.elim
  | x :: xs, hnd, a, b, c, hab, hbc => by
    have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
    rcases hbc with ⟨hbx, hc⟩ | hbc
    · -- `b` is the head: nothing comes before it
      subst hbx
      rcases hab with ⟨-, hb⟩ | hab
      · exact absurd hb hx
      · exact absurd (before_mem hab).2 hx
    · rcases hab with ⟨hax, -⟩ | hab
      · exact Or.inl ⟨hax, (before_mem hbc).2⟩
      · exact Or.inr (before_trans (List.nodup_cons.mp hnd).2 hab hbc)

omit [DecidableEq A] in
/-- A list whose consecutive elements are increasing in `σ` is increasing in `σ`. -/
theorem pairwise_of_consecutive {σ : List A} (hnd : σ.Nodup) :
    ∀ {l : List A}, (∀ x ∈ l.zip l.tail, Before σ x.1 x.2) → l.Pairwise (Before σ)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    have hab : Before σ a b := h (a, b) (by simp)
    have hrest : (b :: t).Pairwise (Before σ) := pairwise_of_consecutive hnd fun x hx => h x (by
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]; exact Or.inr hx)
    refine List.pairwise_cons.mpr ⟨fun c hc => ?_, hrest⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hab
    · exact before_trans hnd hab ((List.pairwise_cons.mp hrest).1 c hc)

omit [DecidableEq A] in
theorem nodup_of_pairwise_before {σ : List A} (hnd : σ.Nodup) {l : List A} (h : l.Pairwise (Before σ)) :
    l.Nodup :=
  List.Pairwise.imp (R := Before σ) (S := fun a b => a ≠ b)
    (fun {a b} (hb : Before σ a b) (e : a = b) => before_irrefl hnd (by rw [e] at hb; exact hb)) h

/-- The elements of `l` after `a` (all of `l` if `a ∉ l`). -/
def afterL : List A → A → List A
  | [], _ => []
  | x :: xs, a => if x = a then xs else afterL xs a

theorem length_afterL_lt : ∀ {l : List A} {a : A}, a ∈ l → (afterL l a).length < l.length
  | [], _, h => absurd h List.not_mem_nil
  | x :: xs, a, h => by
    by_cases hxa : x = a
    · simp [afterL, hxa]
    · have ha : a ∈ xs := (List.mem_cons.mp h).resolve_left fun e => hxa e.symm
      have := length_afterL_lt ha
      simp only [afterL, hxa, ite_false, List.length_cons]; omega

/-- Fewer agents come after a later agent. -/
theorem afterL_lt_of_before : ∀ {l : List A}, l.Nodup → ∀ {a b : A}, Before l a b →
    (afterL l b).length < (afterL l a).length
  | [], _, _, _, h => h.elim
  | x :: xs, hnd, a, b, h => by
    have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
    rcases h with ⟨hax, hb⟩ | h
    · have hbx : x ≠ b := fun e => hx (e ▸ hb)
      have := length_afterL_lt hb
      simpa [afterL, hax, hbx] using this
    · have hxa : x ≠ a := fun e => hx (e ▸ (before_mem h).1)
      have hxb : x ≠ b := fun e => hx (e ▸ (before_mem h).2)
      have := afterL_lt_of_before (List.nodup_cons.mp hnd).2 h
      simpa [afterL, hxa, hxb] using this

/-! ## (B) Consecutive pairs -/

/-- `Consec R l`: every two consecutive elements of `l` are related by `R`. -/
def Consec (R : A → A → Prop) : List A → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => R a b ∧ Consec R (b :: t)

omit [DecidableEq A] in
theorem consec_iff_zip {R : A → A → Prop} : ∀ {l : List A}, Consec R l ↔ ∀ p ∈ l.zip l.tail, R p.1 p.2
  | [] => by simp [Consec]
  | [_] => by simp [Consec]
  | a :: b :: t => by
    rw [show Consec R (a :: b :: t) = (R a b ∧ Consec R (b :: t)) from rfl, consec_iff_zip]
    simp only [List.tail_cons, List.zip_cons_cons, List.forall_mem_cons]

omit [DecidableEq A] in
theorem consec_append_cons {R : A → A → Prop} {a : A} {m : List A} :
    ∀ {l : List A}, Consec R (l ++ [a]) → Consec R (a :: m) → Consec R (l ++ a :: m)
  | [], _, h => h
  | [_], h1, h2 => ⟨h1.1, h2⟩
  | _ :: y :: t, h1, h2 => ⟨h1.1, consec_append_cons (l := y :: t) h1.2 h2⟩

omit [DecidableEq A] in
theorem consec_split {R : A → A → Prop} {a : A} {m : List A} :
    ∀ {l : List A}, Consec R (l ++ a :: m) → Consec R (l ++ [a]) ∧ Consec R (a :: m)
  | [], h => ⟨trivial, h⟩
  | [_], h => ⟨⟨h.1, trivial⟩, h.2⟩
  | _ :: y :: t, h => ⟨⟨h.1, (consec_split (l := y :: t) h.2).1⟩, (consec_split (l := y :: t) h.2).2⟩

omit [DecidableEq A] in
/-- A list with at least two elements ends with two elements. -/
theorem exists_last_two : ∀ {l : List A} {z : A}, 2 ≤ l.length → l.getLast? = some z →
    ∃ pre p, l = pre ++ [p, z]
  | [], _, h, _ => by simp at h
  | [_], _, h, _ => by simp at h
  | [a, b], z, _, hz => ⟨[], a, by simp at hz; simp [hz]⟩
  | a :: b :: c :: t, z, _, hz => by
    rw [List.getLast?_cons_cons] at hz
    obtain ⟨pre, p, h⟩ := exists_last_two (l := b :: c :: t) (by simp) hz
    exact ⟨a :: pre, p, by rw [h]; rfl⟩

omit [DecidableEq A] in
theorem pair_last_two {p z : A} : ∀ {pre : List A}, (p, z) ∈ (pre ++ [p, z]).zip (pre ++ [p, z]).tail
  | [] => by simp
  | [_] => by simp
  | _ :: y :: t => by
    have := pair_last_two (p := p) (z := z) (pre := y :: t)
    simp only [List.cons_append, List.tail_cons, List.zip_cons_cons, List.mem_cons] at this ⊢
    exact Or.inr this

omit [DecidableEq A] in
theorem getLast?_append_cons {l m : List A} {a : A} : (l ++ a :: m).getLast? = (a :: m).getLast? := by
  simp [List.getLast?_append, List.getLast?_cons]

/-! ## (C) Canonical chains -/

section cchain
variable (v : A → G → Nat) (agents : List A) (Y : A → Option G)

/-- **A canonical chain** `ch = (x₀, …, x_t)`, `t ≥ 1` (`k4/oc1max_multi.md` §2): distinct listed agents, each
`x_i` (`i ≥ 1`) a wanter of `Y_{x_{i−1}}`, and the head `z = x_t` unfrozen at the picks. -/
structure CChain (ch : List A) : Prop where
  nodup : ch.Nodup
  mem : ∀ x ∈ ch, x ∈ agents
  tail_ne : ch.tail ≠ []
  wants : ∀ p ∈ ch.zip ch.tail, Wants v Y p.2 p.1
  last_unfrozen : ∀ z, ch.getLast? = some z → ¬ Frozen v agents (fun a => (Y a).toList) z

end cchain

section facts
variable {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A}

omit [DecidableEq A] [DecidableEq G] in
/-- At the picks, being frozen is being wanted. -/
theorem frozen_pick_iff {Y : A → Option G} {j : A} :
    Frozen v agents (fun a => (Y a).toList) j ↔ ∃ i ∈ agents, i ≠ j ∧ Wants v Y i j := by
  constructor
  · rintro ⟨g, hg, i, hi, hij, hlt⟩
    cases hY : Y j with
    | none => simp [hY] at hg
    | some y =>
      simp [hY] at hg; subst hg
      exact ⟨i, hi, hij, g, hY, by rwa [value_pick] at hlt⟩
  · rintro ⟨i, hi, hij, y, hy, hlt⟩
    exact ⟨y, by simp [hy], i, hi, hij, by rwa [value_pick]⟩

omit [DecidableEq A] [DecidableEq G] in
theorem ne_of_wants {Y : A → Option G} {a j : A} (h : Wants v Y a j) : a ≠ j := by
  rintro rfl
  obtain ⟨y, hy, hlt⟩ := h
  rw [mval_some hy] at hlt; omega

/-- (I2) A junk good of the picks is worth at most each agent's pick. -/
theorem junk_le_pick (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) {g : G} (hg : g ∈ goods)
    (hJ : ∀ x, sdPick v σ goods x ≠ some g) {i : A} (hi : i ∈ agents) : v i g ≤ mval v (sdPick v σ goods) i := by
  by_cases hpos : 0 < v i g
  · obtain ⟨y, hy, hle⟩ := sdPick_turn v σ goods (hσ.nodup_iff.mpr hag) hgd i (hσ.mem_iff.mpr hi) g hg
      (fun c _ => hJ c) hpos
    rw [mval_some hy]; exact hle
  · omega

/-- (π) An agent values the pick of a later agent at most its own pick. -/
theorem le_pick_of_before (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) {i j : A}
    (hij : Before σ i j) (hi : i ∈ agents) {g : G} (hj : sdPick v σ goods j = some g) :
    v i g ≤ mval v (sdPick v σ goods) i := by
  have hm := isMatching_sdPick (v := v) hσ hgd
  by_cases hpos : 0 < v i g
  · obtain ⟨y, hy, hle⟩ := sdPick_turn v σ goods (hσ.nodup_iff.mpr hag) hgd i (hσ.mem_iff.mpr hi) g
      (hm.mem j g hj).2.1 (fun c hc hcg => by
        rw [hm.inj c j g hcg hj] at hc
        exact before_asymm (hσ.nodup_iff.mpr hag) hij hc) hpos
    rw [mval_some hy]; exact hle
  · omega

/-- **A canonical chain in which `k` takes an improving set of junk goods is an official chain.** -/
theorem cchain_isChain (hσ : σ.Perm agents) {k : A} {rest : List A}
    (hch : CChain v agents (sdPick v σ goods) (k :: rest)) {H₀ : List G} (hH₀ : H₀.Nodup)
    (hH₀J : ∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ∀ x, sdPick v σ goods x ≠ some g)
    (himp : mval v (sdPick v σ goods) k < value v k H₀) :
    IsChain v agents goods (pickBase v goods σ) (afterE (sdPick v σ goods) k rest H₀) := by
  have hnd := hch.nodup
  have hk : k ∉ rest := (List.nodup_cons.mp hnd).1
  have hne : ∀ x ∈ rest, x ≠ k := fun x hx e => hk (e ▸ hx)
  refine ⟨k, rest, fun a => if a = k then H₀ else [], hch.tail_ne, hnd, hch.mem, fun x _ => ?_,
    fun x _ y _ hxy g hg hg' => ?_, fun g hg => ?_, fun x hx g hg => ?_, ?_, fun p hp => ?_, ?_,
    fun p hp => ?_, fun y hy => ?_⟩
  · by_cases hxk : x = k
    · subst hxk; simp only [ite_true]; exact ⟨hH₀, fun g hg => (hH₀J g hg).2.1⟩
    · simp [hxk]
  · by_cases hxk : x = k
    · have hyk : y ≠ k := fun e => hxy (hxk.trans e.symm)
      simp [hyk] at hg'
    · simp [hxk] at hg
  · simp only [ite_true] at hg
    obtain ⟨hgG, -, h⟩ := hH₀J g hg
    exact Or.inl ((mem_junkOf_pickBase hσ).mpr ⟨hgG, h⟩)
  · simp [hne x hx] at hg
  · simp only [ite_true]; rw [pickBase, value_pick]; exact himp
  · have hp2 : p.2 ∈ rest := (List.of_mem_zip hp).2
    obtain ⟨y, hy, hlt⟩ := hch.wants p hp
    simp only [hne p.2 hp2, ite_false, List.append_nil]
    refine ⟨by simp [pickBase, hy], ?_⟩
    rw [pickBase, pickBase, value_pick, hy]; simpa using hlt
  · simp [afterE]
  · have hp2 : p.2 ∈ rest := (List.of_mem_zip hp).2
    simp only [afterE, hne p.2 hp2, ite_false, List.append_nil, pickBase]
    rw [src_of_pair hnd (by simpa using hp)]
  · have hyk : y ≠ k := fun e => hy (e ▸ List.mem_cons_self)
    have hyr : y ∉ rest := fun h => hy (List.mem_cons_of_mem _ h)
    simp only [afterE, hyk, ite_false, pickBase]
    rw [src_of_not_tail (by simpa using hyr)]

/-- A canonical chain is increasing in `σ` (each wanter comes after the agent it wants). -/
theorem cchain_pairwise (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) {ch : List A}
    (hmem : ∀ x ∈ ch, x ∈ agents) (hw : ∀ p ∈ ch.zip ch.tail, Wants v (sdPick v σ goods) p.2 p.1) :
    ch.Pairwise (Before σ) :=
  pairwise_of_consecutive (hσ.nodup_iff.mpr hag) fun x hx =>
    before_of_wants hσ hag hgd (hmem _ (List.mem_of_mem_tail (List.of_mem_zip hx).2))
      (hmem _ (List.of_mem_zip hx).1) (ne_of_wants (hw x hx)) (hw x hx)

/-- **Walking up**: from any listed agent `w`, following a wanter of the current agent's pick until an agent
unfrozen at the picks is reached gives a walk `w :: ws`, increasing in `σ` (Hall's §21 Remark 2). -/
theorem exists_walk (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) :
    ∀ (n : Nat) (w : A), w ∈ agents → (afterL σ w).length ≤ n → ∃ ws : List A,
      (w :: ws).Pairwise (Before σ) ∧ (∀ x ∈ w :: ws, x ∈ agents) ∧
      Consec (fun a b => Wants v (sdPick v σ goods) b a) (w :: ws) ∧
      ∀ z, (w :: ws).getLast? = some z → ¬ Frozen v agents (fun a => (sdPick v σ goods a).toList) z := by
  have hσnd : σ.Nodup := hσ.nodup_iff.mpr hag
  have base : ∀ w : A, w ∈ agents → ¬ Frozen v agents (fun a => (sdPick v σ goods a).toList) w → ∃ ws : List A,
      (w :: ws).Pairwise (Before σ) ∧ (∀ x ∈ w :: ws, x ∈ agents) ∧
      Consec (fun a b => Wants v (sdPick v σ goods) b a) (w :: ws) ∧
      ∀ z, (w :: ws).getLast? = some z → ¬ Frozen v agents (fun a => (sdPick v σ goods a).toList) z :=
    fun w hw hf => ⟨[], List.pairwise_singleton _ _, by simpa using hw, trivial, fun z hz => by
      simp at hz; rw [← hz]; exact hf⟩
  intro n
  induction n with
  | zero =>
    intro w hw hn
    by_cases hf : Frozen v agents (fun a => (sdPick v σ goods a).toList) w
    · obtain ⟨i, hi, hiw, hwant⟩ := frozen_pick_iff.mp hf
      have := afterL_lt_of_before hσnd (before_of_wants hσ hag hgd hi hw hiw hwant)
      omega
    · exact base w hw hf
  | succ n ih =>
    intro w hw hn
    by_cases hf : Frozen v agents (fun a => (sdPick v σ goods a).toList) w
    · obtain ⟨i, hi, hiw, hwant⟩ := frozen_pick_iff.mp hf
      have hb := before_of_wants hσ hag hgd hi hw hiw hwant
      have := afterL_lt_of_before hσnd hb
      obtain ⟨ws, hpw, hmem, hcon, hlast⟩ := ih i hi (by omega)
      refine ⟨i :: ws, List.pairwise_cons.mpr ⟨fun c hc => ?_, hpw⟩, fun x hx => ?_, ⟨hwant, hcon⟩,
        fun z hz => hlast z (by rw [List.getLast?_cons_cons] at hz; exact hz)⟩
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact hb
        · exact before_trans hσnd hb ((List.pairwise_cons.mp hpw).1 c hc)
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hw
        · exact hmem x hx
    · exact base w hw hf

/-- **Lemma D1-chain**: an agent frozen at the picks starts a canonical chain. -/
theorem exists_cchain (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) {k : A} (hk : k ∈ agents)
    (hf : Frozen v agents (fun a => (sdPick v σ goods a).toList) k) :
    ∃ rest, CChain v agents (sdPick v σ goods) (k :: rest) := by
  obtain ⟨ws, hpw, hmem, hcon, hlast⟩ := exists_walk hσ hag hgd _ k hk (Nat.le_refl _)
  have hws : ws ≠ [] := by rintro rfl; exact hlast k rfl hf
  exact ⟨ws, ⟨nodup_of_pairwise_before (hσ.nodup_iff.mpr hag) hpw, hmem, hws, consec_iff_zip.mp hcon, hlast⟩⟩

/-- An agent frozen at the picks starts a **longest** canonical chain. -/
theorem exists_longest_cchain (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) {k : A}
    (hk : k ∈ agents) (hf : Frozen v agents (fun a => (sdPick v σ goods a).toList) k) :
    ∃ rest, CChain v agents (sdPick v σ goods) (k :: rest) ∧
      ∀ rest', CChain v agents (sdPick v σ goods) (k :: rest') → rest'.length ≤ rest.length :=
  exists_max_of_bdd (fun rest => CChain v agents (sdPick v σ goods) (k :: rest)) List.length agents.length
    (fun rest h => by
      have := h.nodup.length_le_of_subset (l₂ := agents) fun x hx => h.mem x hx
      simp only [List.length_cons] at this; omega)
    (exists_cchain hσ hag hgd hk hf)

omit [DecidableEq A] [DecidableEq G] in
theorem value_relevant_eq (i : A) : ∀ L : List G, value v i (relevant v i L) = value v i L
  | [] => rfl
  | a :: L => by
    have ih := value_relevant_eq i L
    by_cases hpos : 0 < v i a
    · have : relevant v i (a :: L) = a :: relevant v i L := by simp [relevant, hpos]
      rw [this, value_cons, value_cons, ih]
    · have : relevant v i (a :: L) = relevant v i L := by simp [relevant, hpos]
      rw [this, value_cons, ih]; omega

/-- If the junk threatens `k` at its pick value (`k` is truly dangerous), an improving set `H₀ ⊆ J ∩ R_k`
exists. -/
theorem exists_improving (hσ : σ.Perm agents) (hgd : goods.Nodup) {k : A}
    (hT : Threat v k (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) k)) :
    ∃ H₀ : List G, H₀.Nodup ∧ (∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ∀ x, sdPick v σ goods x ≠ some g) ∧
      mval v (sdPick v σ goods) k < value v k H₀ := by
  obtain ⟨x, -, hlt⟩ := hT
  have hJnd : (junkOf agents goods (pickBase v goods σ)).Nodup := hgd.sublist List.filter_sublist
  refine ⟨relevant v k ((junkOf agents goods (pickBase v goods σ)).erase x),
    (hJnd.sublist (List.erase_sublist)).sublist List.filter_sublist, fun g hg => ?_, ?_⟩
  · have hg' := (List.mem_filter.mp hg)
    have hgJ := (mem_junkOf_pickBase hσ).mp ((List.erase_sublist).subset hg'.1)
    exact ⟨hgJ.1, by simpa using hg'.2, hgJ.2⟩
  · rw [value_relevant_eq]; exact hlt

omit [DecidableEq A] in
theorem not_threat_of_length_le_one {i : A} {S : List G} {w : Nat} (h : S.length ≤ 1) : ¬ Threat v i S w := by
  rintro ⟨x, hx, hlt⟩
  have : (S.erase x).length = 0 := by rw [List.length_erase_of_mem hx]; omega
  rw [List.length_eq_zero_iff.mp this, value_nil] at hlt; omega

omit [DecidableEq A] [DecidableEq G] in
theorem length_toList_le (o : Option G) : o.toList.length ≤ 1 := by cases o <;> simp

omit [DecidableEq A] [DecidableEq G] in
theorem value_le_relevant_mul {i : A} {c : Nat} : ∀ {L : List G}, (∀ y ∈ L, v i y ≤ c) →
    value v i L ≤ (relevant v i L).length * c
  | [], _ => by simp
  | a :: L, h => by
    have ih := value_le_relevant_mul (L := L) fun y hy => h y (List.mem_cons_of_mem _ hy)
    have ha := h a List.mem_cons_self
    by_cases hpos : 0 < v i a
    · have : relevant v i (a :: L) = a :: relevant v i L := by simp [relevant, hpos]
      rw [value_cons, this, List.length_cons, Nat.succ_mul]; omega
    · have : relevant v i (a :: L) = relevant v i L := by simp [relevant, hpos]
      rw [value_cons, this]; omega

end facts

omit [DecidableEq G] in
theorem afterE_self (Y : A → Option G) (k : A) (rest : List A) (T : List G) : afterE Y k rest T k = T := by
  simp [afterE]

omit [DecidableEq G] in
theorem afterE_ne (Y : A → Option G) {k : A} (rest : List A) (T : List G) {a : A} (ha : a ≠ k) :
    afterE Y k rest T a = (Y (src (k :: rest) a)).toList := by
  simp [afterE, ha]

omit [DecidableEq G] in
theorem mem_afterE_ne (Y : A → Option G) {k : A} (rest : List A) (T : List G) {a : A} (ha : a ≠ k) {g : G} :
    g ∈ afterE Y k rest T a ↔ Y (src (k :: rest) a) = some g := by
  rw [afterE_ne Y rest T ha, Option.mem_toList]

/-! ## (D) The setting of the proof -/

/-- The setting of Theorem U's proof: a canonical chain `k :: rest = pre ++ [p, z]` at the picks of `σ`, and a set
`H₀ ⊆ J ∩ R_k` of junk goods improving for `k`. -/
structure USetting (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A) (k : A) (rest : List A)
    (H₀ : List G) (pre : List A) (p z : A) : Prop where
  perm : σ.Perm agents
  agents_nodup : agents.Nodup
  goods_nodup : goods.Nodup
  chain : CChain v agents (sdPick v σ goods) (k :: rest)
  dec : k :: rest = pre ++ [p, z]
  H₀_nodup : H₀.Nodup
  H₀_junk : ∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ∀ x, sdPick v σ goods x ≠ some g
  improving : mval v (sdPick v σ goods) k < value v k H₀

namespace USetting
variable {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A} {k : A} {rest : List A}
  {H₀ : List G} {pre : List A} {p z : A}

theorem sigma_nodup (hs : USetting v agents goods σ k rest H₀ pre p z) : σ.Nodup :=
  hs.perm.nodup_iff.mpr hs.agents_nodup

theorem matching (hs : USetting v agents goods σ k rest H₀ pre p z) :
    IsMatching v agents goods (sdPick v σ goods) := isMatching_sdPick hs.perm hs.goods_nodup

theorem k_not_rest (hs : USetting v agents goods σ k rest H₀ pre p z) : k ∉ rest :=
  (List.nodup_cons.mp hs.chain.nodup).1

theorem k_agent (hs : USetting v agents goods σ k rest H₀ pre p z) : k ∈ agents :=
  hs.chain.mem k List.mem_cons_self

theorem pz (hs : USetting v agents goods σ k rest H₀ pre p z) : (p, z) ∈ (k :: rest).zip rest := by
  have h := pair_last_two (p := p) (z := z) (pre := pre)
  rw [← hs.dec] at h; exact h

theorem last (hs : USetting v agents goods σ k rest H₀ pre p z) : (k :: rest).getLast? = some z := by
  rw [hs.dec]; simp

theorem getLast_eq (hs : USetting v agents goods σ k rest H₀ pre p z) :
    (k :: rest).getLast (List.cons_ne_nil k rest) = z := by
  have h := hs.last
  rw [List.getLast?_eq_some_getLast (List.cons_ne_nil k rest)] at h
  exact Option.some.inj h

theorem wants_zp (hs : USetting v agents goods σ k rest H₀ pre p z) : Wants v (sdPick v σ goods) z p :=
  hs.chain.wants (p, z) hs.pz

theorem z_mem (hs : USetting v agents goods σ k rest H₀ pre p z) : z ∈ rest := (List.of_mem_zip hs.pz).2

theorem z_mem' (hs : USetting v agents goods σ k rest H₀ pre p z) : z ∈ k :: rest :=
  List.mem_cons_of_mem _ hs.z_mem

theorem p_mem (hs : USetting v agents goods σ k rest H₀ pre p z) : p ∈ k :: rest := (List.of_mem_zip hs.pz).1

theorem z_agent (hs : USetting v agents goods σ k rest H₀ pre p z) : z ∈ agents := hs.chain.mem z hs.z_mem'

theorem p_agent (hs : USetting v agents goods σ k rest H₀ pre p z) : p ∈ agents := hs.chain.mem p hs.p_mem

theorem z_ne_k (hs : USetting v agents goods σ k rest H₀ pre p z) : z ≠ k := fun e => hs.k_not_rest (e ▸ hs.z_mem)

theorem z_ne_p (hs : USetting v agents goods σ k rest H₀ pre p z) : z ≠ p := ne_of_wants hs.wants_zp

theorem z_no_succ (hs : USetting v agents goods σ k rest H₀ pre p z) : ∀ q, (z, q) ∉ (k :: rest).zip rest := by
  intro q hq
  exact getLast_no_succ (List.cons_ne_nil k rest) hs.chain.nodup q (by rw [hs.getLast_eq]; exact hq)

theorem succ_of_ne_z (hs : USetting v agents goods σ k rest H₀ pre p z) {x : A} (hx : x ∈ k :: rest)
    (hxz : x ≠ z) : ∃ s, (x, s) ∈ (k :: rest).zip rest :=
  exists_succ_of_ne_getLast (List.cons_ne_nil k rest) hx (by rw [hs.getLast_eq]; exact hxz)

theorem pairwise (hs : USetting v agents goods σ k rest H₀ pre p z) : (k :: rest).Pairwise (Before σ) :=
  cchain_pairwise hs.perm hs.agents_nodup hs.goods_nodup hs.chain.mem hs.chain.wants

/-- Every agent of the chain other than its last two comes before `p` (the head's predecessor). -/
theorem before_p (hs : USetting v agents goods σ k rest H₀ pre p z) {x : A} (hx : x ∈ k :: rest) (hxp : x ≠ p)
    (hxz : x ≠ z) : Before σ x p := by
  have h := hs.pairwise
  rw [hs.dec] at h hx
  obtain ⟨-, -, hcross⟩ := List.pairwise_append.mp h
  have hxpre : x ∈ pre := by
    rcases List.mem_append.mp hx with h | h
    · exact h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · exact absurd h hxp
      · exact absurd h hxz
  exact hcross x hxpre p (by simp)

theorem after_pair (hs : USetting v agents goods σ k rest H₀ pre p z) {q r : A}
    (h : (q, r) ∈ (k :: rest).zip rest) : afterE (sdPick v σ goods) k rest H₀ r = (sdPick v σ goods q).toList := by
  have hr : r ∈ rest := (List.of_mem_zip h).2
  have hrk : r ≠ k := fun e => hs.k_not_rest (e ▸ hr)
  rw [afterE_ne _ rest H₀ hrk, src_of_pair hs.chain.nodup h]

theorem after_off (_hs : USetting v agents goods σ k rest H₀ pre p z) {a : A} (ha : a ∉ k :: rest) :
    afterE (sdPick v σ goods) k rest H₀ a = (sdPick v σ goods a).toList := by
  have hak : a ≠ k := fun e => ha (e ▸ List.mem_cons_self)
  have har : a ∉ rest := fun h => ha (List.mem_cons_of_mem _ h)
  rw [afterE_ne _ rest H₀ hak, src_of_not_tail har]

theorem after_z (hs : USetting v agents goods σ k rest H₀ pre p z) :
    afterE (sdPick v σ goods) k rest H₀ z = (sdPick v σ goods p).toList := hs.after_pair hs.pz

/-- Values rise strictly along the chain. -/
theorem value_lt (hs : USetting v agents goods σ k rest H₀ pre p z) {i : A} (hi : i ∈ k :: rest) :
    mval v (sdPick v σ goods) i < value v i (afterE (sdPick v σ goods) k rest H₀ i) := by
  rcases List.mem_cons.mp hi with rfl | hi
  · rw [afterE_self]; exact hs.improving
  · obtain ⟨q, hq⟩ := mem_tail_iff_pair.mp (show i ∈ (k :: rest).tail from hi)
    obtain ⟨y, hy, hlt⟩ := hs.chain.wants (q, i) hq
    rw [hs.after_pair hq, hy]; simpa using hlt

/-- Values never fall. -/
theorem value_le (hs : USetting v agents goods σ k rest H₀ pre p z) (i : A) :
    mval v (sdPick v σ goods) i ≤ value v i (afterE (sdPick v σ goods) k rest H₀ i) := by
  by_cases hi : i ∈ k :: rest
  · exact Nat.le_of_lt (hs.value_lt hi)
  · rw [hs.after_off hi, value_pick]; exact Nat.le_refl _

theorem src_inj (hs : USetting v agents goods σ k rest H₀ pre p z) {i j : A} (hik : i ≠ k) (hjk : j ≠ k)
    (h : src (k :: rest) i = src (k :: rest) j) : i = j := by
  have hnd := hs.chain.nodup
  have key : ∀ {a : A}, a ≠ k → ((src (k :: rest) a, a) ∈ (k :: rest).zip rest) ∨
      (a ∉ k :: rest ∧ src (k :: rest) a = a) := by
    intro a hak
    by_cases har : a ∈ rest
    · obtain ⟨q, hq⟩ := mem_tail_iff_pair.mp (show a ∈ (k :: rest).tail from har)
      exact Or.inl (by rw [src_of_pair hnd hq]; exact hq)
    · exact Or.inr ⟨fun hm => (List.mem_cons.mp hm).elim hak har, src_of_not_tail har⟩
  rcases key hik with hpi | ⟨hi, hsi⟩ <;> rcases key hjk with hpj | ⟨hj, hsj⟩
  · rw [h] at hpi; exact zip_tail_fst_unique hnd hpi hpj
  · exact absurd (List.of_mem_zip hpi).1 (by rw [h, hsj]; exact hj)
  · exact absurd (List.of_mem_zip hpj).1 (by rw [← h, hsi]; exact hi)
  · exact hsi.symm.trans (h.trans hsj)

/-- The state after the chain is a valid state. -/
theorem validState (hs : USetting v agents goods σ k rest H₀ pre p z) :
    ValidState agents goods (afterE (sdPick v σ goods) k rest H₀) := by
  have hm := hs.matching
  refine ⟨fun i _ => ?_, fun i _ j _ hij g hgi hgj => ?_⟩
  · by_cases hik : i = k
    · rw [hik, afterE_self]; exact ⟨hs.H₀_nodup, fun g hg => (hs.H₀_junk g hg).1⟩
    · rw [afterE_ne _ rest H₀ hik]
      cases hy : sdPick v σ goods (src (k :: rest) i) with
      | none => simp
      | some y => simp only [Option.toList_some, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
          List.nodup_nil, and_self, List.mem_cons, or_false, forall_eq, true_and]; exact (hm.mem _ y hy).2.1
  · by_cases hik : i = k
    · rw [hik, afterE_self] at hgi
      have hjk : j ≠ k := fun e => hij (hik.trans e.symm)
      exact (hs.H₀_junk g hgi).2.2 _ ((mem_afterE_ne _ rest H₀ hjk).mp hgj)
    · by_cases hjk : j = k
      · rw [hjk, afterE_self] at hgj
        exact (hs.H₀_junk g hgj).2.2 _ ((mem_afterE_ne _ rest H₀ hik).mp hgi)
      · exact hij (hs.src_inj hik hjk (hm.inj _ _ g ((mem_afterE_ne _ rest H₀ hik).mp hgi)
          ((mem_afterE_ne _ rest H₀ hjk).mp hgj)))

/-- **The junk after the chain** is `(J ∖ H₀) ∪ {Y_z}`. -/
theorem mem_junk (hs : USetting v agents goods σ k rest H₀ pre p z) {g : G} :
    g ∈ junkOf agents goods (afterE (sdPick v σ goods) k rest H₀) ↔
      g ∈ goods ∧ g ∉ H₀ ∧ ((∀ x, sdPick v σ goods x ≠ some g) ∨ sdPick v σ goods z = some g) := by
  have hm := hs.matching
  rw [mem_junkOf]
  constructor
  · rintro ⟨hg, hno⟩
    refine ⟨hg, fun h => hno k hs.k_agent (by rw [afterE_self]; exact h), ?_⟩
    by_cases hall : ∀ x, sdPick v σ goods x ≠ some g
    · exact Or.inl hall
    · refine Or.inr ?_
      obtain ⟨x, hx⟩ : ∃ x, sdPick v σ goods x = some g :=
        Classical.byContradiction fun hne => hall fun x hx => hne ⟨x, hx⟩
      have hxa := (hm.mem x g hx).1
      by_cases hxc : x ∈ k :: rest
      · by_cases hxz : x = z
        · rw [← hxz]; exact hx
        · obtain ⟨s, hsx⟩ := hs.succ_of_ne_z hxc hxz
          have hsr : s ∈ rest := (List.of_mem_zip hsx).2
          exact (hno s (hs.chain.mem s (List.mem_cons_of_mem _ hsr)) (by rw [hs.after_pair hsx, hx]; simp)).elim
      · exact (hno x hxa (by rw [hs.after_off hxc, hx]; simp)).elim
  · rintro ⟨hg, hH, hor⟩
    refine ⟨hg, fun i _ hgi => ?_⟩
    by_cases hik : i = k
    · rw [hik, afterE_self] at hgi; exact hH hgi
    · have hy := (mem_afterE_ne _ rest H₀ hik).mp hgi
      rcases hor with hall | hz
      · exact hall _ hy
      · have hsz : src (k :: rest) i = z := hm.inj _ _ g hy hz
        by_cases hir : i ∈ rest
        · obtain ⟨q, hq⟩ := mem_tail_iff_pair.mp (show i ∈ (k :: rest).tail from hir)
          rw [src_of_pair hs.chain.nodup hq] at hsz
          exact hs.z_no_succ i (by rw [← hsz]; exact hq)
        · rw [src_of_not_tail hir] at hsz
          exact hir (by rw [hsz]; exact hs.z_mem)

/-- With `H = {Y_z}` kept out, the owner's set after the chain is the junk `J` of the picks. -/
theorem mem_ownerSet_iff (hs : USetting v agents goods σ k rest H₀ pre p z) {yz : G}
    (hyz : sdPick v σ goods z = some yz) {g : G} :
    g ∈ ownerSet agents goods (afterE (sdPick v σ goods) k rest H₀) k [yz] ↔
      g ∈ junkOf agents goods (pickBase v goods σ) := by
  rw [mem_ownerSet, afterE_self, hs.mem_junk, mem_junkOf_pickBase hs.perm]
  constructor
  · rintro (h | ⟨⟨hg, -, hor⟩, hne⟩)
    · exact ⟨(hs.H₀_junk g h).1, (hs.H₀_junk g h).2.2⟩
    · refine ⟨hg, hor.resolve_right fun h => hne ?_⟩
      rw [hyz] at h
      exact List.mem_singleton.mpr (Option.some.inj h).symm
  · rintro ⟨hg, hall⟩
    by_cases hH : g ∈ H₀
    · exact Or.inl hH
    · refine Or.inr ⟨⟨hg, hH, Or.inl hall⟩, fun h => ?_⟩
      exact hall z (by rw [hyz, List.mem_singleton.mp h])

theorem threat_iff (hs : USetting v agents goods σ k rest H₀ pre p z) {yz : G}
    (hyz : sdPick v σ goods z = some yz) {i : A} {w : Nat} :
    Threat v i (ownerSet agents goods (afterE (sdPick v σ goods) k rest H₀) k [yz]) w ↔
      Threat v i (junkOf agents goods (pickBase v goods σ)) w :=
  threat_congr (nodup_ownerSet hs.k_agent hs.validState hs.goods_nodup _)
    (hs.goods_nodup.sublist List.filter_sublist) fun _ => hs.mem_ownerSet_iff hyz

/-- **The count of Lemma KEEP**: with `|R_z| ≤ 4`, `v_z(J) ≤ 2 p_z ≤ v_z(a) + p_z`, where `a = Y_p` is the head's
new good. -/
theorem keep (hs : USetting v agents goods σ k rest H₀ pre p z) (hrel : (relevant v z goods).length ≤ 4)
    {a yz : G} (ha : sdPick v σ goods p = some a) (hyz : sdPick v σ goods z = some yz) :
    value v z (junkOf agents goods (pickBase v goods σ)) ≤ v z a + v z yz := by
  have hm := hs.matching
  have hJ : ∀ g ∈ junkOf agents goods (pickBase v goods σ), g ∈ goods ∧ ∀ x, sdPick v σ goods x ≠ some g :=
    fun g hg => (mem_junkOf_pickBase hs.perm).mp hg
  have hJnd : (junkOf agents goods (pickBase v goods σ)).Nodup := hs.goods_nodup.sublist List.filter_sublist
  have hle : ∀ y ∈ junkOf agents goods (pickBase v goods σ), v z y ≤ v z yz := fun y hy => by
    have := junk_le_pick hs.perm hs.agents_nodup hs.goods_nodup (hJ y hy).1 (hJ y hy).2 hs.z_agent
    rwa [mval_some hyz] at this
  have hval := value_le_relevant_mul (i := z) hle
  obtain ⟨a', ha', hlt⟩ := hs.wants_zp
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  rw [mval_some hyz] at hlt
  have hcount : (relevant v z (junkOf agents goods (pickBase v goods σ))).length ≤ 2 := by
    have hnd : (a' :: yz :: relevant v z (junkOf agents goods (pickBase v goods σ))).Nodup := by
      refine List.nodup_cons.mpr ⟨fun h => ?_, List.nodup_cons.mpr ⟨fun h => ?_, hJnd.sublist List.filter_sublist⟩⟩
      · rcases List.mem_cons.mp h with h | h
        · exact hs.z_ne_p (hm.inj z p yz hyz (by rw [← h]; exact ha'))
        · exact (hJ a' (mem_relevant.mp h).1).2 p ha'
      · exact (hJ yz (mem_relevant.mp h).1).2 z hyz
    have hsub : a' :: yz :: relevant v z (junkOf agents goods (pickBase v goods σ)) ⊆ relevant v z goods := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact mem_relevant.mpr ⟨(hm.mem p g ha').2.1, by omega⟩
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact mem_relevant.mpr ⟨(hm.mem z g hyz).2.1, (hm.mem z g hyz).2.2⟩
        · exact mem_relevant.mpr ⟨(hJ g (mem_relevant.mp hg).1).1, (mem_relevant.mp hg).2⟩
    have := hnd.length_le_of_subset hsub
    simp only [List.length_cons] at this; omega
  have : (relevant v z (junkOf agents goods (pickBase v goods σ))).length * v z yz ≤ 2 * v z yz :=
    Nat.mul_le_mul_right _ hcount
  omega

/-- **Step 1 of the proof, the second wanter.** If the head `z` is frozen after a *longest* canonical chain, its new
good `a = Y_p` has a wanter `w` that is off the chain, wanted `a` at the picks, and is unfrozen at the picks
(otherwise the walk up from `w` would give a longer canonical chain). -/
theorem wanter_of_frozen (hs : USetting v agents goods σ k rest H₀ pre p z)
    (hlong : ∀ rest', CChain v agents (sdPick v σ goods) (k :: rest') → rest'.length ≤ rest.length)
    (hf : Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z) :
    ∃ w ∈ agents, w ∉ k :: rest ∧ Wants v (sdPick v σ goods) w p ∧
      ¬ Frozen v agents (fun a => (sdPick v σ goods a).toList) w := by
  obtain ⟨g, hg, w, hw, hwz, hlt⟩ := hf
  rw [hs.after_z] at hg
  obtain ⟨a, ha, -⟩ := hs.wants_zp
  rw [ha] at hg
  obtain rfl : g = a := by simpa using hg
  have hwc : w ∉ k :: rest := by
    intro hwc
    have hv := hs.value_lt hwc
    by_cases hwp : w = p
    · rw [hwp] at hv hlt; rw [mval_some ha] at hv; omega
    · have := le_pick_of_before hs.perm hs.agents_nodup hs.goods_nodup (hs.before_p hwc hwp hwz) hw ha
      omega
  rw [hs.after_off hwc, value_pick] at hlt
  have hwant : Wants v (sdPick v σ goods) w p := ⟨g, ha, hlt⟩
  refine ⟨w, hw, hwc, hwant, fun hfw => ?_⟩
  have hσnd := hs.sigma_nodup
  obtain ⟨ws, hpw, hmem, hcon, hlast⟩ := exists_walk hs.perm hs.agents_nodup hs.goods_nodup _ w hw (Nat.le_refl _)
  have hws : ws ≠ [] := by rintro rfl; exact hlast w rfl hfw
  have hwp : w ≠ p := fun e => hwc (e ▸ hs.p_mem)
  -- the longer chain `pre ++ p :: w :: ws`
  obtain ⟨rest', hrest'⟩ : ∃ rest', k :: rest' = pre ++ p :: w :: ws := by
    have hd := hs.dec
    cases pre with
    | nil => exact ⟨w :: ws, by simp at hd; simp [hd.1]⟩
    | cons x pre' => exact ⟨pre' ++ p :: w :: ws, by simp at hd; simp [hd.1]⟩
  have hpw0 := hs.pairwise
  rw [hs.dec] at hpw0
  obtain ⟨hpre, -, hcross⟩ := List.pairwise_append.mp hpw0
  have hpwb : Before σ p w := before_of_wants hs.perm hs.agents_nodup hs.goods_nodup hw hs.p_agent hwp hwant
  have hpw' : (p :: w :: ws).Pairwise (Before σ) := by
    refine List.pairwise_cons.mpr ⟨fun c hc => ?_, hpw⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hpwb
    · exact before_trans hσnd hpwb ((List.pairwise_cons.mp hpw).1 c hc)
  have hall : (pre ++ p :: w :: ws).Pairwise (Before σ) := by
    refine List.pairwise_append.mpr ⟨hpre, hpw', fun x hx c hc => ?_⟩
    have hxp : Before σ x p := hcross x hx p (by simp)
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hxp
    · exact before_trans hσnd hxp ((List.pairwise_cons.mp hpw').1 c hc)
  have hcon0 : Consec (fun a b => Wants v (sdPick v σ goods) b a) (pre ++ p :: [z]) := by
    have := hs.chain.wants
    rw [hs.dec] at this
    exact consec_iff_zip.mpr this
  have hnew : CChain v agents (sdPick v σ goods) (k :: rest') := by
    rw [hrest']
    refine ⟨nodup_of_pairwise_before hσnd hall, fun x hx => ?_, ?_,
      consec_iff_zip.mp (consec_append_cons (m := w :: ws) (consec_split hcon0).1
        (show Consec (fun a b => Wants v (sdPick v σ goods) b a) (p :: w :: ws) from ⟨hwant, hcon⟩)), fun y hy => ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact hs.chain.mem x (by rw [hs.dec]; exact List.mem_append_left _ hx)
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hs.p_agent
        · exact hmem x hx
    · cases pre <;> simp
    · rw [getLast?_append_cons, List.getLast?_cons_cons] at hy
      exact hlast y hy
  have h1 := congrArg List.length hrest'
  have h2 := congrArg List.length hs.dec
  simp only [List.length_cons, List.length_append, List.length_nil] at h1 h2
  have h3 : 0 < ws.length := List.length_pos_iff.mpr hws
  have := hlong rest' hnew
  omega

end USetting

theorem exists_setting {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A} (hσ : σ.Perm agents)
    (hag : agents.Nodup) (hgd : goods.Nodup) {k : A} {rest : List A}
    (hch : CChain v agents (sdPick v σ goods) (k :: rest)) {z : A} (hz : (k :: rest).getLast? = some z)
    {H₀ : List G} (hH₀ : H₀.Nodup) (hH₀J : ∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ∀ x, sdPick v σ goods x ≠ some g)
    (himp : mval v (sdPick v σ goods) k < value v k H₀) :
    ∃ pre p, USetting v agents goods σ k rest H₀ pre p z := by
  have h2 : 2 ≤ (k :: rest).length := by
    have := hch.tail_ne
    cases rest with
    | nil => exact absurd rfl this
    | cons _ _ => simp
  obtain ⟨pre, p, hdec⟩ := exists_last_two h2 hz
  exact ⟨pre, p, hσ, hag, hgd, hch, hdec, hH₀, hH₀J, himp⟩

/-! ## (E) Theorem U -/

section thmU
variable {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A}

/-- **Theorem U** (K4.MULTI.U, `k4/oc1max_multi.md` §3), in the form the proof uses. Let `Y` be the picks of `σ`, a
perfect start, with at most four relevant goods per agent; `k :: rest` a longest canonical chain from `k` with head
`z`; and `H₀ ⊆ J ∩ R_k` improving for `k`. Suppose the junk `J` threatens no agent other than `k` and `z` at its
pick value, and that if `J` threatens `z` at its pick value, then `z` is unfrozen after the chain. Then the state
after the chain has an S\* completion owned by `k`.

The note's hypotheses `D_T = {k}` and `E_J ⊆ {z}` give the first condition (`thmU_of_DT`): a frozen agent other
than `k` is not truly dangerous, an unfrozen pick holder other than `z` is not in `E_J`, and a pickless agent at a
perfect start values nothing. Strict values and the absence of a one-absorber completion at the picks are not
needed. -/
theorem thmU (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hrel : ∀ i ∈ agents, (relevant v i goods).length ≤ 4)
    (hperf : PerfectStart v agents goods (sdPick v σ goods))
    {k : A} {rest : List A} (hch : CChain v agents (sdPick v σ goods) (k :: rest))
    (hlong : ∀ rest', CChain v agents (sdPick v σ goods) (k :: rest') → rest'.length ≤ rest.length)
    {z : A} (hz : (k :: rest).getLast? = some z)
    {H₀ : List G} (hH₀ : H₀.Nodup) (hH₀J : ∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ∀ x, sdPick v σ goods x ≠ some g)
    (himp : mval v (sdPick v σ goods) k < value v k H₀)
    (hJ : ∀ i ∈ agents, i ≠ k → i ≠ z →
      ¬ Threat v i (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) i))
    (hZ : Threat v z (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) z) →
      ¬ Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z) :
    SStar v agents goods (afterE (sdPick v σ goods) k rest H₀) k := by
  obtain ⟨pre, p, hs⟩ := exists_setting hσ hag hgd hch hz hH₀ hH₀J himp
  have hm := hs.matching
  have hk := hs.k_agent
  obtain ⟨a, ha, hza⟩ := hs.wants_zp
  obtain ⟨yz, hyz⟩ : ∃ yz, sdPick v σ goods z = some yz :=
    Option.isSome_iff_exists.mp (hperf z hs.z_agent ⟨a, (hm.mem p a ha).2.1, by omega⟩)
  have hB'z : afterE (sdPick v σ goods) k rest H₀ z = [a] := by rw [hs.after_z, ha]; rfl
  have hst := hs.validState
  -- `J` threatens nobody other than `k` and `z` after the chain
  have hno : ∀ q ∈ agents, q ≠ k → q ≠ z → ¬ Threat v q
      (ownerSet agents goods (afterE (sdPick v σ goods) k rest H₀) k [yz])
      (value v q (afterE (sdPick v σ goods) k rest H₀ q)) := fun q hq hqk hqz h =>
    not_threat_mono (hJ q hq hqk hqz) (hs.value_le q) ((hs.threat_iff hyz).mp h)
  -- (G1)
  have hG1 : G1 v agents (afterE (sdPick v σ goods) k rest H₀) k := fun j _ hjk _ _ _ _ =>
    not_threat_of_length_le_one (by rw [afterE_ne _ rest H₀ hjk]; exact length_toList_le _)
  -- (G2)
  have hG2 : G2 v agents goods (afterE (sdPick v σ goods) k rest H₀) := by
    intro g hg i hi
    obtain ⟨hgG, -, hor⟩ := hs.mem_junk.mp hg
    rcases hor with hall | hzg
    · exact Nat.le_trans (junk_le_pick hσ hag hgd hgG hall hi) (hs.value_le i)
    · have hg' : g = yz := Option.some.inj (hzg.symm.trans hyz)
      rw [hg']
      by_cases hiz : i = z
      · rw [hiz]
        have := hs.value_lt hs.z_mem'
        rw [mval_some hyz] at this; omega
      · have hun := hch.last_unfrozen z hz
        have hle : v i yz ≤ mval v (sdPick v σ goods) i := Nat.le_of_not_lt fun hlt =>
          hun (frozen_pick_iff.mpr ⟨i, hi, hiz, yz, hyz, hlt⟩)
        exact Nat.le_trans hle (hs.value_le i)
  -- (H1)
  have hH1 : H1 v agents goods (afterE (sdPick v σ goods) k rest H₀) k [yz] := by
    intro q hq hqk hqh
    by_cases hqz : q = z
    · rw [hqz] at hqh ⊢
      intro h
      have hzJ : ¬ Threat v z (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) z) :=
        fun h' => hqh ⟨hZ h', by rw [hB'z]; simp⟩
      exact not_threat_mono hzJ (hs.value_le z) ((hs.threat_iff hyz).mp h)
    · exact hno q hq hqk hqz
  -- `H = {Y_z}` lies in the junk after the chain
  have hyzJ : yz ∈ junkOf agents goods (afterE (sdPick v σ goods) k rest H₀) :=
    hs.mem_junk.mpr ⟨(hm.mem z yz hyz).2.1, fun h => (hH₀J yz h).2.2 z hyz, Or.inr hyz⟩
  have hHJ : ∀ h ∈ [yz], h ∈ junkOf agents goods (afterE (sdPick v σ goods) k rest H₀) := fun h hh => by
    rw [List.mem_singleton.mp hh]; exact hyzJ
  have hinj : ∀ (m : G → A), ∀ h ∈ [yz], ∀ h' ∈ [yz], m h = m h' → h = h' := fun _ h hh h' hh' _ =>
    (List.mem_singleton.mp hh).trans (List.mem_singleton.mp hh').symm
  by_cases hzf : Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z
  · -- the receiver of `Y_z` is an unfrozen second wanter `w` of `a`
    obtain ⟨w, hw, hwc, -, hwun⟩ := hs.wanter_of_frozen hlong hzf
    have hwk : w ≠ k := fun e => hwc (e ▸ List.mem_cons_self)
    have hwz : w ≠ z := fun e => hwc (e ▸ hs.z_mem')
    have hwB : ¬ Frozen v agents (afterE (sdPick v σ goods) k rest H₀) w := by
      rintro ⟨g, hg, i, hi, hiw, hlt⟩
      rw [hs.after_off hwc, Option.mem_toList] at hg
      exact hwun (frozen_pick_iff.mpr ⟨i, hi, hiw, g, hg, Nat.lt_of_le_of_lt (hs.value_le i) hlt⟩)
    have hwE : ¬ Exposed v agents goods (afterE (sdPick v σ goods) k rest H₀) k [yz] w := fun h =>
      hno w hw hwk hwz h
    refine sStar_of_slotMatching hgd hst hk hG1 hG2 hHJ hH1 (m := fun _ => w)
      ⟨fun _ _ => ⟨hw, hwk, ⟨hwB, by rw [hs.after_off hwc]; exact length_toList_le _⟩, Or.inl hwE⟩,
        hinj _, fun u hu huk hhu hex => ?_⟩
    by_cases huz : u = z
    · rw [huz] at hhu; exact absurd hzf hhu.1
    · exact absurd hex (hno u hu huk huz)
  · -- the receiver of `Y_z` is the head `z` itself (Lemma KEEP's count)
    have hEdge : Edge v agents goods (afterE (sdPick v σ goods) k rest H₀) k [yz] yz z := by
      refine Or.inr ⟨(hm.mem z yz hyz).2.2, ?_⟩
      rw [hs.threat_iff hyz, hB'z]
      refine not_threat_of_value_le ?_
      have := hs.keep (hrel z hs.z_agent) ha hyz
      simp only [value_cons, value_nil]; omega
    refine sStar_of_slotMatching hgd hst hk hG1 hG2 hHJ hH1 (m := fun _ => z)
      ⟨fun h hh => ?_, hinj _, fun u hu huk _ hex => ?_⟩
    · rw [List.mem_singleton.mp hh]
      exact ⟨hs.z_agent, hs.z_ne_k, ⟨hzf, by rw [hB'z]; simp⟩, hEdge⟩
    · by_cases huz : u = z
      · exact ⟨yz, List.mem_singleton_self _, huz.symm⟩
      · exact absurd hex (hno u hu huk huz)

/-- **Theorem U, as a repair**: the chain is one move, and the state after it has a one-absorber completion. -/
theorem thmU_oc1 (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hrel : ∀ i ∈ agents, (relevant v i goods).length ≤ 4)
    (hperf : PerfectStart v agents goods (sdPick v σ goods))
    {k : A} {rest : List A} (hch : CChain v agents (sdPick v σ goods) (k :: rest))
    (hlong : ∀ rest', CChain v agents (sdPick v σ goods) (k :: rest') → rest'.length ≤ rest.length)
    {z : A} (hz : (k :: rest).getLast? = some z)
    {H₀ : List G} (hH₀ : H₀.Nodup) (hH₀J : ∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ∀ x, sdPick v σ goods x ≠ some g)
    (himp : mval v (sdPick v σ goods) k < value v k H₀)
    (hJ : ∀ i ∈ agents, i ≠ k → i ≠ z →
      ¬ Threat v i (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) i))
    (hZ : Threat v z (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) z) →
      ¬ Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z) :
    OneMove v agents goods (pickBase v goods σ) (afterE (sdPick v σ goods) k rest H₀) ∧
      OneAbsorber v agents goods (afterE (sdPick v σ goods) k rest H₀) :=
  ⟨Or.inr (Or.inl (cchain_isChain hσ hch hH₀ hH₀J himp)),
    oneAbsorber_of_sStar (thmU hσ hag hgd hrel hperf hch hlong hz hH₀ hH₀J himp hJ hZ)⟩

/-- **Theorem U in the note's terms.** `D_T ⊆ {k}`: no agent frozen at the picks other than `k` is threatened by `J`
at its pick value (an agent of `F ∖ D` values no junk, so it never is). `E_J ⊆ {z}`: no unfrozen pick holder other
than `z` is threatened by `J` at its pick value. If `z ∈ E_J`, then `z` is unfrozen after the chain. -/
theorem thmU_of_DT (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hrel : ∀ i ∈ agents, (relevant v i goods).length ≤ 4)
    (hperf : PerfectStart v agents goods (sdPick v σ goods))
    {k : A} {rest : List A} (hch : CChain v agents (sdPick v σ goods) (k :: rest))
    (hlong : ∀ rest', CChain v agents (sdPick v σ goods) (k :: rest') → rest'.length ≤ rest.length)
    {z : A} (hz : (k :: rest).getLast? = some z)
    {H₀ : List G} (hH₀ : H₀.Nodup) (hH₀J : ∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ∀ x, sdPick v σ goods x ≠ some g)
    (himp : mval v (sdPick v σ goods) k < value v k H₀)
    (hDT : ∀ d ∈ agents, d ≠ k → Frozen v agents (pickBase v goods σ) d →
      ¬ Threat v d (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) d))
    (hEJ : ∀ u ∈ agents, (sdPick v σ goods u).isSome → ¬ Frozen v agents (pickBase v goods σ) u → u ≠ z →
      ¬ Threat v u (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) u))
    (hZ : Threat v z (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) z) →
      ¬ Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z) :
    SStar v agents goods (afterE (sdPick v σ goods) k rest H₀) k := by
  refine thmU hσ hag hgd hrel hperf hch hlong hz hH₀ hH₀J himp (fun i hi hik hiz => ?_) hZ
  by_cases hf : Frozen v agents (pickBase v goods σ) i
  · exact hDT i hi hik hf
  · cases hY : sdPick v σ goods i with
    | some y => exact hEJ i hi (by simp [hY]) hf hiz
    | none =>
      have hnull : ∀ g ∈ junkOf agents goods (pickBase v goods σ), v i g = 0 := fun g hg =>
        Nat.eq_zero_of_not_pos fun hpos => by
          have := hperf i hi ⟨g, (mem_junkOf.mp hg).1, hpos⟩
          simp [hY] at this
      exact not_threat_of_value_le (by rw [value_eq_zero_of_forall hnull]; exact Nat.zero_le _)

/-- **Corollary U1** (K4.MULTI.U1): at a perfect start with at most one unfrozen pick holder, if no frozen agent
other than `k` is threatened by `J` at its pick value, then every longest canonical chain from `k` with every
improving `H₀ ⊆ J ∩ R_k` repairs: the state after it has an S\* completion owned by `k`. -/
theorem thmU1 (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hrel : ∀ i ∈ agents, (relevant v i goods).length ≤ 4)
    (hperf : PerfectStart v agents goods (sdPick v σ goods))
    {k : A}
    (hDT : ∀ d ∈ agents, d ≠ k → Frozen v agents (pickBase v goods σ) d →
      ¬ Threat v d (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) d))
    (hone : ∀ u ∈ agents, ∀ u' ∈ agents, (sdPick v σ goods u).isSome → ¬ Frozen v agents (pickBase v goods σ) u →
      (sdPick v σ goods u').isSome → ¬ Frozen v agents (pickBase v goods σ) u' → u = u')
    {rest : List A} (hch : CChain v agents (sdPick v σ goods) (k :: rest))
    (hlong : ∀ rest', CChain v agents (sdPick v σ goods) (k :: rest') → rest'.length ≤ rest.length)
    {H₀ : List G} (hH₀ : H₀.Nodup) (hH₀J : ∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ∀ x, sdPick v σ goods x ≠ some g)
    (himp : mval v (sdPick v σ goods) k < value v k H₀) :
    SStar v agents goods (afterE (sdPick v σ goods) k rest H₀) k := by
  obtain ⟨z, hz⟩ : ∃ z, (k :: rest).getLast? = some z :=
    ⟨_, List.getLast?_eq_some_getLast (List.cons_ne_nil k rest)⟩
  obtain ⟨pre, p, hs⟩ := exists_setting hσ hag hgd hch hz hH₀ hH₀J himp
  have hm := hs.matching
  -- the head is an unfrozen pick holder
  obtain ⟨a, ha, hza⟩ := hs.wants_zp
  have hzY : (sdPick v σ goods z).isSome := hperf z hs.z_agent ⟨a, (hm.mem p a ha).2.1, by omega⟩
  have hzun : ¬ Frozen v agents (pickBase v goods σ) z := hch.last_unfrozen z hz
  refine thmU_of_DT hσ hag hgd hrel hperf hch hlong hz hH₀ hH₀J himp hDT
    (fun u hu hY hf huz => absurd (hone u hu z hs.z_agent hY hf hzY hzun) huz) (fun _ hzf => ?_)
  obtain ⟨w, hw, hwc, ⟨b, hb, hwb⟩, hwun⟩ := hs.wanter_of_frozen hlong hzf
  have hwY : (sdPick v σ goods w).isSome := hperf w hw ⟨b, (hm.mem p b hb).2.1, by omega⟩
  exact hwc (hone w hw z hs.z_agent hwY hwun hzY hzun ▸ hs.z_mem')

/-- **Corollary U1, as OC₁**: *OC₁ holds at every perfect start with exactly one truly dangerous agent `k` and at
most one unfrozen pick holder*, whatever the number of dangerous agents. Here `k` is frozen at the picks and
threatened by `J` at its pick value, and no other frozen agent is; the existence of the chain is proved (Lemma
D1-chain), not assumed. -/
theorem thmU1_oc1 (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hrel : ∀ i ∈ agents, (relevant v i goods).length ≤ 4)
    (hperf : PerfectStart v agents goods (sdPick v σ goods))
    {k : A} (hk : k ∈ agents) (hkf : Frozen v agents (pickBase v goods σ) k)
    (hkT : Threat v k (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) k))
    (hDT : ∀ d ∈ agents, d ≠ k → Frozen v agents (pickBase v goods σ) d →
      ¬ Threat v d (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) d))
    (hone : ∀ u ∈ agents, ∀ u' ∈ agents, (sdPick v σ goods u).isSome → ¬ Frozen v agents (pickBase v goods σ) u →
      (sdPick v σ goods u').isSome → ¬ Frozen v agents (pickBase v goods σ) u' → u = u') :
    ∃ B', OneMove v agents goods (pickBase v goods σ) B' ∧ OneAbsorber v agents goods B' := by
  obtain ⟨rest, hch, hlong⟩ := exists_longest_cchain hσ hag hgd hk hkf
  obtain ⟨H₀, hH₀, hH₀J, himp⟩ := exists_improving hσ hgd hkT
  exact ⟨_, Or.inr (Or.inl (cchain_isChain hσ hch hH₀ hH₀J himp)),
    oneAbsorber_of_sStar (thmU1 hσ hag hgd hrel hperf hDT hone hch hlong hH₀ hH₀J himp)⟩

end thmU

/-! ## (F) Non-vacuity: Corollary U1 applies

Two agents, five goods, order `(0, 1)`. Agent 0 values goods 0, 2, 3, 4 at 6, 4, 4, 4; agent 1 values goods 0, 1 at
5, 3. The picks are `Y₀ = 0`, `Y₁ = 1`, the junk is `{2, 3, 4}`; agent 0 is frozen (agent 1 wants good 0) and
truly dangerous (`v₀({3, 4}) = 8 > 6`), and agent 1 is the only unfrozen pick holder. All hypotheses of
`thmU1_oc1` are checked by `decide`. -/

namespace ExU

/-- The values. -/
def v : Fin 2 → Fin 5 → Nat := fun i g => match i.val, g.val with
  | 0, 0 => 6 | 0, 2 => 4 | 0, 3 => 4 | 0, 4 => 4
  | 1, 0 => 5 | 1, 1 => 3
  | _, _ => 0

def agents : List (Fin 2) := [0, 1]
def goods : List (Fin 5) := [0, 1, 2, 3, 4]
def σ : List (Fin 2) := [0, 1]

theorem hyp_rel : ∀ i ∈ agents, (relevant v i goods).length ≤ 4 := by decide

theorem hyp_perf : PerfectStart v agents goods (sdPick v σ goods) := by unfold PerfectStart; decide

theorem hyp_kf : Frozen v agents (pickBase v goods σ) 0 := by unfold Frozen; decide

theorem hyp_kT : Threat v 0 (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) 0) := by
  unfold Threat; decide

theorem hyp_DT : ∀ d ∈ agents, d ≠ 0 → Frozen v agents (pickBase v goods σ) d →
    ¬ Threat v d (junkOf agents goods (pickBase v goods σ)) (mval v (sdPick v σ goods) d) := by
  unfold Frozen Threat; decide

theorem hyp_one : ∀ u ∈ agents, ∀ u' ∈ agents, (sdPick v σ goods u).isSome →
    ¬ Frozen v agents (pickBase v goods σ) u → (sdPick v σ goods u').isSome →
    ¬ Frozen v agents (pickBase v goods σ) u' → u = u' := by
  unfold Frozen; decide

/-- Corollary U1 applies to this start: one move repairs it. -/
theorem repair : ∃ B', OneMove v agents goods (pickBase v goods σ) B' ∧ OneAbsorber v agents goods B' :=
  thmU1_oc1 (List.Perm.refl _) (by decide) (by decide) hyp_rel hyp_perf (by decide) hyp_kf hyp_kT hyp_DT hyp_one

end ExU

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.exists_walk
#print axioms EFX.OC1Max.exists_cchain
#print axioms EFX.OC1Max.exists_longest_cchain
#print axioms EFX.OC1Max.exists_improving
#print axioms EFX.OC1Max.cchain_isChain
#print axioms EFX.OC1Max.USetting.validState
#print axioms EFX.OC1Max.USetting.mem_junk
#print axioms EFX.OC1Max.USetting.mem_ownerSet_iff
#print axioms EFX.OC1Max.USetting.keep
#print axioms EFX.OC1Max.USetting.wanter_of_frozen
#print axioms EFX.OC1Max.thmU
#print axioms EFX.OC1Max.thmU_oc1
#print axioms EFX.OC1Max.thmU_of_DT
#print axioms EFX.OC1Max.thmU1
#print axioms EFX.OC1Max.thmU1_oc1
#print axioms EFX.OC1Max.ExU.repair
