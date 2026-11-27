# Literature note: EFX₀ for two agents (the coordinator's question about `kgen/n3.md` Theorem 2)

Referee: `proof/k4-referee`, 2026-11-26.

**Source read.** B. Plaut, T. Roughgarden, "Almost Envy-Freeness with General Valuations", arXiv 1707.04769v3,
11 Nov 2017 (PDF fetched, sha256 `f67cd876…`, text extracted with `pdftotext`).
- Read: §1.3, §2 (definitions), §4.2 (Theorems 4.1–4.3 with proofs), Appendix A (proof of Theorem 4.1), and the
  beginning of Appendix B.
- The journal version (SIAM J. Discrete Math. 34(2), 2020, as cited by Viswanathan–Mehta [16]) was not read
  [unverified].

**What is proved there.**
- *Notion.* Definition 2.3: A is EFX if for all i, j, ∀g ∈ A_j, v_i(A_i) ≥ v_i(A_j ∖ {g}). This is the all-goods form,
  i.e. **EFX₀**: zero-valued goods are not exempt.
- *Valuations.* "General" means normalized and monotone. Allocations are complete partitions (§2).
- *Theorem 4.2.* For identical general valuations the leximin++ solution is EFX.
  - The proof handles zero values. If v(A_i) < v(A_j ∖ g), moving g to the poorest agent i strictly increases i's
    bundle size, which ≺++ compares right after the utility, even when v(g) = 0.
  - Appendix A proves that ≺++ is irreflexive and transitive. That is all the existence of a ≺++-maximum needs.
- **Theorem 4.3.** For two players with general, not necessarily identical, valuations, cut-and-choose returns an EFX
  allocation: player 1 cuts by the leximin++ solution for two copies of itself, and player 2 chooses.
- Appendix B, Theorem B.1 (statement and start of the proof read): additive valuations with identical rankings,
  allocated in descending order, give EFX in O(mn³). With cut-and-choose this gives two additive players in
  polynomial time.

**Answer.**
- **EFX₀ existence for n = 2 is published**: Plaut–Roughgarden, Theorem 4.3, for arbitrary monotone valuations, so for
  arbitrary nonnegative additive valuations with zeros, any number of relevant goods, and complete allocations.
  - Polynomial time for two additive players follows from Appendix B.
  - The exponential lower bound of their Theorem 3.3 is for general valuations [statement seen in §1.3, proof not
    read].
- **It does not cover `kgen/n3.md` Theorem 2** (conditional on Lemma T at `3ba28ba`). Theorem 2 is the stronger, OC₁
  form for two agents:
  - from either serial-dictatorship order, the picks are kept (shape A1) or one chain a → b repairs them (shape B);
  - its key step, Claim T, asks for an EFX₀ allocation in which each of two agents with distinct favourites keeps its
    favourite good.

  Cut-and-choose does not keep prescribed goods, and nothing in the parts of Plaut–Roughgarden I read addresses
  picks or favourites. I know of no published result stating Claim T [unverified: not searched beyond this paper].
- **What Theorem 2 can cite.** The existence part (some EFX₀ allocation for n = 2) is Plaut–Roughgarden Theorem 4.3.
  The new content is the shape, with SD picks kept or one chain.
