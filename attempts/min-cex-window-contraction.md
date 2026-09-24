# Minimal counterexample: shortening a thread by contracting its middle agent

Workstream `proof/min-counterexample`. The first path-shortening reduction tried (plan Step 3.1, used here for the
minimal counterexample): three consecutive P-agents x – L – gl – e – gr – R – y on a thread (gl, gr of degree 2);
contract e, i.e. delete e and p and merge gl, gr into one good g* that L values as gl and R as gr. H′ is again a core
with the same cyclomatic number. Checked with Lemma M1 without the unenvied bundle (M1(b)).

Result: 200 of the 216 profiles reduce. The 16 that do not all have e ranking its private good second or first; for
example L: x > gl > pL, e: gl > p > gr, R: gr > y > pR, with local state of Y: L′ holds {g*} (case B: its top x is
alone), R′ holds {y} (case B: its top g* is alone), x alone, and pL, pR in an outside bundle with outside goods. In H,
the chain "x alone → L holds gl → gl alone → e holds p → R needs gr alone" needs one more alone good than H has
bundles for: the contracted agent brings two goods but only one bundle.

Superseded: Theorem M3 (no good of degree 2 shared by two P-agents) uses two-agent reductions instead and makes this
one unnecessary. Kept because it shows where contraction alone breaks: chains of cases B/C along a thread.

Reproduce: `python attempts/min_cex_failed.py window` (about 3 minutes on 4 CPUs).
