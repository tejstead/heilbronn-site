# Consensus-rule calibration findings (2026-07-23)

Square n=17 champion, recovery tests:
- global shake sigma<=0.01: single polish recovers (88-100%). Trivial vote.
- sigma=0.015: 2/8 recover, both instantly (i.e. still single-polish cases).
- sigma>=0.02, or teleporting even ONE point: ~0% recovery even with 45-90s
  basin-hopping (1/8 lucky instant case). 302 polishes/min, trajectories
  plateau far below champion.

Conclusion: at n>=17 the champion basin is ~0.01 wide and every exit is
one-way for the hopping walk. "Scrambled restarts return" is not a viable
vote at any calibration: below sigma~0.015 it certifies nothing beyond local
optimality; above, it never terminates (the 4h square n=17 run: 156 streams,
0 votes).

Adopted standard instead: "unbeaten-N" — N independent deep streams failed
to beat the value (plus it being an exact SLP critical point). Same evidence
class as historical entries, made quantitative in timings.json.
