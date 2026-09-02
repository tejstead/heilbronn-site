# Prior-art audit for the eight-point result

This review was last updated on 2026-09-02. It concerns the convex-region,
own-hull-normalized problem stated in `HeilbronnChallenge.lean`, not the
different unit-square version of Heilbronn's problem.

The search checked the published neighboring-case chapters by Dress, Yang, and
Zeng, the public Packing Center record for convex regions, and the modern
survey and problem statement by Georgiev, Gómez-Serrano, Tao, and Wagner. The
sources record sharp results for six and seven points and numerical candidate
configurations for other small cases. None states or cites an exact eight-point
value, the quintic value used here, or a proof of the eight-point upper bound.
No public proof of the selected n = 8 result was located.

Sources checked:

- Andreas W. M. Dress, Lu Yang, and Zhenbing Zeng, “Heilbronn Problem for Six
  Points in a Planar Convex Body,” *Minimax and Applications* (1995),
  pp. 173-190, <https://doi.org/10.1007/978-1-4613-3557-3_13>.
- Lu Yang and Zhenbing Zeng, “Heilbronn Problem for Seven Points in a Planar
  Convex Body,” *Minimax and Applications* (1995), pp. 191-218,
  <https://doi.org/10.1007/978-1-4613-3557-3_14>.
- Erich Friedman, “The Heilbronn Problem for Convex Regions,” Packing Center,
  <https://erich-friedman.github.io/packing/heilconvex/>.
- Bogdan Georgiev, Javier Gómez-Serrano, Terence Tao, and Adam Zsolt Wagner,
  “Mathematical exploration and discovery at scale,” arXiv:2511.02864,
  <https://arxiv.org/abs/2511.02864>.

An absence-of-prior-art search cannot prove that no earlier proof exists. The
claim here is the narrower, auditable statement that none was found in these
records or their cited convex-region context.
