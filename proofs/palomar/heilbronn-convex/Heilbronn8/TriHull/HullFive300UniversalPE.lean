import Heilbronn8.TriHull.HullFive300UniversalMM

set_option maxHeartbeats 0

/-!
# The remaining positive-eta PE cell

This file is intentionally downstream only of the proved `MM` closure.  It
does not import the invalid sibling relaxation.

The hard scalar cell is

* `Q >= Delta`;
* `eta = DQR >= 2`.

No sign assumption on `t = Delta-p` is needed: the two places where it occurs
use only `beta*t <= C` and `t <= Delta-2`, both consequences of `p >= 2`.

The proof first reduces the geometry to three nonnegative shifts
`r = e - 2`, `z = Delta - 2`, and `x = b - 2`.  The two strict constraints are
kept division-free.  A rational AM--GM support (proved directly from a square)
then produces `hullFive300_peJp`.  Its positivity is proved by exact Taylor
identities, a three-step rational lower iterate in `z`, and a four-interval
positive-polynomial certificate.  No numerical decision procedure or bulk
certificate is used.
-/

namespace Heilbronn8.TriHull

/-- Cleared rational support polynomial.  Here `b=x+2`, `Delta=z+2`, and
`A=e+Delta-2=r+z+2`. -/
def hullFive300_peJp (r z x : ℝ) : ℝ :=
  let b := x + 2
  let Delta := z + 2
  let A := r + z + 2
  8 * (b * A * (A + 5) + 4 * A + 4 * b) *
      (b + Delta) * (b + 2) * (A + 2) +
    121 * b * A * (b * A * (A - 17) + 4 * A + 4 * b)

def hullFive300_peD (r : ℝ) : ℝ := 13 * r + 18
def hullFive300_peC (r : ℝ) : ℝ := 17 * r + 26
def hullFive300_peK (r : ℝ) : ℝ := 60 * (r + 2) * (r + 4)
def hullFive300_peM (r : ℝ) : ℝ :=
  hullFive300_peD r * hullFive300_peC r ^ 2

/-- Value of `D^3 Jp` at the left endpoint
`b = 30(e+2)/(13e-8)`. -/
def hullFive300_peR (r z : ℝ) : ℝ :=
  (238629888 - 286001280*r - 565083552*r^2 - 201019376*r^3 +
      18807384*r^4 + 18459716*r^5 + 2168340*r^6) +
  (-2903040 - 103409280*r + 196178208*r^2 + 268337504*r^3 +
      92489584*r^4 + 10506748*r^5 + 174720*r^6) * z +
  (146824704 + 373170528*r + 350432520*r^2 + 121936532*r^3 +
      15935996*r^4 + 524160*r^5) * z^2 +
  (91387008 + 118600704*r + 51495144*r^2 + 9025108*r^3 +
      524160*r^4) * z^3 +
  (2695680 + 3588480*r + 1427520*r^2 + 174720*r^3) * z^4

def hullFive300_peRz (r z : ℝ) : ℝ :=
  (-2903040 - 103409280*r + 196178208*r^2 + 268337504*r^3 +
      92489584*r^4 + 10506748*r^5 + 174720*r^6) +
  2 * (146824704 + 373170528*r + 350432520*r^2 + 121936532*r^3 +
      15935996*r^4 + 524160*r^5) * z +
  3 * (91387008 + 118600704*r + 51495144*r^2 + 9025108*r^3 +
      524160*r^4) * z^2 +
  4 * (2695680 + 3588480*r + 1427520*r^2 + 174720*r^3) * z^3

/-- The first Taylor coefficient in the `b` direction. -/
def hullFive300_peP0 (r z : ℝ) : ℝ :=
  4 * (36587*r^5 + 149042*r^4 - 364730*r^3 - 1602964*r^2 +
      110520*r + 2616624) +
  4 * (2236*r^5 + 150453*r^4 + 781750*r^3 + 779180*r^2 +
      88032*r + 1038960) * z +
  4 * (6708*r^4 + 201417*r^3 + 997454*r^2 + 1358094*r +
      804924) * z^2 +
  4 * (6708*r^3 + 97823*r^2 + 374682*r + 385992) * z^3 +
  16 * (13*r + 18) * (43*r + 138) * z^4

/-- Half the second Taylor coefficient in the `b` direction. -/
def hullFive300_peCpos (r z : ℝ) : ℝ :=
  104*r^4*z + 2709*r^4 + 312*r^3*z^2 + 9623*r^3*z + 3515*r^3 +
  312*r^2*z^3 + 11263*r^2*z^2 + 20152*r^2*z + 3590*r^2 +
  104*r*z^4 + 4493*r*z^3 + 24143*r*z^2 + 40400*r*z + 80148*r +
  144*z^4 + 7506*z^3 + 29322*z^2 + 87192*z + 140184

def hullFive300_peU (r : ℝ) : ℝ :=
  97666299224064 + 434819516940288*r + 826094229493248*r^2 +
  866621332005120*r^3 + 543628400774400*r^4 +
  206777527694464*r^5 + 46222350837728*r^6 +
  5542513284048*r^7 + 273455844480*r^8

def hullFive300_peV (r : ℝ) : ℝ :=
  -110725685379072 - 419101249388544*r - 668108453105664*r^2 -
  579164074030080*r^3 - 295482229324800*r^4 -
  89983189763072*r^5 - 15804396401664*r^6 -
  1439690409664*r^7 - 50275580160*r^8

def hullFive300_peS (r z : ℝ) : ℝ :=
  836761536 + 1808597088*r + 1484403708*r^2 + 547945816*r^3 +
  92936005*r^4 + 5907720*r^5 +
  (108908928 + 153382464*r + 76025064*r^2 + 16227748*r^3 +
    1266720*r^4) * z +
  (2695680 + 3588480*r + 1427520*r^2 + 174720*r^3) * z^2

/-- The final one-variable polynomial; this is `W2/256` in the audit. -/
def hullFive300_peW (r : ℝ) : ℝ :=
  190900901826035712 + 904832651241123840*r +
  1719897867313652736*r^2 + 1478975583589890048*r^3 +
  130235166474041088*r^4 - 901514929937971968*r^5 -
  793365779235720576*r^6 - 183901706507500672*r^7 +
  147598061115027168*r^8 + 142826762420856688*r^9 +
  57300409558208180*r^10 + 12741565632501264*r^11 +
  1531443007664947*r^12 + 77729504228805*r^13

private lemma hullFive300_pe_half_powers
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1/2) :
    t^2 ≤ 1/4 ∧ t^3 ≤ 1/8 ∧ t^4 ≤ 1/16 ∧
      t^5 ≤ 1/32 ∧ t^6 ≤ 1/64 ∧ t^7 ≤ 1/128 := by
  have h1 : 0 ≤ t * (1/2 - t) := mul_nonneg ht0 (by linarith)
  have h2 : 0 ≤ t^2 * (1/2 - t) := mul_nonneg (sq_nonneg t) (by linarith)
  have h3 : 0 ≤ t^3 * (1/2 - t) := by positivity
  have h4 : 0 ≤ t^4 * (1/2 - t) := by positivity
  have h5 : 0 ≤ t^5 * (1/2 - t) := by positivity
  have h6 : 0 ≤ t^6 * (1/2 - t) := by positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- Exact four-interval positivity proof for the terminal polynomial. -/
lemma hullFive300_peW_pos {r : ℝ} (hr : 0 ≤ r) :
    0 < hullFive300_peW r := by
  by_cases hhalf : r ≤ 1/2
  · obtain ⟨hr2, hr3, hr4, hr5, hr6, hr7⟩ :=
      hullFive300_pe_half_powers hr hhalf
    set W : ℝ := hullFive300_peW r with hWdef
    set P : ℝ :=
      904832651241123840*r + 1719897867313652736*r^2 +
      1478975583589890048*r^3 + 130235166474041088*r^4 +
      147598061115027168*r^8 + 142826762420856688*r^9 +
      57300409558208180*r^10 + 12741565632501264*r^11 +
      1531443007664947*r^12 + 77729504228805*r^13 with hPdef
    set N : ℝ :=
      901514929937971968*r^5 + 793365779235720576*r^6 +
        183901706507500672*r^7 with hNdef
    have hP : 0 ≤ P := by
      rw [hPdef]
      positivity
    have hN : N < 190900901826035712 := by
      rw [hNdef]
      linarith only [hr5, hr6, hr7]
    have hdecomp : W = 190900901826035712 + P - N := by
      rw [hWdef, hPdef, hNdef]
      dsimp [hullFive300_peW]
      ring
    have hW : 0 < W := by
      linarith only [hdecomp, hP, hN]
    exact hW
  · have hhalf' : 1/2 < r := lt_of_not_ge hhalf
    by_cases hone : r ≤ 1
    · let t : ℝ := r - 1/2
      have ht0 : 0 ≤ t := by dsimp [t]; linarith
      have ht : t ≤ 1/2 := by dsimp [t]; linarith
      obtain ⟨ht2, ht3, ht4, ht5, ht6, ht7⟩ :=
        hullFive300_pe_half_powers ht0 ht
      set W : ℝ := hullFive300_peW r with hWdef
      set P : ℝ :=
        27557866817281242739602*t + 18502789717227236973768*t^2 +
        16834741699151150471936*t^6 + 23381767545287653247488*t^7 +
        14321648371768519949568*t^8 + 5325730263775647612416*t^9 +
        1273255198225338664960*t^10 + 192069214297724055552*t^11 +
        16684521759966654464*t^12 + 636760098642370560*t^13 with hPdef
      set N : ℝ :=
        19592584266079184678928*t^3 +
          36627954463861901597936*t^4 +
          12583432734411698766240*t^5 with hNdef
      have hshift :
          8192 * W = 10036969487617801755915 + P - N := by
        rw [hWdef, hPdef, hNdef]
        dsimp [t, hullFive300_peW]
        ring
      have hP : 0 ≤ P := by
        rw [hPdef]
        positivity
      have hN : N < 10036969487617801755915 := by
        rw [hNdef]
        linarith only [ht3, ht4, ht5]
      have hW : 0 < W := by
        linarith only [hshift, hP, hN]
      exact hW
    · have hone' : 1 < r := lt_of_not_ge hone
      by_cases hfive : r ≤ 5/4
      · let t : ℝ := r - 1
        have ht0 : 0 ≤ t := by dsimp [t]; linarith
        have ht : t ≤ 1/4 := by dsimp [t]; linarith
        have htprod : 0 ≤ t * (1/4 - t) :=
          mul_nonneg ht0 (by linarith)
        set W : ℝ := hullFive300_peW r with hWdef
        set Pair : ℝ :=
          1946188999772052877*t - 5178384369531200640*t^2 with hPairdef
        set Tail : ℝ :=
          281386679666299610*t^3 + 22665093993832572796*t^4 +
          38377265310356809947*t^5 + 33517642527562839392*t^6 +
          18565698726601223564*t^7 + 6972017843121434820*t^8 +
          1809111025000391923*t^9 + 320763508231046816*t^10 +
          37181783054327418*t^11 + 2541926562639412*t^12 +
          77729504228805*t^13 with hTaildef
        have hshift :
            W = 2908135726002037260 + Pair + Tail := by
          rw [hWdef, hPairdef, hTaildef]
          dsimp [t, hullFive300_peW]
          ring
        have hPair : 0 ≤ Pair := by
          rw [hPairdef]
          nlinarith only [ht0, htprod]
        have hTail : 0 ≤ Tail := by
          rw [hTaildef]
          positivity
        have hW : 0 < W := by
          linarith only [hshift, hPair, hTail]
        exact hW
      · let t : ℝ := r - 5/4
        have ht0 : 0 ≤ t := by dsimp [t]; linarith
        set W : ℝ := hullFive300_peW r with hWdef
        set Tail : ℝ :=
          215478087829334026788471093 +
          121310509971425807814348420*t +
          800276116860030301620400224*t^2 +
          4051069669300581785807797632*t^3 +
          7674489980930575109875672832*t^4 +
          8059466017748060776444627968*t^5 +
          5426663529577077469486268416*t^6 +
          2498569979925856326884851712*t^7 +
          808362307511390042041024512*t^8 +
          184400873711579876688658432*t^9 +
          29114926466434192942039040*t^10 +
          3032414285540212359561216*t^11 +
          187538904856410254737408*t^12 +
          5216338728078299627520*t^13 with hTaildef
        have hshift :
            67108864 * W = Tail := by
          rw [hWdef, hTaildef]
          dsimp [t, hullFive300_peW]
          ring
        have hTail : 0 < Tail := by
          rw [hTaildef]
          positivity
        have hW : 0 < W := by
          linarith only [hshift, hTail]
        exact hW

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- Positivity of the first `b`-Taylor coefficient once `z>4/17`. -/
lemma hullFive300_peP0_pos {r z : ℝ}
    (hr : 0 ≤ r) (hz : 4/17 < z) : 0 < hullFive300_peP0 r z := by
  let p : ℝ :=
    972420666048 + 70603424352*r - 455397918992*r^2 -
      56644051272*r^3 + 61743428120*r^4 + 12398898796*r^5
  have hp : 0 < p := by
    by_cases h1 : r ≤ 1
    · have hr2 : r^2 ≤ 1 := by nlinarith [mul_nonneg hr (by linarith : 0 ≤ 1-r)]
      have hr3 : r^3 ≤ 1 := by
        have := mul_nonneg (sq_nonneg r) (by linarith : 0 ≤ 1-r)
        nlinarith
      have hpos : 0 ≤ 70603424352*r + 61743428120*r^4 + 12398898796*r^5 := by
        positivity
      dsimp [p]
      nlinarith
    · have h1' : 1 < r := lt_of_not_ge h1
      by_cases h15 : r ≤ 3/2
      · let t : ℝ := r - 1
        have ht0 : 0 ≤ t := by dsimp [t]; linarith
        have ht : t ≤ 1/2 := by dsimp [t]; linarith
        obtain ⟨ht2, ht3, ht4, ht5, ht6, ht7⟩ :=
          hullFive300_pe_half_powers ht0 ht
        have hid : p =
            605124447052 - 701156360988*t - 130880516128*t^2 +
            314318649168*t^3 + 123737922100*t^4 + 12398898796*t^5 := by
          dsimp [p, t]
          ring
        have htail : 0 ≤ 314318649168*t^3 + 123737922100*t^4 +
            12398898796*t^5 := by positivity
        nlinarith [hid]
      · have h15' : 3/2 < r := lt_of_not_ge h15
        by_cases h2 : r ≤ 2
        · let t : ℝ := r - 3/2
          have ht0 : 0 ≤ t := by dsimp [t]; linarith
          have ht : t ≤ 1/2 := by dsimp [t]; linarith
          have hid : p =
              2153896435125/8 - 2122217093265/4*t +
              541702964269*t^2 + 592791740358*t^3 +
              154735169090*t^4 + 12398898796*t^5 := by
            dsimp [p, t]
            ring
          have htail : 0 ≤ 541702964269*t^2 + 592791740358*t^3 +
              154735169090*t^4 + 12398898796*t^5 := by positivity
          nlinarith [hid]
        · let t : ℝ := r - 2
          have ht0 : 0 ≤ t := by dsimp [t]; linarith
          have hid : p =
              223543040000 + 536984736640*t + 1678491951936*t^2 +
              933259325528*t^3 + 185732416080*t^4 + 12398898796*t^5 := by
            dsimp [p, t]
            ring
          have : 0 <
              223543040000 + 536984736640*t + 1678491951936*t^2 +
              933259325528*t^3 + 185732416080*t^4 + 12398898796*t^5 := by
            positivity
          nlinarith [hid]
  have hpAt : 17^4 * hullFive300_peP0 r (4/17) = p := by
    dsimp [hullFive300_peP0, p]
    ring
  let slope : ℝ :=
    8944*r^5 + 10338132/17*r^4 + 958917736/289*r^3 +
      20031676496/4913*r^2 + 8420115168/4913*r + 24562113408/4913 +
      (26832*r^4 + 13803684/17*r^3 + 1179807784/289*r^2 +
        1672527576/289*r + 1036117872/289) * z +
      (26832*r^3 + 6687740/17*r^2 + 25642728/17*r +
        26406432/17) * z^2 +
      (8944*r^2 + 41088*r + 39744) * z^3
  have hslope : 0 < slope := by dsimp [slope]; positivity
  have hdiff :
      hullFive300_peP0 r z - hullFive300_peP0 r (4/17) =
        (z - 4/17) * slope := by
    dsimp [hullFive300_peP0, slope]
    ring
  have hAt : 0 < hullFive300_peP0 r (4/17) := by nlinarith [hpAt]
  nlinarith [hdiff, mul_pos (by linarith : 0 < z-4/17) hslope]

/-- The derivative of `R` is positive on the entire interval used below. -/
lemma hullFive300_peRz_pos {r z : ℝ}
    (hr : 0 ≤ r) (hz : 4/17 ≤ z) : 0 < hullFive300_peRz r z := by
  let q : ℝ :=
    196178208*r^2 - 103409280*r + 1125245952/17
  have hqid :
      4 * 196178208 * q =
        (2 * 196178208*r - 103409280)^2 +
          701205791458443264/17 := by
    dsimp [q]
    ring
  have hq : 0 < q := by nlinarith [hqid, sq_nonneg (2*196178208*r-103409280)]
  let rest : ℝ :=
    268337504*r^3 + 92489584*r^4 + 10506748*r^5 + 174720*r^6 +
    (746341056*r + 700865040*r^2 + 243873064*r^3 +
      31871992*r^4 + 1048320*r^5) * z +
    (274161024 + 355802112*r + 154485432*r^2 +
      27075324*r^3 + 1572480*r^4) * z^2 +
    (10782720 + 14353920*r + 5710080*r^2 + 698880*r^3) * z^3
  have hrest : 0 ≤ rest := by dsimp [rest]; positivity
  have hlin : 0 ≤ 293649408*z - 2903040 - 1125245952/17 := by
    nlinarith
  have hid : hullFive300_peRz r z = q +
      (293649408*z - 2903040 - 1125245952/17) + rest := by
    dsimp [hullFive300_peRz, q, rest]
    ring
  nlinarith [hid]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- Pure, division-free input interface for the PE certificate. -/
theorem hullFive300_peJp_pos
    {r z x : ℝ} (hr : 0 ≤ r) (hz : 0 ≤ z)
    (hP : 4 * (r + 21) < x * (13 * r + 18))
    (hBH : 2 * (x + 2) * (r + 2) < z * (17 * r + 26 - 4 * z)) :
    0 < hullFive300_peJp r z x := by
  let D : ℝ := hullFive300_peD r
  let C : ℝ := hullFive300_peC r
  let K : ℝ := hullFive300_peK r
  let M : ℝ := hullFive300_peM r
  have hD : 0 < D := by dsimp [D, hullFive300_peD]; linarith
  have hC : 0 < C := by dsimp [C, hullFive300_peC]; linarith
  have hK : 0 < K := by dsimp [K, hullFive300_peK]; positivity
  have hBP : 30 * (r + 4) < (x + 2) * D := by
    dsimp [D, hullFive300_peD]
    linarith
  have hBPscaled := mul_lt_mul_of_pos_left hBP (by positivity : 0 < 2*(r+2))
  have hBHscaled := mul_lt_mul_of_pos_right hBH hD
  have hhard : K < z * D * (C - 4*z) := by
    dsimp [K, C, D, hullFive300_peK, hullFive300_peC, hullFive300_peD]
      at hBPscaled hBHscaled ⊢
    nlinarith
  have hzpos : 0 < z := by
    by_contra hn
    have hznonpos : z ≤ 0 := le_of_not_gt hn
    have hfactor : 0 ≤ C-4*z := by linarith
    have hzD : z*D ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hznonpos hD.le
    have hprod : z*D*(C-4*z) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hzD hfactor
    linarith
  have hC4 : 0 < C - 4*z := by
    by_contra hn
    have hn' : C - 4*z ≤ 0 := le_of_not_gt hn
    have hzD : 0 ≤ z*D := mul_nonneg hzpos.le hD.le
    have : z * D * (C - 4*z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hzD hn'
    linarith
  have hMdef : M = D * C^2 := by
    dsimp [M, hullFive300_peM, D, C]
  have hmax : 16*z*(C-4*z) ≤ C^2 := by
    nlinarith [sq_nonneg (C-8*z)]
  have hmaxD := mul_le_mul_of_nonneg_left hmax hD.le
  have hM16 : 16*K < M := by rw [hMdef]; nlinarith
  have hM4 : 0 < M - 4*K := by nlinarith
  have hM8 : 0 < M - 8*K := by nlinarith

  let z0 : ℝ := K / (D*C)
  let z1 : ℝ := K*C / (M-4*K)
  let z2 : ℝ := K*(M-4*K) / (D*C*(M-8*K))
  have hDC : 0 < D*C := mul_pos hD hC
  have hden2 : 0 < D*C*(M-8*K) := mul_pos hDC hM8
  have hDne : D ≠ 0 := ne_of_gt hD
  have hCne : C ≠ 0 := ne_of_gt hC
  have hDCne : D*C ≠ 0 := ne_of_gt hDC
  have hM4ne : M-4*K ≠ 0 := ne_of_gt hM4
  have hM8ne : M-8*K ≠ 0 := ne_of_gt hM8
  have hden2ne : D*C*(M-8*K) ≠ 0 := ne_of_gt hden2
  have hM48ne : (M-4*K)*(M-8*K) ≠ 0 :=
    mul_ne_zero hM4ne hM8ne
  have hquadFactor :
      M^2-12*M*K+32*K^2 = (M-4*K)*(M-8*K) := by ring
  have hquadNe : M^2-12*M*K+32*K^2 ≠ 0 := by
    rw [hquadFactor]
    exact hM48ne
  have hM4neNorm : M - K * 4 ≠ 0 := by
    nlinarith [hM4]
  have hM8neNorm : M - K * 8 ≠ 0 := by
    nlinarith [hM8]
  have hquadNeNorm :
      -(M * K * 12) + M ^ 2 + K ^ 2 * 32 ≠ 0 := by
    rw [show -(M * K * 12) + M ^ 2 + K ^ 2 * 32 =
      M ^ 2 - 12 * M * K + 32 * K ^ 2 by ring]
    exact hquadNe
  have hC2D4Kne : C ^ 2 * D - K * 4 ≠ 0 := by
    rw [show C ^ 2 * D - K * 4 = M - 4 * K by rw [hMdef]; ring]
    exact hM4ne
  have hzDC : K < z*(D*C) := by
    have hdiff : z*(D*C)-z*D*(C-4*z) = 4*z^2*D := by ring
    have hpos : 0 < 4*z^2*D := by positivity
    have hdrop : z*D*(C-4*z) < z*(D*C) := by nlinarith [hdiff]
    exact hhard.trans hdrop
  have hz0 : z0 < z := by
    dsimp [z0]
    exact (div_lt_iff₀ hDC).2 hzDC
  have hz0four : (4 : ℝ)/17 < z0 := by
    dsimp [z0]
    apply (lt_div_iff₀ hDC).2
    dsimp [K, D, C, hullFive300_peK, hullFive300_peD,
      hullFive300_peC]
    nlinarith [sq_nonneg r]
  have hden0eq : D*(C-4*z0) = (M-4*K)/C := by
    dsimp [z0]
    field_simp [hDne, hCne]
    rw [hMdef] <;> ring
  have hden0 : 0 < D*(C-4*z0) := by
    rw [hden0eq]
    exact div_pos hM4 hC
  have hz1eq : z1 * (D*(C-4*z0)) = K := by
    rw [hden0eq]
    dsimp [z1]
    field_simp [hM4ne, hM4neNorm] <;> ring
  have hz1 : z1 < z := by
    have hscale : 0 < D*(z-z0) := mul_pos hD (sub_pos.mpr hz0)
    have hdenGrow : D*(C-4*z) < D*(C-4*z0) := by nlinarith
    have hscaled := mul_lt_mul_of_pos_left hdenGrow hzpos
    have hK' : K < z*(D*(C-4*z0)) := by nlinarith [hhard, hscaled]
    have hprod :
        z1 * (D*(C-4*z0)) < z * (D*(C-4*z0)) := by
      nlinarith [hz1eq, hK']
    exact lt_of_mul_lt_mul_right hprod hden0.le
  have hz01 : z0 < z1 := by
    have hid : z1-z0 = 4*K^2/(D*C*(M-4*K)) := by
      dsimp [z0, z1]
      rw [hMdef]
      field_simp [hDne, hCne, hM4ne, hM4neNorm, hC2D4Kne] <;> ring
    apply sub_pos.mp
    rw [hid]
    positivity
  have hden1eq : D*(C-4*z1) = D*C*(M-8*K)/(M-4*K) := by
    dsimp [z1]
    field_simp [hM4ne] <;> ring
  have hden1 : 0 < D*(C-4*z1) := by
    rw [hden1eq]
    exact div_pos hden2 hM4
  have hz2eq : z2 * (D*(C-4*z1)) = K := by
    rw [hden1eq]
    dsimp [z2]
    field_simp [hquadNe, hquadNeNorm] <;> ring
  have hz2 : z2 < z := by
    have hscale : 0 < D*(z-z1) := mul_pos hD (sub_pos.mpr hz1)
    have hdenGrow : D*(C-4*z) < D*(C-4*z1) := by nlinarith
    have hscaled := mul_lt_mul_of_pos_left hdenGrow hzpos
    have hK' : K < z*(D*(C-4*z1)) := by nlinarith [hhard, hscaled]
    have hprod :
        z2 * (D*(C-4*z1)) < z * (D*(C-4*z1)) := by
      nlinarith [hz2eq, hK']
    exact lt_of_mul_lt_mul_right hprod hden1.le
  have hz12 : z1 < z2 := by
    have hid : z2-z1 =
        16*K^3/(D*C*(M-8*K)*(M-4*K)) := by
      dsimp [z1, z2]
      field_simp [hDne, hCne, hM8ne, hM4ne, hM8neNorm, hM4neNorm,
        hquadNe, hquadNeNorm, hC2D4Kne, hMdef]
      rw [hMdef]
      ring
    apply sub_pos.mp
    rw [hid]
    positivity
  have hz2four : (4 : ℝ)/17 < z2 :=
    lt_trans hz0four (lt_trans hz01 hz12)

  have hW : 0 < hullFive300_peW r := hullFive300_peW_pos hr
  have hWidentity :
      hullFive300_peW r * 256 =
        hullFive300_peU r * K * (M-4*K) +
          hullFive300_peV r * D*C*(M-8*K) := by
    dsimp [hullFive300_peW, hullFive300_peU, hullFive300_peV,
      K, M, D, C, hullFive300_peK, hullFive300_peM,
      hullFive300_peD, hullFive300_peC]
    ring
  have hAffineIdentity :
      D*C*(M-8*K) *
          (hullFive300_peU r*z2 + hullFive300_peV r) =
        hullFive300_peW r * 256 := by
    calc
      _ = hullFive300_peU r*K*(M-4*K) +
            hullFive300_peV r*D*C*(M-8*K) := by
          dsimp [z2]
          field_simp [hden2ne] <;> ring
      _ = hullFive300_peW r*256 := hWidentity.symm
  have hAffine : 0 < hullFive300_peU r*z2 + hullFive300_peV r := by
    have hright := mul_pos hW (by norm_num : (0 : ℝ) < 256)
    by_contra hn
    have hnonpos : hullFive300_peU r*z2 + hullFive300_peV r ≤ 0 :=
      le_of_not_gt hn
    have hprod : D*C*(M-8*K) *
          (hullFive300_peU r*z2 + hullFive300_peV r) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hden2.le hnonpos
    nlinarith [hAffineIdentity]
  let Hbd : ℝ := z2*D*(C-4*z2)-K
  have hHbdIdentity :
      C^2*D*(M-8*K)^2 * Hbd = -64*K^4 := by
    dsimp [Hbd, z2]
    field_simp [hDne, hCne, hM8ne, hden2ne]
    rw [hMdef]
    ring
  have hHbd : Hbd < 0 := by
    have hcoef : 0 < C^2*D*(M-8*K)^2 := by positivity
    have hright : -64*K^4 < 0 := by
      have hK4 : 0 < K^4 := pow_pos hK 4
      nlinarith
    by_contra hn
    have hnonneg : 0 ≤ Hbd := le_of_not_gt hn
    have hprod : 0 ≤ C^2*D*(M-8*K)^2*Hbd :=
      mul_nonneg hcoef.le hnonneg
    nlinarith [hHbdIdentity]
  have hS : 0 < hullFive300_peS r z2 := by
    dsimp [hullFive300_peS]
    positivity
  have hDivision :
      64*D^2*hullFive300_peR r z2 =
        (-16*D*hullFive300_peS r z2)*Hbd +
          hullFive300_peU r*z2 + hullFive300_peV r := by
    dsimp [Hbd, hullFive300_peR, hullFive300_peS,
      hullFive300_peU, hullFive300_peV, D, C, K,
      hullFive300_peD, hullFive300_peC, hullFive300_peK]
    ring
  have hQH : 0 < (-16*D*hullFive300_peS r z2)*Hbd := by
    have hDS : 0 < D*hullFive300_peS r z2 := mul_pos hD hS
    have hnegQ : -16*D*hullFive300_peS r z2 < 0 := by nlinarith
    exact mul_pos_of_neg_of_neg hnegQ hHbd
  have hR2 : 0 < hullFive300_peR r z2 := by
    have h64D : 0 < 64*D^2 := by positivity
    have hright : 0 < (-16*D*hullFive300_peS r z2)*Hbd +
        hullFive300_peU r*z2 + hullFive300_peV r := by linarith
    by_contra hn
    have hnonpos : hullFive300_peR r z2 ≤ 0 := le_of_not_gt hn
    have hprod : 64*D^2*hullFive300_peR r z2 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h64D.le hnonpos
    nlinarith [hDivision]

  have hRz2 : 0 < hullFive300_peRz r z2 :=
    hullFive300_peRz_pos hr (le_of_lt hz2four)
  let q : ℝ := z-z2
  have hq : 0 < q := by dsimp [q]; linarith
  let R2 : ℝ :=
    146824704 + 373170528*r + 350432520*r^2 + 121936532*r^3 +
      15935996*r^4 + 524160*r^5
  let R3 : ℝ :=
    91387008 + 118600704*r + 51495144*r^2 + 9025108*r^3 + 524160*r^4
  let R4 : ℝ := 2695680 + 3588480*r + 1427520*r^2 + 174720*r^3
  have hR2c : 0 < R2 := by dsimp [R2]; positivity
  have hR3c : 0 < R3 := by dsimp [R3]; positivity
  have hR4c : 0 < R4 := by dsimp [R4]; positivity
  have hRTaylor :
      hullFive300_peR r z = hullFive300_peR r z2 +
        q*hullFive300_peRz r z2 +
        q^2*(R2+3*R3*z2+6*R4*z2^2) +
        q^3*(R3+4*R4*z2) + q^4*R4 := by
    dsimp [q, R2, R3, R4, hullFive300_peR, hullFive300_peRz]
    ring
  have hz20 : 0 ≤ z2 := le_trans (by norm_num) (le_of_lt hz2four)
  have htail2 : 0 ≤ R2+3*R3*z2+6*R4*z2^2 := by positivity
  have htail3 : 0 ≤ R3+4*R4*z2 := by positivity
  have hR : 0 < hullFive300_peR r z := by
    have hqRz : 0 < q*hullFive300_peRz r z2 := mul_pos hq hRz2
    have hq2 : 0 ≤ q^2*(R2+3*R3*z2+6*R4*z2^2) := by positivity
    have hq3 : 0 ≤ q^3*(R3+4*R4*z2) := by positivity
    have hq4 : 0 ≤ q^4*R4 := by positivity
    nlinarith [hRTaylor]

  let s : ℝ := x*D-4*(r+21)
  have hs : 0 < s := by dsimp [s, D, hullFive300_peD]; linarith
  have hzfour : 4/17 < z := lt_trans hz2four hz2
  have hP0 : 0 < hullFive300_peP0 r z := hullFive300_peP0_pos hr hzfour
  have hCp : 0 < hullFive300_peCpos r z := by
    dsimp [hullFive300_peCpos]
    positivity
  have hprod : 0 < (r+z+3)*(r+z+4)*(r+z+6) := by positivity
  have hTaylor :
      D^3*hullFive300_peJp r z x = hullFive300_peR r z +
        s*hullFive300_peP0 r z + s^2*hullFive300_peCpos r z +
        8*s^3*(r+z+3)*(r+z+4)*(r+z+6) := by
    dsimp [s, D, hullFive300_peD, hullFive300_peJp,
      hullFive300_peR, hullFive300_peP0, hullFive300_peCpos]
    ring
  have hright : 0 < hullFive300_peR r z +
        s*hullFive300_peP0 r z + s^2*hullFive300_peCpos r z +
        8*s^3*(r+z+3)*(r+z+4)*(r+z+6) := by positivity
  have hD3 : 0 < D^3 := by positivity
  by_contra hn
  have hnonpos : hullFive300_peJp r z x ≤ 0 := le_of_not_gt hn
  have hprod : D^3*hullFive300_peJp r z x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hD3.le hnonpos
  nlinarith [hTaylor]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- Scalar geometry adapter for the positive-eta PE branch
`Q>=Delta`, `eta>0`.  The sign of `Delta-p` is deliberately unrestricted. -/
theorem hullFive300_pe_qge_eta_pos_scalar
    {beta a b c d e f g x y z w p Q Delta A B N delta eta axr v earF H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hg : 2 ≤ g) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hp : 2 ≤ p) (hQ : Delta ≤ Q) (hDelta : 2 ≤ Delta)
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hN : 2 ≤ N)
    (hdelta : 2 ≤ delta) (heta : 2 ≤ eta) (haxr : 2 ≤ axr)
    (hv : 2 ≤ v) (hearF : 2 ≤ earF)
    (hBeta : beta = d+e+f)
    (hADef : A = e+Delta-p) (hBDef : B = a+Delta-Q)
    (hNDef : N = b+d-Delta)
    (hCentralE : e*N = d*A+f*Delta)
    (hCentralA : a*N = b*B+c*Delta)
    (hCentralG : a*e = p*Q+g*Delta)
    (hvDef : v = b+y-delta) (hearFDef : earF = z+w-f)
    (hAXRrow : b*axr = v*A-delta*f-y*e)
    (hfanQ : b*x = a*y+c*delta)
    (hetaRow : f*eta = z*A-w*N)
    (hH : H = a+b+d+e+x+y+z+w+g) :
    25 ≤ H := by
  by_contra hnot
  have hHlt : H < 25 := lt_of_not_ge hnot
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hepos : 0 < e := lt_of_lt_of_le (by norm_num) he
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hbetapos : 0 < beta := by
    rw [hBeta]
    linarith only [hd, he, hf]
  let t : ℝ := Delta-p
  let C0 : ℝ := e*(b-2)-2*f
  have htA : t = A-e := by dsimp [t]; rw [hADef]; ring
  have hcentral1 : e*(b-Delta) = d*t+f*Delta := by
    rw [hNDef, hADef] at hCentralE
    dsimp [t]
    nlinarith only [hCentralE]
  have hC0id : C0 = d*t+(Delta-2)*(e+f) := by
    dsimp [C0]
    nlinarith only [hcentral1]
  have hbetat : beta*t = b*e-p*(e+f) := by
    rw [hBeta]
    nlinarith only [hcentral1]
  have hrow : b*axr = v*t+b*e-delta*(e+f) := by
    calc
      b*axr = v*A-delta*f-y*e := hAXRrow
      _ = v*t+b*e-delta*(e+f) := by
        rw [htA, hvDef]
        ring
  have hrowUpper : b*axr ≤ v*t+C0 := by
    have hdeltaProd : 0 ≤ (delta-2)*(e+f) := by positivity
    dsimp [C0]
    nlinarith only [hrow, hdeltaProd]
  have hlocal : 2*b ≤ v*t+C0 := by
    have hscaled := mul_le_mul_of_nonneg_left haxr (le_of_lt hbpos)
    nlinarith only [hscaled, hrowUpper]
  have hbt : beta*t ≤ C0 := by
    have hpProd : 0 ≤ (p-2)*(e+f) := by positivity
    dsimp [C0]
    nlinarith only [hbetat, hpProd]
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv
  have hlocalScaled := mul_le_mul_of_nonneg_left hlocal hbetapos.le
  have htScaled := mul_le_mul_of_nonneg_left hbt hv0
  have hhard : 2*b*beta ≤ C0*(beta+v) := by
    nlinarith only [hlocalScaled, htScaled]
  have hC0pos : 0 < C0 := by
    have hleft : 0 < 2*b*beta := by positivity
    have hsum : 0 < beta+v := by linarith only [hbetapos, hv0]
    by_contra hn
    have hC0nonpos : C0 ≤ 0 := le_of_not_gt hn
    have hprod : C0*(beta+v) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hC0nonpos hsum.le
    linarith only [hleft, hhard, hprod]
  have hbetaV : beta+v < 19-a-g := by
    have hid : beta+v = H-(g+(a+x+delta)+earF) := by
      rw [hBeta, hvDef, hearFDef, hH]
      ring
    nlinarith only [hid, hHlt, hx, hdelta, hearF]
  have hbetaV15 : beta+v < 15 := by
    linarith only [hbetaV, ha, hg]
  have hstrict : 2*b*beta < 15*C0 := by
    have := mul_lt_mul_of_pos_left hbetaV15 hC0pos
    nlinarith only [this, hhard]
  have hbetaLower : e+4 ≤ beta := by
    rw [hBeta]
    linarith only [hd, hf]
  have hpoly : 60 < 13*b*e-8*b-30*e := by
    dsimp [C0] at hstrict
    have hbetaScaled :=
      mul_le_mul_of_nonneg_left hbetaLower (by positivity : 0 ≤ 2*b)
    nlinarith only [hstrict, hbetaScaled, hf]
  have hdenP : 0 < 13*e-8 := by linarith only [he]
  have hBP : 30*(e+2) < b*(13*e-8) := by
    nlinarith only [hpoly]

  have htCap : t ≤ Delta-2 := by
    dsimp [t]
    linarith only [hp]
  have hCcap : C0 ≤ beta*(Delta-2) := by
    rw [hC0id, hBeta]
    have := mul_le_mul_of_nonneg_left htCap
      (by linarith only [hd] : 0 ≤ d)
    nlinarith only [this, hDelta]
  have htwoB : 2*b ≤ (Delta-2)*(beta+v) := by
    have hmul := mul_le_mul_of_nonneg_right hCcap
      (by linarith only [hbetapos, hv0] : 0 ≤ beta+v)
    have hchain : beta*(2*b) ≤ beta*((Delta-2)*(beta+v)) := by
      nlinarith only [hhard, hmul]
    exact le_of_mul_le_mul_left hchain hbetapos
  have hae : 4*Delta ≤ a*e := by
    have hQ0 : 0 ≤ Q := by linarith only [hQ, hDelta]
    have hpQ0 := mul_le_mul_of_nonneg_right hp hQ0
    have hpQ : 2*Delta ≤ p*Q := by nlinarith only [hQ, hpQ0]
    have hgD0 := mul_le_mul_of_nonneg_right hg
      (by linarith only [hDelta] : 0 ≤ Delta)
    have hgD : 2*Delta ≤ g*Delta := by nlinarith only [hgD0]
    nlinarith only [hCentralG, hpQ, hgD]
  have haLower : 4*Delta/e ≤ a := by
    apply (div_le_iff₀ hepos).2
    nlinarith only [hae]
  have hBVsharp : beta+v < 17-4*Delta/e := by
    nlinarith only [hbetaV, haLower, hg]
  have hBVpos : 0 < beta+v := by linarith only [hbetapos, hv0]
  have hDeltaStrict : 2 < Delta := by
    by_contra hn
    have : Delta ≤ 2 := le_of_not_gt hn
    have hright : (Delta-2)*(beta+v) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith only [this]) hBVpos.le
    nlinarith only [htwoB, hright, hbpos]
  have hBH : 2*b*e < (Delta-2)*(17*e-4*Delta) := by
    have hmul := mul_lt_mul_of_pos_left hBVsharp
      (by linarith only [hDeltaStrict] : 0 < Delta-2)
    have hraw : 2*b < (Delta-2)*(17-4*Delta/e) := by
      nlinarith only [htwoB, hmul]
    have hscaled := mul_lt_mul_of_pos_left hraw hepos
    have hid : e*((Delta-2)*(17-4*Delta/e)) =
        (Delta-2)*(17*e-4*Delta) := by
      field_simp [ne_of_gt hepos] <;> ring
    nlinarith only [hscaled, hid]

  let r : ℝ := e-2
  let q : ℝ := Delta-2
  let X : ℝ := b-2
  have hr : 0 ≤ r := by dsimp [r]; linarith only [he]
  have hq : 0 ≤ q := by dsimp [q]; linarith only [hDelta]
  have hPshift : 4*(r+21) < X*(13*r+18) := by
    dsimp [r, X]
    nlinarith only [hBP]
  have hBHshift : 2*(X+2)*(r+2) < q*(17*r+26-4*q) := by
    dsimp [r, q, X]
    nlinarith only [hBH]
  have hJ : 0 < hullFive300_peJp r q X :=
    hullFive300_peJp_pos hr hq hPshift hBHshift

  let A0 : ℝ := e+Delta-2
  let Z : ℝ := 2*(b+Delta)*(b+2)*(A0+2)/(b*A0)
  have hA0 : 0 < A0 := by dsimp [A0]; linarith only [he, hDelta]
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hJid :
      hullFive300_peJp r q X = b^2*A0^2 *
        ((4*Z+121)*(A0-17+4/b+4/A0)+88*Z) := by
    let L0 : ℝ := A0-17+4/b+4/A0
    let P0 : ℝ := (b+Delta)*(b+2)*(A0+2)
    let K0 : ℝ := b*A0*(A0-17)+4*A0+4*b
    let I0 : ℝ := b*A0*(A0+5)+4*A0+4*b
    have hLclear : b*A0*L0 = K0 := by
      dsimp [L0, K0]
      field_simp [ne_of_gt hbpos, ne_of_gt hA0] <;> ring
    have hIclear : I0 = K0+22*b*A0 := by
      dsimp [I0, K0]
      ring
    have hZclear : Z*b*A0 = 2*P0 := by
      dsimp [Z, P0]
      field_simp [ne_of_gt hbpos, ne_of_gt hA0] <;> ring
    have hJexpand :
        hullFive300_peJp r q X = 8*I0*P0+121*b*A0*K0 := by
      dsimp [r, q, X, A0, I0, P0, K0, hullFive300_peJp]
      ring
    calc
      hullFive300_peJp r q X = 8*I0*P0+121*b*A0*K0 := hJexpand
      _ = 4*I0*(2*P0)+121*b*A0*K0 := by ring
      _ = 4*I0*(Z*b*A0)+121*b*A0*K0 := by rw [hZclear]
      _ = 4*(K0+22*b*A0)*(Z*b*A0)+121*b*A0*K0 := by rw [hIclear]
      _ = 4*(b*A0*L0+22*b*A0)*(Z*b*A0)+
            121*b*A0*(b*A0*L0) := by rw [hLclear]
      _ = b^2*A0^2*((4*Z+121)*(A0-17+4/b+4/A0)+88*Z) := by
        dsimp [L0]
        ring
  have hba : 0 < b^2*A0^2 := by positivity
  have hclearPos :
      0 < (4*Z+121)*(A0-17+4/b+4/A0)+88*Z := by
    by_contra hn
    have hnonpos : (4*Z+121)*(A0-17+4/b+4/A0)+88*Z ≤ 0 :=
      le_of_not_gt hn
    have hprod : b^2*A0^2 *
        ((4*Z+121)*(A0-17+4/b+4/A0)+88*Z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hba.le hnonpos
    have hpositive := hJ
    rw [hJid] at hpositive
    exact (not_lt_of_ge hprod) hpositive
  have hdenZ : 0 < 4*Z+121 := by linarith only [hZ]
  have hratPos : 0 < A0-17+4/b+4/A0+88*Z/(4*Z+121) := by
    have hid : (4*Z+121)*
          (A0-17+4/b+4/A0+88*Z/(4*Z+121)) =
        (4*Z+121)*(A0-17+4/b+4/A0)+88*Z := by
      field_simp [ne_of_gt hdenZ]
    by_contra hn
    have hnonpos : A0-17+4/b+4/A0+88*Z/(4*Z+121) ≤ 0 :=
      le_of_not_gt hn
    have hprod : (4*Z+121)*
        (A0-17+4/b+4/A0+88*Z/(4*Z+121)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdenZ.le hnonpos
    rw [hid] at hprod
    exact (not_lt_of_ge hprod) hclearPos

  have hleft : 2*(N+f) ≤ z*A := by
    have hwN : 2*N ≤ w*N :=
      mul_le_mul_of_nonneg_right hw (by linarith only [hN] : 0 ≤ N)
    have hfeta : 2*f ≤ f*eta := by
      calc
        2*f = f*2 := by ring
        _ ≤ f*eta :=
          mul_le_mul_of_nonneg_left heta (by linarith only [hf] : 0 ≤ f)
    calc
      2*(N+f) = 2*N+2*f := by ring
      _ ≤ w*N+f*eta := add_le_add hwN hfeta
      _ = z*A := by rw [hetaRow]; ring
  have hFbound : 2*N/A + 2*f/A + 2-f ≤ z+w-f := by
    have hraw : 2*(N+f)/A ≤ z := (div_le_iff₀ hApos).2 hleft
    have hid : 2*N/A+2*f/A = 2*(N+f)/A := by
      field_simp [ne_of_gt hApos] <;> ring
    calc
      2*N/A + 2*f/A + 2-f = 2*(N+f)/A + (2-f) := by
        rw [hid] <;> ring
      _ ≤ z + (2-f) := by
        simpa [add_comm, add_left_comm] using
          add_le_add_right hraw (2-f)
      _ ≤ z + (w-f) := by linarith only [hw]
      _ = z+w-f := by ring
  have hEbound : 2*(a+c)/b + 2-c ≤ x+y-c := by
    have hay : 2*a ≤ a*y := by
      have hscaled := mul_le_mul_of_nonneg_left hy
        (by linarith only [ha] : 0 ≤ a)
      nlinarith only [hscaled]
    have hcd : 2*c ≤ c*delta := by
      have hscaled := mul_le_mul_of_nonneg_left hdelta
        (by linarith only [hc] : 0 ≤ c)
      nlinarith only [hscaled]
    have hbx : 2*(a+c) ≤ b*x := by
      calc
        2*(a+c) = 2*a+2*c := by ring
        _ ≤ a*y+c*delta := add_le_add hay hcd
        _ = b*x := hfanQ.symm
    have hraw : 2*(a+c)/b ≤ x := by
      apply (div_le_iff₀ hbpos).2
      calc
        2*(a+c) ≤ b*x := hbx
        _ = x*b := by ring
    nlinarith only [hraw, hy]
  have hA0ge : A ≤ A0 := by
    rw [hADef]
    dsimp [A0]
    linarith only [hp]
  have hArecip : 1/A0 ≤ 1/A := by
    apply (div_le_div_iff₀ hA0 hApos).2
    nlinarith only [hA0ge]
  have haN : 2*(b+Delta) ≤ a*N := by
    have hb0 : 0 ≤ b := by linarith only [hb]
    have hDelta0 : 0 ≤ Delta := by linarith only [hDelta]
    have hbB : 2*b ≤ b*B := by
      calc
        2*b = b*2 := by ring
        _ ≤ b*B := mul_le_mul_of_nonneg_left hB hb0
    have hcD : 2*Delta ≤ c*Delta :=
      mul_le_mul_of_nonneg_right hc hDelta0
    calc
      2*(b+Delta) = 2*b+2*Delta := by ring
      _ ≤ b*B+c*Delta := add_le_add hbB hcD
      _ = a*N := hCentralA.symm
  let S : ℝ := (1+2/b)*a + (1+2/A0)*N
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hZexpand : Z = 2*(b+Delta)*(1+2/b)*(1+2/A0) := by
    dsimp [Z]
    field_simp [ne_of_gt hbpos, ne_of_gt hA0] <;> ring
  have hSsq : 4*Z ≤ S^2 := by
    let ub : ℝ := 1+2/b
    let uA : ℝ := 1+2/A0
    have hub : 0 ≤ ub := by dsimp [ub]; positivity
    have huA : 0 ≤ uA := by dsimp [uA]; positivity
    have hcoef : 0 ≤ ub*uA := mul_nonneg hub huA
    have hmul : 2*(b+Delta)*(ub*uA) ≤ a*N*(ub*uA) :=
      mul_le_mul_of_nonneg_right haN hcoef
    have hquad : 4*(ub*a)*(uA*N) ≤ (ub*a+uA*N)^2 := by
      have hs := sq_nonneg (ub*a-uA*N)
      nlinarith only [hs]
    calc
      4*Z = 4*(2*(b+Delta)*(ub*uA)) := by
        rw [hZexpand]
        dsimp [ub, uA]
        ring
      _ ≤ 4*(a*N*(ub*uA)) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 4*(ub*a)*(uA*N) := by ring
      _ ≤ (ub*a+uA*N)^2 := hquad
      _ = S^2 := by dsimp [ub, uA, S]
  have hRatBound : 88*Z/(4*Z+121) ≤ S := by
    have hclear : 88*Z ≤ (4*Z+121)*S := by
      by_cases h22 : 22 ≤ S
      · calc
          88*Z = 4*Z*22 := by ring
          _ ≤ 4*Z*S := mul_le_mul_of_nonneg_left h22 (by positivity)
          _ ≤ (4*Z+121)*S := by
            have hh : 0 ≤ 121*S := by positivity
            nlinarith only [hh]
      · have hS22 : S ≤ 22 := le_of_not_ge h22
        have h22S : 0 ≤ 22-S := by linarith only [hS22]
        have hscale := mul_le_mul_of_nonneg_right hSsq h22S
        have hsquare : 0 ≤ S*(S-11)^2 := by positivity
        have hcubic : S^2*(22-S) ≤ 121*S := by
          nlinarith only [hsquare]
        have hZS : 4*Z*(22-S) ≤ 121*S := le_trans hscale hcubic
        nlinarith only [hZS]
    apply (div_le_iff₀ hdenZ).2
    simpa [mul_comm] using hclear
  have hOuterActual :
      e+Delta+g-21 + (1+2/b)*a + (1+2/A)*N +
          2*c/b + 2*f/A ≤ H-25 := by
    have hEbound' : 2*a/b+2*c/b ≤ x+y-2 := by
      have hid : 2*(a+c)/b = 2*a/b+2*c/b := by
        field_simp [ne_of_gt hbpos] <;> ring
      rw [← hid]
      linarith only [hEbound]
    have hFbound' : 2*N/A+2*f/A ≤ z+w-2 := by
      linarith only [hFbound]
    calc
      e+Delta+g-21 + (1+2/b)*a + (1+2/A)*N +
          2*c/b + 2*f/A =
        e+Delta+g-21+a+N+(2*a/b+2*c/b)+(2*N/A+2*f/A) := by
          ring
      _ ≤ e+Delta+g-21+a+N+(x+y-2)+(z+w-2) := by
        linarith only [hEbound', hFbound']
      _ = H-25 := by
        rw [hH, hNDef]
        ring
  have hrecN : 2*N/A0 ≤ 2*N/A := by
    have hh := mul_le_mul_of_nonneg_left hArecip
      (by positivity : 0 ≤ 2*N)
    simpa [div_eq_mul_inv, mul_assoc] using hh
  have hrec4 : 4/A0 ≤ 4/A := by
    have hh := mul_le_mul_of_nonneg_left hArecip
      (by norm_num : (0 : ℝ) ≤ 4)
    simpa [div_eq_mul_inv] using hh
  have hcdiv : 4/b ≤ 2*c/b := by
    apply (div_le_div_iff₀ hbpos hbpos).2
    have h4c : 4 ≤ 2*c := by nlinarith only [hc]
    exact mul_le_mul_of_nonneg_right h4c hbpos.le
  have hfdiv : 4/A ≤ 2*f/A := by
    apply (div_le_div_iff₀ hApos hApos).2
    have h4f : 4 ≤ 2*f := by nlinarith only [hf]
    exact mul_le_mul_of_nonneg_right h4f hApos.le
  have hOuter : A0-17+4/b+4/A0+S ≤ H-25 := by
    have hbase : A0-17 ≤ e+Delta+g-21 := by
      dsimp [A0]
      linarith only [hg]
    have hfourA : 4/A0 ≤ 2*f/A := hrec4.trans hfdiv
    have hcompare :
        A0-17+4/b+4/A0+S ≤
          e+Delta+g-21 + (1+2/b)*a + (1+2/A)*N +
            2*c/b + 2*f/A := by
      dsimp [S]
      have hleftRecip :
          2*N/A0 ≤ 2*N/A := hrecN
      have hNterm : (1+2/A0)*N ≤ (1+2/A)*N := by
        calc
          (1+2/A0)*N = N + 2*N/A0 := by ring
          _ ≤ N + 2*N/A := add_le_add (le_refl N) hleftRecip
          _ = (1+2/A)*N := by ring
      nlinarith only [hbase, hcdiv, hfourA, hNterm]
    exact hcompare.trans hOuterActual
  have hposOuter : 0 < A0-17+4/b+4/A0+S := by
    calc
      0 < A0-17+4/b+4/A0+88*Z/(4*Z+121) := hratPos
      _ ≤ A0-17+4/b+4/A0+S := by
        convert add_le_add
          (le_refl (A0-17+4/b+4/A0)) hRatBound using 1 <;> ring
  have hnegOuter : A0-17+4/b+4/A0+S < 0 :=
    lt_of_le_of_lt hOuter (by linarith only [hHlt])
  exact (not_lt_of_ge hposOuter.le) hnegOuter

end Heilbronn8.TriHull
