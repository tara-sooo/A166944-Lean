# Astra max 研究引き継ぎ資料 — Negative MIN / 双子素数予想

2026-11-28 JST。対象: tara-sooo/A166944-Lean, Issue #10 (親 #1), branch research/min-negative-lean-live-survival。目的は4.80後半の停滞を突破し、無条件の双子素数予想の証明へつながる新しい数学を得ること。研究の全履歴を順番に再読する必要はない。本資料を起点として、必要な原資料だけを開く。

## 0. 最初に解く問題（OPEN）

\(L=\log R,\ H=\lfloor R^{2/5}\rfloor,\ B=4H\) とする。標準初期値 \(A\in[R,2R]\cap6\mathbb Z\) の実軌道が初めて高さ \(H\) に達した位置を \(x\) とし、そこまでの総移動量 \(A-x\le B\) を要求する。異なる位置の集合を \(S_H(B)\) とする。

**主目標 M85:**
\[
 |S_{\lfloor R^{2/5}\rfloor}(4\lfloor R^{2/5}\rfloor)|
 \ge c\,R/(\log R)^2
\]
をある絶対定数 \(c>0\) について、十分大きい \(R\)（少なくとも無限に増大する明示された部分列）で無条件に証明する。十分大きい全 \(R\) の主張と部分列の主張は区別する。元の経過時間は \(\le3H\)。同じ終点を持つ多数の祖先は1個と数える。

M85 は中間研究目標であり、双子素数予想の十分条件ではない。これを固定しすぎて最終問題から離れないこと。より直接的な十分条件を導く、または M85 より強い核心障壁の突破を示す場合は、証明方針を変更してよい。低い高さの補題や有限データの追加だけを達成扱いにしない。

**より動力学的な診断:** \(q_{\min}(x)=\min(P^-(x-1),P^-(x+1))\) とし、\(q_{\min}<H/16\) を満たす第一到達状態を intrinsically active と呼ぶ（漸近的な強い診断は \(q_{\min}<H/L^6\)）。この種の状態で密度下界が得られれば、初期静止の延長だけでなく移動を経た輸送を証明したことになる。active 条件は M85 の必須条件ではない。

## 1. 正確な力学・記号・停止条件

- 状態 \((x,n)\): \(x>2\) 偶数、\(n\in\mathbb Z\) 符号付き時計。高さ \(h=x/2+n\)。初期状態 birth(A)=(A,3−A/2), h=3。元の経過時間 \(t=n-(3-A/2)\)。正の偶数の研究領域を扱う。
- 次の tick の時計 \(n'=n+1\)。偶数時計なら \(p\mid x+1,\ n'\equiv0\pmod{2p}\) を満たす奇素数、奇数時計なら \(p\mid x-1,\ n'\equiv p+2\pmod{2p}\) を満たす奇素数が eligible。
- 全 eligible 奇素数のうち最小のものが winner。候補なしなら idle。発火時 \(x'=x-p+1,n'=n+1\)、idle 時 \(x'=x,n'=n+1\)。平方根でのラベル打切りは実力学ではない。
- 高さ座標では発火時 \((x,h)\mapsto(x-p+1,h+1-(p-1)/2)\)、idle 時 \((x,h+1)\)。
- 実軌道では \(h\ge0,\ G=A-x=2(t+3-h),\ t=h-3+G/2\)。\(G\) 非減少、\(h\) の上昇は一 tick に高々1。発火は高さを増やさない。初回 H 到達は正確に H、最後は idle。固定 B の予算で途中の超過を除外してよい。成功経路は \(x\in[R-B,2R]\)。
- 前状態の高さ h で eligible な p は、符号 \(s=\pm1\) に応じ \(p\mid2h+3s,\ p\mid x+s\)（時計 parity も必要）。従って \(p\le2h+3\)。canonical prefix なら \(p\le2t+7\) という粗い年齢上界も使える。
- 発火完了後の状態 \((y,n')\): \(y\equiv c_s=1-s\pmod p,\ h'=mp+b_s\) (\(b_+=0,b_-=3,m\ge0\))。時計の合同条件はそのまま。ピンだけでは winner や canonical occupation を意味しない。
- 完全待機 \(w\) = 前の発火直後（または birth）から次の発火までの正の tick 数。空間因子の周期 \(2p\) により \(w\le2p\)、かつ次の待機 \(\le2q_{\min}(x)\)。不完全な最終 idle \(I<2q_{\min}(x)\)。同時刻なら最小素数。イベントスキップはこの最小 (wait,p) を厳密に選ぶ。
- \(x\) の両隣が素数なら、短い研究 horizon ではラベルが大き過ぎるため発火しない。逆は一般には成立しない。

正式な実装: [NegativeMINCore.lean @c9b2d47](https://github.com/tara-sooo/A166944-Lean/blob/c9b2d47f7cf473e3f8768a7c9292d4b2205c536a/research/lean/NegativeMINCore.lean) (blob bd0fef2174a497a5c9988b169ea5441d66c5b649)。過去の記録では Lean 4.33.1, CI run 46055354706 green, 614 theorem declarations と報告。今回ソースを再取得したが CI は再実行していない。def を含む全宣言数とは区別。独自 executable oddPrime と標準 Nat.Prime の同値ブリッジは別途確認すること。入口の定義 State, eligible, firstLabel, winner, tick, birth, evolve, orbit, height2, gain, FirstEvent。関連 theorem: tick_wall, evolve_wall_gain, gain_evolve_add, mixedSupport_gain, finiteSupport_gain_bound, completed_segment_wait_bound, optimalNetDeath_formula, optimalNet_record_sharp, twin_above_of_optimal_net 等。必要な宣言だけ検索して読む。

## 2. 双子素数予想に接続できる既存の十分条件

### 2.1 最短の証明鎖: 低移動量の実軌道

[mod2310 研究ノート](https://github.com/tara-sooo/A166944-Lean/blob/c0e45b0e53ba494ede63cb17b85609891683fe7d/research/2026-11-28-min-negative-mod2310-and-single-cap-gain-record.md) にある整数ポテンシャル \(0\le\Phi\le1580\):
\[
48w-102(p-1)\le\Phi(\mathrm{target})-\Phi(\mathrm{source}).
\]
任意の連続する完全イベントのブロックに対して
\[
 W\le\frac{17}8G+\frac{395}{12}
       -\frac18\sum_{\rm events}(p-281)_+.
\]
ここで W は完全待機の和、G は同じイベントの総移動量。ポテンシャルは緩和有限状態グラフを全数検査し、無限ラベルの尾を解析的に処理した証明候補。単なる軌道標本ではないが、まだ Lean 化されていない。[C++ 証明書](https://github.com/tara-sooo/A166944-Lean/blob/faec05e6bb82acc679ab4e11569d1e608fe22654/research/lean/negative_min_mod2310_potential.cpp) は 148,495,530 lifted edges を再検査した過去の実行記録。

\(T=\lceil8\sqrt{2R+1}\rceil\) に対し、非双子素数中心なら \(q_{\min}(x)\le\sqrt{2R+1}\)。\(I=T-W<2q_{\min}\) より
\[
 17G_T-\sum(p-281)_+\ge8(T-2\sqrt{2R+1})-790/3.
\]
従って、無限に増大する slab R で canonical A と固定 \(\eta>0\) に対し \(G_T/T\le6/17-\eta\) を得れば、双子素数は無限。単に \(G_T/T<6/17\) という strict inequality だけでは有限加法誤差に負け得る。元の 0.40 目標は M85 候補で、8√ の時点では双子素数を強制しない。\(T\ge14\sqrt{2R+1}\) なら 0.40 に固定しても大 R で強制できる。

**根本障壁:** [粗さの同値性](https://github.com/tara-sooo/A166944-Lean/blob/627f57be4c7a600293079cb2bd4e0c0c862f4139/research/2026-11-28-min-negative-roughness-equivalence-variable-level-sieve.md)。任意の固定 \(\gamma<8/17\) について
\[
 q_{\min}(x)>\frac{1-17\gamma/8}{2}T-\frac{395}{24}
\]
が \(G_T\le\gamma T\) の必要条件。時間指数 θ（定数倍を許す）の低移動量 witness の存在は静的な粗い隣接数の存在と同値。逆向きは粗い中心を birth として、最大発火ラベルの年齢上界で十分短い horizon を選ぶ。θ=.5 の 0.40 at 8√ には少なくとも .6√ 規模の粗さが必要で、非双子中心は balanced semiprime を含む。二つとも合成なら四素数の ad−bc=2 型。通常の篩のパリティ障壁を回避したことにはならない。

### 2.2 別の十分条件: single-cap 正の record bins

上記 mod2310 ノート §§3–5 の別ルート（解析上界は paper deduction、最適化の有限部分は既存 Lean）。\(T\asymp\sqrt R/L^b\)（固定 \(b>0\)）、全 canonical cohort \(N\asymp R\)、窓・観測・prefix/death 規約は原ノート/Lean をそのまま使う。低ラベル cost \(17(p-1)\) for \(0<p<Y\), \(Y=T/(\log L)^a,\ 0<a\le1\)、その他0、観測 tick reward 8。物理状態 cap M=1 の最適 net profit \(P_1^*\) に対し
\[
 P_1^*/(8NT)\le C\,\#\{\text{slab の双子中心}\}/N+O_b(\log L/L^3).
\]
従って \(P_1^*/(8NT)=\omega(\log L/L^3)\) を無限に増大する部分列で得れば双子素数は無限。既存の厳密最適化は recordProfit の正の bins を数える形で使える。大きな cap や二次モーメントはこの特定ルートの必須条件でない。まだ下界は未証明。ここに M85 の輸送を接続する新原理が得られるなら有力。ほかの good-field 路線の未レビュー多形式上界と混ぜない。

### 2.3 もう一つの接続先: 近平方根の粗い中心

\(H\asymp\sqrt R/L^b\) で \(G\le H/4\) の first-H witness なら
\[
 I\ge H-3-(13/8)G-395/12,\quad q_{\min}\ge19H/64-O(1).
\]
既存の二形式上界によると、\(q_{\min}\ge H/L^c\) の非双子素数中心（固定 c）は \(O(R\log L/L^3)\)。したがってこの粗さを持つ実到達先の \(\Omega(R/L^2)\) 下界を近平方根で得ても十分。M85 の大きい予算 \(4H\) では粗さは保証されないため、この結論を自動的に得たと扱わない。次の段階ではどの橋を閉じるかを明示する。

## 3. 現在の無条件 lower の起点（paper deductions）

### 3.1 Canonical semiprime supply（最重要）

[積の分布・逆祖先ノート](https://github.com/tara-sooo/A166944-Lean/blob/c20b70c398f0e2165e08da694790dacc1b724d50/research/2026-11-28-min-negative-product-sieve-canonical-supply-and-reverse-ancestry.md) §§1–3:
\[
 A=pv-1\in[R,2R],\quad
 R^{.2855}\le p\le R^{.2856},\quad p,v\ {\rm prime},\quad
 P^-(pv-2)\ge4R^{.2856}.
\]
各固定 v 条件 RESET: \(v=1\bmod420\)、HIGH: \(v=7\bmod12,\ v=1\bmod5,7\) で \(\gg R/L^2\) 個の canonical 根。粗さで \(p=1\bmod3\)、従って \(6\mid A\)。最初の実発火は p。HIGH は wait \((3p-7)/2\), \(x_0=p(v-1), n_0=p-x_0/2, h_0=p\)。RESET の発火後 h=0、直後の3 tick の静止で新しい birth(x) と一致するよう構成。
- Wu (2004) [原論文](https://www.impan.pl/shop/publication/transaction/download/product/82961), printed pp220–222, Lemmas 2.2,2.5, (i),(ii)。小さい prime p に SW 条件（p は AP に制限しない）、大きい prime v の indicator に任意の固定 AP。\(X=MN\asymp R,\nu=\log N/\log X\in[1/4,2/7]\)。普通の well-factorable order-one weight の分布指数 \((2-\nu)/3-\epsilon_{\rm dist}\)。固定 residue +2 に適用。
- \(D=R^{.5713},\epsilon_{\rm dist}=.0001,z=4R^{.2856}\)。\(d-2\theta_2=.0001\)、分布 margin \(2/30000\)。linear lower f(s)>0。dyadic p box ごとに \(\gg R/L^3\)、\(\gg L\) boxes。sieve correction \(p\mid d_0\) は weighted sum \(\ll B_P L/R^{.2855}\)。普通の下界篩 remainder weight の正確な適用は原ノートおよび Lichtman [arXiv:2109.02851v2](https://arxiv.org/pdf/2109.02851) Theorem 2.10, (5.15)–(5.20) を確認すること。原論文の内容は当時のノートで検証した記録があるが、Astra による独立確認はまだ。
- 固定指数を上げるには \(d>2\theta,\ d<(2-\theta)/3\) の両条件から \(\theta<2/7\)。これは現在の入力の限界であり、一般の不可能性定理ではない。固定 p ごとの BV では概ね \(\theta<1/5\)。
- この family の birth は静止したまま \(h_*=\lfloor R^{.2854}\rfloor\) に到達する。従って \(|S_{h_*}(0)|\gg R/L^2\)。これが M85 の最も単純な種。

### 3.2 種からの既知の拡張（ここを繰り返すだけでは停滞）

[modular short transfer](https://github.com/tara-sooo/A166944-Lean/blob/07503a495c962aeb854ba29e7a20a73e7f6eefe5/research/2026-11-28-min-negative-modular-short-transfer-and-canonical-approximation.md):
HIGH 到達後、\(z=cL\)、小素数試行の profile は \(p,v\bmod B_0\), \(B_0=4\prod_{\ell\le z,\ell\ {\rm odd}}\ell\le R^{.01}\) で決まる。外部 eligible \(q>z\) は \(q\mid2p+2u-g+1-2b_s,\ q\mid p(v-1)-g+s\)（時刻 u、既移動 g）。小 q は二つの CRT、巨大 q は高さ整数の因子数で評価。例外
\[
 E(T_0)\ll R/L^2\,[T_0/(z\log z)+T_0 R^{-.05}].
\]
小さな定数倍 \(T_0\asymp L\log L\) まで \(\gg R/L^2\) 本が完全一致、高さ \((1-o(1))p\)、移動 \(O(L^2\log L)\)、物理状態分離。実際の起点の p,v 構造を使うので任意の後続占有集団には適用できない。後続発火で得られた正の高さ増加は [二連続正増加](https://github.com/tara-sooo/A166944-Lean/blob/58cabbc3669768c54fa8d348dfaf7104c4884544/research/2026-11-28-min-negative-consecutive-positive-height-events.md) の p,q,3 pattern（q は loglog 規模）。初回発火前の最高高さ \((3p-3)/2\) を超えない。真の新記録とは別。

## 4. 主要な大域的道具（証明済み部分と OPEN を区別）

以下の §§4–6 は数学的論証または有限証明書のある paper results。新規 Lean 検証済みとはしない。

### 4.1 固定予算 min-plus と全合流損失

[断面輸送・terminal defect](https://github.com/tara-sooo/A166944-Lean/blob/0c4cd9ee528c3f052ec49db917d6bf02d32a54aa/research/2026-11-28-min-negative-height-section-minplus-and-terminal-defect.md) §§4–6。\(a_h^B(x)\) = first-h state へ到達する最小の実 canonical 祖先 A（存在しなければ∞）。同一の物理状態からの未来は一意、以後の総 gain=A−x なので最小 A が常に最適。固定 B なら中間高さの最小祖先だけを伝播して厳密に次断面の最小祖先を再現する。下降を許す。途中で B を小さくしてから大きくする版は下界 subset であり厳密再現ではない。

各段階の異なる入力数 \(N_j\)、budget failure \(e_j\)、合流による削除 \(m_j\) について \(N_{j+1}=N_j-e_j-m_j\)。種の \(h_*\) から H へ倍増させる O(L) 段階において

**OPEN A:** \(e_j+m_j\le C N_j/\log h_j\) を一貫したコホート・固定予算で一様に証明できれば M85。実際 \(\sum 1/\log h_j=O(1)\)、積 \(\prod(1-C/\log h_j)\) は正の定数以上。より一般に全損失 \(\le(1-c)N_0\) の直接証明でもよい。有限データでは現状この損失率を保証できていない。各段階で定数割合を失うだけでは不十分。

全グラフで代表を1個だけ残し、各 merge と budget exit を一度だけ課金する厳密会計がある。実軌道の辺を変えず、最小 A を選ぶ。既に到達した頂点への source injection の合流も計上。DAG の順序は x 降順、同一 x では h 昇順。first-H は吸収。ここに以下の局所上界を使う。

### 4.2 Return closure と last entry

[再入場・strip](https://github.com/tara-sooo/A166944-Lean/blob/5eb4d861204018f0696682efec5e65b61a660cc8/research/2026-11-28-min-negative-last-entry-strip-and-terminal-scale-gap.md) §1。下端 h0 の first-entry minimum から、上端 H に達するか h0 未満に落ちて次の upward entry へ戻るまで進める。return は x を厳密に減少させるため descending x sweep で全 upward entry minimum と正確な first-H minimum を回復。全 entry を高さ帯に注入し、帯外へ下がる経路は打切る方式も最終出力は同じ。成功経路には last upward entry があるから。first entry のみ注入した confined trial は取りこぼす。

### 4.3 近似モデルの残差と uniform defect

同じ DAG 頂点、同じ source \(b(v)\)、出次数≤1、共通辺の重み \(w\in[0,1]\) として true capped flow \(C(v)=\min(1,b(v)+\sum w C(u))\)。trial F との差の正部は後続へ分岐して増幅されない。任意試験配列 F の正残差 \(r(v)=[F(v)-\min(1,b(v)+\sum_{\rm true}w F(u))]_+\) に対し \(\sum C(\text{sinks})\ge\sum F(\text{sinks})-\sum r(v)\)。さらに common subgraph と各 sink に至る last-bad edge のみを用いる \(C(s)\ge[F(s)-D_s]_+\) がある。重み \(L^{-\Delta x/H}\) を使う場合、非予算祖先の寄与は固定 B=4H で合計 O(R/L^4)。clipped flow の中間断面再始動は一般には min-plus のように厳密でない。

特に整数 distinct-sink 版は有用。同じ予算を持つ実占有入力から trial を走らせ、異なる成功終点ごとに一代表を選ぶ。異なる終点への trial paths は頂点非交差。従って、true edge と異なる物理頂点の総数 E に対し \(N_{\rm true}\ge N_{\rm trial}-E\)。近似モデルの successful paths であっても canonical 入口が必要。

帯 [h0,H], W=H−h0, cutoff Z≥R^α (固定 α>0) の中だけ p>Z を無視する場合、変更頂点は p|2h±3 と x≡∓1 modp の同時ピン。各 h に O(1) factors、O(R/Z) positions。従って
\[
 E\ll RW/Z.
\]
H=R^.4,W=R^.2,Z=R^.3 なら E=O(R^.9)=o(R/L²)。成功した confined 経路の発火は p≤2W+1、しかし中間 (2W+1,Z] の eligible 発火は exit として検査を省けない。複数の疎な帯に変更を限定すれば E≪RΣW_j/Z_j（再訪問を重複課金しない）。全高さ帯をこの条件で覆うことはできない。**OPEN B:** 実入口から trial 自身の密度下界。これは前回まで最大の未解決点。

### 4.4 逆祖先を圧縮する厳密漸化式

[product sieve & reverse](https://github.com/tara-sooo/A166944-Lean/blob/c20b70c398f0e2165e08da694790dacc1b724d50/research/2026-11-28-min-negative-product-sieve-canonical-supply-and-reverse-ancestry.md) §4。固定の許容根区間、target age bound は最初に上端 Ahi を一回縮める。ℓ(x,n) は x における n 以下の最新 eligible tick（実 occupation を仮定しない）。I(x,n)=1 iff x が許容根かつ birth clock∈[ℓ,n]。実祖先数は
\[
 C(x,n)=I(x,n)+\sum C(x+p-1,\tau-1)
\]
（ℓ≤τ≤n、poststate spatial/height/clock pins、親の actual minimum=p を満たす incoming）。last arrival は一意、空間逆向きに増大するので有限。birth/arrival は ℓ を含む。FIRST-H の逆グラフには以前の H hit を禁止する制約を追加する。祖先存在と祖先数を別に扱う。**OPEN C:** この漸化式から実祖先の存在を密度規模で下界評価。局所の多数の incoming pins だけでは不可。

### 4.5 成功を保証する特別な高い帯

[clean translated height](https://github.com/tara-sooo/A166944-Lean/blob/8145ffbd6a0c3e334c004ff49fe422879ce676ed/research/2026-11-28-min-negative-clean-height-translation-and-basin-repair.md)。\(D=\lfloor c\log L\rfloor,\ z=2D+11,\ Q=2\prod_{3\le p\le z}p,\ B_0=2Q\le L^\epsilon\)。低い高さ3から3+D へのモデルは小素数壁で gain<Q、必ず上端に到達、出力 fiber≤Q/2+1。shift \(a=0\bmod B_0\) で \(2a+c'\), \(c'=-3,-1,\ldots,2D+7\) に z<p≤Z=exp(√L) の因子がないと、切断 trial は低いモデルの厳密な平行移動。各窓長 R^β (0<β<.4) に R^{β−o(1)} 個の shift が存在（Bonferroni/CRT、可変次元の固定次元篩を仮定しない）。任意の実入口集団 S0 と残り予算≥Q で
\[
 N_{\rm true}\ge |S_0|/(Q/2+1)-O(R(D+1)\sqrt L/e^{\sqrt L}).
\]
任意の固定 log power に対し誤差は無視可能。しかし入口の存在、帯の間の輸送、fiber loss の累積は未証明。帯幅の改善だけでは多項式距離をつなげない。

## 5. すでに分かった障壁・除外（Astra の時間を節約する）

1. **固定小素数 cutoff:** \(Q_z=2\prod_{3\le p\le z}p\) の倍数を越えて下へ移動できない。連続小ラベル区間 G<Q_z。z=o(log H) で first H に達する実軌道は qmin≥(1−o(1))H/2。単純な trial/common graph の下界は静的粗さを証明しているだけの場合がある。近平方根で非双子数の粗さ上界に当たる。
2. **first-record deficit:** [deficit theorem](https://github.com/tara-sooo/A166944-Lean/blob/ed81dc1f3660062ccfc1ce92bfdf01f90e813389/research/2026-11-28-min-negative-active-first-record-and-deficit.md)。発火後 \(d_j=H-h_j>0,\ p_j\le2d_j+1,\ d_{j-1}\le4d_j+2\)。初回の強化と終端 idle から \((6q_{\min}-1)4^{k-1}\ge H-2\) for k≥1。qmin<H/L^6 には Ω(log L) 回の発火が必要。2発火 active 下界は小さい固定 δ で H=R^δ, R/L^9、CRT modulus H³。H=.4 には通用しない。
3. **高い局所キーと canonical ancestry は別:** [top local corridors](https://github.com/tara-sooo/A166944-Lean/blob/e9f611d1e40e414b7c663df569f2cabc5b1a7e9f/research/2026-11-28-min-negative-top-local-corridors-and-entry-reduction.md) の局所 top keys は豊富でも、標準 birth からの reachability を保証しない。345有限 proxy targets のうち祖先のあるものは1（10根）、逆漸化式で一致。この数字は漸近推定でない。
4. **global merger upper の既知部分:** [macro-small connectors](https://github.com/tara-sooo/A166944-Lean/blob/7499425edc87c961cf5f757848d73db676d1e65c/research/2026-11-28-min-negative-macro-small-connector-terminal-reduction.md)。z=c log L,Q≤L^.25, macro Y=H/L^.25,K=H/L^5。rough-neighborhood macro keys O(R/L^2.5) と非reset pair O(R/L^3.75) を削除すると、良い非reset macro→small connector は全区間互いに非交差、良いresetとの交差もなし。reset-reset、fast/intermediate contacts、budget exits、source injections は残る。全損失の上界ではない。
5. **terminal exclusion:** 同ノート §4、最後の anchor p≥Y'=H exp(−√L) 以降の移動 d≤Q≤L^.25 の witness を一つでも持つ distinct first-H sites は O(R/L^2.25)。粗さに関係なし。[last-entry note](https://github.com/tara-sooo/A166944-Lean/blob/5eb4d861204018f0696682efec5e65b61a660cc8/research/2026-11-28-min-negative-last-entry-strip-and-terminal-scale-gap.md) §3 の強化: fixed θ<.5, H=R^θ, fixed α>0, p≥R^α, d≤Q の場合、O(R/L^2.25) 例外以外は qmin(x)>p exp(√L)。高さ alignment と二形式篩で得た必要条件。θ=.5 に自動拡張不可。したがって large anchor を増やすだけでは active density lower にならない。
6. **未確定の .295/.296 篩:** [variable-level/switching draft](https://github.com/tara-sooo/A166944-Lean/blob/627f57be4c7a600293079cb2bd4e0c0c862f4139/research/2026-11-28-min-negative-roughness-equivalence-variable-level-sieve.md) は appended prime 付き remainder weights の分布定理への transfer が未レビュー。数値 margin が正でもこの step が未解決。Pascadi arXiv:2505.00653 Prop5.5/Thm5.4, Lichtman arXiv:2109.02851v2 Lemma5.3/Cor5.6, (6.17)–(6.20) を原文で検証するなら別途進める価値があるが、.295 を達成済みとして他の証明に使用しない。これ単独で M85 でもない。
7. **uniform drift の危険:** 一様 CRT 状態モデルでは各 prime eligibility ~1/p²、期待 gain ~const loglog z。実軌道分布ではない。一様分布・独立性・正 drift を仮定した長期推定で証明を代用しない。

## 6. 有限データ: どこに計算を追加する価値があるか

最初から全 finite audit を再実行する必要はない。必要な検証を絞る。

| checkpoint | 実行済みデータ（漸近証明ではない） | 示唆 |
|---|---|---|
| min-plus | R=3,072,000, h=71→142→284→393: 74,437→53,290→40,335→35,465 sites; 合流19,608,12,228,4,567; budget failure1,539,727,303 | 合流が主要損失。最終 sites の33,886は min gain<H/4、active qmin<H/16 は40 | 
| strip/return | R=768,000,H=226,W=56: first confined10,636, 全10,884, trial11,650, common10,882 | last entry が必要。太い帯の粗い E は大き過ぎる |
| clean-height | 6有限 clean blocks / 6,006 local starts / 5,949 common input transfers | local transfer は機能するが入口は canonical とは限らない |
| basin repair | R=192,000,H=129,z=31: common3177, preserved3180, exact same sink3180, true3391 | 誤差修復だけで大域的改善は小さい |

再現用の pinned files:
- [height section min-plus C++](https://github.com/tara-sooo/A166944-Lean/blob/09b59095d0341f4560397a2cba089c05b1ee33ee/research/lean/negative_min_height_section_transfer_audit.cpp) / [CSV](https://github.com/tara-sooo/A166944-Lean/blob/ee4e0fb4030b1ebf2d7790cd998ef3a166e6aa41/research/lean/negative_min_height_section_transfer_audit.csv) (g++ -O3 -std=c++17, 出力/CLI は原コード参照)。
- [height residual pilot](https://github.com/tara-sooo/A166944-Lean/blob/0b213f7f689f85c7be80357aaf9fde390954bdc7/research/lean/negative_min_height_residual_pilot.cpp) (floating tolerance; exact interval certification ではない)。
- [reverse audit](https://github.com/tara-sooo/A166944-Lean/blob/bf424c09b85e0e2881f3f6f9e6090d4df815d96c/research/lean/negative_min_reverse_ancestry_semiprime_audit.mjs)
- [last-entry strip audit](https://github.com/tara-sooo/A166944-Lean/blob/b7fb91c6fe9e881b13cf00d52b07a7b1e22411d4/research/lean/negative_min_last_entry_strip_audit.mjs)
- [clean height audit](https://github.com/tara-sooo/A166944-Lean/blob/791ae69296d8e0c582421fd1190a51a5ff841715/research/lean/negative_min_clean_height_translation_audit.mjs)
JS は node <file>。既存ノートにパラメータと finite proxy の限界を記録済み。数値検証を増やすなら「どの未証明補題の反例を探すか」を先に定義し、単なる R の増加で終わらせない。

## 7. Astra max に期待する研究（候補であって拘束条件ではない）

最初に、M85 と最終十分条件の間の論理的距離を点検する。主目標が良い中間指標か、別の直接目標がより強力か比較する。次に、最も有望な一つを選び、証明を最大限進める。

**候補 A: 合流損失に対する大域的下界/上界。** §3.1 の種から §4.1 の厳密会計へ。既知の削除可能クラスを除いたうえで、fast/medium/idle/reset/source の全損失を同時に制御する。例えば各 merge に過去の異なる素数因子、異なる wall-crossing、または消費された gain を charge し、重複課金を制限できないか。必要量は O(N_j/L) per dyadic scale か、全段階で総損失<(1−c)N0。一般論だけではなく実 pin を使って定数・log 指数を閉じる。反例なら、どのクラスが必要量を超えるか示す。

**候補 B: 双対・逆方向からの basin lower。** 各 canonical 根の first-H への成功、失敗、合流は有限 DAG の逆方向色付け、min-plus potential、吸収境界への flow として完全に定義できる。逆漸化式を first-hit 制約付きにし、占有を保証する適切な arithmetic subsolution または多重度の制御を探す。出次数1なので、異なる成功 sinks の祖先経路は交差しない。候補的な「豊富な逆枝」の存在と actual winning/ancestry の証明を切り離さない。全グラフをそのまま計算するだけのアルゴリズムは漸近下界にならない。

**候補 C: 異なる解析的整数論の手法。** 粗さへの還元が不可避なら、現在の積の分布指数 2/7 を越える実質的な手法を探す。例えば switching/double sieve、複数の bilinear variables、dispersion、factorable sieve weights、加法的組合せ論の構造など。ただし実際に該当する剰余類・係数・平均範囲への適用を原定理からチェックする。もし静的粗さはさらに難しいなら §2.2 の record lower 等へ転換する。既存定理の仮定を満たさないまま exponent を上げない。

**優先する成果:** 単発の局所補題ではなく、上記のいずれかについて新しい定理を証明し、その定理を既存の種と十分条件に代入して残る gap を定量化する。障壁があれば反例や必要条件を得て別候補へ進む。可能なら4.85を越えて無条件証明まで進める。全履歴・多数の小補題の再説明より、新しい証明の核心に時間を割く。現時点で新方針が成功するかは未確定。

## 8. 検証と保存、成果判定

- 4.80: 多項式規模の実軌道の lower/局所解析。現在ここ。4.85: M85 または同等以上の根本障壁の突破を無条件に証明。4.90: 双子素数無限性を導く定量条件を閉じる。4.95: 無条件の全証明案が揃い独立レビュー可能。5.00: 全証明が独立に検証され、可能な限り Lean で形式化（有限 audit の PASS のみではない）。
- 中心の証明は lemma→dependency→conclusion を明示。有限例・heuristic・conditional・paper proof・kernel-checked を区別。既存の論証も精査し、誤りを発見したら依存結論を修正する。
- 論文を使う場合、[Context BOOTSTRAP](https://github.com/tara-sooo/ChatGPT-Context/blob/main/BOOTSTRAP.md) の調査手順と verification/discovery protocols に従い、原論文の正確な theorem/section、全仮定、範囲、主項/誤差、重みを対応付ける。原文を未確認の新しい定理を既知扱いしない。
- Lean の数学的定義、Nat/Int の境界、prime bridge、証明書の無限尾、外部解析定理の扱いを検証。sorry/admit/新規未証明 axiom で閉じた体裁にしない。証明構築と独立査読を可能な範囲で別に実施し、独立した human review は実施された場合のみ記載する。
- 研究ノート・コード・出力・Lean を対象ブランチ上の実ファイルとして GitHub 保存し、commit SHA と remote readback で照合。main や他 research lanes を変更しない。ローカル worktree を使うなら Context の sparse checkout/storage discipline に従う。関連 Issue #10 に成果と未解決点を記録。重い環境構築・不要な一括 checkout は避ける。
- 今回の引き継ぎは既存資料の編集・統合であり、新しい証明の完成や Astra の実行を意味しない。

## 9. 最初に開く原資料（推奨順）

1. 本資料 §0–§7。
2. [0c4cd9e — min-plus, global losses, active barrier](https://github.com/tara-sooo/A166944-Lean/blob/0c4cd9ee528c3f052ec49db917d6bf02d32a54aa/research/2026-11-28-min-negative-height-section-minplus-and-terminal-defect.md)
3. [c0e45b0 — twin sufficient condition and record objective](https://github.com/tara-sooo/A166944-Lean/blob/c0e45b0e53ba494ede63cb17b85609891683fe7d/research/2026-11-28-min-negative-mod2310-and-single-cap-gain-record.md)
4. [c20b70c — true initial supply / reverse recurrence](https://github.com/tara-sooo/A166944-Lean/blob/c20b70c398f0e2165e08da694790dacc1b724d50/research/2026-11-28-min-negative-product-sieve-canonical-supply-and-reverse-ancestry.md)
5. [5eb4d86 — last-entry and strip defect](https://github.com/tara-sooo/A166944-Lean/blob/5eb4d861204018f0696682efec5e65b61a660cc8/research/2026-11-28-min-negative-last-entry-strip-and-terminal-scale-gap.md)
6. 選んだ方針に応じて §5 の原資料・Lean の関係宣言。

本資料の source pins は主な論証についてこの turn に GitHub から読み直した。§3.2 の二連続増加などの補足リンク・コード/CSV の一部は原ノートに記録された locator を採用。すべての定理の独立再証明・全コード再実行は本資料作成の範囲外。最新の研究レベルを上げたとの主張はない。
