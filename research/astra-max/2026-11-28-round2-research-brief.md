# Astra max 第2回研究引き継ぎ — 5/16 の先と大域輸送

2026-11-28 JST。対象: tara-sooo/A166944-Lean、Issue #10（親 #1）、branch research/min-negative-lean-live-survival。研究内容の基準スナップショット 94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce。現在水準4.80後半。第1回の使用量制限からの再開用。最終目標は無条件の双子素数予想、今回の目標は M85（4.85）または同等以上の核心突破。全履歴を再読せず、本資料の優先順で原ノートを開くこと。

旧引き継ぎ（力学の定義・初期の証明鎖・既存の道具の詳細）:
https://github.com/tara-sooo/A166944-Lean/blob/3aca5220fede34116e9ad300cfb0d2d44f3767c9/research/astra-max/2026-11-28-research-brief.md

## 1. 第1回の成果と今回の位置

Astra 第1回はユーザー報告で5時間枠の使用量制限により中断。記録された思考表示は34m46s。Astra は Wu の分布定理を用いた3素数積の種を得て、固定 sigma<3/10 に対する密度下界を論証し、Pascadi の二因子化による 5/16 を検討中だった。前回の保存成果:
https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-three-prime-supply.md
その後の GPT-6.2 研究では Wu 原論文の該当箇所を確認し、Pascadi の二因子用 squarefree-mask を構成、任意の固定 sigma<5/16 の静止 first-height 密度下界を paper deduction として得た。ただし Prop.4.4 の Q3=1 の定数 dyadic 端点解釈は独立レビュー待ち。以後の5/16を越える下界や M85 は未達。最新の動的経路構成は §4。第1回の仮説や試行をそのまま復元して繰り返す必要はない。

Lean core: research/lean/NegativeMINCore.lean、blob b0e26798535b2c997f1383c1dc37bbe560aac938、過去の狭義 core CI 46122447492 成功、定理宣言618（private含む）。近年の解析的補題は paper deductions と有限検証であり、Lean 検証済みではない。Mathlib adapter の条件付き推論は無条件の下界を含まない。今回の引き継ぎ作成では新規 Lean ビルドや独立数学査読は実行していない。

## 2. 目標と厳密な力学

L=log R。標準初期状態 A∈[R,2R]∩6ℤ、(x,n)=(A,3−A/2)、高さ h=x/2+n。次時計 n'=n+1 の偶数時は p|x+1, n'≡0 mod 2p、奇数時は p|x−1, n'≡p+2 mod 2p を満たす奇素数の最小が winner。発火 x'=x−p+1, h'=h+1−(p−1)/2、候補なしなら h'=h+1。p≤2h+3（preheight、厳密な候補は 2h±3 の素因数）。qmin(x)=min(P^−(x−1),P^−(x+1))。全待機 w≤2qmin(source), w≤2p。最終 idle I<2qmin(x)。発火後の空間・高さピン: plus y≡0,h'≡0 mod p; minus y≡2,h'≡3 mod p。

G=A−x、経過 t=h−3+G/2。最初の高さH到達は最後が idle、発火後高さは増えない（p=3なら不変）。区間内で途中にHへ到達した経路を後の「first-H」として数えない。成功軌道の空間は [R−4H,2R]。同じ物理状態からの未来は一意。

M85（OPEN）: H=floor(R^(.4))、G≤4H、異なる実 first-H 到達位置の数 N_H≥c R/L²（固定 c>0、全十分大Rまたは無限増大する部分列）。同じ終点の祖先多数は1個。局所 connector、発火後の HIGH anchor、固定時刻の visited state、補助 trial の終点は、そのまま canonical first-H の下界ではない。M85 そのものも双子素数予想の十分条件ではない。

## 3. 第一優先 — shifted prime-product の正の下界で 5/16 を越える

### 3.1 既存の到達点と最初に確認する依存関係

https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-pascadi-two-factor-supply.md

Wu 2004 Lemma2.5 の exponent (2+nu)/4 は短い unrestricted prime u と長い m=pv に適用する。短い係数の SW/rough support を守る。Pascadi arXiv:2505.00653v2 Def.4.3, Prop.4.4 の二因子 Q3=1 端点では、任意の二つの独立した 1-bounded 係数を使う。level D=R^(5/8−delta)、短変数指数3/8の直下、固定 power slack。通常の二因子 well-factorable lambda=lambda1*lambda2 の squarefree/odd/sifting-prime restriction は各因子の制限と sum_{e|gcd(d1,d2)}mu(e) で処理する。e≤L^K を分布定理、尾を O(R L³/L^K) で抑える。mask の結果を well-factorable と仮定する必要はない。ここで Q3=1 が許されるか、原文の定数 dyadic 端点と proof/Prop.4.5 を短く独立に確認すること。失敗なら修正または代替入力を探し、依存する結論を降格する。原論文の定理そのものを全て再証明する課題ではない。

通常の s>2 下界だけでは分布指数 5/8 を超えないため、粗さ指数の限界は5/16。より高い level の文献を機械的に代入しても解決しない。Yang arXiv:2608.13299v2 の長い free integer l に prime/rough indicator を挿入することは未許可。Ratliff Zenodo v3 の .3844197214、>1/3 は v4 (2026-11-22) で著者撤回、旧版を使わない。通常の下界篩を繰り返すだけでなく、実 sequence の乗法構造に踏み込む必要がある。

### 3.2 明示された OPEN target（最優先）

https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-variable-cutoff-and-absolute-marginal.md

実 source n=pv∈[R+1,2R+1]、p,v prime、p指数 [.374900,.374950]、v>p。B_R=#source~c R/L。C2=prod_{ell>2}(1−1/(ell−1)^2)、M_R=4 C2 B_R/L≈R/L²。S(z)=#source with P^−(n−2)≥z。S_k(z) は k|n−2 を追加。d=.6246、二因子容量 .3748,.2498。F0(b)=log((d−b)/b)/d。q指数 t∈[.160,b)、a(t)=(d−t)/3+.0002。Buchstab の二段の厳密恒等式と ordinary plateau から（上記の分布定理への依存あり）
    S(R^b)/M_R ≥ F0(b)+ C_R(b)/M_R−epsilon
を任意に小さい固定 epsilon>0 で得る。C_R(b)=sum_q sum_{R^a(t)≤r<q} S_qr(r) は非負の incidence correction。prime triple 部分 K_b を使ってよい。

D_b^* は t,u=log_R r の領域:
    .160≤t≤b−.0002,
    a(t)≤u≤t−.0002,
    u≤1−2t−.0002,
    t+u≤.49.
k=qr について既存の絶対剰余分布（固定 margin、平方自由 k≤R^.49、因子 [.08,.35]）:
    sum_k |#(n=2 mod k)−B_R/phi(k)| ≪ R^(1−delta)
（delta=.0004 可、原ノート §4）。このため divisor incidence の総数 T_b^*~J_b^* B_R、J_b^*=integral_{D_b^*} dt du/(t u) が既に評価されている。商 s=(n−2)/(qr) が素数である incidence の個数を K_b^* とする。上の領域で r<q<s、表現は一意で K_b^*≤C_R。

**A1（具体的な最小突破）**: b=.313 で
    K_b^*/T_b^* ≥ .10/L
を無限増大する slab で証明（または同等の正の余剰）。J≥.289054、−F0(.313)≈.007177196 なので .10 J > 4 C2(−F0(b))。これが正の固定 margin を与え、任意の固定 sigma<.313、特に .3129>5/16 で stationary first-height Ω(R/L²) を得る。b=.32 では同じ形の 1.06/L が十分（C2<1 での保守的定数）。

**A2（より広い目標）**: D_b^* の参照 prime triple 密度 I_b^*=(1/2)∫dtdu/[tu(1−t−u)] に対する正の割合を実 source に証明する。b=.313,.315,.320 の十分な参照割合はそれぞれ .03,.12,.32。これは A1 の「divisor incidence 中の割合」と別の正規化。D_b^* の t+u≤.49 を外した全領域なら b=.320 で .24、b=.350 で .86 が十分。実際の達成割合は未証明。現 source だけで .4 まで自動的に行けないため、成功後は source の変更または大域輸送へ進む。

実質的な障壁は prime quotient にある。既知の絶対合同分布は分母を確定するが、商の素数性や numerator の下界を含まない。shifted-product Type II、switching、非対称な convolution、指数域ごとの genuine surplus、あるいは新しい方法を検討する。明示的な prime quotient 条件を固定しすぎず、S(R^b) の下界に十分な別の非負 correction でもよい。

### 3.3 すでに試したことと parity countermodel

https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-padded-parity-and-type-ii-bridge.md
https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-beyond-five-sixteenths-reverse-buchstab.md

人工的な padded sequence j=m ell、ell≈R^.375 prime、m≈R^.625 odd、重み w(m)(1+lambda(m)) は <5/8 の強い絶対局所剰余分布を満たしながら 5/16 を超える粗さおよび capped domain の correction がゼロ。したがってこの種の合同分布と恒等式だけでは一律に A1 を導けない。実 source n=pv の n−2 には exponent .375 近傍の因子を除外する anti-padding upper があり、人工モデルを排除するが、全ての極値模型の分類や下界を与えていない。実 source 固有の相関を抽出する方向が残る。全 D_b では padded m=qr の例外があり、ゼロとは主張しない。
深い reverse Buchstab sector の upper を21%程度改善済みだが、通常の補正のみで .315,.32,.325 の正下界は出なかった。可変 cutoff の恒等式では plateau 以下の通常の pair lower が upper 増分を正確に相殺する。新規の余剰が必要。

## 4. 第二優先 — HIGH 起点、占有局所輸送、M85

### 4.1 現在の最強の canonical 起点（A1 が失敗しても利用可）

https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-phase-split-absolute-bv-and-high-arrival.md

固定 mod4 source classes に対する e<.5 の絶対 BV を独立に導出し、RESET upper を引いて、上記 Pascadi 依存の二者択一を得た。各十分大Rで S(R^.313)≥.001 M_R（stationary sigma=.3129 の突破）または ≥.004 M_R の canonical roots A=n−1 で、n−2=r u、唯一の小さい因子 r∈[R^.300,R^.3128)、他因子≥R^.313、u≡1 mod4。実 first winner は minus r、age=(3r−1)/2、poststate (x0,h0)=(r(u−1)+2,r+3)。phase upper 自体は Q3=1 に依存しないが、二者択一の lower は依存する。sigma を5/16に任意に近づけた HIGH 代替も可能。HIGH postheight は先行 prefire max (~1.5r) を超えておらず、その時点は first new height record ではない。

https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-adaptive-high-transcript-and-quadratic-time.md
HIGH の adaptive CRT transcript を最初の正の pin と負の query の集合で数え、Bonferroni と3/5-form sieve により同じ密度規模を T=cL² まで実際に保持。gain=O(L³/log L)、高さ (1−o(1))r、分離された物理状態、qmin<L^K、発火数→∞。多項式規模の高さ増加は未証明。

https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-polynomial-stopped-high-and-record-ladders.md
https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-global-top-relays-and-rough-anchor-packing.md
T と D の停止（時間Tまたは追加 gain≥D の先到達）を使い、大ラベルの候補除外と粗さを使った接触 packing を強化。多項式時間枝の密度割合は未証明。gain 枝の多数の record labels と cut crossings は visited states や高さ増加の下界とは別。

### 4.2 必要条件が強くなった理由

https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-progress-weighted-record-capacity-and-hard-transfer.md
H が固定正の多項式規模〜平方根。k は全発火ではなく strict postevent height records（出生高さからの最大発火後高さ）。G≤4H（または固定 O(sqrt R)）で、qmin<4H の distinct sinks のうち k 以下の witness を持つものは
    ≪ R/L³ [1+log(1+k)]
（k≤R^eps0 の固定小さい eps0）。高さが near-square なら非双子中心について同様に +log L。k=R^o(1) の density-scale family は既に静的な粗さ、平方根近傍では双子素数を強制する。従って少数の fixed words を大量に積むだけでは genuine dynamic M85 に届かない。
仮に dynamic M85 の密度下界を得たなら、固定小さい delta,eps を密度に応じ選び、qmin≤H R^-delta、全成功 witness の strict records ≥c R^eps L、Omega(L) の deficit scales に分散、half-height 以前に p≤H R^-eps の記録による gain Ω(H) を持つ部分集団を残せる。これは条件付き必要構造であり、深い経路の存在下界ではない。

https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-signed-band-cost-and-active-section-slicing.md
dynamic M85 を仮定し、D=floor(H R^-delta/2), Q=floor(H R^-delta)=o(D) として [H/2,H] を幅Dの連続 first sections に分解すると、多数の区間で actual connector が密度規模、両端 qmin≤Q、g=Theta(D) (下界 (8/13−o(1))D)、T=D+g/2、全 labels≤MD+1（固定 M）。さらに local postevent records Ω(R^sigma L) を要する（sigma>0 小固定）。各 witness の多数区間、総イベント Ω(R^(delta/2+sigma)L)。global record と local record を混同しない。canonical 占有状態からこの輸送を構築する lower が未証明。

### 4.3 最新の構成的下界 — 使える部品と限界

https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-decreasing-prime-staircase-and-local-supply.md

canonical prefix 5,3 から、減少する prime p_i≡1 mod Q0（固定小素数積）と奇数 a_i で postheight h_i=a_i p_i、各 h_i が前段 prefire max を超えるように比率を設計。p_i の空間 pin と他因子の禁止、終端 q の pin で winner/first-H を保証。固定 prime boxes、lower block Bonferroni sieve、reverse p_i|arrival で一定の overcount を除き、固定 k≥1、十分小さい固定 beta_k>0 について H≈R^beta_k、G≤4H の distinct moving first-H が
    ≫_k R/L^{3(k+1)}
個。qmin/H≤2(.46)^(k−2) (k≥2) は固定kでは小さい定数。初めて任意固定段数の具体的な canonical 動的下界を構成できたが、指数・密度とも M85 未達。

固定 k で X=L^{1/(k+1)}、一つの prime tuple、完全CRT周期 R^o(1) から ≫R/[L(log L)^{2(k+1)}] 個。遅い diagonal k→∞ で H→∞, H=R^o(1), qmin/H→0, ≥R/L^{3/2} distinct canonical sinks。
高い任意開始高さ u≡3 mod 6 prod p_i q への template translation では、外部 prime l>Z が 2u+c_t と spatial neighbor を同時に割る必要を利用し、u の平均で sum_t sum_{l|2u+c_t,l>Z}1/l≪1/log X。空間 CRT union bound で残存を得る。Hbig=R^.4 の高さ帯で ≥Hbig/(10L²) 個の good heights（対角化後）、各 ≥R/L^{3/2} 個の実 local connectors、幅 D→∞, D=R^o(1), g=Theta(D), 両端 qmin=o(D)。
**未接続部分**: 高い局所開始点の canonical occupation、隣接区間での matching、幅の多項式化、合流・予算損失。局所始点が大量でも実 first-H の下界ではない。固定kの下界を uniform k→R^eps に外挿できない。有限 CRT 実例の巨大な A を R^beta 高さの証明と混同しない。

### 4.4 具体的な OPEN B（輸送の突破）

https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-height-section-minplus-and-terminal-defect.md
固定 B=4H の first-section map は最小祖先 A だけを保てば exact min-plus transport。N_{j+1}=N_j−e_j−m_j（budget failure、merge）。種の h_*≈R^(.3) から H へ倍増する O(L) 段で e_j+m_j≤C N_j/log h_j、または総損失が初期数の固定割合未満なら M85。一般の定数割合の損失を各段で許すだけでは足りない。下降・再入場を無視しない。distinct trial successful sinks − changed physical vertices は true lower、ただし trial 自体の occupied start が必要。高さ帯幅 W、label cutoff Z で欠損≪R W/Z。全域をそのまま覆うことはできない。
探索候補: HIGH source の合同構造と局所 supply の交差を定量化し、出力に保存される「次段で再使用可能な占有性」を設計すること。あるいは祖先の逆方向 lower、深い path の集団的な評価、または直接全体損失を抑える新構造。単発の connector lower や fixed words の数の追加だけでは終了せず、次の段階に利用する。

## 5. 第三優先 — 直接双子素数へ（M85 に固定しない）

https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-signed-band-cost-and-active-section-slicing.md
https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-mod2310-and-single-cap-gain-record.md

既存の mod2310 ポテンシャルによる任意連続 complete-block upper (paper + finite certificate):
    W≤17G/8+395/12−sum(p−281)_+/8.
H polynomial-to-sqrt, G≤4H、cutoff Y polynomial。top=p≥Y。distinct sinks の代表 witness で top full waits の総和/H ≪ R/L³[1+log^+(H/Y)]。低ラベルの gain G_low、上位 G_top、S_low=sum_low(p−281)_+、m=#top とすると
    C_Y=13G_low−S_low−4G_top,
    H−3≤C_Y/8+W_top+I+(395/12)(m+1).
hard-budget 最小 C_min(x) を全実 witness で取り V_Y(x)=clip_[0,1]((H−3−C_min(x)/8)/H)（unreachable 0）。H=floor(4 sqrt R/L^B0) で
    sum_non-twin V_Y ≪ R/L³[1+log L+log^+(H/Y)]
（B0=0 なら log L 不要）。Y=H exp(−L^gamma), 0<gamma<1 の density-scale score lower Ω(R/L²) が無限増大 slab で得られれば双子素数無限。あるいは十分小さい固定 eps の Y=H R^-eps、density-scale distinct sinks の C_Y≤8(1−eta)H でもよい（eps は下界定数と eta に依存）。発火回数制限不要。A,C の Pareto dominance は exact、C の負辺はDAGなので問題なし。正の下界は OPEN、score total は誤差精度で静的 twin count と一致する点に留意。単なる上界の改良では breakthrough にならない。

別の十分条件（旧 brief 詳細）: T=ceil(8 sqrt(2R+1)) の実軌道で G_T/T≤6/17−eta、固定 eta>0、無限増大 slab。T≥14sqrt(2R+1) なら .40 でも十分。低gain自体が粗さを要求するため、静的 parity barrier の迂回と自動的にはいえない。single-cap net reward P_1^*/(8NT)=omega(log L/L³) も既存十分条件。近平方根 short-record criterion: density-scale distinct actual first-H, G≤4H, k=R^o(1)。いずれも下界未証明。

## 6. 実行・検証・保存

優先順位: A1/A2 を中心に、5/16 の入力を短く検査してから実 shifted-product lower に進む。突破したら得られた新しい seed を次の輸送/解析へ直ちに使う。A が実質的障壁に止まれば B（占有を伴う大域輸送）、またはより直接的な §5 に移る。単一の数値目標に固執しない。モデル使用枠に応じ、同じ論点の繰り返し・形式的な再説明・不必要な並列作業を省く。

外部文献の検証には tara-sooo/ChatGPT-Context の BOOTSTRAP.md、RESEARCH_VERIFICATION_PROTOCOL.md、RESEARCH_DISCOVERY_PROTOCOL.md、保存には ARTIFACT_PERSISTENCE_PROTOCOL.md を用いる。引用定理は原文の係数・レベル・重み・端点を確認すること。既存の有限検証は各原ノートに実行結果・コード・commit locator がある。有限コードの検査は漸近下界の証明の代用ではない。独立確認・Lean・実験・paper proof を区別。重大な誤りを発見したら修正して依存する主張を追跡。

作業対象は research/min-negative-lean-live-survival のみ。開始時に最新 HEAD と本基準との差分を確認し、他セッションの新規コミットを保全する。main/他研究ブランチは変更しない。研究ノートと実行可能な検証コードを途中の意味のある段階ごとにコミットし、コミットとリモート内容を照合。終了時は最強の新規定理、必要な仮定、M85/双子への接続、残る具体的命題、独立/Lean 検証の状態、保存先を報告する。4.85 到達後も有望なら無条件証明、独立検証、Lean へ続ける。

本資料は 94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce 時点の保存済み研究の要約・実行方針。新しい漸近証明や Astra の実行を報告するものではない。
