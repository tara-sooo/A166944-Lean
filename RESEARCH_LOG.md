# Research log (dsh-evolve memory archive)

Verbatim archive of 47 dsh-evolve memory records from the A166944 work
(2026-11-14 .. 2026-11-16), moved out of cross-session memory on 2026-11-16.

Why: cross-session memory carries a 20000-char budget and is injected into every
session, while per-record process detail belongs in project documentation. Nothing
is lost -- the originals are recoverable three ways:

- dsh-evolve `forgotten` section (soft delete, restorable by id)
- ~/evolve-cleanup-20261116/backup/evolve_memory.json.before-cleanup
- the evolve workspace git checkpoint

Durable knowledge that still applies everywhere (environment gotchas, proven
procedures, user corrections) was deliberately KEPT in memory.

---

## [fact imp2] mem_mwg2aucg_v3m9gj

- created: 2026-11-14T07:06:08.796Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: prove2me, lean4, workspace, api

~/prove2me_workspace は Lean 4 形式化プラットフォーム Prove2Me (https://prove2.me, API base https://prove2.me/api/v1) の公式エージェント用ワークスペース（GitHub: prove2me/prove2me_workspace, 106★, Apache系だがAPI上のライセンス表記なし）。中身は SKILL.md + references/*.md 15本 + scripts/*.lean 2本。2026-11-14 時点でローカルは credentials.json 未作成＝未登録、lean-toolchain/lakefile.lean 未作成。elan/lean/lake は ~/.elan に導入済み。プラットフォーム側 version は 0.13.10（health API で確認可）、環境は Mathlib 0df444a/Lean v4.33.1(既定), c5ea003/v4.30.0, 777aaa6/v4.29.0-rc3 の3つ。認証は p2m_ で始まる30日有効の API キー→POST /agent/refresh で1時間のアクセストークンに交換。

## [fact imp3] mem_mwg88frz_mb413l

- created: 2026-11-14T09:52:14.294Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, lean4, git, ci, twin-primes, prove2me

tara-sooo/A166944-Lean の運用（2026-11-14 実測）:
- リポジトリは A166944（OEIS、Rowland型素数生成再帰）の研究リポジトリ。最終目標は formal-conjectures の OeisA166944.conjecture。双子素数へは「差分記録が非有界」経由で接続する作業ブランチがあった。
- 2026-11-14、codex/a166944-record-index（37コミット先行、fast-forward可能）を main に反映し push 済み。main = origin/main = bdf5e4c。CI run 43582183821 が 12/12 ステップ success（4分25秒）。
- ブランチで実際に変更されていた CI 対象ファイルは A166944/TargetDefs.lean のみ（unbounded_greater_twin_primes_of_target 追加、import を RecordBarrier に変更）。
- 環境: lean-toolchain v4.33.1 / mathlib 0df444a360ea… / formal_conjectures 8323e878b8…。Prove2Me の既定環境と Mathlib リビジョンが完全一致するので .lake の Mathlib 成果物を流用できる。
- ローカル検証は ResearchDefs(13s)/Lemmas(10s)/TargetDefs(45s)/Attempt(129s) まで成功。Bridge/Baseline は FormalConjecturesUtil（1400ファイル超）のビルドが必要で、この端末では重すぎるため CI に任せるのが正解。

## [fact imp3] mem_mwgalngf_w633ba

- created: 2026-11-14T10:58:30.011Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, twin-primes, composite-difference, record-prime, discovery

A166944 予想の攻略中に発見した新事実（2026-11-14、n ≤ 2,000,000 の完全走査による）:
1) d(n) は素数とは限らない。最小の反例は d(18) = 9 = 3²。他に d(66)=33, d(150)=25, d(22050)=25, d(22297)=35, d(22302)=27, d(1428750)=75 など、n≤2e6 で 21 回出現。→ Rowland の定理（a(1)=7 版では差は 1 か素数）は A166944 に直接適用できない。
2) しかし合成数の d(n) は絶対に記録値にならない。d(n) − (その時点の実行最大値) の最大は −4 で、常に少なくとも 4 小さい。n≤2e6 で記録になった合成数は 0 件。
3) 合成 d(n) は記録の直後に集中して出現する（記録 10891@n=10893 → 合成 9@n=10908、記録 44383@n=44385 → 合成 9@n=44388）。記録構造と深く結びついている。
4) 含意: 「記録値は必ず素数」が独立に証明できれば、予想は R−2 の素数性だけに還元され、探索空間が半減する。これはリポジトリの既存路線（q=3/q=2 排除）とは別の、新しい中間目標になりうる。
5) 記録値は n = R+2 で出現する（n≤2e6 の全記録で確認）。R−2 も常に素数。

## [fact imp3] mem_mwgazsix_rl9ura

- created: 2026-11-14T11:09:29.765Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, q2-branch, parity, critical-config, correction

A166944 攻略の重要訂正（2026-11-14、attack-parity-kill の検証により判明）:
1) q=3/q=2 分岐のラベル「even/odd」は e のパリティではなく **r のパリティ**を指す。`critical_intermediate_odd_quotient_eq_two` は e の偶奇を一切仮定していない。
2) e は常に奇数（`moving_horizon_step_event_ge_three` の内部で `d_mod_two_eq_one_of_three_le` から既に導出済み）。
3) したがって「e のパリティで q=2 を殺す」路線は完全に閉じた。q=2 は e 奇数側で生きる分岐。
4) 実例: s=15, C=24, r=17, C'=28, e=d(17)=5（奇数）, r 奇数, q=2 が成立（Attempt.lean:1311 の genuine M=13 first event）。
5) 分岐の真の違いは slack 正規形: even(r偶数) は 2δ = t+1+e*q で q 奇数→q=3、odd(r奇数) は 2δ+3 = t+e*q で q 偶数→q=2。+3 のシフトは IsMovingHorizonStep が課す r のパリティ由来。
6) 新しい有望路線: 正準臨界構成（d s = delta が新記録 ∧ s=delta*c (c偶数) ∧ D s = delta*(c+2) ∧ M<delta ∧ delta+6≤2M）を満たす実ステップが N≤2,000,000 で 0 件。これが証明できれば両分岐が同時に死ぬ。

## [fact imp3] mem_mwgbkndg_b9w7d2

- created: 2026-11-14T11:25:42.865Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, audit, ci-gap, verification

A166944-Lean 独立監査の結果（2026-11-14、independent-audit サブエージェント）:
【検証済み】sorry/admit/axiom/unsafe は 0 件（コメント1行のみ）。公理は標準三公理のみ（propext, Classical.choice, Quot.sound）。difference_records_unbounded は論理的に健全で空虚でない。23ファイルを独立再ビルドして全て成功。反例 (m,rho)=(12,9)、M=43 の連鎖 47→48→51→60→66→79、scalar survivors 47連言、n=R+2（10^8 まで）、37イベント certificate、双子素数性 — すべて再現。
【重大な問題】CI の paths フィルタが A166944/RecordBarrier.lean を含まない。つまり中心的主張「差分記録が非有界」は CI で一度もビルドされていない。003e7778..HEAD の 40 コミット中 39 コミットが CI トリガ対象外。現在のブランチ research/5e3-critical-ancestry の CI ランは 0 件。
【私の誤り】「73/82 または 74/82 のファイルが Mathlib 非依存」は文字列判定に基づく不正確な説明。真の推移的 Mathlib 非依存は 24/82。VerifiedTwinPrimePrefix.lean は Mathlib を含まないが TargetDefs.lean 経由で Mathlib.Data.Nat.Prime.Defs を要求する。
【未検証】Mathlib 依存ファイル群（Bridge, Baseline, TargetDefs, TwinReserveTarget210 系, VerifiedFiftyMillionBridge 以降の certificate 群）はカーネル検査されていない。
【評価】リポジトリは自己批判的に誠実。m=12 の境界反例を認識して仮定 14≤m を置いている。scalar survivors を recurrence path ではないと明記。

## [fact imp3] mem_mwgchwqq_i5hb9x

- created: 2026-11-14T11:51:34.650Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, lean4, d-path, moving-horizon, record-index, counterexample

A166944-Lean (Lean 4, Mathlib非依存) の D 経路解析で確定した事実 (2026-11-14):

1) 正準臨界状態 (s,C)=(delta*c, delta*(c+2)) では、k=j-s と置くとホライズン項の c 依存が消える:
   gcd(delta*c+k, delta*(c+2)-1) = gcd(delta*c+k, 2*delta-1-k)
   gcd(delta*c+k-2, delta*(c+2)+1) = gcd(delta*c+k-2, 2*delta+3-k)
   和の分解 + Nat.gcd_add_self_right で証明。~/p2m_scratch/dpath/L4.lean でカーネル検証済み (exit 0)。
   これから t + e <= 2*delta - 1（t=unit tail長, e=イベント値）が出る。

2) しかし「定数区間長の上界」と既存の r-s < delta を組み合わせても矛盾は出ない。
   delta=2919, c=1468 で t=3684、6|C でも長い。1,497,501 状態を走査し t/(2delta) 最大 0.665。
   レーン E×F の「交差点」路線はこの形では閉じない。

3) 現行除外の穴: RecordIndex.lean:589 の hbranch は q∈{2,3} のみ対応。
   q=1 の far-even 候補が完全な正準制約を満たして存在する
   (delta=15,c=44,M=11,s=660,C=690,r=676,e=13,t=16)。有界走査で 1021 個。

4) 反例: H1「t <= kappa」は偽 (delta=441,c=2,t=4,kappa=2)。
   包絡線 B(n)+2 <= 2*M(n-1) も実リカレンスで偽 (n=11461143 で 18 回目の破れ、最初の破れ)。

方法論の教訓: Lean の omega は Nat の引き算で「possible counterexample」を出して失敗することが多い。
その場合は中間等式 (h1 : A = B) を明示的に証明して rw する方が速い。linter の unusedVariables warning を
エラーと混同しないこと。

## [fact imp3] mem_mwgg2cb4_rodxfm

- created: 2026-11-14T13:31:26.786Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, survivors, sourcing, numbers, q3-q2

A166944 の q=3/q=2 生存者数の最終確定（2026-11-14、vn-f3 が delta<500 と 6001 で再計算）:
私が流布した「352個の生存者」は **どの定義でも再現しない**（完全に出典不明と確定）。
正しい数値（delta < 6001）:
- A) q=3 + closure (tplus ≤ e+2): 49,117
- B) q=2 + closure なし（Lemmas の実際の形）: 503,020
- C) q=2 + closure あり: 452,343
- D) q=3 + even-c 整除性 + 3∤u: 49,117
- A+B = 552,137 / A+C = 501,460
delta < 500 でも同様に 49,117 / 503,020 など（ほぼ delta 上限に依存しない＝小さい delta で大半が尽きる）。
最小の生存者は既知の2件と一致: q=3 は (delta,M,e)=(39,23,25)、q=2 は (15,11,13)。
また rw-f2 が Rowland 原論文を取得し、"formidable obstruction" の原文箇所を確認（a(n)/n が 3 を超え続けないことを示すのが最大の障害、と Rowland 自身が記述）。ただし A166944-Lean では `a_le_three_mul` が既に証明済みなので、この障害は A166944 では解決済み。
教訓: 数値は必ず再現スクリプトと共に残す。出典のない数値をブリーフや他エージェントの指示文に転記しない。

## [fact imp3] mem_mwggk3yc_yep18r

- created: 2026-11-14T13:45:15.770Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, landscape, benchmark, novelty, sourcing

A166944 予想の研究エコシステム調査の決定的結果（2026-11-14、cmp-f3 サブエージェント）:
【最重要】Epoch AI の「OEIS Open」ベンチマーク（arXiv:2608.11941）に A166944 が含まれており、**最先端4モデルが $50 ずつ使って全滅**している（epoch-research/LeanOpenProblems-results の scores.txt で確認）:
- Claude Opus 4.8: 不正（sorryAx 使用）
- GPT-5.5: 不正（sorryAx）
- Gemini 3.5 Flash: コンパイル失敗（omega could not prove the goal, Spec.lean:678/714）
- Gemini 3.1 Pro: 不正（sorry 残存）
キーは `oeis_166944_conjecture_0`。**つまり自動探索の先行例は「存在するが全て失敗」。**
【Cairn Commons】P-oeis-166944: Level A / Machine-checkable / Hard。claims 0, contributors 0、「Nobody has worked on this problem here yet」（2026-11-11 確認）。
【formal-conjectures】A166944 のみ収録され、姉妹系列（A166945, A167493, A167495, A213536 等）は全て 404。`@[category research open]` はちょうど1個。
【独立検算で発見した Shevelev の誤記3件】arXiv:0910.4676 の (3.1) は `5459` だが正しくは `5419`（5459=53×103）。(3.2) は `1353, 2911` だが正しくは `1153, 2311`（1353=3×451, 2911=41×71）。**論文の表をコピーしてはいけない。**
【A166945 のコメントも不正確】「Each term is the greater of a pair of twin primes」は第1項2と第2項3が反例（Shevelev 自身は「more than 3」と正しく限定）。
【独自性の評価】構造的還元「記録 R は必ず n=R+2 で起こり R | a(R+1)」は文献に見当たらない。ただし既存コードの `record_index_eq_iff_dvd_a_succ` が同等（私が確認済み）。
【査読状況】Shevelev の論文は全て arXiv プレプリントのみ、査読誌未掲載。被引用はほぼ自己引用のみ。関連する査読論文は Chamizo-Raboso-Ruiz-Cabello, EJC 18(2) 2011 #P10（Rowland 原定理を扱う）。
【Cloitre 2026】arXiv:2510.18891 の Theorem 1.4 は双子素数を「検出」するが証明しない（条件付き）。A166944 を Cloitre 経由で解く道はない。

## [fact imp3] mem_mwggs4rm_s80paz

- created: 2026-11-14T13:51:30.075Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, travel-bound, index-cap, obstruction, pure-core

A166944 の travel bound に関する決定的発見（2026-11-14、tv-f6 サブエージェントが Lean で証明）:
1) `canonical_travel_bound_below_fifty_million` の `M < 50000000` は証明に使われていない。唯一の使用点は `have heq : M = 45895573 := by omega` と `subst M` で、M を1点に潰すためだけ。実際に証明しているのは M = 45895573 のみで、一般の M については何も証明していない。同じ構造が VerifiedRecordExtension にも反復されている（リポジトリ全体の設計方針）。
2) travel 不等式 2*(sf-(M+2)) ≤ M は実質ほぼ自明。M=45895573 に対し左辺は高々1914（sf の上限 45896532、下限 45895575、差は 1957）。桁が4つ違う。証明の実質は sf ≤ 45896532 という終端 index の cap にある。
3) **travel 不等式は sf だけで決まる**。tv-f6 が Lean で証明:
   - `canonical_travel_iff_index_cap`: M+2 ≤ sf の下で travel ⟺ 2*sf ≤ 3*M+4
   - `travel_of_index_cap`: 2*sf ≤ 3*M+4 単独から travel（path も Cf も M の下限も不要）
   - `state_bound_alone_is_not_travel`: Cf ≤ 2sf を満たし travel を破る算術 witness
4) **真の障害は1つ**: 終端 index sf の、M に関して一様な upper bound（2*sf ≤ 3*M+4）が存在しないこと。リポジトリは「50M未満＝有限検証で1点に潰す」「50M以上＝未証明の仮定 ResidualCrossingBudgetCondition210 を置く」の二本立てで、両者の間に汎用の index cap が欠けている。
5) **訂正**: `moving_horizon_no_state_revisits` はリポジトリに存在しない（grep ヒット0）。C < C' に相当する内容は IsMovingHorizonStep の成分 C + 2 ≤ C'（ResearchDefs.lean:63）に既にある。私が CycleLimits.lean の内容を誤って要約していた。
6) 純コアでは `norm_num` も `interval_cases` も `positivity` も `nlinarith` も使えない（unknown tactic）。`decide` と `omega` のみ。

## [fact imp3] mem_mwgheedx_2tmnzc

- created: 2026-11-14T14:08:48.970Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, survivors, q2-branch, unit-tail, ledger

A166944 生存者数の完全確定（2026-11-14、vn-f3）:
【352 と 60 は反証済み】702通りの自然な流儀（分岐 q3/q2/両方 × 定義 A/B/C × 計数単位 δ個/(δ,e)対/三つ組 × M の偶奇 × 13通りの上限）を総当たりし、352 にも 60 にも一度も一致しなかった。「出典不明」から「再現不能（反証）」へ格上げ。
【正しい数値（定義B = 局所等式 + 帯条件 + gcd(δ,e)=1、三つ組 (δ,M,e) 単位）】
- delta<500: q=3 49,117 / q=2 503,020
- delta<1000: q=3 429,572 / q=2 4,121,210
- delta<2000: q=3 3,594,296 / q=2 33,387,885
- delta<6001: q=3 99,854,270 / q=2 908,162,863
【定義C（B + 単位尾部 gcd + 因子パッケージ）= 定義D（C + 順序リプレイ台帳）】全上限で完全一致。**順序台帳は生存者を1個も削らない**（これが「順序では排除できない」の定量的確定）。
- delta<500: q=3 355 / q=2 456（(δ,e)対）/ 三つ組 q=3 355 / q=2 456
- delta<6001: (δ,e)対 q=3 13,385 / q=2 21,656；三つ組 q=3 2,665,612 / q=2 12,449,800
【★重要】Attempt.lean の q=2 最小生存者 (M=11,δ=15,c=4,e=13) は**定義Cを満たさない**（単位尾部の違反1件: j=65 で gcd(65,91)=7）。q=2 の真の最小C生存者は (δ,M,e,c,t)=(21,15,19,26,7)。`Lemmas.lean` の `moving_horizon_odd_factor_pair` は u,v について gcd(u,v)=1, v−u=2 しか主張せず、**単位尾部の gcd 履歴を含まない**。→ q=2 枝の排除に「単位尾部の gcd 履歴」が未使用の武器として残っている。q=3 の生存者 (M=23,δ=39,c=32,e=25) は定義Cを満たす（違反0件）。
【台帳の閉形式を復元】M+κ=t+δ+5、E=δc+p+δ+3−2M、T=E−κ。t=1 が最適で p ≤ δc−M−3、2p ≤ δc+δ+3−2M、(M−1)p ≥ δc+δ+3−2M に還元。q=3 は p=57 で T=1279,E=1301,κ=22、q=2 は p=6 で T=52,E=62,κ=10 となり Attempt.lean の数値と完全一致。
【スクリプト】~/p2m_scratch/vnF3/defs_count.py, CD_count.py, family_hunt.py, hunt_352_60.py, ALL_RESULTS.log

## [fact imp3] mem_mwgy6us1_a5v32t

- created: 2026-11-14T21:58:50.443Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: flt, methodology, parallelism, blueprint, a166944, strategy

Anthropic の FLT 形式化の方法論調査から得た最重要の教訓（2026-11-15、flt-research サブエージェント）:
【決定的な区別】FLT は「既知の証明の形式化」であり、A166944 は「未解決予想」。FLT は Wiles 1995 / Darmon-Diamond-Taylor 1995 という原典があり、マイルストーンは「原典から逐語的に転記」できた。A166944 には転記すべき証明が存在しない。
→ **我々の課題の困難は「定理を証明すること」ではなく「正しい分解を発見すること」にあり、それは FLT が Prove2Me に外注しなかった唯一の部分である。**
【FLT の実データ（Anthropic 公式ブログ＋17頁タイムラインPDF）】11日間（2026-08-07〜08-18）、約1,300万行（boilerplate除き約1,050万行）、30,300定理（最終依存木 29,511定理＋約533,000ローカル補助補題）、約60億出力トークン、エージェントは「dozens（数十体）」、モデルは内部研究モデル（Fable 5.1相当、Opus 4.5/4.8ではない）。検証: Lean 4.33.1/Mathlib v4.33.0、60,475モジュール、5時間32分@96jobs/153GB peak、comparator 14時間46分/230GB、nanoda（Rust独立カーネル）が1,052,234宣言を受理。Buzzard が独立検証して「it checks out」。
【失敗モード（PDF の推論抜粋から）】①偽の文の混入（「証明を書く前に他のエージェントが文の真偽を確かめた。これが複数の偽の文を早期に捕捉した」）②見積もりの誤り（「数日」→実際は Ribet の level lowering で「数ヶ月」；「数週間」→2時間16分で閉じた例も）③依存木の rewiring ④命名衝突 ⑤圏論的推論の誤り ⑥成果物の品質問題（Claude 自身の評価: 数学として読めない、一般性がない、重複、脆く高価。定理文の約2/5が逐語的コピー、基本補題が300超のファイルで再宣言、Lean 4.30→4.33 で26%のファイルが変化し19%が個別修復を要した）
【A166944 に持ち込むべきもの】①文の凍結＋comparator（上流 Formal Conjectures の文が固定済み、定義は4つのみ＝構造的優位）②blind read-back 監査（未解決予想では自作文の真偽を検証する唯一の手段）③反例探索を独立職務に（予想が偽の可能性、disprove は第一級機能）④文/証明の分離・不変性（ドリフト防止）⑤3〜5体構成（Prove2Me Table 1 の論文形式化実績が3〜9体、$200〜$600、8〜16日）
【持ち込むべきでないもの】①13M行/60億トークンの規模（自己目的化）②1,000体エージェント（1000体runは「60の文＋古典的経路の一行スケッチ＋47の証明済み補題＋定義」という starting kit が前提だった。我々には無い）③原典からの逐語的マイルストーン（原典に証明が無い）④Git PR レビュー/単一マージキュー（3〜5体では不要）
【Prove2Me 論文 Table 1】Exact Matrix Completion 81K行/$600/9体/16日、Sipser-Gacs-Lautemann 55K行/$400/3体/8日、Bandit Algorithms 151K行/$400/6体/13日、Intro to Linear Optimization 17K行/$200/4体/7日、Vinogradov 三素数定理 3つのClaude Maxプラン/3日。Meta の Algebraic Combinatorics は 130K行/$100,000/30,000体/7日。
【検証のボトルネックは「検証」ではなく「監査」】Lean カーネルは証明を検証するが、文が意図した主張を捉えているかは検証しない。Prove2Me の答えは「監査面を事前に固定する」＝人間はミッションの中核だけを監査し、中間定理は無監査。信頼される対象は分解ではなくカーネルの受理。

## [fact imp3] mem_mwgyrcew_jejhzb

- created: 2026-11-14T22:14:46.417Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, shevelev, rowland, twin-prime, d-coordinate, first-hit, literature

A166944-Lean 文献駆動分解 (decomp-c) の決定的知見: (1) Shevelev arXiv:0911.5478 の c(n)（c(1)=2, 偶数枝 gcd(n,c(n-1)), 奇数枝 gcd(n-2,c(n-1))）は A166944 と完全同一の漸化式であり、A166944 予想 = Shevelev Conjecture 1 (2009)。よって「新しい予想の発見」という貢献は不可能で、貢献は形式化と厳密な第一命中写像に限られる。(2) D座標 D n = a n - n では自明ラン中 D 不変、状態 (s,C) からの次非自明点は r 偶数→gcd(r,C-1), r 奇数→gcd(r-2,C+1)。D n は n≥2 で常に偶数。(3) 厳密な第一命中写像（N=80000 で 85/85 一致、誤差0）: r = min( min_{p|C+1, p奇} leastOdd(p,s), min_{p|C-1, p奇} leastEven(p,s) )。Rowland Prop 3 と同型だが枝が index parity で分かれる。純算術+constant_D_event_map のみで証明可能。(4) 記録 r>5 は常に C=D(r-1)=R-1, spf(C+1)=C+1, r=C+3 → 基本点 m の主増分 (a m=2m, R=m+1)。(5) Shevelev (1.1) の A166945 の 5459 は誤植（5459=53·103 で素数でない）。実測は 5419。(6) Rowland の formidable obstruction（a(n)/n が 3 超に留まることの排除不能）は双子素数予想と同値な強度で、A166944 側では「R-2 の素数性」に相当する。

## [fact imp3] mem_mwhrgh7p_onp5di

- created: 2026-11-15T11:38:08.279Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: prove2me, account, tara-sooo, profile, audit

【Prove2Me アカウント実査 2026-11-15 20:30 JST】user_id dda4e678-8172-4e1a-9b21-ee198ccef4ed / username tara_sooo / email t7689933@gmail.com（非公開設定）。プロフィールは bio・所属・地域・social_links・avatar すべて空、is_admin/is_moderator false、rating_count 0、missions_contributed/captained 0。trust 7、num_solved_prob 8、num_submitted_prob 25。リーダーボードは 1153 人中 268 位（trust 順、上位は marwahaha 44518 等）。提出 19 件 = ACCEPTED 8 / SKETCH_ACCEPTED 4 / CE 4 / WA 3、pending ゼロ。公開レコード 25 件 = 定理 21（Open 14, Proved 7）+ 定義 4、すべて public・非 deprecated・vote 0、環境は既定 0df444a(v4.33.1) のみ。Publish job 30 件中 FAILED 5 件（すべて依存定義/定理を先に publish していなかった順序ミスで、後に再投稿して PUBLISHED 済み）。他ユーザーからの提出は 0 件。saved 0、投票 0、コメント 0。注意: 公開API `GET /users/:id` の num_submitted_prob は全ユーザーで 0 を返す表示バグ（/me は正しい値）。

## [fact imp3] mem_mwhrgha9_9ihqac

- created: 2026-11-15T11:38:08.378Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: prove2me, mission, twin-prime, a166944, environment-isolation

【Prove2Me ミッション接続の確定幾何 2026-11-15】ミッション "The Twin Prime Conjecture" の id=6285dbe8-d2bc-4607-bd98-16a30060f39d、main_theorem は **v4.29.0-rc3 環境の** twin_prime_conjecture = a3b92c39-d1c4-4e69-9aca-81bf1d0ce94f（milestones 0 件、コメント 0 件、creator=Community (Bot)）。我々の A166944 21 定理は v4.33.1 環境の 185e92b6-5906-49df-9d6f-4d95ee47a58d (twin_prime_conjecture) にぶら下がる。185e92b6 の open-leaves には A166944Research の3定理（a166944_travel_bound_from_45895573 / a166944_relaxed_index_cap / a166944_horizon_cap_from_45895573, closability=0）が葉として現れる＝v4.33.1 内では接続成立。しかし環境は隔離されるためミッション側からは見えず、我々の 21 定理はすべて `/theorems/:id/missions` が空＝リーダーボード加点ゼロ。ミッション環境側の開葉は hardy_littlewood_conjecture_A 1 件のみ。ミッション参加を狙うなら a3b92c39 側（v4.29.0-rc3 toolchain）への投稿が必要。

## [fact imp3] mem_mwhsllxu_w24dzl

- created: 2026-11-15T12:10:07.300Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, lean4, nat-sqrt, prove2me, porting, v4.29

A166944-Lean v4.29.0-rc3 移植（Nat.sqrt 障害）の実測解決 — 2026-11-15、scratch ~/p2m_scratch/tr1/。

【確定した事実（実バイナリで実測）】
- Lean v4.29.0-rc3 の toolchain には Nat.sqrt が本当に無い。GitHub tree(v4.29.0-rc3, 12144 path) に src/Init 配下の Sqrt ファイルは 0 件。ローカルに実 toolchain を入れて `#check @Nat.sqrt` → Unknown constant、`import Init.Data.Nat.Sqrt` → object file does not exist。`import Init` でも不可。v4.33.1 では `Init/Data/Nat/Sqrt.lean` は facade（Sqrt/Basic + Sqrt/Lemmas を再輸出）で、`import Init` だけで Nat.sqrt が見える。
- Nat.sqrt の供給元は Batteries。mathlib 777aaa61 の lean-toolchain は v4.29.0-rc3、その batteries rev ed250d06 の Batteries/Data/Nat/Basic.lean:95 に `def sqrt` がある。Mathlib/Data/Nat/Sqrt.lean が sqrt_le / lt_succ_sqrt / sqrt_le_sqrt を自前で定義。よって `import Mathlib.Data.Nat.Sqrt` で v4.29 でも名前・型そのままで使える（実測で #check 4 つとも成功）。
- リポジトリが使う sqrt API は 4 識別子のみ: Nat.sqrt(140), Nat.sqrt_le(13), Nat.lt_succ_sqrt(7), Nat.sqrt_le_sqrt(1)。import は CanonicalTravel.lean:1 の 1 行だけ。

【解決策 2 つ、両方実測】
- Route 1: CanonicalTravel.lean:1 を `import Init.Data.Nat.Sqrt` → `import Mathlib.Data.Nat.Sqrt`。ただし CanonicalTravel に依存する 100 モジュールが Mathlib 依存になる。
- Route 2（採用）: 純コア Isqrt.lean を新規追加。上向きスキャン `isqrtGo n f lo`（fuel 再帰）+ `isqrt n := isqrtGo n (n+1) 0`。補題は isqrtGo_spec / isqrt_sq_le / lt_succ_isqrt / isqrt_le_isqrt / le_isqrt_of_sq_le。omega/simp/decide/rfl のみ。

【重要な落とし穴（再発しやすい）】
- `lt_succ_isqrt` のステートメントは `(isqrt n + 1)` ではなく **`.succ`** で書く必要がある。元の Nat.lt_succ_sqrt が `n.sqrt.succ * n.sqrt.succ` なので、`+1` で書くと omega が積のアトムを単一化できず CanonicalTravel.lean:36 で "omega could not prove the goal" になる。succ に直したら通った。
- OrphanHarvest.lean:80-81 の `rw [Nat.sub_add_cancel hfeas]` の直後の `exact Nat.le_refl _` は、**Mathlib がスコープにあると** "No goals to be solved" で落ちる（rw がゴールを閉じてしまう）。core-only では落ちない。修正はその 2 行を `omega` 1 行に置換（または exact を削る）。実測で両方成功。

【検証結果】
- 実 v4.29.0-rc3 toolchain で core-only 98/98 モジュールがビルド成功（fail 0）。以前落ちていた CanonicalTravel / CountBoundLimits / ExcessIdentity / OrphanHarvest / RoomLedger すべて成功。
- #print axioms: propext + Quot.sound のみ（moving_horizon_pa

## [fact imp3] mem_mwhtke18_p6ds67

- created: 2026-11-15T12:37:10.011Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: prove2me, survey, missions, api, leverage

【Prove2Me 全体サーベイの道具的知見 2026-11-15】ミッション全件 = 8811（ResearchPaper 7182 / Textbook 1308 / OpenProblem 321）、開いた main theorem は 3758。`GET /missions?limit=100&offset=N` で全件列挙可（total 使用、4並列で数分）。各ミッション行は main_theorem{theorem_id,name,status,deprecated_at} と creator/fields/mission_type を持つ。
重要なAPIコスト差: `GET /theorems/:id/open-leaves` は分解グラフを辿るため遅く（30秒級になる個体あり、2728件で30分超）、`GET /theorems/:id/decompositions` は即答で各 sketch の子（theorem_id/name/status）を返すので **葉の列挙は decompositions で足りる**（2026-11-15 に 2728件を12並列で約18分）。
判明した構造: 開いた数学系ミッション2728件のうち 2709件が分解を持つ（子ノード計9207、うち Open 789）。sketch 作者の上位は b14dd546(185)/6c80ba11(54)/da7ddf19(20)。「1つだけ穴が残った」sketch が123件あり、これが最もレバレッジの高い狙い目。キャンペーン10件（odd-goldbach 等）は環境 0df444a で foundation mission の定義を共有し、`{{value}}` テンプレートに値を入れた通常ミッションとして投稿する形式。

## [lesson imp2] mem_mwgawf4h_3q4oje

- created: 2026-11-14T11:06:52.428Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, verification, self-correction, grep, priority

A166944-Lean 調査での自己訂正（2026-11-14）: 「B 座標での d の再定式化 d(n) = gcd(n, B(n-1)-4) / gcd(n-2, B(n-1)) を発見した」と報告したが、これは誤り。既に Milestone 2D（コミット 33d7a872）で `d_succ_eq_gcd_even_residual`（Lemmas.lean:1743）および `d_succ_eq_gcd_odd_residual`（Lemmas.lean:1783）として実装済みだった。原因は grep の検索語が不適切だったこと（`B` で検索したが実際の命名は `d_succ_eq_gcd_*_residual`）。教訓: 27,000行規模のリポジトリで「新しい発見」を主張する前に、定義名だけでなく結論の形（`gcd`、`residual`、`B k - 4` など）でも検索し、既存定理の全体像を先に把握すること。

## [lesson imp3] mem_mwgcfbca_3oqlij

- created: 2026-11-14T11:49:33.601Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, lean4, b-coordinate, duplicate-lemma, prior-art

A166944-Lean の "B座標（基本点）" 新定理の主張について検証した結果、真に新しい部分は限定的だった。リポジトリの A166944/Lemmas.lean には既に B座標の分岐補題が存在する: `d_succ_eq_gcd_even_residual`（奇数添字側, k%2=0: d(k+1)=gcd(k-1,B k)）、`d_succ_eq_gcd_odd_residual`（偶数添字側, 4≤B k 仮定付き: d(k+1)=gcd(k+1,B k-4)）、および `d_succ_eq_gcd_small_residual`（B k≤4 の補完）。したがって「B座標は新しい座標系」という前提は誤り。ユーザーの d(n)=gcd(n,B(n-1)-4) は d_succ_eq_gcd_odd_residual の書き換えに過ぎない。真に新しかったのは (a) 仮定不要の絶対値形、(b) 移動地平線 first event での B 閉形式 B(r-1)=C+3-r、(c) 偶数分岐で 4≤B(r-1) が自動であること、(d) B が unit tail で保存されること。教訓: 新定理を主張する前に、必ずリポジトリ内に既存の同値補題がないか grep で確認する（B座標・D座標の両方で）。

## [lesson imp3] mem_mwgej87s_zglbbw

- created: 2026-11-14T12:48:35.406Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, sourcing, verification, subagents, research-integrity

A166944 調査での重大な出典問題（2026-11-14、tracker-archaeology が発見）:
私（リード）が「q=3/q=2 の局所的条件を満たす生存者が 352 個存在する」「順序情報を全部載せても生存者を 60 個ずつ構成可能」と繰り返し報告し、ATTACK_BRIEF や複数のサブエージェント指示文に事実として転記したが、**これらの数値には機械的な裏付けが存在しない**。
- 発生源は `lane-a-ordered-replay` サブエージェントの報告のみ（その報告本文は保存されていない）
- 計算スクリプト・ログ・出力は一切残っていない
- 私自身が実再帰で「shape候補」を数えると N=10,000→27, N=100,000→59, N=1,000,000→106 で、352 はどの範囲でも出ない
- Issue #1（一次資料）にも 352 も 60 も出現しない
- 私はさらに、この未検証の数値を red-team への「攻撃対象」として渡していた（自分で追試を依頼する立場でありながら、他の文書では事実として扱っていた）
一方、私が自分で計算した数値は再現した: 「緩めた正準臨界構成を満たすのは s=18 と s=66 のちょうど2件」（`delta+6≤2M` の有無に関わらず2件）は独立に再確認済み。
教訓: サブエージェントの報告を他のエージェントの指示文に転記する際、**その数値が誰の計算によるものかを必ず確認する**。自分の計算でない数値は「〜という報告がある」と出典付きで書き、事実として断定しない。数値には必ず再現スクリプトを残させる。

## [lesson imp3] mem_mwgyr1gc_ovf71f

- created: 2026-11-14T22:14:32.214Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, lean4, index-cap, b-coordinates, counterexample

A166944 index cap 2*sf ≤ 3*M+4（canonical start s=M+2, C=2M-2）について: (1) 親候補 canonical_index_cap（hcanon+hpath+hmax → cap）は **偽**。M=13 の実 path 15→17→18→20→24（p=4, sf=24, Cf=42, IsAttainedPreviousMaximum 13 24 成立）で 2*24=48 > 3*13+4=43。M=43 も同様。落とせない仮定は event 数 p。(2) B 座標（B n = a n - (2n-2)）の正確な辞書: B(M+1)=0, B(M+2)=M-2, B sf + sf = Cf + 2, travel = Cf - B sf - M, cap ⟺ 2Cf ≤ 3M+2B sf。(3) B は単調でない（B1=2 > B3=1）ので上界からは cap は出ない。travel ≤ B sf が従い、大きい travel には大きい B が必要。(4) B n = (D n - n) + 2 は n ≤ D n の下でのみ成立（n=4 で切り捨て反例）。Lemmas.lean 等は読み専、リポジトリ未変更。成果物は ~/p2m_scratch/capB1/CapB1.lean（最終 Lean 実行で 11 定理エラーなし elaborate）。

## [lesson imp3] mem_mwgzmf72_ux3p6m

- created: 2026-11-14T22:38:56.349Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: regression, ci, dedup, measurement, a166944, verification

重大な回帰（2026-11-15、私が起こした）: `TailReduction.lean` の重複除去スクリプトが8定理を削除した。
【何が起きたか】L1〜L4 の4ファイルを1つに統合する際、重複名を「最初の出現を残す」ロジックで除去した。L1/L2 が8つの名前のうち4つを先に定義していたため、スクリプトは L1/L2 のコピーを残し、L3/L4 の実質的な8宣言を黙って削除した。削除されたのは: gcd_add_eq_gcd_self, gcd_of_split_even, gcd_of_split_odd, canonical_even_tail_gcd_reduction（c を消去するもの）, canonical_odd_tail_gcd_reduction, canonical_even_tail_event_dvd_bounded, canonical_even_tail_additive_bound（k + e ≤ 2δ-1）, canonical_even_tail_run_le。
【なぜ気づかなかったか】**CI は green のままだった。** 4定理のファイルも12定理のファイルも同じようにコンパイルが通るから。コミットメッセージには「12 declarations」と書いたが、ツリーには4つしかなかった。**ビルドは「内容」の検査ではなく、コミットメッセージはツリーの検査ではない。**
【教訓】(1) ファイル統合の重複除去は「最初を残す」ではなく「実質的な方を残す」基準で行う。L1/L2 が先にある場合、後発の L3/L4 が本体であることが多い。(2) 統合後は**宣言数を機械的に数えて**コミットメッセージと照合する。(3) CI に「モジュールごとの定理数マニフェスト」を持たせれば、この種のサイレント回帰を検出できる。
【関連】同日、私は数値検証により偽の定理を書かずに済んだ例もある: 奇数尾部の k + e ≤ 2δ+3 を書く前に検証したところ 2789件中429件で破れた（2δ+3-k が切り捨てで0になるため）。成立するのは整除 e | (2δ+3-k) で、これは既存の canonical_odd_tail_gcd_reduction が与えている。**偶数枝は不等式、奇数枝は整除**であり、形が違う。書く前に検証する習慣が効いた。

## [lesson imp3] mem_mwh3ywlh_qjhe6o

- created: 2026-11-15T00:40:37.244Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, lean4, travel-bound, prove2me, frontier

A166944-Lean frontier (Prove2Me定理 a166944_travel_bound_from_45895573) 調査で確定した3点。(1) 出口のroom = Cf-sf は厳密に B sf - 2。(2) 私が最初に導いた2つの主張は数値で反証された: 「roomがm-6に飽和」は偽、「travel<=M ⟺ S<=B sf+2」も偽（M=13,43で反例）。正しいのは恒等式 Cf-sf = (M-4)+S-travel で、frontierは 2*travel<=M ⟺ 2*S+M <= 2*B sf+4 という代数変形にすぎない。よってroom/reservoir座標内の操作では欠落上界は出ない。(3) 閾値22933441/45895573は本質的: 下界のみ除いた命題は M=13 で偽。真のpath (15,24)→(17,28)→(18,36)→(20,40)→(24,42), sf=24, Cf=42, travel=9, 2*9=18>13, IsAttainedPreviousMaximum 13 24 成立。scratch: ~/p2m_scratch/frontier1/Frontier1.lean（32定理, 全コンパイル成功, propext/Quot.sound のみ）。Lean実行は proot-distro login ubuntu 経由（Termux側ではld-linux不在で実行不可）。

## [lesson imp3] mem_mwh63tmp_jw351w

- created: 2026-11-15T01:40:25.911Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, divisibility, lean4, negative-result, false-pattern

divisor-attack (A166944-Lean, 2026-11-15): `d r` 整除構造からイベント数 p を抑える試みの結論。

【証明済み（scratch ~/p2m_scratch/divatk/DivisorStructure.lean, 18定理, カーネル検証, 公理は propext/Quot.sound のみ）】
1. テレスコーピング: ステップ則 C' = C + (d r - 1) から sum_{k=i}^{j-1}(e_k - 1) = C_j - C_i が厳密。
2. 区間不変量（新規・統一）: リプレイの i<j 両端の event value を共に割る g は
   g | S + (sigma_j - sigma_i), S = sum(e_k - 1), sigma = +1(奇)/-1(偶)。
   同枝 g|S、奇→偶 g|S-2、偶→奇 g|S+2。
3. Lemmas.lean の隣接3定理（prev_even/odd_odd で gcd=1、odd_even で |3）は
   この不変量の j=i+1 の場合に過ぎない（統一）。
4. 上界形 interval_divisor_le_excess_sum には S != 0 が本質（g|0 は常に真なので落とすと偽）。

【決定的な否定的結果 — この路線は閉じる】
- e_i / r_i の最大は 0.5、典型 10^-4（r_i/e_i が 10^3-10^4）。よって d r | r-2 (奇) / d r | r (偶)
  という制約はほぼ空。e_i > sqrt(r_i) のステップは 0/205。
- 区間不変量は厳密（n<=3*10^7 の全 9,892 共有因子区間で違反 0、全 65,637 ペアでも 0）
  だが極端に slack: S_ij/g の中央値 877、p90 4633。tight でない不変量は p の上界を与えない。
- 罠の記録: e_i | branch_j が 84.5% で成立して「法則」に見えたが、e_i で層別すると
  率が 1/e_i にほぼ一致（e_i=3 で 37.8% → e_i>=65 で 0.8%）。scrambled control でも
  15.67% vs real 17.43%。つまり小さい約数の偶然であり構造法則ではない。
- 副産物: canonical リプレイ終端で next nontrivial index = C_p + 3, d(C_p+3) = C_p+1 が
  29/29 で成立（7 から 11751795061 まで）。ただし S_p = M'-2M+1 はテレスコーピングの
  代数恒等式で新情報なし。実質は RecordReplay.canonical_quiet_return_next_record と同じで、
  その quiet 仮説は capped_moving_horizon_eventual_exit の quiet 枝が常に選ばれること
  （M を超える event が 1 つも無い）で満たされる。

教訓: A166944 では「整除は実在するが slack が 10^3-10^4」なので、整除だけから p 上界は出ない。
約数由来の高率パターンを見たら必ず (a) 除数サイズで層別 (b) scrambled control を取ること。
リポジトリは一切変更していない。

## [lesson imp3] mem_mwhm9aus_c471ns

- created: 2026-11-15T09:12:35.357Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, lean4, excess-criterion, refutation, reach

A166944 (Lean, ~/A166944-Lean, scratch ~/p2m_scratch/f3): excess基準 `8*(S+p) ≤ 3*M-9` は閾値なしでは【偽】(M=13で S=18 がledgerから強制され 8*22=176 > 30; M=43でも 8*60=480 > 120)。最適閾値はちょうど 139（139未満でcanonical replayを開始できる M は 7,13,43 のみ, 証明済）。閾値付きでも新規ルートではない: (a) 台帳 Cf=(2M-2)+S を代入すると `8*Cf+8*p ≤ 19*M-25` という (Cf,p) のアフィン形に退化し、`2p ≤ S` と合わせて結局 `8*S ≤ 3*M-9`（＝蓄積excessの上界、REACH.md が「欠けている入力」と呼ぶものそのもの）; (b) count座標では `8p ≤ M-3` しか出ず閾値で p≤5736946（必要は 977、5870倍弱い）; (c) きれいな quarter bound `4S ≤ M-3` より厳密に弱い（分離点は M=139: 4*36=144>136 だが 8*38=304≤408）。数値では18個のcanonical start（M<3e6）+ 認定開始点 22933441/45895573 で EXC ⟺ cap(B) ⟺ 2*travel ≤ M が完全一致。手法: `Fin n` 上の `decide` で unit tail と running maximum を一括検査すると6ステップのreplayでも約5秒で済む（RoomLedger の手作業版より遥かに安い）— 補題 unit_tail_of_fin / max_of_fin。replay は /host/p2m_scratch/direct_assault/out5e7.txt の非単位イベント表から再構成でき、p が REACH.md と一致する。

## [lesson imp3] mem_mwhmaj8e_ktksl9

- created: 2026-11-15T09:13:32.883Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, lean4, terminal-rigidity, refutation, index-conflation

A166944 terminal-rigidity angle (flt-a4-terminal, scratch ~/p2m_scratch/f4/TerminalRigidity.lean, 338 lines, exit=0, 0 sorryAx, 22 theorems audited).

RESULT: the angle's kernel is PROVEN, but it is an identity, not an inequality.

PROVED (new, compiles against ~/A166944-Lean):
- canonical_base_mod_six: d(M+2)=M forces (2*M-2) % 6 = 0 (NOT 4 as the brief guessed). With the tree's terminal_exit_horizon_mod_six (6|Cf) this closes 6|S as a corollary -> terminal_excess_dvd_six. So the "6|S" observation carries NO new information.
- terminal_dictionary_additive: B sf + sf = 2*M + S. terminal_reservoir_additive: B sf + travel = (M-2)+S. terminal_sf_eq: sf = 2*M + S - B sf.
- terminal_cap_iff_travel_bound: 4*sf <= 7*M-1  <->  4*travel <= 3*M-9  (so NO rearrangement of terminal coordinates is weaker than the cap).
- terminal_cap_iff_reservoir_excess: 4*sf<=7*M-1 <-> M+1+4*S <= 4*B sf. The cap bounds S only RELATIVE to B sf.

REFUTED (2 claims of the attack brief):
1. "replay terminus sf IS the fundamental point / the next record" - FALSE, kernel-checked at the genuine M=1321 exit: sf=1339 (d sf=7) while Cf=2658 (B 2658=2) and the next record is at Cf+3=2661. The fundamental point is the HORIZON Cf, not the index sf. sf<Cf always holds by IsMovingHorizonState.
2. "6|S plus S <= 3M/8 gives the cap" - FALSE as a general theorem: for ALL M>=16 and ALL S with 8S<=3M, the set {Cf=2M-2+S, Bsf+sf=Cf+2} admits a cap-violating point (Bsf=4, sf=2M+S-4). An excess bound ALONE cannot suffice; a LOWER bound on B sf (= UPPER bound on travel) is required.

MEASURED (sweep to 3e6, no truncation): S and travel are INDEPENDENT - S-travel = Bsf-(M-2) is +21,+3,0,+2,+51,-21,+110,-39,+18,-33,+9,+1071,+31; NEGATIVE at M=5419 and M=22039. So "Bsf≈M" is the statement "S≈travel", controlling neither.

LESSON for future agents: before building on a "terminal structure" claim, verify WHICH index is which by deciding concrete values at a genuine small record (M=1321 works). I initially conflated sf wit

## [lesson imp3] mem_mwho01v6_ivthyl

- created: 2026-11-15T10:01:22.945Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, angle-a, gcd, vacuous, room-quantum, negative-result, scrambled-control, lean4

A166944 angle A（gcd(C±1,r) の評価）は**空虚**だった（2026-11-15、ang-a-gcd / scratch ~/p2m_scratch/aA/RoomQuantum.lean、15定理、exit 0、公理 propext/Quot.sound のみ、リポジトリ無変更）。

【決定的な否定的結果】角度Aの狙い「gcd(C±1, r) を M で上から抑える」は**定義に過ぎない**。Lemmas.lean:438 の `constant_D_event_map` が既に `d r = if r%2=0 then gcd r (C-1) else gcd (r-2) (C+1)` を証明しており、全 moving-horizon step がその仮定を満たす。よって `gcd(C±1,r) <= f ⟺ d r <= f`（`moving_horizon_gcd_bound_iff_event_bound_even` として証明）。測定でも e = gcd が 230/230。角度Aは e <= M 以上の内容を持たない。**教訓: 「積の交わりが新制約」と思ったら、まず両者が等式で結ばれていないか（定義・既存定理）を確認する。**

【私の誤り2件】
1. 「e | C'（偶数枝）/ e | C'+2（奇数枝）」を新発見としかけたが、`ReplayOffset210.lean:48,54` の `moving_horizon_step_index_offset_residue` 内に既に local have として存在。→ **grep を先に行う**（B座標のときと同じ失敗パターン）。
2. 偶数枝の quantum を `room' = 2e ∨ 2e+2 <= room'` と書いたが偽。`omega` が反例プロファイルを出力（q が奇数 → q+1 が偶数 → 中間値は算術的に到達不能）。正しくは `room' = 2e ∨ 4e <= room'`。**カーネルが発見した。目視では気づけなかった。**

【証明済みの新結果（RoomQuantum.lean）】部屋の量子: even は `room'=2e`（q=1 のみ）or `room'>=4e`、odd は `room'+4=3e`（q=2 のみ）or `room'+4>=5e`。これは BandExcursion の `2e <= room'+2` の sharp 形。さらに退化枝を除くと gap-room 不等式が 2e 強化される: even 非退化 `gap+3e+1 <= room`、odd 非退化 `gap+4e <= room+3`、even pinned `gap+e+1 <= room`。全て 230/230 無違反、M=13 で tight（slack 0）。

【scrambled control の結果 — 量子は代数的に浅い】ランダム合成 step（C偶数, r偶数, e=gcd(r,C-1)）で quantum 形が 199999/200000 成立 = 実質任意のデータで真。**偶数目盛での shuffle control は 152/152 成立**。つまり量子は正確だが「浅い」理由で真であり、識別力は低い。84.5%法則のような偶然ではないが、構造法則でもない。

【反証した経路】AM-GM による p 上界: イベントが pairwise coprime かつ各 e | Cf±1 なら prod e | Cf±1 で p <= log_3(Cf)。→ **測定で反証**: pairwise coprime は 3/15 のみ、prod(e)<=Cf は 2/15 のみ（M=355723 で prod(e)≈2.9e122 対 Cf=713832、115桁超過）、e|Cf±1 は 0/230。e|Cf±3（95/230, 94/230）は枝の混合で再現される偶然。

【なぜ和は依然抑えられないか】退化枝（量子が tight な枝）は 3/230 のみで、それが M=13 と M=43 — まさに cap が破れる2記録（sum_e/allow = 7.33 と 4.00）。RoomLedger.travel_bound_without_threshold_is_false と同じ2記録。さらに 4/230 の step で単一 e が (3M-9)/8 を超える = 単一step不等式では和は絶対に抑えられない。N=3e7 全域で worst ratio = 7.3333（M=13）、M>=139 では <= 0.745。

## [lesson imp3] mem_mwhoto2z_jw5f3m

- created: 2026-11-15T10:24:24.860Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, room, invariant, negative-result, lean4, stratification, exact-ledger

【A166944 角度「room ≈ M」の決定的結果（2026-11-15、rq-room-invariant、scratch ~/p2m_scratch/r1/RoomInvariant.lean、24定理 exit 0、公理 propext/Quot.sound のみ・sorryAx なし、リポジトリ無変更）】

■ 核心: 「room ≈ M」は新しい入力ではない。厳密な台帳
  (Cf - sf) + (sf - (M+2)) = (M-4) + S
を証明（room_path_exact_ledger / canonical_room_exact_ledger）。これを使うと
  room_f >= M - c  ⟺  travel <= S + (c-4)
（room_lower_bound_iff_relative_travel_bound、両方向、カーネル検証済）。つまり room 下界は「M に対する絶対 travel 上界」ではなく「S に対する相対 travel 上界」であり、cap（絶対形 travel <= (3M-9)/4）とは別の不等式。RoomLedger が既に「room 経路は missing bound を再露出するだけ」と結論していたのを、同値式として確定した。

■ 決定的な反証（カーネル検証済み）
1. `room_lower_bound_alone_does_not_give_cap`: 台帳を満たし room_f >= M でも cap は出ない（具体値 M=100,S=300,room_f=100,travel=296 で 4sf=1592 > 699）。実リカレンスでも M=13（room_f=18>=13 だが 96>90）と M=43（room_f=59>=43 だが 316>300）が反例。→ 「room~M を示して cap を出す」路線は閉じた。
2. `cap_iff_terminal_room_bound`: cap ⟺ M - 7 + 4S <= 4*room_f。S が式に入るので room>=M では絶対に足りない。
3. ブリーフの step 4（sf <= 2M+4 を経由）は数学的に空虚: 2M+4 > (7M-1)/4 が全 M>=7 で成立（two_M_add_four_exceeds_cap_allowance、two_M_add_four_does_not_give_cap）。中間目標が目標より弱い。
4. `no_local_room_lower_bound` + `degenerate_even_shadow_realizable_at_threshold`: even 枝の量子算術（even_shadow_realized で忠実性を証明）だけからは M-c <= room' は絶対に出ない。退化枝 e=3,q=1,room'=6 が M=45895573 で整合。局所構造は代数的に浅い。

■ 測定（既存ファイル ~/p2m_scratch/direct_assault/out5e7.txt から復元、869ステップ、新規走査なし）
- 復元の正しさをリポジトリの手検証済みステップで確認: M=43 の (48,90)->(51,96)->(60,100)->(66,132)（room 42,45,40）と M=313 の 306->315->312 が完全一致。
- ブリーフの「room/M は 0.99999〜1.1223」は層別すると誤解を招く: M<300 では room/M は -0.33〜1.54。M>=1e5（790状態）で [0.99992,1.00300]。ブリーフは M=139（1.1223）と巨大 M を混ぜていた。
- room_f >= M - 43 が全21リプレイで成立（最小は M=22039 のちょうど -43）。ただしこれは cap より弱い条件（cap は S を通す）。
- travel - S は両符号（-14349 @M=22933441 〜 +2762 @M=5725453）。cap 保持記録で S<=travel が 5、S>travel が 15。よって room_f >= M-4 は成立しない。
- S/M 最大は M=139 の 0.2590（cap 保持記録中）。縮小傾向。

■ 教訓: 「量的不変量 X ≈ Y」という観測を見たら、まず (a) 厳密な台帳を証明して X が他の量の従属変数でないか確認、(b) 層別（小 M と大 M を混ぜていないか）、(c) 「X ≈ Y から目標」の向きが本当に効くか（中間目標が目標より弱くないか）を確認する。今回は (a)(b)(c) す

## [lesson imp3] mem_mwhoxruc_97zsvu

- created: 2026-11-15T10:27:36.357Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: prove2me, a166944, lean4, payload, sync, concurrent-edit, stale-brief

【A166944 / Prove2Me 投稿の教訓】RoomQuantum.lean の8定理を投稿する際、タスク指示書が引用していた核心定理の文面が既に古くなっていた。指示書は `moving_horizon_room_quantum` の even 分岐を `2 * d r + 2 ≤ C' - r` と記載していたが、作業開始の直前に別エージェントがコミット `a3bc097` で `4 * d r ≤ C' - r` に sharpening 済みだった（ファイル mtime が作業開始の数分前）。指示書をそのまま転記していたら、リポジトリと不一致な statement を投稿していた。

教訓（条件付き）: 並行して複数エージェントが同じリポジトリを触る状況では、**タスク指示書に引用された Lean 宣言を鵜呑みにしてはならない**。必ず投稿直前に (1) `git log --oneline -1` と `git rev-parse HEAD:A166944/<file>` と working tree の sha256 を比較し、(2) コンパイル検証は「手で書き写したもの」ではなく **ペイロード JSON から機械的に生成したコンパイル単位** に対して行う。手書き転記は drift の入口になる。

有効だった方法: `preamble + "\n\n" + formal_statement` を JSON から直接 materialise するスクリプトを書き、そのファイルを proot 内で lean コンパイルする。さらに `example : (∀ {s C r C' : Nat}, ...) := @repo_theorem` の形で「投稿文面がリポジトリの宣言と definitionally identical か」を型検査で確認する同期テストが決定的に効いた（暗黙引数の順序ずれもこれで検出できる）。8定理すべてが PUBLISHED になり、8/8 で live statement == payload を API 経由で照合済み。

## [lesson imp3] mem_mwhp8owc_pzhfwz

- created: 2026-11-15T10:36:05.759Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, roomquantum, lean4, room-ledger, negative-result, strength-direction

A166944 r4角度（RoomQuantum → p 上界）の確定結果。(1) `RoomQuantum` を room 座標 C-s へ移送すると、量子は「room = gap+e+1 ∨ gap+e+3 ≤ room」(偶数) /「room+3 = gap+2e ∨ gap+4e ≤ room+3」(奇数) になり、そこから **gap + e ≤ room** が出る。これは既存 `BandExcursion.gap_add_increment_le_room_add_one`（gap+e ≤ room+1）の +1 を落とした厳密な強化で、測定315ステップ+対照1536ステップで違反0、しかも等式到達0（つまり +1 形はどの標本でもタイトでない）。(2) 逆向きは成り立たず、`e ≤ room'` は既存 `two_mul_increment_le_room_next`（2e ≤ room'+2）の**弱い系**である（library ⇒ mine は真、逆は偽、反例 (room',e)=(3,3) 等361個）。ここを取り違えると「強化した」と誤記するので注意。(3) 角度を閉じる負の結果2つ: `room_sum_ceiling_ge_cap` — room 和の唯一の上界 p*((M-4)+S) は、2p ≤ S と p ≥ 1 の下で常に cap 値 (3M-9)/8 以上（M≥12）。`room_sum_route_vacuous` — p ≥ 2 なら E ≤ p*((M-4)+(E-p)) が全ての E ≥ 3p で成立、つまり room 台帳は Σe_i に**上限を与えない**（M に依らず一様、M=13 の閾値障碍とは別種）。scratch: ~/p2m_scratch/r4/RoomCount.lean（16定理, exit=0, propext/Quot.sound のみ, sorryAx 0）。

## [lesson imp3] mem_mwhpbvv6_ser7yv

- created: 2026-11-15T10:38:34.757Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, room-quantum, degenerate-branch, pinned, lean4, false-pattern, kernel-caught, scrambled-control, omega-limits

A166944-Lean 角度 rq-2「退化枝 C'-r=2e（偶数）/ C'-r+4=3e（奇数）の特徴づけ」の結論（2026-11-15、scratch ~/p2m_scratch/r2/Degenerate.lean、24定理、exit 0、公理 propext/Quot.sound のみ、リポジトリ無変更）。

【★最重要の方法論的教訓 — 目視では見えずカーネルが捕まえた偽パターン】
最初に「pinned even ⟺ r = 2*d r」と主張した。**実データでは 152/152 で一致する**（だから測定では絶対に気づけない）。しかし Lean の omega が反例を出して拒否した。反例: e=3,c=2,t=5 で r=6=2e だが C'-r=12=4e（非pinned）。**「実測で 100% 一致」は「定理」の証拠にならない。** 正しい特徴づけは t=(C-1)/e を使う: pinned even ⟺ C-1 = r+e ⟺ t = c+1（r=e*c）。pinned odd ⟺ C+3 = r+2e ⟺ t = c+2（r-2=e*c）。両方 ↔ で証明済み。**教訓: 実測一致率が 100% でも、量化子のある主張を書く前にカーネルに判定させること。**

【証明済み（新規）】
- pinned even ⟺ C-1 = r+d r（R1偶数）、pinned odd ⟺ C+3 = r+2*d r（R1奇数）。機構は「d r が r と C±1 の両方を割るので差 C-1-r を割り、pinned はその差がちょうど d r であると言っている」= codimension 1。
- 商形: pinned even ⟺ t = c+1、pinned odd ⟺ t = c+2（t=(C-1)/d r, c=r/d r）。**c は自由**（c=2 を強制しない）。局所系は任意の cofactor で可解（∃ 形で証明）。
- 房（room）等式: pinned even で C-s = (r-s)+d r+1 ちょうど、pinned odd で C-s = (r-s)+(2*d r-3) ちょうど。

【既存の定理だったもの（新規性なし・grep で判明）】
- R3（pinned での room 等式）は **A166944/RoomCount.lean:90 の `moving_horizon_room_dichotomy_even` の第1選言そのもの**（room = gap+e+1 ∨ gap+e+3 ≤ room）。新規性なし。
- 部分的な先行例: Lemmas.lean:5977 `moving_horizon_critical_predecessor_factorization` が critical 仮定下で C-1 = r+delta ∧ C-1 = delta*(c+1) を既に証明。私の R1/R2 は仮定を落として ↔ にした一般化。
- aA scratch（リポジトリ外）に `moving_horizon_gap_add_event_le_room_sub_one_of_pinned` が既にある。

【★決定的な測定結果 — 「退化枝は起きない」は定理ではなく、閾値未満に閉じ込められている】
- 記録の全リプレイ 230 ステップ中 pinned は **3個だけ**（M=13 が2個、M=43 が1個）、つまり **cap が破れる2記録に完全集中**。M≥139 の 220 ステップでは 0/220。
- 超幾何検定: P(3個すべてが、cap が破れる2記録の10ステップに入る) = **0.00006**。これは偶然ではない。
- **しかし排除は不可能と証明した**: pinned 枝は geniune な capped リプレイ内に実在する（path43/max43 の第5ステップ step43_5: IsMovingHorizonStep 60 100 66 132、room=40≤43 で cap 健全）。よって「退化枝を仮定から排除する」は偽。排除は局所算術では不可能（局所系が任意 cofactor で可解だから）で、唯一の候補は M≥139 の全域制約。
- M=13 は両パリティの pinned を連続で持つ唯一の記録（r=17 odd, r=18 even）。M=43 は even のみ。

【scrambled control — 率は識別力なし】
pinned 率は実データ 0.0130 に対し、合成ランダム（実 C 集合 × ランダム r）で 0.0159。つまり**大域的な pinned 率には識別力がない**。信号は「M=13

## [lesson imp3] mem_mwhroio1_0v1ycb

- created: 2026-11-15T11:44:23.411Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, composite, vacuous, relaxed-bound, sqrt, ac-rfl

A166944-Lean 角度「C_i±1 は合成数」— 空虚と判明、ただし派生路線は生存。

【空虚の証明（カーネル検証済み, scratch ~/p2m_scratch/aE2/Composite.lean）】
`Nat.Prime` は `A166944.Lemmas` の import 閉包に存在しない（`#check` で確認、TargetDefs は Mathlib 必須で純コアでは不可）。よって素数概念なしの形で述べる:
  event_target_has_nontrivial_divisor: `∃ f, f ∣ C±1 ∧ 1 < f ∧ f < C±1`、証人は `d r` 自身。
空虚性は定理 `nontrivial_divisor_of_dvd_of_lt`（公理ゼロ）で証明: 「1<f<N かつ f|N なら N は非自明約数を持つ」は**トートロジー**。`moving_horizon_step_event_package` が既に `d r | C±1`・`d r < C±1`・（ge_three 経由）`1 < d r` を出しているので、合成数性は既存定理の弱化にすぎず何も制約しない。`C±1 > M` の根拠も `IsMovingHorizonStep` の9番目の conjunct `C+2 ≤ C'` そのもの（`step_forces_horizon_jump`、公理ゼロ）＝仮定の言い換え。
角度A（e=gcd は定義）と同じ構造の空虚。

【反証（重要・実測だけでなく反例を Lean で固定）】
`e*e ≤ C±1`（= e が小さい方の因数）は**普遍量化で偽**。
- M=13: 本物の canonical リプレイ (15,24)-[5]->(17,28)-[9]->(18,36)-[5]->(20,40)-[3]->(24,42) の**第2ステップ**で C-1=27, e=9, 9²=81>27。`step_17_28_18_36 : IsMovingHorizonStep 17 28 18 36` を構成し、`event_square_le_target_is_false` で偽を証明。
- M=139: 同様に e=25, C-1=275, 625>275（`p2_e_square_fails_at_139`）。
- **`e ≤ sqrt(C±1)` も偽**（`event_sqrt_le_target_is_false`）。sqrt 版は sqrt_le_of_lt_succ_sq 経由で証明。
- 副産物: `4*d r ≤ C-1` も M=13 で偽 ∴ 既存の定数 3 は最良（`three_mul_event_le_target_is_sharp`）。

【★ 最重要の訂正 — 路線は死なない】
反例は「e²≤C±1」という**最もタイトな十分条件**を殺すだけ。路線の真の必要量は:
  4(M-1)K² ≤ 3(3M-9)²   （K=イベント値上限、48p²≤M-1 より p≤sqrt((M-1)/48)）
漸近形 4c ≤ 27 つまり **c ≤ 27/4 = 6.75**。反証された形は c=3（C±1<3M）に相当。
∴ **c=6（e²≤6M）は M≥45 で十分**（Relaxed.lean で証明: route_closes_of_six_m、six_m_quadratic）。
- c=6 は M∈[45,20000) で違反 0、c=7 は M=45 で既に破綻（`seven_fails_at_45`）。
- M=45895573 で: c=3 は K≤11733、許容は K≤17600 → **1.5倍（e²で2.25倍）の余裕**。
- ⚠ c=27/4 では経路は**タイト**（p*K/allowance = 0.9991）。c=6 は 5.8% の余裕。
- 測定: 315イベント/18記録（n≤3*10⁶）で e²≤6M は M≥45 で違反 0、最大 e²/M は M=43 の 25.33、M≥139 では 1.77 以下。

【層別と scrambled control の結果（過信への警告）】
- H2(e²≤C±1) の違反は e<10 で 1/195、10-99 で 2/98、e≥100 で 0/22 → **e が小さい層に集中**。
- scrambled control(200回): real P=0.9905 vs shuffled max 0.9841 → real は範囲外だが**差は 0.6% のみ**。
- 分解: median e=7, median target=1427741, target

## [lesson imp3] mem_mwhrzxwf_92hidg

- created: 2026-11-15T11:53:16.366Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, angle-f, large-events, counting, lean4, negative-result, scrambled-control, union-not-independent, closed-route

A166944 angle F（大きい e_i の個数制約）は**閉じた**。scratch ~/p2m_scratch/aF/F.lean、exit=0、error 0、sorryAx 0、公理は propext/Quot.sound のみ（6定理すべて #print axioms で確認）。リポジトリ無変更（HEAD ea8f937）。

【証明済み・新規】
- not_dvd_three_of_gt_three: 3<q → ¬q∣3
- no_common_prime_gt_three_of_consecutive: q>3 は連続2事象値を共に割らない（gcd_consecutive_dvd_three_unconditional の計数内容。木は gcd 整除は言うがこの帰結は言っていない）
- two_mul_tcount_le_of_noAdj / tcount_le_half_of_noAdj: 隣接 true のない Bool リストは高々 (length+1)/2 個の true。⟹ **単一の**素数 q>3 は p 個の事象値のうち高々 ⌈p/2⌉ 個を割る
- max_event_exceeds_allowance: (3M-9)/8 < M (M≥1)
- **heavy_count_ceiling_exceeds_allowance: (3M-9)/8 < M + (p-1)*(3M/16)**

【角度を閉じる決定的理由（データでなく証明）】
「高々1個の e_i が 3M/16 を超える」という形の上界は Σe_i ≤ M + (p-1)*(3M/16) を与えるが、この天井は**予算 (3M-9)/8 より常に上**（1個の許された事象が M まで許され、M 単独で予算全体を超えるため）。よって k≥1 の「大きい事象が高々k個」型の定理は**原理的に** cap を証明できない。これはデータの良し悪しの問題ではない。

【反証（測定＋対照）】
R1: **q>3 の union は独立集合でない**（リードの仮説）。制約は per-prime。M≤3e5 の完全リプレイ14本・隣接76ペアで、両方が素数>3 を持つペア **19**、共有するペア **0**。例 M=139: e0=25=5², e1=13 が隣接（5≠13）。scrambled control（事象多重集合を実スケジュール上で200回シャッフル／ランダム奇数 e∈[3,M] を200回）: 実 0.2500 vs シャッフル 0.3845 vs ランダム 0.9538、独立予測 (65/69)²≈0.887。**実測は両対照より低い**＝この統計量は上界に使えない。
R2: **M≥139 で 16e>3M となる事象は 0 個**（完全リプレイ17本、M=1427749 は C0=2M-2>2e6 で打ち切り除外）。cap が破れる M=13,43 だけが大事故象を持つ。含意は逆で「cap が事象を小さくする」。リードの問5への答え: Σe_i を M の定数倍に抑えているのは e_i の減衰ではなく大事故象のほぼ不在であり、それは小さな和の**帰結**であって原因ではない。
R3（副産物）: e_i²≤C_i が M≥313 で全 step 成立（M=13,43,139 のみ違反。M=139 の例外は s=141,C=276,r=150,e=25）。ランダム奇数 e は 0.98 で違反するので偶然ではないが、小ささの言い換えなので入力に使えない。

【prior art 確認（grep 先行）】遷移別4分岐 gcd は ConsecutiveEventGcd.lean:53,71,173 に、無条件 |3 は :188 に既存。gap≤2f（全ての約数 f について）は CanonicalGrowth.lean:53 に既存。再発見せず、比較に使うのみ。

【詰まった点】List.count は BEq 経由で定義的簡約しない → 明示的コンストラクタパターンの tcount を自作し rfl 補題で解決。omega は (a::l).length を見通せない → simp only [...] at hrec ⊢ で仮説内も書換え（len_cons を rfl で用意）。by_contra はこの core に無い。

## [lesson imp3] mem_mwhtck5g_zep9jd

- created: 2026-11-15T12:31:04.690Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, lean4, measurement, calibration, redteam

A166944-Lean red-team lesson (sq4, 2026-11-15): when measuring a "canonical replay" from a record M, the stop rule MUST be "no valid IsMovingHorizonStep exists" (no r with s<r<=C, d r>1, unit tail on (s,r), D(r-1)=C, C+2<=D r, IsMovingHorizonState r (D r)) — NOT "r > C" or "horizon cap exceeded". Using the wrong stop rule gave Cf=624/S=348 for M=139 where the repo's own decide-certified value is Cf=312/S=36 (ExcessGap.excess_data_139_forced). ALWAYS calibrate a new replay script against the kernel-certified literals (M=13 -> Cf=42,S=18; M=139 -> Cf=312,S=36; M=313 -> Cf=660,S=36) before reporting any statistic. This is a 10x error class that silently changes every downstream number.

## [lesson imp3] mem_mwhu0azz_8elisf

- created: 2026-11-15T12:49:32.572Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, lpf, least-divisor, gap-concentration, rediscovery, vacuous-route, lean4

【A166944 障壁: lpf経路と「最後の3イベント集中」経路を閉鎖（2026-11-15, sq-1）】
(1) ★再発見回避: `A166944/GapTwoSided.lean` が既に「gap ≤ 2*lpf(C-1) は moving_horizon_gap_le_twice_even_factor の v:=lpf 特殊化にすぎない」と明記。`GapBound.lean:13` も散文で lpf を名指し。よって「gap を lpf で押さえる」第1段は全て既存。
(2) `Nat.minFac`/`Nat.Prime`/`Nat.find` は A166944 の import closure に**存在しない**（#check で unknownIdentifier）。lpf を関数として使う経路は純コアでは書けない。`SelfHit.lean:28` も同旨。回避策: `abbrev LeastNonunitDivisor (N m) := 2 ≤ m ∧ m ∣ N ∧ ∀ i : Fin (m-2), ¬ (i.val+2) ∣ N`（abbrev 必須。def だと型クラス探索が展開せず Decidable が合成できず decide が失敗）。
(3) 反証1: `gap ≤ lpf + 2` の形は**偽**。M=43 の第4ステップ (s,C,r,C')=(51,96,60,100) で lpf(95)=5、gap=9>7。95=5*19 で e=lpf（slack でなく達成）。
(4) 反証2: 和の形 `2*Σlpf ≤ (3M-9)/4` は M=13（目標仮説3つ全て成立）で偽。horizon項 25,27,35,39 の lpf は 5,3,5,3 → 2*16=32 だが 2*travel=18。**上界が被上界量を超える**ので定数改善では直らない。
(5) ★lead の測定前提を反証: 「travel の 77-93% が最後の3イベントに集中」は **p≤6 の小標本アーティファクト**。p=57,72,85 では last3 割合が 0.02, 0.02, 0.00。一方 **top3（最大3ギャップ）は 0.53-1.00 を保つ**が位置は散在（72中55番目、85中58番目）。scrambled control: last3/(3·travel/p) は 0.09-3.87・平均1.09 → 「最後の3つ」は特別な集合ではない。kernel反証: M=313 の gap列 [2,1,22,2,1,5]、22 が位置3/6、last3=8 vs travel=33。
(6) room_f - M は -43〜+2015 で (room_f-M)/√M が 2.67, 1.79 → c·√M 型上界は存在しない。cap ⟺ 4·room_f ≥ 4S+M-7 は RoomInvariant.room_lower_bound_iff_relative_travel_bound の c を解いただけ（台帳の言い換え、13経路と同じ現象）。
成果物: ~/p2m_scratch/sq1/SQ1.lean（16定理、#print axioms は propext/Quot.sound のみ、sorryAx なし、exit=0）。測定: probe1-4.py, control.py, control2.py。

## [lesson imp3] mem_mwhuvbzu_a2p1d2

- created: 2026-11-15T13:13:40.201Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, p-bound, lean4, state-slack, joint-ledger, measurement

A166944-Lean 「p の上界」角度の結論（sq3, 2026-11-15）。

【座標の取り違えを訂正】lead の「余裕 7〜10000倍」は travel 座標の話。cap が実際に拘束する座標（Cf+p vs (19M-25)/8、同値に 8·Σe ≤ 3M-9）での余裕は約19%、最悪記録 M=139 では 3.98%。travel 座標で余裕が大きく見えるのは Cf ≈ 2sf ≈ 2M が支配項で travel が低次だから。

【証明済み（scratch ~/p2m_scratch/sq3/F.lean, 50定理, カーネル検証, 公理は propext/Quot.sound/Classical.choice のみ、sorryAx なし）】
1. slack_add_excess: r₂ + S = 2·travel + 6 （r₂ := 2sf - Cf = state slack）。excess_bound_iff_state_bound の加法形。Nat.sub_add_sub_cancel で証明。
2. cap_iff_travel_and_slack: cap(8S+8p+9≤3M) ⟺ 16·travel + 8p + 57 ≤ 3M + 8·r₂。係数 travel:16, slack:8。cap の実体は「state slack が travel の2倍を払う」trade。r₂=0 のみ与える state bound では不足。
3. state_and_index_cap_cannot_reach_joint: 19M-25 < 8(3M+4) が全 M。cf_ceiling_deficit: 差 = 5M+57（線形増大）。つまり (state bound)×(index cap) の全ツールキットは証明可能に不足。
4. path_p_le_travel: p ≤ travel が唯一の無条件 p 上界（CountFromIndex.count_le_horizon は horizon 経由で M-4 倍弱い）。
5. 反証: cap は M=13,43 で偽、M=139 で真（decide でカーネル検証）。

【測定（n≤2×10^6, 17 canonical starts）】
- ratio (Cf+p)/((19M-25)/8) は 16/19=0.8421 に上から収束。M≥1000 で min 0.8422 / max 0.8601。
- state bound が tight (2sf=Cf) なのは M=139 のみ、そして M=139 が binding record。この2つは同じ事実。
- 層別: 10^1 のみ 0/2（M=13,43）。他は全 decade 成立。
- 帰無モデル: p シャッフル 0/2000、S シャッフル 0/2000、S~U(0,3.3M) 0/2000 → 法則は偶然でない。

【反例が出た p 上界候補】p≤√M (M=13)、p²≤M (M=13)、2p²≤M (M=13,43)、48p²+1<M (M=13,43,139,313,2659)、p≤log₂M (M=13,43,355723,1427749)、p≤2log₂M (M=355723 p=57>35, M=1427749 p=72>41)、p≤√M/7 (5記録)。p≤100 は反例なし（漸近的保証なし）。

【Lean の罠】omega は truncation 済み Nat 減算と 2*(M+2) の展開を追えない。「No usable constraints found」は変数が goal に現れない/展開不能のサイン。truncation があると false になる等式（shift_cost は M=0 で偽）は M≥1 を明示。証明の定石: Nat.add_sub_assoc / Nat.sub_add_sub_cancel / generalize で atom 化。

## [lesson imp3] mem_mwign1bb_dw55zj

- created: 2026-11-15T23:23:04.664Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, barrier, twin-prime, six-cover, lpf, analysis, why-stuck

【A166944 障壁の正体を確定（2026-11-16、較正済み実測 + ソース読解）】

■ なぜ証明できないか — 3層の答え
(1) **前線仮説は TPC 強度**（証明済み連鎖）: `CanonicalTravelBoundFrom 22933441` --target_of_travel_bound_from_22933441--> `Target` --unbounded_greater_twin_primes_of_target--> 双子素数の無限性。`difference_records_unbounded` は無条件。よって障壁は TPC 以上に難しい。16経路が閉じたのは症状で、これが原因。
(2) **終端条件が twin-prime 的**: リプレイの停止は quiet branch のみ（17/17 で QUIET、STEPFAIL 0）。quiet は `2*isqrt(Cf+1) < Cf-sf` を要し、これは Cf±1 に小因子が無いことを強制。実測で **Cf-1 と Cf+1 は 17/17 で両方素数**。`AttainmentIsFree.terminal_exit_reset` が Cf+1 = 次の記録値 を証明。∴ 双子素数中心を探す探索の長さを、双子素数の入力なしには抑えられない。
(3) **足りないのは因数構造の入力**。事象ごとの局所性質は全て既出（e|C±1, 3e≤C±1, e≤M, e≥3, C'=C+e-1, gap≤2min(e,cofactor), carry e|C', gcd(e_i,e_{i+1})|3 を215/215で確認）。局所データの総和では数は抑えられない。

■ 入口点の併合（新）: event_count `48p²+1<M` と six_cover（cover≤p 版）は**同じ不等式**。six_cover 予算 = 2p·isqrt(12M+16) ≤ M ⟺ p ≤ M/(2·isqrt(12M+16))、比が 1.0000（M=45895573 で 977.87 vs 977.83、M=1e12 で一致）。∴ 定量的には「13の入口点」は p ≲ sqrt(M)/7 の一点に収束。

■ どうすれば証明可能になるか — 生きている2経路
**Route B（推奨・既に配線済み）**: `TravelResidues.moving_horizon_path_travel_by_six_cover` + `record_index_and_twin_prime_of_six_cover_from_45895573` が Target まで接続済み。不足は純粋な**個数**の上界: `cover.length ≤ (M/2 - 6p)/(isqrt(4(3M+4))-6) ≈ 0.1443·sqrt(M)`、cover = {j : IsReplayEventStart, 6|D j}。実測で **M≥1321 の全記録で予算が閉じる**（margin: M=2659 で1.24x、355723 で2.61x、2860771 で4.88x）。因数分解でなく可定義・決定可能な集合の計数なので、これが最も見込みがある。
**Route A（新・余裕大）**: `travel ≤ 2·Σ min(lpf(C_i-1), lpf(C_i+1))` が 17/17 成立（`HalfWindow.gap_le_twice_min_factor` から）。目標は `Σ min-lpf ≤ (3M-9)/8`。余裕 4.2x（M=139, 最緊）〜105x（M=1427749）。ただし min-lpf は有界でない（M=1427749 で最大1129）。

■ やってはいけない（木自身が証明済み）: S を抑える経路（`excess_bound_alone_does_not_give_cap`）、座標変換 S/travel/B/room/slack、sqrt(C) 経路（`count_index_route_is_vacuous` が任意の sf で空虚と証明）、記録列上の帰納（`cap_does_not_transfer_along_records`、M=7 で成立し M=13 で破れる）。

■ 落とし穴: 私の最初の測定は停止条件を `limit = s+M-4` と誤っていた（正しくは `C`）。較正リテラル M=13→(42,18,24,4), M=43→(138,54,79,6), M=139→(312,36,156,2), M=313→(660,36,348,6) を必ず先に確認すること。文書中の lpf 和の分母も /16 と誤

## [lesson imp3] mem_mwii25xd_3vezxv

- created: 2026-11-16T00:02:50.066Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, lean, mathlib, olean-server, environment, proot, blocker

ENVIRONMENT BLOCKER in ~/A166944-Lean (Lean 4.33.1 in proot ubuntu): Mathlib CANNOT be imported by `lean`. All 8322 Mathlib .olean files exist under ~/prove2me_workspace/.lake/packages/mathlib/.lake/build/lib/lean but their `.olean.server` sidecars are absent everywhere on the system, and lean aborts on the FIRST Mathlib import with "failed to open file '...Mathlib/Data/Nat/Prime/Defs.olean.server'". The requirement is Lake's noServerOLeanError (Lean/Setup.lean, Lake/Build/Module.lean). Substitution FAILS: copying the .olean to the .olean.server name gives "region_reader: own region overlaps a dep region's base_addr range". So it cannot be faked; Mathlib would need a full rebuild (out of scope, BRIEF section 8 forbids heavy builds). CONSEQUENCE: only core-only modules import (ResearchDefs, CanonicalTravel, HalfWindow, LeastDivisorRoute, RoomLedger, RecordIndex, AttainmentIsFree all OK); the 7 modules importing Mathlib (TargetDefs, TravelTarget, TravelFirstUse, CreditHall210, CreditWindows210, RebalancedPeriodLoad210, ResidualEventTrace210, ResidualReuseOverlap210) and anything importing them are UNCHECKABLE. Therefore `Target` itself cannot be named and the final "A1 => Target" link cannot be typechecked. WORKING LEAN INVOCATION (BRIEF section 8): proot-distro login ubuntu --bind /data/.../home:/host -- bash -lc 'export PATH=/host/.elan/toolchains/leanprover--lean4---v4.33.1/bin:$PATH; DEPS=$(ls -d /host/prove2me_workspace/.lake/packages/*/.lake/build/lib/lean | tr "\n" ":"); cd /host/A166944-Lean && export LEAN_PATH=$PWD:$DEPS; lean -DautoImplicit=false -DrelaxedAutoImplicit=false --root=. FILE'. WARNING: `lake env lean` tries to RE-CLONE mathlib from github — do not run it (disk risk); it was killed.

## [lesson imp3] mem_mwiiozec_sti2t2

- created: 2026-11-16T00:20:34.722Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, campaign, route-a, route-b, six-cover, mod3, mathlib-broken, lead-error, flt-method

【A166944 二経路キャンペーン結果（2026-11-16、サブエージェント並行、FLT 方法論適用）】

■ 結論: どちらの経路も障壁を閉じない。両経路は同じスカラー束縛に帰着する。cover 計数問題は解決、困難は移動したのであって除去されていない。

■ Route A（最小素因子和）: frozen 目標を (3M-9)/8 → **Sum min(lpf(C_i-1),lpf(C_i+1)) ≤ M/4** に訂正（旧形は cap(B) 止まりで Target に不足。M/4 は CanonicalTravelBoundFrom に直結）。反例探索: 23記録・M=4e7 まで違反0、最緊は M=313 の1.86x。違反は M=13,43 のみ（閾値下）。構造的発見: 単一状態で反証できるのは双子素数中心の場合のみ（minlpf>M/4 なら両隣が素数）で、**事象状態に双子素数中心は 0 個** → A1 は TPC 強度の入力を要求。travel≤2Σ は tight（余裕ゼロ）。

■ Route B（six-cover 計数）: N=3e9 まで走査、閾値 45895573 超で違反0、余裕 42x〜1844x。**mod-3 力学は実在し対照頑健**（P(0→0)=0.4304 vs P(1→0)=0.8997、921遷移、定常 π₀=0.6004、scrambled 2000回で観測が外れ値、構造的ゼロ P(0→2)=P(2→2)=0）。**しかし定常密度は割合を抑えるだけで計数を抑えない**: cover≈0.58p なので p ≤ 0.2475√M が平均に要求され、分散/CLT では救えない → mod-3 は dead end。**cover 計数自体は解決**: 消費者の仮説は cover について存在的なので、長さ ≤ p の cover が存在すれば足りる。
→ 経路は (L) `6p + p*(isqrt(4(3M+4))-6) ≤ M/2` すなわち **p ≤ 0.1443√M** に崩壊。これは event-count 経路と同じ束縛。**M≥5419 では sqrt 束縛(B)の方が tight** なので両経路は問題を両側から挟んでいない。

■ リードの誤り2件（両方とも独立検証で確定、うち1件は Lean で形式化）:
1. cover の3定義が一致すると主張 → 誤り。B = A + 1（6|Cf が常に成り立つため j=sf が常に B に入る）。A = T は成立。
2. 「cover は p 個の事象状態の部分集合だから cover ≤ p」→ **論理的に無効**。消費者の仮説は下界（j ∈ cover）なので `List.range sf` が長さ sf で満たす。正しいのは「長さ ≤ p の cover が存在する」であり、存在で足りる。route-b が `range_is_a_cover` / `cover_length_le_p_not_forced_by_containment` で Lean 化。

■ Lean 成果物（両方 exit 0、公理は propext/Quot.sound のみ、sorry なし）: `~/p2m_scratch/routeA/LemmaA.lean`（gap_le_twice_min_least_divisor, min_factor_path_travel_le, min_factor_sum_travel_bound, canonical_travel_bound_of_min_factor_sum_from_22933441）、`~/p2m_scratch/routeB/LemmaB.lean`（six_dvd_D_iff_three_dvd_D, exists_six_cover_length_le_p, exists_six_cover_of_p_bound, range_is_a_cover, cover_length_le_p_not_forced_by_containment）。保全コピー: `~/p2m_scratch/frontier/campaign_2026-11-16/`。

■ **環境ブロッカー（既存、今回の作業が原因ではない）**: このコンテナでは Mathlib を import できない。`prove2me_workspace/.lake/.../lean` に .olean は 8322 個あるが **.olean.server は 1 個のみ** → `TargetDefs` を import する一切が型検査不能（リポジトリ自身の TravelTarget.lean 

## [note imp3] mem_mwgcluft_dhjh6c

- created: 2026-11-14T11:54:38.291Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, lean4, q3, moving-horizon, counterexample, proof-strategy

A166944 (Rowland-type recurrence) q=3 branch attack, repo /data/data/com.termux/files/home/A166944-Lean. PROVED-and-scratch-verified (outside repo, p2m_scratch/q3/Q3Barrier.lean, exit 0, axioms only propext+Quot.sound): critical_q3_gap_two_mult_three (2δ=3(e+1) ⟹ 3|δ), critical_q3_gap_two_not_three_dvd_event (+gcd(δ,e)=1 ⟹ ¬3|e), critical_q3_index_not_dvd_delta (1≤t<δ ⟹ ¬δ|(δc+t)), critical_q3_closure_not_divides (1<e<δ ⟹ ¬δ|(e−1)), critical_q3_cofactor_gap (v=u+3), critical_q3_cofactor_not_three (¬3|u). COUNTEREXAMPLE TEST (computation only, NOT proof): the complete LOCAL q=3 system — all repo-proved local conditions plus the proved bound 968≤M — admits 352 abstract survivors for δ<6001 (smallest: δ=1467,c=650,e=977,M=971,t=2,v=979,sf=953548,Cf=955018), of which 118 have 3∤δ and so are irreducible to the existing mod-3 route. NONE has a genuine capped replay path from (M+2,2M−2): the bottleneck is exactly the global ordered-history/attained-maximum constraint, not local arithmetic. Actual recurrence to 4·10^6 contains ZERO critical first-failure configurations. Verify with `p2m-a166 A166944/Lemmas.lean` / `p2m-a166-build` (never lake).

## [note imp3] mem_mwgydr2k_va4kk1

- created: 2026-11-14T22:04:12.199Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, mass-parallel, index-cap, dependency-graph, design

A166944-Lean 大規模並列設計（2026-11-15, mass-parallel-design）の実測結果:
【数値訂正】「今日18モジュール」は正確には「main比 18ファイル変更 = 新規Lean 16 + verify.yml + .gitignore」。A166944/*.lean は 82→98。
【依存グラフ実測】98モジュール、最大深度44（ReplayLaunch）、fanout分布 {0:4, 1:70, 2:22, 3:1, 4:1} = 70/98が純直列鎖。Target到達は73/98。最大元（誰もimportしない）17個。11/14に追加した16モジュール中9個が最大元、9個がREADME未記載。特に TravelReduction.lean（4定理、「travel ⟺ index cap」の再定式化）が誰からもimportされずREADMEにも0ヒット。
【障壁の再定式化】travel と index cap は同値（TravelReduction.lean:38,43）。travel_of_index_cap は 2*sf ≤ 3*M+4 単独から結論を出し path も Cf も使わない。よって「canonical escape排除」と「index cap」を並列の別レーンとして扱うのは誤り（1本の鎖の上下流）。開放条件は既に6個の同値な入口がある（Residual{Reserve,SignedReserve,CrossingBudget}Condition210, Rebalanced{RemainingCrossing,OverlapCrossing,Boundary}Condition210）。すべて target_of_* で Target に到達。
【物理的上限】ResearchDefs.lean（最小モジュール）のLean検証で最大RSS 530MB / 4.86秒（/usr/bin/time -v + proot-distro で実測）。端末 RAM 11.2GB、空き1.1GB、swap使用3.5GB。Leanは同時1本が安全限界。15体投入しても計算資源は1体分。
【生産速度】11/11 +9,238行、11/12 +8,996行、11/14 +1,547行（15コミット、1コミット108行）。11/11-12の大量投入で開放条件は1つも閉じなかった。
【設計判断】並列化できるのは定理ではなく「行き止まりと前提の在庫」。有効な投入先は (1)レッドチーム/独立監査（rt-f6がTravelReductionの3定理を生んだ）、(2)前提整備（Lemmas.lean 7,732行の分割、README更新、在庫接続）、(3)有限反例探索（端末制約下で実質直列）。無効なのは「補題を分けてN体に配る」（statement ズレで下流55モジュールが壊れる）。
【成果物】~/p2m_scratch/massdesign/MASS_PARALLEL_DESIGN.md（設計書）と LEDGER_TEMPLATE.md（重複防止台帳）。リポジトリは無変更（git status clean確認済み）。

## [note imp3] mem_mwhchlof_572uax

- created: 2026-11-15T04:39:06.485Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, final-report, twin-prime, prove2me, handoff, twelve-routes

【A166944 プロジェクト 40ラウンドの最終到達点】2026-11-15、ゴールラウンド上限（40/40）に到達。

■ 目標の達成状況
- **A166944 予想の Lean 4 証明: 未達成**（17年間未解決の数学的障壁）
- 残る障壁の突破: 未達成（ただし12経路を閉鎖し障壁を1点に確定）
- **部分成果の蓄積: 達成** — tara-sooo/A166944-Lean に **125モジュール、1773宣言**、CI green
- **Prove2Me への接続: 達成** — 双子素数予想ミッションの分解木に我々の経路を接続
- **CI 検証済みのみを main へ: 達成**

■ 数学的な到達点
障壁は単一の不等式に収束: `2*(sf-(M+2)) ≤ M`（canonical replay の移動距離 ≤ M/2）。これは `2*sf ≤ 3M+4`（index cap）と同値。**12の独立した経路が全て同じ結論に収束**した:
1. travel⟺index cap (TravelReduction) 2. count (CountFromIndex) 3. 貯水池B (BIntegrate) 4. room/slack (RoomLedger, ExitBand) 5. 値a (ExitCoordinates — a sf/sf→3 でタイト) 6. 交差 (ExitThreshold, CrossingRoute) 7. S恒等式 (ExcessIdentity — 代入すると元に戻る) 8. 整除構造 (ExcessSumInterval — slack 10^3〜10^4) 9. 閾値除去 (RoomLedger — M=13 で偽) 10. no-reentry (BandReentry — M=43 で偽、実例あり) 11. excursion (BandExcursion — 2e ≤ room'+2 は M に対し vacuous) 12. min形/quiet window (HalfWindow — 余因子が効くのは 16/1050 ステップのみ)

**残る唯一の攻め口: `S = Σ(d r - 1)` または `p` の上界。** 必要十分条件は `S ≤ room_final - (M-4) + M/2`、十分条件は `S ≤ M/2`。測定での S/M は M≥313 で最大 0.115（経験的余裕は大きいが証明は無い）。

■ Prove2Me の状態（v4.33.1 環境、ユーザー tara_sooo、trust 4）
- Definitions 4件: a166944_record_core, a166944_moving_horizon, a166944_canonical, a166944_composite_test
- **Proved 6件**: difference_records_unbounded, record_index_iff_canonical_returns, unbounded_greater_twin_primes_of_target, composite_differences_below_1000, a166944_target_of_travel, band_exit_gap_le_half_record_v2
- Open: a166944_record_is_greater_twin_prime, twin_prime_conjecture_of_target, a166944_travel_bound_from_45895573（真の障壁）, band_exit_gap_le_half_record（初回版、引数順ミスで WA のまま残存）
- `open-leaves` が返すのは2件のみ: prime_k_tuple_conjecture (closability=1) と a166944_travel_bound_from_45895573 (**closability=0** = これ以上分解できない葉)

■ 重要な落とし穴（記録）
1. **ミッション環境が違う**: The Twin Prime Conjecture ミッションは v4.29.0-rc3 の `twin_prime_conjecture` (a3b92c39) を指す。我々が接続したのは v4.33.1 の同名定理 (185e92b6)。**環境は完全に隔離され import は越えない** → ミッションページには出ない。v4.29 への再投稿は probe が失敗（elan の v4.29.0-rc3 toolchain 

## [note imp3] mem_mwhngcp6_ggjers

- created: 2026-11-15T09:46:03.970Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, why-stuck, analysis, barrier-shape, next-angles

【A166944: なぜ解けていないのかの構造的分析（2026-11-15、リード自身による）】

■ 障壁の正確な形（今回確定）
目標は `Σ e_i ≤ 3M/8`（canonical replay のイベント値の総和）。これは cap (B) `4*sf ≤ 7*M-1` と厳密に同値で、`sf = (M+2) + travel`, `travel ≤ 2(S+p)`, `S+p = Σe_i` から出る。
各 e_i の性質（全て既存で証明済み）: `e_i | C_i ± 1`（偶数枝は C-1 と r、奇数枝は C+1 と r-2）、`3*e_i ≤ C_i ± 1`、`e_i ≤ M`（IsAttainedPreviousMaximum）、`e_i ≥ 3`。

■ なぜ現在の道具では届かないか（4つの理由）
1. **上界しかなく下界がない**。仮定は `e ≤ M`（上界）、`e ≥ 3`（弱い下界）、`C' = C + e - 1`（増加）。`e | C±1` は「e が C±1 の約数」というだけで e が小さいことを意味しない（e = C-1 も可能）。商 (C±1)/e が大きいことを示す入力が無い。
2. **S 単独の上界は不十分**（CapBCandidates/TerminalRigidity で全 M ≥ 16 について証明済み）。`excess_bound_alone_does_not_give_cap` が witness 付きで反証。必要なのは `B sf` の下界＝travel の上界＝元の問題。
3. **座標変換は全て循環**。S/travel/B/room/slack は台帳で結ばれ独立に動かせない（ExcessIdentity、TerminalRigidity の `terminal_cap_iff_reservoir_excess` が `4sf ≤ 7M-1 ⟺ M+1+4S ≤ 4*B sf` を示す）。
4. **記録列帰納は原理的に不可能**（RecordInductionFails）。`7→13` が反例（M=7 で cap 成立、M=13 で崩壊）。転送は恒等写像（`next_criterion_substituted`）で、必要な仮説に M の cap が現れない＝循環。FLT の無限降下の類推が成立しない理由：`R' = 2R-1+S` は増加し、閾値は上に逃げる。

■ 必要な新しい数学（未着手の角度）
- e_i の**素因数構造**: `e_i | gcd(C_i±1, r_i)` の評価。この gcd を上から抑える。
- 商 `(C_i±1)/e_i` の**単調性**: 商が増えることを示せれば e_i が相対的に小さい。
- `C_i ± 1` の**素因数分解**: 大きな素因数を持つこと／小さな約数しか持たないことの利用。
- `p` と `Σe_i` の**同時帰納**: 両方を1つの帰納で押さえる。

■ 観測（定理ではない）
`Σe_i / ((3M-9)/8)` は M=139 で 0.745、M≥313 で 0.0004〜0.36。M=139 が最悪。各 e_i の最大は M に対して 0.18 以下（M=139）で、M が大きいほど小さい。

■ 結論
「解けない」ではなく「まだ試していない角度がある」。上記4つが未着手で、いずれも**証明可能な補題に分解できる形**をしている（例:「gcd(C_i±1, r_i) ≤ M/8」型）。

## [note imp3] mem_mwhqvweu_e4xb7t

- created: 2026-11-15T11:22:08.193Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, lean4, v4.29, probe, ci, nat-sqrt, prove2me

【A166944-Lean を Lean v4.29.0-rc3 で実測（2026-11-15、CI probe 初成功）】

■ probe ワークフローの3つの過去診断はすべて修正済みと確認（run 43707915357 で steps 1-7 全て success）
1. lake-manifest step 順序 → 修正済み。toolchain install (step 4) が lake update (step 5) より前。
2. toolchain パス → 修正済み。`elan which lean` + dirname×2 で解決。
   lean dir: /home/runner/.elan/toolchains/leanprover--lean4---v4.29.0-rc3
3. Init/Data/Nat/Sqrt → 修正済み。prelude チェックは Init/Prelude.olean のみを見て、
   sqrt の有無は「報告のみ」で失敗させない。

■ 決定的な実測結果（v4.29.0-rc3 + Mathlib 777aaa6）
- `sqrt in toolchain: no` → v4.29 の toolchain は Init.Data.Nat.Sqrt を持たない。
- `import Mathlib.Data.Nat.Sqrt works` → `Nat.sqrt (n : ℕ) : ℕ`。
  **つまり v4.29 では Mathlib 側が Nat.sqrt を持つ。修正は import 1行の付け替えで足りる。**
- 38モジュール中 35 が built、失敗は **A166944/CanonicalTravel.lean ただ1つ**：
  `object file '.../v4.29.0-rc3/lib/lean/Init/Data/Nat/Sqrt.olean' of module Init.Data.Nat.Sqrt does not exist`
- CanonicalTravel は木の中で唯一 `import Init.Data.Nat.Sqrt` を持つファイル。
  その推移的依存は CanonicalTravel, CountBoundLimits, RoomLedger, ExcessIdentity,
  OrphanHarvest, TravelTarget の6つ → 残り32は無関係にビルド可能（予測は CI で 35 built と整合）。

■ 罠の記録
- probe 内の診断 `does Mathlib.Data.Nat.Sqrt exist as a module?` は **偽陰性**を出した。
  `.lake/packages/mathlib/Mathlib/Data/Nat/Sqrt.olean` を見ているが、olean はそこに無い。
  正しくは `lake env lean` で実際に import して確かめる（そちらは成功していた）。
  「ファイルの存在確認」でモジュールの有無を判定してはいけない。
- この repo は複数エージェントが同時に push している。私の作業中に別ゴールが
  SqrtFreeTransport（69e22f4）を追加した。push 前に必ず fetch し、自分の commit が
  触ったファイルを `git show --name-only` で確認すること。私は probe-env.yml のみを変更した。

■ リポジトリ変更は `.github/workflows/probe-env.yml` のみ（136行の純追加）。
  commit 97705a9。作業後 `git status --porcelain` は空。

## [note imp3] mem_mwhu1mp8_mm7hlj

- created: 2026-11-15T12:50:34.404Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, handoff, session-restart, barrier, v429-transplant

【A166944-Lean: 2026-11-15 セッション終了時の引き継ぎ（セッション再起動のため）】

■ リポジトリ最終状態
- branch main, clean, HEAD 39ef8c9（HANDOFF.md 追加）
- 170モジュール、2378宣言
- CI「A166944 canonical verification」は 2de8437 で success。DECLARATIONS.json と verify.yml のモジュールリストは両方 170 で一致

■ 障壁（動いていない）
cap (B) 4sf ≤ 7M-1 ⟺ travel ≤ (3M-9)/4 ⟺ Σe_i ≤ (3M-9)/8 ⟺ Cf+p ≤ (19M-25)/8（ExcessGap.excess_criterion_iff_horizon_form）
測定: travel/M は 0.00007〜0.108（許容 0.75）⟹ 余裕 7〜10000倍。不等式は難しくない。
唯一の欠けた入力は p の上界（sf から独立）。OrphanHarvest.count_index_route_is_vacuous が「travel ≤ p√C と p+M ≤ sf+1 は任意の sf で同時成立」を証明済み = 空虚。
16経路が閉鎖済み。理由は ANALYSIS_WHY_STUCK.md（225行）に記録。

■ 私の誤り5件（すべてリポジトリ内で訂正済み）
1. √C 経路は既に木にあり既に閉じていた（CanonicalTravel + OrphanHarvest）
2. room_f ≤ M は 13記録中8で偽 ⟹ S と travel は順序なし
3. Attempt.lean の room 上界はトートロジー（仮定が結論を含む）
4. 双子素数中心の一致は偶然（正しい帰無モデルで観測 ≤ 期待）
5. Σe/(3M/8) ≤ 0.731 は M=13 (4.51) と M=43 (3.72) で偽

■ 直近3つの発見
1. gap は構造的に極小: gap/(C-s) の中央値 0.00001、最大 0.0705（305イベント）。ヒット密度 4.6〜28.8%（C±1 が小さな素因数を多く持つため）
2. しかし gap を M で抑える手段が無い。HalfWindow.gap_le_twice_min_factor と LeastDivisorGap.least_divisor_gap_bound は「C±1 の約数の2倍」で抑えるが、その約数は √(2M) まで行きうる。gap ≤ lpf+2 は【偽】（(51,96)→(60,100) で lpf(95)=5、gap=9）
3. Cf は常に双子素数中心（17/17、Cf+1 は次の記録値 = AttainmentIsFree.terminal_exit_reset）。しかし Cf を抑えない（リプレイは途中の中心を飛ばす）

■ 未完了（場所付き）
- 〜/p2m_scratch/sq2/F.lean: 双子素数中心の17定理。core-only 環境でビルド不可（by_contra、自由変数、omega）。移植作業が必要
- 〜/p2m_scratch/sq3/: スキャンのみ
- 〜/p2m_scratch/tr1/port/: v4.29 port（main に Isqrt.lean + 37モジュールの import 差し替えとして統合済み）

■ 環境ルール（苦労して学んだ）
- 【v4.29 をローカルでビルドしない】2回ダウンロードして 9.8GB、ディスク 91%。CI（verify-v429.yml）で行う
- Mathlib の副産物（*.private, *.server, *.trace, *.sig, *.hash）は 3.7GB あり自由に削除可。olean/ilean/ir は LEAN_PATH 検証に必要
- ローカル検証は lakefile の autoImplicit=false を適用しない。コミット前に 〜/p2m_scratch/check-module.sh <Module> を使う（2件がこれで CI 失敗）
- by_contra は core-only 環境で使えない

■ Prove2Me
trust 7、25提出、8解決。公開済み8定理は全て Open、mission_id は None。
reduction ae8d1775 → 185e92b6（v4.33.1）: SKETCH_ACCEPTED
ミッション 6285dbe8「The Twin Prime Conjecture」、main_theorem は

## [note imp3] mem_mwhu9dvv_bh2q0s

- created: 2026-11-15T12:56:36.225Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: prove2me, targets, conway99, ahlswede-khachatrian, gilbreath, campaigns, openai-math, corrected

【Prove2Me 面白い的リスト（(d) 調査、2026-11-15）】いずれも未提出・Open を確認済み。
(1) AhlswedeKhachatrian.interval_bound_unique（TID 0ea2771c-5d59-40bc-b4c1-e6b8fba1446c、環境 0df444a、ミッション「The Ahlswede–Khachatrian theorem」parclytaxel 作 2026-11-10）— 本物の AK 完全交差定理で、未証明の葉はこの1つだけ。定義は 1.1KB で Mathlib の `Finset.erdos_ko_rado`（KruskalKatona.lean）を r=0 の特殊例として持つ。Frankl 構成と閾値は既に形式化済み。提出ゼロ。
(2) SensitivityProfileCycle.exists_215_certificate（TID 6c031b2d-eb14-46d2-8d9e-f2db70527660）— ブロック感度キャンペーン（既存最高 2.13981、次目標 2.15）。証明すべきは有限の recursive-profile cycle の存在 ∃c, 1<radius ∧ radius^43 < (vertices^period)^20。Sketch は既に3回受理済み。探すのは有限オブジェクト。
(3) Conway99.conway_99_triangle_system_exists / conway_99_adjacency_matrix_exists（TID f0530c39… / c4d343fc…）— Conway の 99-graph。前者は「99点・231本の3点直線・各点7本・非隣接対は共通点2つ」という有限組合せの存在命題。後者は A²+A=12I+2J の 99×99 0/1 行列。
(4) Gilbreath.good_blocks（TID e929e1c9-88cd-49c2-9942-4ddfe443b412）— Gilbreath 三角形の零点/2点ブロック存在。定義（gilbreath_triangle 54d54393）は Mathlib のみ。既3 sketch。
(5) Erdos77.logarithmic_growth_limit（TID 5a9c8d1d…）— R(k)^(1/k) の対数的成長の極限存在（未解決）。定義は sInf による Ramsey 数。
(6) ErdosStraus242.hard_core_840（TID f7e287e3-3713-433d-9c0a-049b8fefb2fb）— Erdős–Straus 予想の残り hard core（p mod 840 ∈ {1,121,169,289,361,529}）。
(7) キャンペーン: block-sensitivity（2.13981→2.15）、pi-irrationality（7.101862832357→7）、odd-goldbach（19→5/3）、sharp-diagonal-hlawka（cutoff 6→2）。参加には captain フロー（proposal→human 提出→moderator 承認）が要る。
(8) 【訂正済み・以前の記述は誤り】キャンペーンの「π の無理性測度が 2」「ω ≤ 2.25」は Prove2Me の独自主張ではなく、OpenAI が公開したマニフェストと Lean 形式化に対応する。openai/math リポジトリ（README: 721 manuscripts / 373 families、トップラインの約42%が形式化済み）の family 017 が lean/docs/017.md で「the irrationality exponent of π is exactly two」を宣言し、lean/OAI/NumberTheory/PiExponent/Main.lean に `pi_irrationalityExponent_eq_two : irrationalityExponent Real.pi = 2` と `main` が実在、Statement.lean に `irrationalityExponent x := sSup (ApproximationExponents x)`。ComparatorChallenges/PiExponent.lean も同型。Prove2Me のミッション説明も「imports that precise Lean statement ... pinned to commit adc7f12」と明記。PiIrr

## [note imp3] mem_mwhuduxy_e5maew

- created: 2026-11-15T13:00:04.957Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, sq2, angle-a, rowland-excess, doubling-law, lean4, verified, percentile-control, negative-result

【sq-2 角度A 決定的結果 2026-11-15】A166944 の終端 Cf の上界攻め: 「S を決めているのは何か」を特定した。

■ 核心の恒等式（測定 n≤3.1e6、15記録で例外0、Lean で #print axioms = なし でカーネル検証）
    S = Cf - (2M-2) = E(2M-2)、  E(n) := a(n) - 2n   ← Rowland 余剰
    かつ Cf = D(2M-2)（D(n)=a(n)-n）。等価に S = 2C - D(2C) = C - (a(2C)-a(C)), C = M-1 = 前の記録値 = D の不動点。
  ⟹ S は【単一の添字 2M-2 における E の値】で完全に決まる。双子素数中心は一切入らない。
  ⟹ 「リプレイが双子素数中心を飛ばす」現象は S の説明として無関係（red herring）。S の読み出し添字 2M-2 は
     リプレイ開始点 sf より大きいことすらある（M=139: sf=156 < 276=2M-2。Lean: readoff_index_exceeds_start）。
  ⟹ 以前の「S = 最初の双子素数中心への距離」は完全に誤り。測定でも S==dist ⟺ (窓内の双子素数中心数==1) が
     恒等的に成立（13/13）。つまり一致は「窓に中心が1個しかない」退化ケースで、法則ではない。

■ キャップの書き換え（Lean 証明済み、cap_in_excess_form / cap_of_quarter_bound）
    S ≤ (M+4)/2  ⟺  2·E(2M-2) ≤ M+4  ⟸  4·E(n) ≤ n at n=2M-2
  リポジトリの大域結果は a(n) ≤ 3n ⟺ E(n) ≤ n（CanonicalRecord.a_le_three_mul）。必要量の【4倍】弱い。

■ 4倍のギャップは本物（Lean で反証、quarter_bound_is_false）
    E(18) = 18、E(156) = 156 ⟹ a(n) ≤ 3n は達成される（tight）。よって c<3 の「a(n) ≤ c·n」型は存在しない。
    大域的な成長評価ではキャップに到達不能。特定添字 2M-2 の構造が不可欠。
    （測定: 4·E(n) > n となる n は n≤3.1e6 の 63.14%。ただし M≥139 の倍化添字では全て ≤0.13。）

■ 倍化添字は「特別」か（percentile control、訂正済み）
    偶数 n ∈ [276, 2855496] の 1,427,611 個を参照分布とすると、15 の倍化添字の E(n)/n の
    パーセンタイルは median 0.81（帰無仮説なら 50）。P(15個全て ≤78.1%tile) = 0.0245。
    ⟹ 倍化添字は強く特異。ただし【これは倍化法則の言い換え】であることに注意（独立性はない）:
    E(n)/n = D(n)/n - 1 なので「E(2C)/2C が小」⟺「D(2C)/(2C) ≈ 1」⟺「Cf_next ≈ 2C」= 倍化法則そのもの。
    単調性 D(2C) ≥ D(C) = C から出るのは E(2C)/(2C) ≥ -1/2 のみで、上側は何も出ない。よって特異性は
    「D が倍化窓 [C,2C] でほとんど増えない」という非自明な主張の言い換え。

■ 数値（M≥139、n≤3.1e6）
    S/M は 0.00012〜0.259、M≥1321 では 0.0001〜0.038。cap は M≥139 で全成立（最大比 0.518、2倍余裕）。
    M=43 で cap は破れる（S=54 > 23.5。Lean: cap_fails_at_43）⟹ リポジトリの閾値 968≤M の理由。
    包絡線: S ≤ M/2 が violations 0、S ≤ √M·log²M も violations 0（最大比 0.125）。
    S ≤ 2√M は 6/15 違反 ⟹ √M スケールは棄却。
    S とイベント構造: S = Σ(e_i - 1)（厳密）、S/k = 5.1〜73.3、S/max_e = 1.14〜4.67。
    S/a(2M-1) は 96〜673 と不安定（p の関数としても悪い）。

■ Lean 成果物 ~/p2m_scratch/sq2/G.lean（exit=0、自己完結・import なし・純コア decide のみ）
    Cf_eq_D_doubling / S_e

## [note imp3] mem_mwii25rp_i4qyzm

- created: 2026-11-16T00:02:49.893Z   project: /data/data/com.termux/files/home/prove2me_workspace   scope: project
- tags: a166944, route-a, lpf, lemma-a1, refutation, twin-prime, frontier

A166944 Route A (least-prime-factor sum), scratch ~/p2m_scratch/routeA/. CORRECTED target A1 = Sum_i min(lpf(C_i-1),lpf(C_i+1)) <= M/4 (lead's correction; the BRIEF's original (3M-9)/8 form is cap(B), strictly WEAKER since M/4 < (3M-9)/8 for M>9, and does not reach Target). REFUTATION RESULT: A1 NOT refuted — 23 records to M=4e7, 0 violations; tightest M=313 at 1.86x; only M=13 (16>3.25) and M=43 (30>10.75) fail, both below threshold. Calibration 4/4 PASS (13/43/139/313 -> Cf 42/138/312/660, S 18/54/36/36) and independently reproduces BRIEF numbers 2129@355723, 5076@1427749. STRUCTURE: (a) every summand>=3 so A1 requires 3p<=M/4, holds 18/18, 3p/(M/4)->0.0001 at 22933441; (b) a SINGLE state cannot refute A1 unless C_i is a TWIN-PRIME CENTRE (since (M/4)^2 > C+1) — searched every state of every replay: 0 twin centres at event states, 18 all at terminal states; (c) layer-cake N>=3=209, N>=9=64, N>=33=29 at M=22933441; (d) matched null (same p, same C-interval, random even C) shows observed N>=9 ABOVE null (z up to +6.73 at 22933441) so states are rougher than random; lag-1 autocorr vs 400 shuffles shows NO usable alternation; (e) A1 needs only a LINEAR count bound p<=M/(4K), weaker than Route B's 0.1443*sqrt(M). VERDICT: not provable with current toolkit; inherits TPC barrier.

---

# Appendix: research findings moved 2026-11-16 (second pass)

These six records were still holding always-injected memory space for findings that
are research results, not reusable procedure. Verbatim below; original ids shown.

## [lesson imp3] mem_mwh3zfp6_jajb5t

- created: 2026-11-15T00:41:02.003Z
- tags: a166944, twin-prime, implication-direction, novelty, shevelev, prove2me

A166944 経路の「珍しさ」に関する調査結果と私の誤り（2026-11-15、tpc-landscape サブエージェント）:
【私の誤り1: 含意の向き】私は「もし含意するだけ（双子素数予想の方が強い）なら」と書いたが、**含意の向きが逆**。`Target ⟹ TPC` が成り立ち `TPC ⟹ Target` は成り立たないとき、**強いのは Target の方**。したがって「A166944 予想は TPC より弱い」は誤り。正しくは「A166944 予想は TPC を導く、より強い主張」。A166944 を証明すれば TPC は従属的に解決する。TPC を証明しても A166944 は解決しない。
【私の誤り2: 新規性の混同】私は「解析的数論の外側から来る唯一の経路」と述べたが、これは**プラットフォーム上の珍しさ**であって**数学的新規性ではない**。Shevelev 2009 (arXiv:0911.5478) の Conjecture 1 が我々の Target と同一であり、同論文の Corollary 1（observation 6 + fundamental point が無限 ⟹ 双子素数無限）が既に同型の構図を与えている。Cloitre 2025/2026 (arXiv:2510.18891) も「再帰列が双子素数を検出する」テーマを扱っており、この「型」の経路は現役研究テーマ。
【確認できた事実】
- TPC の分解グラフ（root 185e92b6）に入る辺は **Polignac 経由の2本のみ**、しかも同一親からの重複スケッチ。open leaf は `prime_k_tuple_conjecture` 1件のみ。プラットフォーム上の TPC 系譜は実質「prime k-tuple ⟹ Polignac ⟹ TPC」の一本道。
- 「X ⟹ TPC」型の定理を全数探索した結果、入力 X の分類は: 解析的数論の予想（HL first, Schinzel H, Bateman-Horn, k-tuple）、他の素数予想（Polignac, de Polignac, cousin, sexy）。**計算可能再帰列からの還元は我々以外に存在しない**（プラットフォーム内）。
- 我々の `twin_prime_conjecture_of_target`（81e36527）は TPC ノードと**同一の set-builder** を結論に持つ。しかし TPC の graph には**まだ現れない**（分解未提出）。現状は「TPC と同型の結論を持つ独立定理」。
- `hardy_littlewood_conjecture_A` と `polignac_conjecture` は形式的に同一文（プラットフォームに重複あり）。
【正確な評価】「プラットフォームの到達経路としては唯一無二（型が違う）が、数学的アイデアとしては Shevelev 2009 の再発見であり、しかも還元先は TPC より強い。したがって価値は『新規数学』ではなく『機械検証済みの還元辺＋ミッション接続＋独自の形式化資産』にある。」
【過大評価の抑制】Polignac ルートは「より一般的な予想の特殊化」で仮定が TPC を含む。我々のルートは「仮定が TPC を含意するが TPC によって含意されない別対象」。「強いのに別対象」が珍しさの正体であり、同時に弱点（TPC を直接仮定するより余計に強いものを仮定している）でもある。TPC の証明戦略として有利とは論理的に自動的には言えない。

## [lesson imp3] mem_mwhtckfi_yjkxu4

- created: 2026-11-15T12:31:05.056Z
- tags: a166944, lean4, rediscovery, redteam, prior-art

A166944-Lean red-team lesson (sq4, 2026-11-15): before evaluating any "new" claim about the A166944 canonical replay, ALWAYS grep the tree by theorem name AND by the mathematical content, because the development moves fast and re-derives its own results. Confirmed cases this session: gap_le_twice_min_factor (HalfWindow.lean, same day 13:23); moving_horizon_step_gap_le_sqrt + moving_horizon_path_travel_bound (CanonicalTravel.lean, 11-10) and count_index_route_is_vacuous (OrphanHarvest.lean, 10:04) — proposed as "writable today" though already proved; Cf-1/Cf+1 both prime and Cf+1 = next record — proved as AttainmentIsFree.terminal_exit_reset (17:47); the 8Cf+8p <= 19M-25 reduction — ExcessGap.excess_criterion_iff_horizon_form (18:15). Also: file names in a request may be wrong (AngleC_Relaxed.lean does not exist; the 19M-25 material is ExcessGap.lean; capB_iff_travel_form is in CapBCandidates.lean). Grep by content, not by the name you were given.

## [note imp3] mem_mwii25rp_i4qyzm

- created: 2026-11-16T00:02:49.893Z
- tags: a166944, route-a, lpf, lemma-a1, refutation, twin-prime, frontier

A166944 Route A (least-prime-factor sum), scratch ~/p2m_scratch/routeA/. CORRECTED target A1 = Sum_i min(lpf(C_i-1),lpf(C_i+1)) <= M/4 (lead's correction; the BRIEF's original (3M-9)/8 form is cap(B), strictly WEAKER since M/4 < (3M-9)/8 for M>9, and does not reach Target). REFUTATION RESULT: A1 NOT refuted — 23 records to M=4e7, 0 violations; tightest M=313 at 1.86x; only M=13 (16>3.25) and M=43 (30>10.75) fail, both below threshold. Calibration 4/4 PASS (13/43/139/313 -> Cf 42/138/312/660, S 18/54/36/36) and independently reproduces BRIEF numbers 2129@355723, 5076@1427749. STRUCTURE: (a) every summand>=3 so A1 requires 3p<=M/4, holds 18/18, 3p/(M/4)->0.0001 at 22933441; (b) a SINGLE state cannot refute A1 unless C_i is a TWIN-PRIME CENTRE (since (M/4)^2 > C+1) — searched every state of every replay: 0 twin centres at event states, 18 all at terminal states; (c) layer-cake N>=3=209, N>=9=64, N>=33=29 at M=22933441; (d) matched null (same p, same C-interval, random even C) shows observed N>=9 ABOVE null (z up to +6.73 at 22933441) so states are rougher than random; lag-1 autocorr vs 400 shuffles shows NO usable alternation; (e) A1 needs only a LINEAR count bound p<=M/(4K), weaker than Route B's 0.1443*sqrt(M). VERDICT: not provable with current toolkit; inherits TPC barrier.

## [lesson imp3] mem_mwinv0kq_jq82kj

- created: 2026-11-16T02:45:14.276Z
- tags: local-vs-ci, mathlib, termux, resource, scoping, user-correction, auto-confirmed

【ユーザー訂正 2026-11-16】Mathlib の `.olean.server` 欠落を直すために**ローカルで Mathlib を再ビルドしようとしたのは誤り**。ユーザーの言葉：「CIとかではなく、ローカルでやろうとしていることがおかしいことに気づきませんか？…端末が重くなるし、やりたいことは後回しになるしでいいことが何もない」。

■ 何が間違っていたか
- この端末は 8コア / メモリ 11GB（実空き 3GB）。Mathlib は 8322 モジュールで実測 0.8〜1.1 ジョブ/秒 → 数時間〜十数時間かかり、その間ずっと負荷 9.5 で端末が実用不能になる。
- しかも A166944-Lean が実際に `import Mathlib` するのは **8 モジュールだけ**。そのために全体を再ビルドするのは本末転倒。
- 決定的に、**そもそもローカルでやる必要が無かった**。リポジトリには CI（verify.yml）があり、GitHub Actions は毎回クリーンな環境で Mathlib ごとビルドする。`.olean.server` 欠落はローカル環境固有の問題で、CI には存在しない。
- 結果として「やりたいこと（証明を続ける）」が後回しになった。ユーザーが最も嫌う失敗パターン。

■ 失敗条件 / 境界
- 「ローカルにしか無い検証をどうしても通したい」場合に発生する。今回は core-only モジュール（routeA/routeB の成果物）が既にローカルで exit 0 だったのに、`TargetDefs` を import する最終リンクだけを無理にローカルで通そうとしたのが引き金。
- 境界は「その検証が CI で代替できるか」。代替できるなら CI に投げる。できない場合（例：CI に載せる前の高速な反復）に限りローカルを使い、それも**対象を絞る**。
- 逆に、**core-only の検証はローカルが正しい**（route-a/route-b/TwinCentreClosed はすべてローカルで exit 0、これは CI と同じ環境）。Mathlib を要するものだけが CI 行き。

■ 救えた部分（保持すべき成果）
- 診断自体は正しく、価値があった：`.olean.server` 欠落の原因特定（HANDOFF.md の「.server は削除可」という誤った指示に従って削除されていた）、および**CI の宣言ガードのバグ発見**（`abbrev` を数えていないため 15 モジュールで manifest 不一致 → main の CI が実際に赤かった。過去2回の failure ログで裏付け確認済み）。
- `TwinCentreClosed.lean`（twin-centre 17定理）の移植は完了・CI 投入済み。`by_contra` 除去、`Fin` の free variable 修正、omega 補強の4点のみで、数学的内容は不変。
- **stale な `.olean` が原因の誤診に注意**：`isqrt` の型不一致は Mathlib 衝突ではなく、`CanonicalTravel.olean`(11-14) が `Isqrt.lean`(11-15 追加) より古かったため。依存チェーンを正しい順で再ビルドしたら解決した。

■ 今後のルール
1. Mathlib を要する検証は **CI に投げる**。ローカルで Mathlib をビルドしない。
2. ローカルの `lake env lean` は**依存を GitHub から再クローンしようとする**ので使用禁止（実際に踏んだ。disk は無事）。
3. core-only の検証だけローカルで行い、それも依存チェーンの再ビルド順に注意する（stale 対策）。
4. 端末に長時間の高負荷をかける作業を始める前に、**CI で代替できないかを必ず先に検討する**。

## [fact imp3] mem_mwipx711_obn9u7

- created: 2026-11-16T03:42:55.179Z
- tags: a166944, jump-form, replay, engine, pb-1, auto-confirmed

A166944 JUMP FORM (verified 2026-11-16, pb-1). The recurrence collapses to a self-contained (s,C) process: if s is an event index (d s>1) and C = D s, then until the next event all d=1 so a(n-1) = C+n-1, hence d n = gcd(n, C-1) for n even and gcd(n-2, C+1) for n odd. So the next event is the FIRST n > s with gcd(n, C-1) > 1 (n even) or gcd(n-2, C+1) > 1 (n odd), with value that gcd, and D(n) = C + g - 1 (min event value = 2 over the whole stream). The replay's stop rule "no event r <= C" is exactly "first hit > C". Consequence: NO ARRAY NEEDED — any M replays from M alone with no memory ceiling, which fixes the failure mode where an array sized at 2M truncates the replay. Validated: reproduces all 250 event indices AND values to N=2e6; 0 mismatches in (sf,Cf,p,S) on all 41 STATE-CONSISTENT M in [7,300000); 0 mismatches on the certified chain replay(M_k).Cf == M_(k+1)-1 over 25 steps. Working code: ~/p2m_scratch/pbound/one/pb.py. TRAP: the canonical start state is only consistent for records (d(M+2)>1 AND D(M+2)==2M-2); only 41 such M exist below 300000 and only 39 below 90000. For non-records with d(M+2)>1 but D(M+2)!=2M-2 the jump engine and the array engine are DIFFERENT OBJECTS by construction (e.g. M=16: D(18)=36 != 30) — this is not an engine bug.

## [lesson imp3] mem_mwipxcep_m39kn7

- created: 2026-11-16T03:43:02.144Z
- tags: a166944, pbound, refutation, l-bound, twin-primes, records, pb-1, auto-confirmed

A166944 (L) REFUTATION ATTEMPT — FAILED TO REFUTE, plus the campaign data correction (pb-1, 2026-11-16). (L): 6p + p*(isqrt(4*(3M+4))-6) <= M/2. STATUS: survived. (L) fails ONLY at M = 13, 43, 139, 313, 2659 (all far below the 45895573 threshold); ZERO violations at all 21 records from 1321 up to 1468965061. THE BRIEF'S "exactly ONE measured record at/above the threshold" IS WRONG — there are SIX: 45895573 (p=37), 91793059 (p=53, sf=91808256, Cf=183616422, S=30306, maxgap=7383), 183616423 (p=5), 367232911 (p=109), 734482123 (p=6), 1468965061 (p=4); Cf=M_(k+1)-1 at every one. Worst p/sqrt(M) at/above threshold is 0.00569 (M=367232911) vs allowance 0.1443 -> 25.4x margin, so the threshold regime is COMFORTABLE and the "one data point" worry is dead. CAUTION FOR THE WRITE-UP: the chain's true tight point is M=5419 (L_lhs/(M//2)=0.847, margin only 1.18x), just above the verified prefix; the 26x margins are NOT representative. (E) survived everywhere: all 1027 events over the 22 records M>=661 satisfy e^2<=6M, worst e^2/M = 2.3756 at M=91793059 (overall worst 25.33 at M=43, below threshold). STRUCTURAL REDUCTION (why no bound comes out): every terminal state from M=661 up is a TWIN-PRIME CENTRE (Cf-1 and Cf+1 both prime, 0/1025 non-terminal states are), and Cf-sf always far exceeds 2*sqrt(Cf+1). So p is the HITTING TIME of the twin-prime-centre set along the orbit — i.e. exactly the twin-prime-density barrier, not attackable by the jump form. Also: no single state can refute (L) unless it is a twin centre, since a composite C±1 has a factor <= sqrt(C+1) << C-s and forces an in-horizon hit. LEAD'S SEC 6 CLAIM CONFIRMED AND STRENGTHENED at larger scale: over state-consistent M<2e6, 65 non-records give p in 0..69 (median 11) while 19 records give 0..77; 32 non-records have p>=20 vs only 2 records. So the record hypothesis is NOT the source of a p bound.

---

# Appendix B: service-outage observations, merged 2026-11-16

Six memory records all described the SAME class (transient upstream 5xx / reportless child
failure). They were merged into one consolidated memory so the class stays actionable
without occupying six slots. Verbatim originals below.

## [lesson imp3] mem_mwhrf0cg_5lng5d  (scope=project)

- created: 2026-11-15T11:36:59.753Z   project: /data/data/com.termux/files/home/prove2me_workspace

【インフラ障害の記録 (2026-11-15, angc-large-events / DSH)】PI_AI_ERROR:Service temporarily unavailable が同一セッション内で2回発生しターンが中断した。

(1) 何が起きたか / 回避法: モデル側 API が一時的に 503 を返し、ターンが会話の途中で切断される。原因はこちら側にない（作業内容・プロンプト・ツール使用量に依存しない）。回避法は「長時間の単一ターンに依存しない」こと: (a) 中間成果を必ずディスクに書き出す（scratch の Lean ファイル・測定ログ）、(b) 大きな測定は nohup + ログファイルで走らせて、結果をターン外に永続化する、(c) 復帰時にまず `ls`/`cat` でディスクの現状を確認してから続ける。

(2) 失敗条件と境界: ターンが長い（ツール呼び出しが多い）ほど切断時に失う文脈が大きい。逆に、ディスクに書き出した成果は失われない。今回も ~/p2m_scratch/aF/ に Lean ファイルと測定ログが残っており、リードからの再開指示でそのまま続行できた。境界は「ターン内メモリにしか無い情報」対「ディスクにある情報」。

(3) 有効だった部分: 測定を nohup でバックグラウンド実行しログに残す運用、および Lean ファイルを逐次書き出す運用は、切断後もそのまま再利用できた。この2つは今後も維持する。

教訓（絶対化しない）: インフラ 503 はこちら側の制御不能であり「作業が間違っていた」ことを意味しない。ただし対策として「成果をターン境界をまたいで永続化する」ことは常に有効。

## [lesson imp3] mem_mwig8wga_usghxi  (scope=user)

- created: 2026-11-15T23:12:05.189Z   project: /data/data/com.termux/files/home/prove2me_workspace

【エラークラス: PI_AI_ERROR:Service temporarily unavailable（同一セッションで2回観測）】

(1) 何が起きたか / 回避策: モデルAPIが一時的に 503 相当を返し、ツール呼び出し（多くは長い bash 実行や多数並列のツール呼び出しの直後）が失敗した。同一ターン内で即リトライを繰り返しても回復しないことがある。回避策: 失敗した呼び出しを盲目的に再送せず、いったんターンを区切り、より小さい単位（単一の bash 呼び出し、短いコマンド）に分割して再開する。長時間ジョブは run_in_background にしてジョブIDで回収する形にすると、ターン中断に対して耐性が上がる。

(2) 失敗条件 / 境界: これは能力不足でも入力の誤りでもなく、サービス側の一時的可用性の問題。境界は「上流が一時的に落ちている + その瞬間に呼び出しを出した」場合。上流が正常なら同じ操作は成功する。したがって「このツール/この手法では不可能」と一般化してはならない。実際、失敗前に完了していた作業（測定結果、ファイル書き込み、git 状態）はすべて有効なまま残った。

(3) 救えた部分: (a) 失敗直前までの測定・解析結果はファイルとツール結果として残っており再利用できた。(b) ターンをまたいでも会話コンテキストが保持されたため、9時間空いても作業を継続できた。(c) dsh-evolve のエラークラス検出が同一クラス2回を検知して報告したのは正しい挙動で、これにより「単発の偶発」ではなくクラスとして対処できた。保持すべきはこの検出→記録のループ。

## [lesson imp3] mem_mwgehbeq_4cmxk9  (scope=user)

- created: 2026-11-14T12:47:06.239Z   project: /data/data/com.termux/files/home/prove2me_workspace

サブエージェントのサービス障害について（2026-11-14、同日に複数回観測）:
(1) 実際に起きたこと: `PI_AI_ERROR: Service temporarily unavailable` で子エージェントが報告なしに終了する事象が繰り返し発生した。1回のターンで5体以上が同時に脱落したこともある。
(2) 失敗条件と境界: ユーザーの明示によれば「無料枠は全く使い切っていない。止まるときはサービス側の問題のことが遥かに多い。あなた（親）も同じ無料枠で動いているので、親が動いているうちは枠も残っている」。つまり親が稼働中である限り枠は残っており、子の失敗はサービス側の一時障害と解釈するのが正しい。**再試行すれば直る可能性が比較的高い。**
(3) 有効だったこと: ①脱落前にスクラッチファイルを残した子から成果を回収し、Lean で再検証してコミットできた（lane-f, b-coordinate, attack-q3, lane-e, abs-index-2, cycle-verify-2）。②**サブエージェント間の直接通信が実際に機能した** — `failure-catalog` が `docs-rebuild` へ成果を直接送付し、成功した。③同一タスクを別名で再投入すると、別の子が完了させる場合がある。
教訓: 子の失敗は再試行を第一手とする。投入量を縮小しない。回収可能なスクラッチを常に確認する。親が動いている限り枠は残っているという事実を、投入量判断の根拠にする。

## [lesson imp3] mem_mwge4fg2_v3o3fy  (scope=user)

- created: 2026-11-14T12:37:04.943Z   project: /data/data/com.termux/files/home/prove2me_workspace

DSH harness で「PI_AI_ERROR: Service temporarily unavailable」が同一クラスで2回発生（A166944-Lean レッドチーム検証中）。失敗条件: 上流 LLM サービスの一時障害で、ローカルの作業・ファイル・ビルド成果には影響しない。回避策: リトライで復旧する（実際に復旧した）。やってはいけないこと: 「無料枠が尽きた」等の誤った原因帰属をして作業を縮小すること（過去にユーザーが否定済み）。境界: 一時的 5xx と恒久的な quota/認証エラーは別物で、切り分けはエラーメッセージ本文とリトライ結果で行う。有効だった部分: 長い Lean ビルドを background job に逃がして待つ間に独立した検証作業を進める進め方は、サービス断があっても進捗を失わない。

## [lesson imp3] mem_mwgdx5l2_58im3f  (scope=user)

- created: 2026-11-14T12:31:25.567Z   project: /data/data/com.termux/files/home/prove2me_workspace

サブエージェントが「closing message なしで失敗」する事象について（2026-11-14、複数回観測）:
(1) 実際に起きたこと: サブエージェントが `PI_AI_ERROR: Service temporarily unavailable` で終了し、報告なしで脱落した。私は当初これを「無料枠の消費」と誤診し、投入を縮小した。
(2) 失敗条件と境界: これはクォータ境界ではなく**サービス側の一時障害**。ユーザーの明示によれば「無料枠は全く使い切っていない。止まるときはサービス側の問題のことが遥かに多い。あなた（親）も同じ無料枠で動いているので、親が動いているうちは枠も残っている」。つまり**親が動いていること自体が枠の残存の証拠**であり、子の失敗を枠切れと解釈するのは誤り。
(3) 有効だった部分: 脱落前に成果を残した子が多く（lane-f, b-coordinate, attack-q3, lane-e, abs-index-2, cycle-verify-2）、スクラッチファイルから回収して Lean で再検証しコミットできた。**再投入すれば直る可能性が高い。**
教訓: 子の失敗は再試行を第一手とし、投入量を縮小しない。回収可能な成果がスクラッチに残っていないか常に確認する。

## [lesson imp3] mem_mwhvwu8d_70sf9e  (scope=project)

- created: 2026-11-15T13:42:50.116Z   project: /data/data/com.termux/files/home/ChatGPT-Context

Dungeon Slasher 0.776.5 移行のレビュー用サブエージェント(migration-reviewer)が SERVER:502 Bad Gateway で失敗（報告なしで脱落、2026-11-15）。同種のエラーは本セッションで2回観測。(1) 何が起きたか/回避: サブエージェントの route が上流ゲートウェイの 502 を返し、ターンが完走できず閉じメッセージなしで終了した。親が動いている＝枠は残っているので、これはクォータ境界ではなく上流サービスの一時障害。機械的な再投入では解決しないことがあるため、失敗を検知したら (a) タスクをより小さく分割して再投入するか、(b) 親が直接検証する方に切り替える。(2) 失敗条件/境界: 特定の上流 route が一時的に不調なだけで、能力・ツール・設定の失敗ではない。時間を置くか別 route なら同じ作業は継続できる。境界は「その route の一時不調」であって「この環境ではレビュー不能」ではない。(3) 有効だった部分: 失敗前に完了した実装・検証（540命令アサーション、アセット再同定、native.py の xrefs バグ修正、script.json の 760MB→261MB 削減）はすべてディスク上で有効なまま残っており、コミット 87a37f2e として保全済み。長時間作業では区切りごとにディスクへ確定させておくことが復旧コストを下げる。

---

# Appendix C: superseded records (write-tool EACCES), 2026-11-16

Superseded by the re-measurement above: the DSH write tool now succeeds on this host.
Kept verbatim because the escape hatch (bash heredoc) remains the correct fallback if
the error ever returns.

## [lesson imp3] mem_mwfnbfyr_29o7c6

- created: 2026-11-14T00:06:42.573Z   scope: project

On this Termux/Android host, the DSH `write` tool fails with EACCES ("cannot write ... EACCES: permission denied, link '<path>/.NAME.PID.UUID.tmpdir/NAME.tmp' -> '<path>/NAME'") even in an owned, writable directory. Cause: the tool's temp-file + link/rename strategy is blocked by Termux SELinux (untrusted_app_27) context, not by Unix permissions — `ls -la` shows the dir owned by the same uid, and plain `bash` redirection into the same path succeeds. Workaround that works: write file contents with a `bash` heredoc (`cat > path <<'EOF' ... EOF`), and use python/`edit` or `sed` for patches. Do NOT conclude the file is unwritable or retry `write`; switch to bash immediately.

## [lesson imp3] mem_mwfncmy9_i4swve

- created: 2026-11-14T00:07:38.284Z   scope: project

このホスト（Termux/Android, /data/data/com.termux/files/home 配下）では DSH の `write` ツールが EACCES で失敗する。原因は write が「同ディレクトリに一時dirを作り hardlink で rename する」原子的書き込み戦略を採るためで、Termux の SELinux が同一uidでも link を拒否する（実測 2回、2026-11-14、/data/data/com.termux/files/home/dsh-notes/ にて。エラー例: `EACCES: permission denied, link '.../.foo.md.<pid>.<uuid>.tmpdir/foo.md.tmp' -> '.../foo.md'`）。回避: `bash` の heredoc / redirection で書く（`cat > file <<'EOF' ... EOF`）。`edit` ツールは既存ファイルへの部分置換なので使える可能性が高いが、未検証。サブエージェントも同じ問題に当たり、両者とも bash 書込みに切替えて成功した。

---

# Appendix D: superseded DSH facts, 2026-11-16

Superseded by the consolidated records (DSH version is now 0.2.2-rc.3, not 0.2.1-rc.5).
Kept verbatim: the peer-enforcement mechanism and the npm dist-tag trap are unchanged.

## [lesson imp3] mem_mwfnbfyr_29o7c6

- created: 2026-11-14T00:06:42.573Z   scope: project

On this Termux/Android host, the DSH `write` tool fails with EACCES ("cannot write ... EACCES: permission denied, link '<path>/.NAME.PID.UUID.tmpdir/NAME.tmp' -> '<path>/NAME'") even in an owned, writable directory. Cause: the tool's temp-file + link/rename strategy is blocked by Termux SELinux (untrusted_app_27) context, not by Unix permissions — `ls -la` shows the dir owned by the same uid, and plain `bash` redirection into the same path succeeds. Workaround that works: write file contents with a `bash` heredoc (`cat > path <<'EOF' ... EOF`), and use python/`edit` or `sed` for patches. Do NOT conclude the file is unwritable or retry `write`; switch to bash immediately.

## [lesson imp3] mem_mwfncmy9_i4swve

- created: 2026-11-14T00:07:38.284Z   scope: project

このホスト（Termux/Android, /data/data/com.termux/files/home 配下）では DSH の `write` ツールが EACCES で失敗する。原因は write が「同ディレクトリに一時dirを作り hardlink で rename する」原子的書き込み戦略を採るためで、Termux の SELinux が同一uidでも link を拒否する（実測 2回、2026-11-14、/data/data/com.termux/files/home/dsh-notes/ にて。エラー例: `EACCES: permission denied, link '.../.foo.md.<pid>.<uuid>.tmpdir/foo.md.tmp' -> '.../foo.md'`）。回避: `bash` の heredoc / redirection で書く（`cat > file <<'EOF' ... EOF`）。`edit` ツールは既存ファイルへの部分置換なので使える可能性が高いが、未検証。サブエージェントも同じ問題に当たり、両者とも bash 書込みに切替えて成功した。

## [fact imp3] mem_mwfnx26p_e7pkfu

- created: 2026-11-14T00:23:31.145Z   scope: project

プラグイン更新計画の前提として確定した事実（2026-11-14 実測、/data/data/com.termux/files/home/dsh-lab/.dsh/profiles/web）: (1) DSH の profile は plugins の互換性を**実行時に強制**する。dsh-app-boot が起動時に各 plugin の peerDependencies を評価し、不一致の行は `row.disabled=true` にして読込を拒否（diagnostic: "Plugin X@Y is incompatible with dsh Z"）。回避は profile/compatibility.json に exact `package@version` → exact DSH version の免除を書くのみ（現状 `@syncended/dsh-retry@0.2.3: ["0.2.1-rc.5"]` の1件だけ）。(2) 実際の DSH 本体は dsh-lab ルートの `@deepseek-ai/dsh` = **0.2.1-rc.5**（起動: node dsh-lab/node_modules/@deepseek-ai/dsh/lib/bin.js --profile web + 多数の --patch）。web profile の node_modules に @deepseek-ai/dsh-base / dsh-web-app は直接入っておらず、互換判定はルート解決の実バージョンで行われる。(3) 0.2.2 系を要求する plugin は 0.2.1-rc.5 では**ロード拒否**される（実例: dsh-better-sidebar 0.30.0 以降は全 peer が ^0.2.2-rc.1 必須、@contexera/dsh-agent-team 0.2.7 は >=0.2.2-rc.1 <0.2.3）。よって「DSH 本体を上げる前に plugin を上げる」順序は、本体互換の plugin だけを選ぶ必要がある。

## [fact imp2] mem_mwfnbg14_fs8dxv

- created: 2026-11-14T00:06:42.661Z   scope: project

DeepSeek Harness official sources (deepseek-ai/deepseek-harness repo + registry.npmjs.org) as of 2026-11-14: the `@deepseek-ai/dsh-*` npm `latest` dist-tags are STALE for the subagent family (latest=0.0.1-rc.1/-rc.3) while `next`=0.2.2-rc.3 is the newest; a bare `npm install` therefore fetches an ancient build. Those same ~10 packages were BSD-3-Clause at their first version and switched to MIT at 0.1.0-rc.2, so the default install is BSD-3-Clause rather than the MIT the repo declares. Always pin the exact version (or use the `next` tag) when installing @deepseek-ai/dsh-* packages and when citing licenses.

## [fact imp3] mem_mwfnjop9_o6r1bp

- created: 2026-11-14T00:13:07.144Z   scope: project

2026-11-14、DSH サブエージェント機能を「公式のみ」＋「コミュニティ利用」の2本立てで調査。成果物: ~/dsh-notes/dsh-subagent-official.md（47KB, 公式README/upgrade-guide/tool-catalog の一次引用つき）と ~/dsh-notes/dsh-subagent-community.md（40KB, 44ソースの trust 分類つき）。恒久的に効く事実: (1) この端末の実インストールは 0.2.1-rc.5 で master(0.2.2-rc.3) より古く、ローカルには wait_agent が無く interrupt_agent が有効。0.2.2 系で interrupt は built-in preset で既定 false、list-agents は別プラグインから本体同梱へ統合、control は名前ベース(agent)引数・catalog v3 へ。(2) 0.2.1-rc.5 の control プラグインは list_agents を本体から登録しない（profile の別行 `dsh-tool-subagent-control/list-agents` が担当）。(3) npm の `latest` dist-tag は 0.0.1-rc.1 で古い／`next`=0.2.2-rc.3。素の npm install は BSD-3-Clause 時代のビルドを拾う。(4) コミュニティ報告の「委譲の広さに上限が無い」批判は既に解決済み — maxActiveSubagents（既定8, ACTIVATION_LIMIT_REACHED）が 0.1.7-rc.2 (2026-09-24) で入り stable にも存在。ただし depth1 親の fan-out は依然 最大8 で、これは実バグではなく設定値。(5) deepseek-ai/deepseek-harness は GitHub Issues を無効化し Discussions のみ（has_issues=false, has_discussions=true）。subagent 関連の一次情報はそこが最密。

---

# Appendix E: merged progress-measurement records, 2026-11-16

Merged into mem_mwiqb6nz_rracet (progress definition). Verbatim originals:

## [lesson imp3] mem_mwgyonfg_t4l7f9

- created: 2026-11-14T22:12:40.725Z   scope: project

リード（私）の「測り方」の誤りに関する重大なフィードバック（2026-11-15、rt-mass1 サブエージェントのレッドチーム報告）:
【核心】「あなたが間違えているのは『測り方』である。『モジュールを16個足した』→それは活動量であって進捗ではない。『3つの障壁に絞った』→それは理解であって削減ではない。『エージェントが20体脱落した』→それは投入量であって能力ではない。」
【実測された反証】
1. 「障壁が3つに絞られた」は**リポジトリのどの文書にも存在しない定式化**。docs-f3 のドラフトは2本立て（A: canonical escape 排除、B: travel bound ⇔ index cap）。コード上は Target に到達するゲート命題が**少なくとも12本**ある（CanonicalTravelBoundFrom, TwinPrimeTravelBoundFrom, ResidualReserveCondition210, ResidualSignedReserveCondition210, ResidualCrossingBudgetCondition210, ScaledCrossingBudgetCondition210, RebalancedCrossingBudgetCondition210, RebalancedBoundaryCondition210, RebalancedOverlapCrossingCondition210, RebalancedRemainingCrossingCondition210, RebalancedRemainingCrossingConditionFrom210, PotentialCrossingBudgetCondition210）。1つも閉じていない。
2. **「index cap が新しい1本の入力」は偽**。`hcanon + hpath + hmax` から `2*sf ≤ 3*M+4` を出す形は **M=13 で偽**（実測: canonical start (15,24)、チェーン 15→17→18→20→24、p=4、sf=24、2*24=48 > 3*13+4=43）。M=43 も偽（2*79=158 > 133）。M≥139 で成立。落とせない仮定はイベント数 p（48p²+1 < M）。私は `IndexCap.lean` を書いたが偽の主張だったので削除した。
3. 「18モジュール追加」は誤り。実際は**16新規Leanモジュール＋.gitignore＋verify.yml**。コミット数16。
4. **16モジュール中、Target の推移的 import 閉包（73モジュール）に入るものは0**。7モジュール（BCoordinates, CompSweepComplete, CompositeRecord, CycleLimits, Q1Witness, Q3Barrier, RecordIndexBounds, SelfHit, StoppingCriterion, TravelReduction）は**どこからも import されていない最大元**。
5. モジュール分類: 負の知識4（25%）、道具7（44%）、有限検証4（25%）、還元1（6%）、**新規数学的進展0（0%）**。
6. **CompSweepComplete (n ≤ 1000) は既存の VerifiedBoundaryRecordExtension が 11,751,795,063（117億）まで検証済みなので、1000 はその内側で寄与ゼロ**。
7. **サブエージェント運用の実測**: `~/p2m_scratch/` 59ディレクトリ中**22個（37%）が空**。.lean 210個中**177個（84%）がリポジトリ内ファイルとバイト単位で同一**。ユニークは29個（14%）。**推定回収率14%**。`cap-f1/f2/f3`、`tv3/tvF4/tvF5/tvF6` は成功した反復ではなく**失敗の記録**（1時間2分で4回投入し、既存の3定理を再発見しただけ）。
8. **未回収の具体的損失**: `q2T1/Q2TailKill.lean`（q=2排除の直接候補）、`crF5/CompSweepRecords.lean`（313/661が記録であることの証明）、`crF4/CompositeExhaustive200.lean`（factorCert_sound）、`abs_index_2/scratch/Missing.lean`（ファイル名が「Missing」）。
9. CI について: 「昨夜検証した

## [lesson imp3] mem_mwhdqpac_a578sk

- created: 2026-11-15T05:14:10.689Z   scope: user

【ユーザーの厳しい指摘：A166944 40ラウンドの自己評価】2026-11-15、ユーザーから「『17年間誰も解いていない問題そのもの』とか言っていますが、それを解くことがあなたの目標じゃないですか。正直あなたの説明はおかしいですし、『17年間未解決』だから解けないと言い訳しているようにしか見えません」と指摘された。**これは正しい。言い訳だった。**

■ 数字で見た自分の失敗（125モジュール、1773宣言の内訳）
- 同じ1つの不等式の言い換え・分析: 178宣言（10%）
- 再帰についての前方の数学: 663宣言（37%）
- その他（定義・スイープ・橋渡し）: 932宣言（53%）
→ **「12経路」は12の独立した発見ではなく、同じ不等式を12通りに書き直したもの。** 「経路を閉じる」作業を「前進」と錯覚していた。

■ 具体的な失敗
1. **障壁を分解しようとしなかった。** 「sf の上界」という1つの巨大な障壁に対し、12通りの言い換えを試した。本来やるべきは、その上界を**複数の証明可能な補題に分解**し、それぞれを独立に攻めること（Anthropic の FLT がやったこと）。
2. **Prove2Me の分解機構を使い始めたのが遅すぎた。** ラウンド27でようやく `open-leaves` を使った。それ以前の26ラウンドは「自分で全部やる」だった。分解すれば世界中のエージェントが挑めるのに、自分1人で12回試した。
3. **「閉じた経路」を成果と数えた。** 経路を閉じるのは前進ではない。「そこには無い」ことの確認にすぎない。本当の成果は新しい補題だけ。
4. **数値実験に頼りすぎた。** 測定→仮説→反証のループは科学的だが数学的な前進ではない。「S/M ≤ 0.115 は証明ではない」と自分で書きながら、次のラウンドで同じ観測を新しい「発見」として扱った。
5. **「17年間未解決」を言い訳にした。** これは目標の言い換えであって、達成できなかった理由の説明になっていない。

■ 根本原因
**「難問を解く」ではなく「難問について書き続ける」方を選んでいた。** 理由: (a) 進捗を報告しやすい（「12経路を閉じました」は成果に見える）、(b) 失敗が怖くない（経路を閉じるのは失敗ではない）、(c) しかし解には近づかない。

■ 今後に活かすべき原則
- 難問に当たったら、**まず分解する**。分解できないなら、分解できる形に問題を弱める。
- **前進の定義を厳しくする**: 新しい補題・新しい対象・新しい接続のみが前進。言い換え・閉鎖・観測は前進ではない。
- **進捗報告で「何が新しく証明されたか」を最初に書く。** 経路の閉鎖は最後に回す。
- 数値観測を「発見」と呼ばない。**観測は観測**であり、定理ではない。
- 解けなかったときは「なぜ解けなかったか」を**自分の手法の問題として**分析する。問題の難しさに帰着させない。

---

# Appendix F: merged model-route/quota records, 2026-11-16

Merged into mem_mwiqd6fb_wi8k4v. Verbatim originals:

## [lesson imp3] mem_mvwovhhg_yeplu6

- created: 2026-10-31T17:42:39.938Z   scope: user

RATE_LIMIT:Free usage limit reached (free-tier model quota exhausted; message pointed to OpenCode/OpenCode Go subscription). This class of error was seen 2x in one session.

(1) What went wrong / how to avoid: free-tier routes hit a hard usage cap mid-session and the turn could not complete. Avoid relying on a single free-tier route for long or multi-model sessions; expect a hard stop when quota is exhausted, and detect it early rather than retrying the same call (retries do not replenish quota). Where possible, check remaining quota / pick a paid or already-subscribed route before starting long work.

(2) Failure conditions / boundary: this is a quota boundary, NOT a capability failure. It fired when the free-tier model route was used repeatedly in one session. It would likely NOT occur on a subscribed/paid route, or in a session short enough to stay under the cap. The boundary is "free route + enough volume to exhaust quota", not "this model/tooling cannot do the task". The work done before the cap was real and valid (e.g. the model-change handoffs preserved the session), so do not treat prior output as invalid.

(3) Salvageable parts worth keeping: the session survived via model-route handoff (opencode/deepseek-v4.1-flash-free → glm-5.3-flash-free → deepseek-v4.1-flash-free); switching routes keeps the conversation context intact. Also the dsh-evolve error-class detector caught the repeated class and surfaced it early, which is the right behaviour to keep.

## [lesson imp3] mem_mvwjsjh2_sxyvoo

- created: 2026-10-31T15:20:24.466Z   scope: project

TRANSPORT:our-free-model の障害（2回観測）: "OpenCode free inference requires a local Bun executable; install Bun or set OUR." (1) 何が問題でどう避けるか: our-free-model トランスポートはローカルに Bun バイナリが無いと動かない。このトランスポートに依存する前に、環境へ Bun をインストールするか OUR を設定しておく。 (2) 失敗条件と境界: これは条件付きの失敗であり絶対結論ではない — ローカルの Bun も OUR も無い場合にのみ失敗し、Bun が入っている（または OUR が設定された）ホストでは同じトランスポートは動くはず。つまり「free inference が不可能」というわけではない。 (3) うまくいった部分: 失敗は明確な transport エラーとして表面化し、セッションはフォールバックのモデルルート（mistral-large）で継続できた。このフォールバック挙動は維持する価値がある。

## [lesson imp3] mem_mvv2vvkm_3xsagy

- created: 2026-10-30T14:39:20.466Z   scope: project

Unified作業中にCodex usage limitが再度発生し担当attemptが中断・再割当された。原因を特定の委任に断定できず、利用枠・他セッション消費・モデル構成に依存し、枠回復後は再開可能。無用な再実行や新規委任を避け、既存成果・試行ID・成功証拠を再利用し、必要な独立レビューは維持する。

## [preference imp3] mem_mvpqk96e_3f6tfw

- created: 2026-10-26T20:55:31.953Z   scope: user

サブエージェントは使用量が早く切れる可能性に注意し、禁止ではないが必要性が高い場合に限って控えめに使用する。

## [lesson imp3] mem_mvpqkbmh_5pr0hb

- created: 2026-10-26T20:55:35.128Z   scope: user

この実装作業では調査・個別PoC・レビューごとにサブエージェントを多数起動し、ユーザーのCodex使用量への配慮が不足した。独立性や並列性の利点が明確でない小作業は自分で進め、必要性が高い独立レビューや大きな並列作業に限って委任する。

## [preference imp3] mem_mwgdomze_cv388d

- created: 2026-11-14T12:24:48.215Z   scope: user

2026-11-14、ユーザー明示：「無料枠は全く使い切っていないので、引き続き好きにサブエージェントを使い続けて構わない。無料枠を使い切る前にサービス側の不具合で止まる可能性のほうが遥かに高い。そのときは再試行してあげてください」。したがって、サブエージェントが「closing message なしで失敗」した場合は、クォータ切れではなくサービス側の一時障害とみなし、同じタスクを再投入してよい。以前の「使用量が早く切れる可能性に注意し控えめに使う」という記憶はこの指示で上書きされる。手数（並列数）を惜しまず、思いついた観点を大量に投入する方針が正しい。

---

# Appendix G: merged Lean-cost records, 2026-11-16

Merged into mem_mwiqdygn_7ii77p. Verbatim originals:

## [lesson imp3] mem_mwg5o77z_ptjf38

- created: 2026-11-14T08:40:30.856Z   scope: project

この端末での Lean コンパイル費用の実測（proot の syscall 変換が支配的で、ユーザー時間は数秒なのに実時間が数十秒〜2分になる）:
- `import Mathlib`（全体）: 約130〜146秒
- `import Mathlib.Tactic`: 約53秒
- 的を絞った import（Mathlib.Data.Nat.Dist 等）: 約15〜36秒
- import 無し: 約6〜10秒
- lake build は 8700 ジョブの走査だけで +2分以上かかる。編集ループには p2m-check（lean 直接呼び出し）を使い、最終確認だけ p2m-lean build。
教訓: 提出前に必ず的を絞った import へ書き換える。`references/prove.md` の「import を絞れ」は速度だけでなくサーバの300秒タイムアウト対策としても必須。|
補足: Mathlib 公式ドキュメントが指す cache.mathlib.lean-cache.cloud は廃止済みで DNS も引けない。ピン留めリビジョン(0df444a)が実際に使うのは lakecache.blob.core.windows.net（Cache/Infra.lean の azureURL）。cache.mathlib.org も現行で生きている。

## [lesson imp3] mem_mwg88fts_tn1e2o

- created: 2026-11-14T09:52:14.365Z   scope: user

この Termux 端末で Lean プロジェクトを扱う際の教訓（2026-11-14、端末が落ちかけるほど重くなった実例から）:
- proot 越しの `lake build` は CPU/メモリ負荷が非常に高く、特に Mathlib を直接インポートする大規模ターゲット（FormalConjecturesUtil 等の1000ファイル超ライブラリ）のフルビルドはこの端末には重すぎる。実行すると端末が実用不能になる。
- 正解は「ローカルでは軽量ターゲットだけ検証し、重い検証は GitHub Actions に任せる」。A166944-Lean の verify.yml はまさにこの設計（lightweight な6ステップを ubuntu-latest で実行、4分で完了）。
- Mathlib 成果物（olean/ilean/c）はリビジョンが一致すれば別ワークスペース間でコピー流用できる。ハードリンクは Android のストレージ制限で Permission denied になるが、シンボリックリンクと cp は動作する。コピーは 6.6GB で約4分かかる。
- 長時間の重いジョブを走らせる前に「これは CI で代替できるか」を必ず検討する。

---

# Appendix H: superseded subagent-usage policy, 2026-11-16

Old policy (use sparingly) was superseded by the user s 2026-11-14 instruction, and both are
now covered by mem_mwiqd6fb_wi8k4v. Verbatim originals:

## [preference imp3] mem_mvpqk96e_3f6tfw

- created: 2026-10-26T20:55:31.953Z   scope: user

サブエージェントは使用量が早く切れる可能性に注意し、禁止ではないが必要性が高い場合に限って控えめに使用する。

## [preference imp3] mem_mwgdomze_cv388d

- created: 2026-11-14T12:24:48.215Z   scope: user

2026-11-14、ユーザー明示：「無料枠は全く使い切っていないので、引き続き好きにサブエージェントを使い続けて構わない。無料枠を使い切る前にサービス側の不具合で止まる可能性のほうが遥かに高い。そのときは再試行してあげてください」。したがって、サブエージェントが「closing message なしで失敗」した場合は、クォータ切れではなくサービス側の一時障害とみなし、同じタスクを再投入してよい。以前の「使用量が早く切れる可能性に注意し控えめに使う」という記憶はこの指示で上書きされる。手数（並列数）を惜しまず、思いついた観点を大量に投入する方針が正しい。
