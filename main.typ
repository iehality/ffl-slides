#import "@preview/numbly:0.1.0": numbly
#import "@preview/codelst:2.0.0": sourcecode
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "@preview/syntree:0.2.0": tree
#import "@preview/ctheorems:1.1.3": *
#import "@preview/touying:0.5.3": *
#import themes.simple: *

#show: thmrules

#let sqthmbox(name, title, base: "heading") = thmbox(
  name,
  title,
  stroke: (paint: luma(230), thickness: 4pt),
  base: base)

#let barthmbox(name, title) = thmbox(
  name,
  title,
  stroke: (
    left: (thickness: 1pt, paint: luma(230))
  ),
  inset: (left: 12pt, top: 5pt, bottom: 8pt),
  radius: 0pt
)

#let lemma = sqthmbox("lemma", "補題")

#let theorem = sqthmbox("theorem", "定理")

#let theoremq = sqthmbox("theoremq", "定理?")

#let corollary = sqthmbox("corollary", "系", base: "theorem")

#let definition = barthmbox("definition", "定義")

#let remark = barthmbox("remark", "Remark")

#let example = barthmbox("example", "例")

#let proof = thmproof("proof", "Proof")

#let struct(body) = {
  rect(
    width: 100%,
    stroke: (left: (thickness: 1pt, paint: luma(230))),
    inset: (left: 12pt, top: 5pt, bottom: 8pt))[#body]
  }

#let sourcecode = sourcecode.with(frame: none,)

#let brak(..args) = {
  let a = args.pos().join(", ")
  $lr(angle.l #a angle.r)$
  }

#let proves = $tack.r$
#let nproves = $tack.r.not$

#let uprsans(X) = $upright(sans(#X))$

#let PA = $uprsans("PA")$
#let CobhamR0 = $uprsans("R"_0)$
#let Ind(X) = $uprsans("I")#X$

#let Robinson = $uprsans("Q")$

#let qed = $square$

#let sourcecode = sourcecode.with(frame: none)

#show: simple-theme.with(
  aspect-ratio: "16-9",
  footer: [Lean4を用いたGödelの第一/第二不完全性定理の形式化],
  config-colors(
    primary: rgb("#000000"),
    secondary: rgb("#aaaaaa"),
    tertiary: rgb("#dddddd"),
    neutral-lightest: rgb("#ffffff"),
    neutral-darkest: rgb("#000000"),
  ),
)

#set text(size: 18pt, font: "Shippori Mincho B1 OTF", lang: "ja")
#show raw: set text(font: ("JuliaMono", "Noto Sans CJK JP"))
#show math.equation: set text(font: ("New Computer Modern Math", "Shippori Mincho B1 OTF"))
#set heading(numbering: numbly("{1}.", default: "1.1"))

#title-slide[
  #text(size: 50pt, weight: "bold")[
    Lean4を用いたGödelの \ 第一/第二不完全性定理の形式化
  ]

  #v(2em)

  齋藤彰悟

  #text(size: 18pt, font: "Noto Sans CJK JP", lang: "ja")[東北大学大学院理学研究科数学専攻]
]

== FFL

形式論理学の形式化プロジェクト： #link("https://github.com/FormalizedFormalLogic")[`github.com/FormalizedFormalLogic` #box(height:2em, baseline: 40%, image("ffl.png",))]
- 古典命題論理 `LO.Propositional`
- 直観主義命題論理 `LO.IntProp`
- 古典命題様相論理 `LO.Modal`
- *古典一階述語論理 `LO.FirstOrder`*
- 直観主義一階述語論理 `LO.IntFO`


== 不完全性定理

理論 $T$ を計算可能な一階算術の理論とする．
#theorem([不完全性定理])[
  #align(left)[
  / (G1):
    $T$ が基礎的な算術を扱える程度に強く，まともならば， $T$ から証明も反証もできない論理式が存在する．
  / (G2):
    $T$ が十分強く，無矛盾ならば，$T$ の無矛盾性を表す文は証明できない．]
]

/ 1986(!), Shanker: NqthmによるG1の形式化．
/ 2004, O'Connor: CoqによるG1の形式化．
/ 2004, Harrison: HOL Light によるG1の形式化．

#pagebreak()

/ 2021, Paulson:
  Isabelle/HOL によるG1と #underline[G2] の形式化 @paulson2015mechanised．
  算術ではなく遺伝的有限集合の理論 $sans("HF")$ (ペアノ算術 $sans("PA")$ と同等)の上で証明している．
  - 私が知る限り唯一の第二不完全性定理の形式化#footnote[ただし可証性条件を仮定した上でのG2の証明はいくつか存在する．]．

#theorem([Formalized by Paulson])[
  #align(left)[
    / (G1): $sans("HF")$ からは証明も反証もできない論理式が存在する．
    / (G2): 自己の無矛盾性を表す文は $sans("HF")$ からは証明できない．
  ]
]

#pagebreak()

次の不完全性定理の一つのバリエーションを形式化した#footnote[後述するように完全性定理を用いているため非構成的．]：
#theorem[
  #align(left)[
  / (G1):
    $T$ が $sans(upright(R)_0)$ より強く$Sigma_1$-健全ならば， $T$ から証明も反証もできない論理式が存在する．
  / (G2):
    $T$ が $sans(upright("I"))Sigma_1$ より強く無矛盾ならば， $T$ の無矛盾性を表す文は証明できない．]
]
- $Sigma_1$-健全：$T$ から証明可能な $Sigma_1$文は標準モデルの上で真．
- $sans(upright("R"_0))$ : Cobham の最弱の算術．
- $sans(upright("I"))Sigma_1$: ペアノ算術の断片理論．

#pagebreak()

以下の５つのステップを踏んで証明を行う．

  / 1.: 一階述語論理の形式化．
    - 項と論理式，代入操作などの形式化．
    - 証明可能性，充足性の形式化．
  / 2.: 完全性定理．
    - 証明探索
  / 3.: $sans(upright("I"))Sigma_1$ の内部で算術を展開する．
    - 指数関数が定義可能であることを証明する．
    - 有限集合，有限列といった基礎概念をコード化する．
  / 4.: メタ数学の算術化．
    - 項，論理式，証明可能性などをコード化する．
  / 5.: Hilbert-Bernays-Löb の可証性条件

= 一階述語論理の形式化．

== 項・論理式の形式化

論理式（擬論理式）は常に否定標準形を取るように定義する#footnote()[否定 $not$ は論理式の関数として定義する． また $phi -> psi := not phi or psi$ とする．]． すなわち，

$ phi, psi ::= top | bot | R(arrow(v)) | not R(arrow(v)) | phi and psi | phi or psi | forall phi | exists phi $

#text(size: 15pt)[
#sourcecode[```lean
inductive Semiformula (L : Language) (ξ : Type*) : ℕ → Type _ where
  | verum  {n} : Semiformula L ξ n
  | falsum {n} : Semiformula L ξ n
  | rel    {n} : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  | nrel   {n} : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  | and    {n} : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  | or     {n} : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  | all    {n} : Semiformula L ξ (n + 1) → Semiformula L ξ n
  | ex     {n} : Semiformula L ξ (n + 1) → Semiformula L ξ n
```]]

#text(size: 15pt)[
#align(center)[
  #table(
    columns: 2,
    align: center,
    stroke: none,
    [論理式], [糖衣構文],
    [$overline(98) + overline(6748) = overline(6846)$], [`“98 + 6748 = 6846”`],
    [$(forall x)(forall y)[a dot (x + y) = a dot x + a dot y]$], [`“a | ∀ x y, a * (x + y) = a * x + a * y”`],
    [$(forall x)[x < overline(n) <-> or.big_(i < n) x = overline(i)] $], [`“∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”`])
]]

== 証明可能性の形式化

証明体系には Tait計算を採用する．

#align(center)[
  #text(size: 10pt)[
  #table(
    columns: 9,
    align: center + horizon,
    stroke: none,
    inset: 8pt,
    [
      #proof-tree(
        rule(
          name: `axL`,
          $R(arrow(v)), not R(arrow(v)), Delta$,
        )
      )  
    ],
    [
      #proof-tree(
        rule(
          name: `verum`,
          $top, Delta$,
        )
      )  
    ],
    [
      #proof-tree(
        rule(
          name: `or`,
          $phi or psi, Delta$,
          $phi, psi, Delta$
        )
      )  
    ],
    [
      #proof-tree(
        rule(
          name: `and`,
          $phi and psi, Delta$,
          $phi, Delta$,
          $psi, Delta$,
        )
      )  
    ],
    [
      #proof-tree(
        rule(
          name: [`all`#footnote[
            ここでは自由変数を $\&0, \&1, ...$ と表記する．また $phi^+, Gamma^+$ はそれぞれに含まれる自由変数をインクリメントしたもの]],
          $forall phi, Delta$,
          $phi^+(\&0), Delta^+$,
        )
      )
    ],
    [
      #proof-tree(
        rule(
          name: `ex`,
          $exists phi, Delta$,
          $phi(t), Delta$,
        )
      )  
    ],
    [
      #proof-tree(
        rule(
          name: `wk`,
          $Gamma$,
          $Delta$,
        )
      )
      (if $Delta subset.eq Gamma$)
    ],
    [
      #proof-tree(
        rule(
          name: `cut`,
          $Delta$,
          $phi, Delta$,
          $not phi, Delta$,
        )
      )  
    ],
    [
      #proof-tree(
        rule(
          name: `root`,
          $phi$,
        )
      )
      (if $phi in T$)
    ],
  )]
]

#text(size: 13pt)[
  #sourcecode[```lean
  inductive Derivation (T : Theory L) : Sequent L → Type _
    | axL (Δ) {k} (r : L.Rel k) (v) : Derivation T (rel r v :: nrel r v :: Δ)
    | verum (Δ)    : Derivation T (⊤ :: Δ)
    | or {Δ p q}   : Derivation T (p :: q :: Δ) → Derivation T (p ⋎ q :: Δ)
    | and {Δ p q}  : Derivation T (p :: Δ) → Derivation T (q :: Δ) → Derivation T (p ⋏ q :: Δ)
    | all {Δ p}    : Derivation T (Rew.free.hom p :: Δ⁺) → Derivation T ((∀' p) :: Δ)
    | ex {Δ p} (t) : Derivation T (p/[t] :: Δ) → Derivation T ((∃' p) :: Δ)
    | wk {Δ Γ}     : Derivation T Δ → Δ ⊆ Γ → Derivation T Γ
    | cut {Δ p}    : Derivation T (p :: Δ) → Derivation T (∼p :: Δ) → Derivation T Δ
    | root {p}     : p ∈ T → Derivation T [p]
  ```]]

Tait計算は推論規則が少ないため扱いやすく，LKなどの他の推論規則に比べ様々な証明が簡易になる（こともある）．

= 完全性定理

== 完全性定理

#theorem([完全性定理])[
  すべての 論理式 $phi$ について，
  $ T proves phi <==> T tack.r.double phi $
]

$==>$ 方向（健全性定理）は証明に関する帰納法により従う．$<==$ を示すには以下を証明すれば良い．

#lemma[推件 $Gamma$ について， 次のいずれかが成立する．
  - $T attach(proves, br: sans(upright("T"))) Gamma$
  - すべての $phi in Gamma$ を充足しないような $T$ のモデルが存在する．
]

== 証明探索
#slide[
  証明はTait計算の証明探索による(参考: @pohlers2008proof)．
#text(size: 5pt)[
  #tree([$(exists x)[(x <= a and x eq.not a) or (forall y)[a <= y]]$],
    tree([$(exists x)[(x <= a and x eq.not a) or (forall y)[a <= y]], (b <= a and b eq.not a) or (forall y)[a <= y]$],
      tree([$(exists x)[(x <= a and x eq.not a) or (forall y)[a <= y]], b <= a and b eq.not a, (forall y)[a <= y]$],
        tree([$(exists x)[(x <= a and x eq.not a) or (forall y)[a <= y]], b <= a and b eq.not a, a <= c$],
          tree([$(exists x)[(x <= a and x eq.not a) or (forall y)[a <= y]], b <= a and b eq.not a, a <= c, b <= a$],
            [$dots.v$]),
          tree([$(exists x)[(x <= a and x eq.not a) or (forall y)[a <= y]], b <= a and b eq.not a, a <= c, b eq.not a$],
            tree([$(exists x)[(x <= a and x eq.not a) or (forall y)[a <= y]],
              b <= a and b eq.not a, a <= c, b eq.not a, (c <= a and c eq.not a) or (forall y)[a <= y]$],
              tree([$(exists x)[(x <= a and x eq.not a) or (forall y)[a <= y]],
                b <= a and b eq.not a, a <= c, b eq.not a, c <= a and c eq.not a, (forall y)[a <= y]$],
                $dots.v$,
  )))))))]
  #text(size: 6pt)[#sourcecode[```lean
    inductive Redux (T : Theory L) : Code L → Sequent L → Sequent L → Prop
      | axLRefl   {Γ : Sequent L} {k} (r : L.Rel k) (v) :
        Semiformula.rel r v ∉ Γ ∨ Semiformula.nrel r v ∉ Γ → Redux T (Code.axL r v) Γ Γ
      | verumRefl {Γ : Sequent L} : ⊤ ∉ Γ → Redux T Code.verum Γ Γ
      | and₁      {Γ : Sequent L} {p q : SyntacticFormula L} : p ⋏ q ∈ Γ → Redux T (Code.and p q) (p :: Γ) Γ
      | and₂      {Γ : Sequent L} {p q : SyntacticFormula L} : p ⋏ q ∈ Γ → Redux T (Code.and p q) (q :: Γ) Γ
      | andRefl   {Γ : Sequent L} {p q : SyntacticFormula L} : p ⋏ q ∉ Γ → Redux T (Code.and p q) Γ Γ
      | or        {Γ : Sequent L} {p q : SyntacticFormula L} : p ⋎ q ∈ Γ → Redux T (Code.or p q) (p :: q :: Γ) Γ
      | orRefl    {Γ : Sequent L} {p q : SyntacticFormula L} : p ⋎ q ∉ Γ → Redux T (Code.or p q) Γ Γ
      | all       {Γ : Sequent L} {p : SyntacticSemiformula L 1} : ∀' p ∈ Γ → Redux T (Code.all p) (p/[&(newVar Γ)] :: Γ) Γ
      | allRefl   {Γ : Sequent L} {p : SyntacticSemiformula L 1} : ∀' p ∉ Γ → Redux T (Code.all p) Γ Γ
      | ex        {Γ : Sequent L} {p : SyntacticSemiformula L 1} {t : SyntacticTerm L} :
        ∃' p ∈ Γ → Redux T (Code.ex p t) (p/[t] :: Γ) Γ
      | exRefl    {Γ : Sequent L} {p : SyntacticSemiformula L 1} {t : SyntacticTerm L} :
        ∃' p ∉ Γ → Redux T (Code.ex p t) Γ Γ
      | id        {Γ : Sequent L} {p : SyntacticFormula L} (hp : p ∈ T) : Redux T (Code.id p) ((∼∀∀p) :: Γ) Γ
      | idRefl    {Γ : Sequent L} {p : SyntacticFormula L} (hp : p ∉ T) : Redux T (Code.id p) Γ Γ
  
    local notation:25 Δ₁" ≺[" c:25 "] " Δ₂:80 => Redux T c Δ₁ Δ₂
  
    inductive ReduxNat (T : Theory L) (s : ℕ) : Sequent L → Sequent L → Prop
      | redux {c : Code L} : decode s.unpair.1 = some c → ∀ {Δ₂ Δ₁}, Redux T c Δ₂ Δ₁ → ReduxNat T s Δ₂ Δ₁
      | refl : decode (α := Code L) s.unpair.1 = none → ∀ Δ, ReduxNat T s Δ Δ
    
    local notation:25 Δ₁" ≺⟨" s:25 "⟩ " Δ₂:80 => ReduxNat T s Δ₁ Δ₂
    ```]]
][
  #text(size: 14pt)[  
    探索木が well-founded ならば証明可能．
    #sourcecode[```lean
      noncomputable def syntacticMainLemma
          (wf : WellFounded (SearchTree.Lt T Γ))
          (p : SearchTree T Γ) :
          T ⟹ p.seq
    ```]
    
    探索木が well-founded でないならば `Γ` の反例モデル `Model T Γ` が構成できる．
  
    #sourcecode[```lean
      lemma Model.models : Model T Γ ⊧ₘ* T 
      
      lemma semanticMainLemmaTop
          (nwf : ¬WellFounded (SearchTree.Lt T Γ))
          {φ : SyntacticFormula L}
          (h : φ ∈ Γ) :
          ¬Evalf (Model.structure T Γ) Semiterm.fvar φ
    ```]
  ]
]



#let ISigma(i) = $sans(upright("I"))Sigma_(#i)$

= $ISigma(1)$の内部で算術を展開する

== 算術の公理系を定義する

#table(
    columns: 2,
    align: horizon,
    stroke: none,
    inset: 8pt,

    [$sans("PA"^-)$],
    [
      #sourcecode[```lean
        inductive PeanoMinus : Theory ℒₒᵣ
          | equal         : ∀ φ ∈ 𝐄𝐐, PeanoMinus φ
          | addZero       : PeanoMinus “x | x + 0 = x”
          | addAssoc      : PeanoMinus “x y z | (x + y) + z = x + (y + z)”
          | addComm       : PeanoMinus “x y | x + y = y + x”
          | addEqOfLt     : PeanoMinus “x y | x < y → ∃ z, x + z = y”
          | zeroLe        : PeanoMinus “x | 0 ≤ x”
          | zeroLtOne     : PeanoMinus “0 < 1”
          | oneLeOfZeroLt : PeanoMinus “x | 0 < x → 1 ≤ x”
          | addLtAdd      : PeanoMinus “x y z | x < y → x + z < y + z”
          | mulZero       : PeanoMinus “x | x * 0 = 0”
          | mulOne        : PeanoMinus “x | x * 1 = x”
          | mulAssoc      : PeanoMinus “x y z | (x * y) * z = x * (y * z)”
          | mulComm       : PeanoMinus “x y | x * y = y * x”
          | mulLtMul      : PeanoMinus “x y z | x < y ∧ 0 < z → x * z < y * z”
          | distr         : PeanoMinus “x y z | x * (y + z) = x * y + x * z”
          | ltIrrefl      : PeanoMinus “x | x ≮ x”
          | ltTrans       : PeanoMinus “x y z | x < y ∧ y < z → x < z”
          | ltTri         : PeanoMinus “x y | x < y ∨ x = y ∨ x > y”
      ```]
    ],
)

#pagebreak()

#table(
    columns: 2,
    align: horizon,
    stroke: none,
    inset: 12pt,

    [$sans(upright(I)) phi$],
    [
      #sourcecode[```lean
        def succInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ :=
          “!φ 0 → (∀ x, !φ x → !φ (x + 1)) → ∀ x, !φ x”
      ```]
    ],
    [$sans(upright("I"))Sigma_k$],
    [
      #sourcecode[```lean
        def indScheme (Γ : Semiformula L ℕ 1 → Prop) : Theory L :=
          { q | ∃ p : Semiformula L ℕ 1, Γ p ∧ q = succInd p }
      
        abbrev indH (Γ : Polarity) (k : ℕ) : Theory ℒₒᵣ :=
          𝐏𝐀⁻ + indScheme ℒₒᵣ (Arith.Hierarchy Γ k)
        
        abbrev iSigma (k : ℕ) : Theory ℒₒᵣ := 𝐈𝐍𝐃 𝚺 k
      ```]],
    [$sans("PA")$],
    [
      #sourcecode[```lean
        abbrev peano : Theory ℒₒᵣ := 𝐏𝐀⁻ + indScheme ℒₒᵣ Set.univ
      ```]
    ],
    [$sans(upright("R")_0)$],
    [
      #sourcecode[```lean
        inductive CobhamR0 : Theory ℒₒᵣ
          | equal        : ∀ φ ∈ 𝐄𝐐, CobhamR0 φ
          | Ω₁ (n m : ℕ) : CobhamR0 “↑n + ↑m = ↑(n + m)”
          | Ω₂ (n m : ℕ) : CobhamR0 “↑n * ↑m = ↑(n * m)”
          | Ω₃ (n m : ℕ) : n ≠ m → CobhamR0 “↑n ≠ ↑m”
          | Ω₄ (n : ℕ)   : CobhamR0 “∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”
      ```]],
)

== （形式的）証明のルーチン
何らかの算術の体系 $T$ からある論理式を証明できること を証明したい．

$ sans("Lean") proves quote.l T proves phi quote.r $

しかし，そもそもLeanが形式化された数学であり，その内部でさらに形式化された証明を証明するのはかなり煩雑になる
（さらに後には「形式化された形式化された形式化された証明」のようなものさえ扱うことになる）．

これは大変なので， 完全性定理を用いて代わりに意味論帰結を証明する．

$ sans("Lean") proves quote.l T models phi quote.r $

意味論的な議論では，Leanのライブラリに用意された代数学の種々の補題やメタプログラミングや自動証明が利用できるため，より簡単に作業を行うことができる．

#pagebreak()

まず理論の任意のモデル `V` を固定する．

#sourcecode[```lean
  variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈open]
```]

- *`ORingStruc V`:* `V` が言語 $cal(L)_"OR"$ の構造であることを主張するtypeclass.
- *`V ⊧ₘ* 𝐈open`:* `V` が理論 `𝐈open` を満たすことを主張するtypeclass.

この仮定のもとで証明を行う． 関数を追加したいならば選択関数を用いる．

#sourcecode[```lean
  lemma sqrt_exists_unique (a : V) :
      ∃! x, x * x ≤ a ∧ a < (x + 1) * (x + 1) := by ...
  
  def sqrt (a : V) : V := Classical.choose! (sqrt_exists_unique a)

  prefix:75 "√" => sqrt

  @[simp] lemma sqrt_mul_self (a : V) : √(a * a) = a := by ...
```]

ただし，帰納法を適用するために，定義した関数や関係を含む述語がある算術的階層に含まれることが示せなければならない．

== `definability` tactic

`definability` tactic はLeanの述語がある算術的階層に含まれることを（可能なら）自動証明する.

#let data = (
  [$Sigma_1$`-Predicate (fun k ↦ k ≤ l → ∃ v, ∀ i < k, R (l - k + i) v.[i])`],
  ([$Pi_1$`-Predicate (fun k ↦ k ≤ l)`]),
  
  ([$Sigma_1$`-Predicate (fun k ↦ ∃ v, ∀ i < k, R (l - k + i) v.[i])`], [F])
)

#text(size: 14pt)[
  #tree([$Sigma_1$`-Predicate (fun v ↦ ∀ i < len v, v.[i] ≤ listMax v)`],
  tree([$Sigma_1$`-Function len`], [$checkmark$]),
  tree([$Sigma_1$`-Relation (fun i v ↦ v.[i] ≤ listMax v)`],
    tree([$Sigma_1$`-Relation (fun x y ↦ x ≤ y)`], [$checkmark$]),
    tree([$Sigma_1$`-Function₂ (fun i v ↦ v.[i])`], [$checkmark$]),
    tree([$Sigma_1$`-Function₂ (fun i v ↦ listMax v)`], [$checkmark$]),))]

typeclassに登録された関数や関係は自動証明の末尾を示すために使用される．

#sourcecode[```lean
instance exp_definable : 𝚺₀-Function₁ (Exp.exp : V → V) := by ...

instance length_definable : 𝚺₀-Function₁ (‖·‖ : V → V) := by ...

instance dvd_definable : 𝚺₀-Relation (fun a b : V ↦ a ∣ b) := by ...

instance Language.isSemiterm_definable : 𝚫₁-Relation L.IsSemiterm := by ...
```]

== 指数関数
指数関数のグラフ $"Exp"(x, y) <=> 2^x = y$ は $Sigma_0$ 論理式で定義可能 @hajek2017metamathematics @cook2010logical．
#align(center)[#image("expp.png", width: 90%)]

== 遺伝的有限集合

「$x$ は $y$ の要素」 $<==>$ 「$y$ を二進数展開したとき $x$ 桁目が $1$」 と定義する．

$ x in y <==> "Bit"(x, y) <==> floor(y \/ 2^x) mod 2 = 1 $

Ackermann coding によって遺伝的有限集合 $V_omega$ が扱える．
$ISigma(1)$ のもとで基礎的な集合論が展開できる．

#sourcecode[```lean
  theorem finset_comprehension₁ {Γ} {P : V → Prop} (hP : Γ-[1]-Predicate P) (a : V) :
      ∃ s < exp a, ∀ i < a, i ∈ s ↔ P i -- (制限された)内包公理図式

  theorem sUnion_exists_unique (s : V) :
      ∃! u, ∀ x, (x ∈ u ↔ ∃ t ∈ s, x ∈ t) -- 和集合公理

  theorem sigma₁_replacement {f : V → V} (hf : 𝚺₁-Function₁ f) (s : V) :
      ∃! t, ∀ y, (y ∈ t ↔ ∃ x ∈ s, y = f x) -- (制限された)置換公理図式
```]

また有限の関数/有限列も扱える．

#sourcecode[```lean
  def IsMapping (m : V) : Prop := ∀ x ∈ domain m, ∃! y, ⟪x, y⟫ ∈ m

  def Seq (s : V) : Prop := IsMapping s ∧ ∃ l, domain s = under l
```]

== 原始再帰

$ISigma(1)$では原始再帰法を用いて関数を定義できる．
#text(size: 14pt)[
#theorem[
  $f(arrow(v)), g(arrow(v), x, z)$ を $Sigma_1$ 定義可能な関数とする．
  このとき，以下を満たす $Sigma_1$定義可能関数 $"PRec"_(f, g)(arrow(v), x)$ が存在する．
  $
  "PRec"_(f, g)(arrow(v), 0) &= f(arrow(v)) \
  "PRec"_(f, g)(arrow(v), x + 1) &= g(arrow(v), x, "PRec"_(f, g)(arrow(v), x)) \
  $
]]

#align(center)[#text(size: 9pt)[#sourcecode[```lean
structure Blueprint (k : ℕ) where
  zero : 𝚺₁-Semisentence (k + 1)
  succ : 𝚺₁-Semisentence (k + 3)

structure Construction {k : ℕ} (φ : Blueprint k) where
  zero : (Fin k → V) → V
  succ : (Fin k → V) → V → V → V
  zero_defined : DefinedFunction zero p.zero
  succ_defined : DefinedFunction (fun v ↦ succ (v ·.succ.succ) (v 1) (v 0)) p.succ

...

variable {k : ℕ} {φ : Blueprint k} (c : Construction V φ) (v : Fin k → V)

def Construction.result (u : V) : V

theorem Construction.result_zero :
    c.result v 0 = c.zero v

theorem Construction.result_succ (u : V) :
    c.result v (u + 1) = c.succ v u (c.result v u)
```]]]

== 再帰的定義
#theorem[
  $Phi_bold(C)(arrow(v), x)$ を*クラス* $bold(C)$ をパラメータとして取る述語だとする．
  $Phi$ が以下を満たすならば，

  1. 述語 $P (c, arrow(v), x) := Phi_{z | z in c} (arrow(v), x)$ は $Delta_1$ 定義可能．
  2. 単調： $bold(C) subset.eq bold(C')$ ならば， $Phi_bold(C)(arrow(v), x) ==> Phi_bold(C')(arrow(v), x)$
  3. 有限： $Phi_bold(C)(arrow(v), x)$ ならば，ある $m$ が存在して $Phi_({z in bold(C) | z < m})(arrow(v), x)$
  
  次を満たす $Sigma_1$ 定義可能な述語 $"Fix"_Phi (arrow(v), x)$ が存在する．
  $ "Fix"_Phi (arrow(v), x) <==> Phi_({x | "Fix"_Phi (arrow(v), x)}) (arrow(v), x) $

  さらに次を満たすならば，$"Fix"_Phi (arrow(v), x)$ は $Delta_1$ 定義可能でその構造帰納法が証明できる．

  4. 強有限： $Phi_bold(C) (arrow(v), x) ==> Phi_{y in bold(C) | y < x} (arrow(v), x)$
  ]

$"Fix"_Phi$ を用いることで帰納的に定義されたクラス（リスト，形式化された項，形式化された論理式，形式化された証明, ...）を定義できる．

#text(size: 16pt)[#sourcecode[```lean
structure Blueprint (k : ℕ) where
  core : 𝚫₁-Semisentence (k + 2)

structure Construction (φ : Blueprint k) where
  Φ : (Fin k → V) → Set V → V → Prop
  defined : Arith.Defined (fun v ↦ Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0)) φ.core
  monotone {C C' : Set V} (h : C ⊆ C') {v x} : Φ v C x → Φ v C' x

class Construction.Finite (c : Construction V φ) where
  finite {C : Set V} {v x} : c.Φ v C x → ∃ m, c.Φ v {y ∈ C | y < m} x

class Construction.StrongFinite (c : Construction V φ) where
  strong_finite {C : Set V} {v x} : c.Φ v C x → c.Φ v {y ∈ C | y < x} x
...

variable {k : ℕ} {φ : Blueprint k} (c : Construction V φ) [Finite c] (v : Fin k → V)

def Construction.Fixpoint (x : V) : Prop

theorem Construction.case :
    c.Fixpoint v x ↔ c.Φ v {z | c.Fixpoint v z} x

theorem induction [c.StrongFinite] {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (H : ∀ C : Set V, (∀ x ∈ C, c.Fixpoint v x ∧ P x) → ∀ x, c.Φ v C x → P x) :
    ∀ x, c.Fixpoint v x → P x
```]]

= メタ数学の算術化

== 項のコーディング

$Delta_1$述語 $T_bold(C)$ を以下のように定める．
#text(size: 15pt)[
  $ 
    u in T_bold(C) <==>
    &(exists z)[u = hat(\#z)] or (exists x)[u = hat(\&x)] or \
    &(exists k, f, v)["Func"(k, f) and "len"(v) = k and (forall i < k)["nth"(v, i) in bold(C)]and u = hat(f^k (v))]
  $
  
  $
    "bounded variable: "&& hat(\#z) &:= brak(0, z) + 1 \
    "free variable: " && hat(\&z)    &:= brak(1, z) + 1 \
    "function: "&& hat(f^k (v))     &:= brak(2, f, k, v) + 1
  $
]

`L` を形式化された言語だとする． fixpoint construction により $T_bold(C)$ の不動点 `L.IsUTerm : V → Prop` が得られる． 
また， その構造帰納法から束縛変数の最大値$+1$ を返す $Sigma_1$関数 `L.termBV : V → V` が定義でき，
`t ∈ V` がコード化された（`n`個の束縛変数を持つ）擬項であることを表す $Delta_1$述語 `L.IsSemiterm n t : Prop` が定義される． 

#sourcecode[```lean
  def Language.IsSemiterm (n t : V) : Prop := L.IsUTerm t ∧ L.termBV t ≤ n
```]

== 論理式のコーディング

$Delta_1$述語 $F_bold(C)$ を以下のように定める．
#text(size: 15pt)[
$
  u in F_bold(C) <==>
    &(exists k, R, v)["Rel"(k, R) and u "is a list of UTerm of length" k and u = hat(R^k (v))] or \
    &(exists k, R, v)["Rel"(k, R) and u "is a list of UTerm of length" k and u = hat(not R^k (v))] or \
    &u = hat(top) or u = hat(bot) or \
    &(exists p, q in bold(C))[u = hat(p and q)] or (exists p, q in bold(C))[u = hat(p or q)] or \
    &(exists p in bold(C))[u = hat(forall p)] or (exists p in bold(C))[u = hat(exists p)]
$

#align(center)[#text(size: 16pt)[#table(
    columns: 4,
    align: center + horizon,
    stroke: none,
    inset: 12pt,
    [$ hat(R^k (v)) &:= brak(0, R, k, v) + 1 \
       hat(not R^k (v)) &:= brak(1, R, k, v) + 1 $],
    [$ hat(top) &:= brak(2, 0) + 1 \
       hat(bot) &:= brak(3, 0) + 1 $],
    [$ hat(p and q) &:= brak(4, p, q) + 1 \
       hat(p or q) &:= brak(5, p, q) + 1 $],
    [$ hat(forall p) &:= brak(6, p) + 1 \
       hat(exists p) &:= brak(7, p) + 1 $]    
)]]
]

擬項のときと同様にして形式化された擬論理式を指す $Delta_1$述語 `IsSemiformula n p : Prop` が定義される．

== Tait計算のコーディング

$T$ を $Delta_1$ 定義可能な理論とする． $Delta_1$述語 $ D^T_bold(C)$ を以下のように定める．

#text(size: 15pt)[
  $
    d in D^T_bold(C) <==> &(forall p in "sqt"(d))["Semiformula"(0, p)] and \
    [
      &(exists s, p)[d = "AXL"(s, p) and p in s and hat(not)p in s] \
      &(exists s)[d = top"-INTRO"(s) and hat(top) in s] or \
      &(exists s, p, q)(exists d_p, d_q in bold(C))[
        d = and"-INTRO"(s, p, q, d_p, d_q) and hat(p and q) in s and "sqt"(d_p) = s union {p} and "sqt"(d_q) = s union {q}] or \
      &(exists s, p, q)(exists d in bold(C))[
        d = or"-INTRO"(s,p,q,d) and hat(p or q) in s and "sqt"(d) = s union {p, q}] or \
      &(exists s, p)(exists d in bold(C))[
        d = forall"-INTRO"(s, p, d) and hat(forall p) in s and "sqt"(d) = s^+ union {p^+(hat(\&0))}] or \
      &(exists s, p, t)(exists d in bold(C))[
        d = exists"-INTRO"(s, p, t, d) and hat(exists p) in s and "sqt"(d) = s union {p(t)}] or \
      &(exists s)(exists d' in bold(C))[d = "WK"(s, d') and s supset.eq "sqt"(d')] or \
      &(exists s)(exists d' in bold(C))[d = "SHIFT"(s, d') and s = "sqt"(d')^+] or \
      &(exists s, p)(exists d_1, d_2 in bold(C))[d = "CUT"(s, p, d_1, d_2) and "sqt"(d_1) = s union {p} and "sqt"(d_2) = s union {hat(not) p}] or \
      &(exists s, p)[d = "ROOT"(s, p) and p in s and p in T]]
  $
]

#align(center)[#text(size: 15pt)[#table(
    columns: 3,
    align: center + horizon,
    stroke: none,
    inset: 12pt,
    [$  "sqt"(d) &:= pi_1(d - 1) \
        "AXL"(s, p) &:= brak(s, 0, p) + 1 $],
    [$ top"-INTRO"(s) &:= brak(s, 1, 0) + 1 \
       and"-INTRO"(s, p, q, d_p, d_q) &:= brak(s, 2, p, q, d_p, d_q) + 1 \
       or"-INTRO"(s, p, q, d) &:= brak(s, 3, p, q, d) + 1 \
       forall"-INTRO"(s, p, d) &:= brak(s, 4, p, d) + 1 \
       exists"-INTRO"(s, p, t, d) &:= brak(s, 5, p, t, d) + 1$],
    [$ "WK"(s, d) &:= brak(s, 6, d) + 1 \
       "SHIFT"(s, d) &:= brak(s, 7, d) + 1 \
       "CUT"(s, p, d_1, d_2) &:= brak(s, 8, p, d_1 d_2) + 1 \
       "ROOT"(s, p) &:= brak(s, 9, p) + 1 $], 
)]]

$D^T_bold(C)$ の不動点を取って `T.Derivation` とする．以下のように定める．

#text(size: 18pt)[#sourcecode[```lean
  def Language.Theory.Derivable (T) (s : V) : Prop := ∃ d, T.DerivationOf d s

  def Language.Theory.Provable (T) (p : V) : Prop := T.Derivable {p}
```]]

定義より `T.Derivable` や `T.Provable` は $Sigma_1$.

== Gödel数化

（メタ論理の）項/論理式から（ $V$ の内部の）形式化された項/論理式への翻訳 $t |-> ceil(t)$, $phi |-> ceil(phi) $ をコーディング通りに定義する．

#text(size: 14pt)[#sourcecode[```lean
  #eval Encodable.encode (“⊤” : Sentence ℒₒᵣ)
    /- 7 -/
  
  #eval Encodable.encode (“1 + 1 = 2” : Sentence ℒₒᵣ)
    /- 2811283025421999017712752184705287682765933652183125347889924839244702557909257480149303662
       0226056829379396867558990018685021300411793862047857546098162625163543635122202320614830504
       5032994237166744576048470977246790815309324291777191455007248230247852452218972967918789604
       6549123727569857552482425621934531125928101852294893549785680809310809523176634584145844302
       5403080631492029306853223861326740190114231247862748245410665797364948572233034830050682843
       0586068980626109306946946510933159275481055524034583309159054488191374946941436375286182247
       2934435856999319941455469415760760469554147547207581743524630022634897251631217278137049000
       0720142817763639758008432269310312579231167553225000584223488849283104065326226084742908739
       1926282639848319450229266995417413133859040482530307149746254214536136234612283878168584544
       0140202739452286492522894832319502650575282054270818964898878686030069994727438159066748780
       6793436703922580916715270838972818987012192890409519287109955207836968510432355251110156455
       5848127363401105585258109417133714744133195894888409659553672360357137318621009961116974146
       9010059357928982517174650081907896565063353817595634565097605705845515007215881579535384687
       7165987904543322149860791463967564337677539451591793909705364343215133849384526734310253600
       618529011635630072568447447378714105148191145285 -/
```]]

= Hilbert-Bernays-Löb の可証性条件 <hbl>


== 可証性条件

#lemma[
  #align(left)[
    $T$ を $ISigma(1)$より強い理論， $U$ を $sans(upright("R")_0)$ より強い $Delta_1$定義可能な理論だとする． このとき，
    / D1: $U proves sigma ==> T proves "Provable"_U (ceil(sigma))$
    / D2: $T proves "Provable"_U (ceil(sigma -> tau)) -> "Provable"_U (ceil(sigma)) -> "Provable"_U (ceil(tau))$
    / D3: $T proves "Provable"_U (ceil(sigma)) -> "Provable"_U (ceil("Provable"_U (ceil(sigma))))$
    $NN models T$ ならば
    #footnote[
      実際には $Sigma_1$ 健全性で十分．
    ]
    更に次が成り立つ．
    / D1': $U proves sigma <==> T proves "Provable"_U (ceil(sigma))$
  ]
]

#pagebreak()

D1 及び D2, D1' は形式化された証明の性質を地道に証明すれば示せる．

#sourcecode[```lean
  theorem provableₐ_D1
      [𝐈𝚺₁ ≼ T] [U.Delta1Definable] {σ : SyntacticFormula L} :
      U ⊢! σ → T ⊢! U.bewₐ σ 

  theorem provableₐ_D2
      [𝐈𝚺₁ ≼ T] [U.Delta1Definable] {σ π : SyntacticFormula L} :
      T ⊢! U.bewₐ (σ ➝ π) ➝ U.bewₐ σ ➝ U.bewₐ π

  theorem provableₐ_complete
      [𝐈𝚺₁ ≼ T] [ℕ ⊧ₘ* T] [𝐑₀ ≼ U] {σ : LO.FirstOrder.Sentence ℒₒᵣ} :
      U ⊢! σ ↔ T ⊢! U.bewₐ σ
```]
#footnote[
  `T ⊢ φ` は`φ`の理論`T`-証明の型，`T ⊢! φ`はそのような証明が存在することを表す命題．
]
#footnote[
  `T.Provable p` は `p ∈ V` に関するモデル上の形式化された証明可能性を表す．
  一方`T.bewₐ σ` は`T.Provable ⌜σ⌝`を定義する論理式を指す．
]

== 形式化された $Sigma_1$-完全性

D3 は直接示すのは難しいが，次の補題より従う．

#lemma([形式化された $Sigma_1$-完全性])[
  $T$ を $ISigma(1)$より強い理論， $U$ を $sans(upright("R")_0)$ より強い $Delta_1$定義可能な理論だとする． 
  文 $sigma$ が $Sigma_1$論理式ならば，次が証明可能．
  $ T proves sigma -> "Provable"_U (ceil(sigma)) $
]

#text(size: 16pt)[
/ 証明:
  $T$ のモデル $V$ の内部で作業する．

  次を示せばよい：
  すべての $Sigma_1$論理式 $phi(x_1, ..., x_k)$, $a_1, ..., a_k in V$ について，
  $V models phi[a_1, ..., a_k] ==> "Provable"_U (ceil(phi)(overline(a_1), ..., overline(a_k)))$
  これは $phi$ に関する帰納法で示せる．#qed
]

#sourcecode[```lean
  theorem provableₐ_sigma₁_complete
      {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
      T ⊢! σ ➝ U.bewₐ σ
```]


= 不完全性定理

== 第一不完全性定理

G1 は 1, 2, 3, 4 までの結果で証明できる．
#theorem([G1])[
  $T$ が $Delta_1$ 定義可能で $sans(upright(R)_0)$ より強く $Sigma_1$-健全ならば， $T$ から証明も反証もできない論理式が存在する．
]
#text(size: 15pt)[
/ 証明:
  $D := {ceil(phi) | phi: "1変数の論理式", T proves not phi(ceil(phi)) }$ と定義する．
  $T proves pi <=> NN models "Provable"_T (ceil(pi))$, また $"Provable"_T$ は $Sigma_1$定義可能なので， $D$ は r.e.集合.

  表現定理より次を満たす $theta$ が存在する: すべての $n in NN$ について $n in D <==> T proves theta(overline(n)) $．

  $n = ceil(theta)$ と置くと，
  $ T proves theta(ceil(theta)) <==> ceil(theta) in D <==> T proves not theta(ceil(theta)) $
  よって $T$ が完全だと仮定すると矛盾する． #qed
]
#pagebreak()

#text(size: 12pt)[#sourcecode[```lean  
theorem goedel_first_incompleteness : ¬System.Complete T := by
  let D : ℕ → Prop := fun n : ℕ ↦ ∃ p : SyntacticSemiformula ℒₒᵣ 1, n = ⌜p⌝ ∧ T ⊢! ∼p/[⌜p⌝]
  -- D の定義
  have D_re : RePred D := by ...
  -- D は r.e.
  let θ : SyntacticSemiformula ℒₒᵣ 1 := codeOfRePred (D)
  have : ∀ n : ℕ, D n ↔ T ⊢! θ/[‘↑n’] := fun n ↦ by
    simpa [Semiformula.coe_substs_eq_substs_coe₁] using re_complete (T := T) (D_re) (x := n)
  -- D を表現する論理式 θ を取る
  let ρ : SyntacticFormula ℒₒᵣ := θ/[⌜θ⌝]
  -- ρ := θ(⌜θ⌝)
  have : T ⊢! ∼ρ ↔ T ⊢! ρ := by
    simpa [D, goedelNumber'_def, quote_eq_encode] using this ⌜θ⌝
  -- T ⊢ ¬ρ ↔ T ⊢ ρ
  have con : System.Consistent T := consistent_of_sigma1Sound T
  -- T は無矛盾
  refine LO.System.incomplete_iff_exists_undecidable.mpr ⟨↑ρ, ?_, ?_⟩
  -- ρ が T から独立であることを示す
  · intro h
    have : T ⊢! ∼↑ρ := by simpa [provable₀_iff] using this.mpr h
    exact LO.System.not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable h this) inferInstance
    -- T ⊢ ¬ρ ならば矛盾．
  · intro h
    have : T ⊢! ↑ρ := this.mp (by simpa [provable₀_iff] using h)
    exact LO.System.not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable this h) inferInstance
    -- T ⊢ ρ ならば矛盾．
```]]

== 第二不完全性定理

#lemma([不動点補題])[
  1変数の論理式 $theta$ について，次を満たす 文 $"fixpoint"_theta$ が存在する．
  $ ISigma(1) proves "fixpoint"_theta <-> theta(ceil("fixpoint"_theta)) $
]
#text(size: 12pt)[
/ 証明:
  形式化された論理式に数項を代入する関数のグラフ $"substNumeral"(y, p, x)$ は $Sigma_1$ 定義可能．
  $ ISigma(1) proves "substNumeral"(y, p, x) <-> y = p(overline(x)) $
  $"fixpoint"_theta$ を次のように定義する．
  $ "diag"_theta (x) &:= (forall y)["substNumeral"(y, x, x) -> theta(y)] \
    "fixpoint"_theta &:= "diag"_theta (ceil("diag"_theta)) $
  このとき，$ISigma(1)$ に於いて，

  $ "fixpoint"_theta &eq.def (forall y)["substNumeral"(y, ceil("diag"_theta), ceil("diag"_theta)) -> theta(y)] \
    &<-> theta (ceil("diag"_theta (ceil("diag"_theta)))) \
    &eq.def theta(ceil("fixpoint"_theta)) $
  #qed
]

#pagebreak()

#let goedelSentence = $upright("G")$

Gödel文  「この文は証明できない」を定義する．
$goedelSentence_T &:= "fixpoint"_(not "Provable"_T)$

以降 $T$ を $ISigma(1)$ より強い理論とする．
#lemma[
  1. $T$ が無矛盾ならば $T tack.r.not goedelSentence_T$，
  2. $NN models T$ ならば $T tack.not not goedelSentence_T.$ ]<g-independent>

#text(size: 16pt)[
/ 証明:
  1. $T proves goedelSentence_T$ と仮定する.
    不動点補題より $T proves not "Provable"_T (ceil(goedelSentence_T))$を得る．
    一方 D1より $T proves "Provable"_T (ceil(goedelSentence_T))$ なので $T$ は矛盾する．これは仮定に反する．
  2. $T proves not goedelSentence_T$ と仮定する．
    不動点補題より $T proves "Provable"_T (ceil(goedelSentence_T))$ を得る．
    D1' より $T proves goedelSentence_T$ なので $T$ は矛盾する．これは仮定に反する．
]

#pagebreak()

$T$ の無矛盾性を表す文を定義する．
$"Con"_T := not"Provable"_T (ceil(bot)) $

#lemma[ $T proves "Con"_T <-> goedelSentence_T $ ]<con-equiv-g>
#text(size: 14pt)[
/ 証明: 
  / $(->)$:
    $not goedelSentence_T -> "Provable"_T (ceil(bot))$ を示せばよい．
    $not goedelSentence_T$ を仮定する．不動点補題より$"Provable"_T (ceil(goedelSentence_T))$.
    また，不動点補題と D1 より
    $"Provable"_T (ceil(goedelSentence_T -> not"Provable"_T (ceil(goedelSentence_T))))$.
    よって D2 より $"Provable"_T (ceil(not"Provable"_T (ceil(goedelSentence_T))))$.

    一方 D3 より $"Provable"_T (ceil("Provable"_T (ceil(goedelSentence_T))))$.
    再び D2 を用いて $"Provable"_T (ceil(bot))$ を得る．
  / $(<-)$:
    $ "Provable"_T (ceil(bot)) -> not goedelSentence_T$ を示せばよい．
    $"Provable"_T (ceil(bot))$ を仮定する．D1 より $"Provable"_T (ceil(bot -> goedelSentence_T))$, 
    よって D2 より $"Provable"_T (ceil(goedelSentence_T))$. 不動点補題より $not goedelSentence_T$ を得る．#qed
]

#theorem([G2])[
  $T$ が無矛盾ならば $T tack.not "Con"_T$.
  $NN models T$ ならば $T tack.not not"Con"_T$.
]

#pagebreak()

よって以下が証明できる．

#sourcecode[```lean
  theorem goedel_second_incompleteness 
      [𝐈𝚺₁ ≼ T] [T.Delta1Definable] [LO.System.Consistent T] :
      T ⊬ ↑𝗖𝗼𝗻
  
  theorem inconsistent_undecidable
      [𝐈𝚺₁ ≼ T] [T.Delta1Definable] [ℕ ⊧ₘ* T] :
      System.Undecidable T ↑𝗖𝗼𝗻
```]

ただし，上の証明が本質的に依存しているのは D1, D2, D3 と述語の健全性のみ．


== 証明可能性論理

#text(gray)[以下の内容は私（齋藤）ではなく，主に神戸大の野口氏の形式化した結果である．]

型クラスを用いて証明可能性述語やHilbert-Bernaysの可証性条件を抽象的に定義できる．

#sourcecode[```lean
structure ProvabilityPredicate (T : Theory L) (U : Theory L) where
  prov : Semisentence L 1
  spec {σ : Sentence L} : U ⊢! σ → T ⊢! prov/[⌜σ⌝] -- 少なくともD1を満たす

class Diagonalization (T : Theory L) where
  fixpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢!. fixpoint θ ⭤ θ/[⌜fixpoint θ⌝]

...

class ProvabilityPredicate.HBL2 (𝔅 : ProvabilityPredicate T U) where
  D2 {σ τ : Sentence L} : T ⊢! 𝔅 (σ ➝ τ) ➝ (𝔅 σ) ➝ (𝔅 τ) -- D2

class ProvabilityPredicate.HBL3 (𝔅 : ProvabilityPredicate T U) where
  D3 {σ : Sentence L} : T ⊢! (𝔅 σ) ➝ 𝔅 (𝔅 σ) -- D3

class ProvabilityPredicate.HBL (𝔅 : ProvabilityPredicate T₀ T)
  extends 𝔅.HBL2, 𝔅.HBL3 -- D1 + D2 + D3

```]

#pagebreak()

これらの仮定の上で一般的にG1やG2が証明できる．

第一不完全性定理：
#text[#sourcecode[```lean
theorem goedel_independent
    [T ≼ U] [Diagonalization T] [LO.System.Consistent U]
    (𝔅 : ProvabilityPredicate T U) [𝔅.GoedelSound] :
    System.Undecidable U (goedel 𝔅)
```]]

第二不完全性定理：
#text[#sourcecode[```lean
theorem unprovable_consistency
    [T ≼ U] [Diagonalization T] [System.Consistent U]
    (𝔅 : ProvabilityPredicate T U) [𝔅.HBL] :
    U ⊬ con 𝔅
```]]

== 今後

- 算術的完全性定理．
- Paris-Harringtonの定理等の独立命題に関する結果．
- 集合論．
- 二階算術．
- 直観主義一階述語論理, 特に Heyting arithmetic．
- Büchi arithmetic や $sans("S2S")$ の決定性．
- 自動証明．
$dots.v$

#pagebreak()

#set text(size: 14pt, lang: "en")

#bibliography("main.bib")

#text(size: 25pt)[*Sponsor*]

#link("https://github.com/FormalizedFormalLogic")[`FormalizedFormalLogic` #box(height:2em, baseline: 40%, image("ffl.png",)) ] is supported by #link("https://proxima-ai-tech.com/")[Proxima Technology #box(height:3em, baseline: 40%, image("proxima_technology.svg",))]