# term-lisp 移植到 Emacs Lisp —— 设计文档

日期：2026-10-01
状态：待评审

## 1. 背景与目标

现有项目 `termlisp` 是一个用 JavaScript 实现的**项重写语言**（term-rewriting language），带一等的模式匹配、按名传递的惰性实参、数据构造子、以及一个半成品的类型检查器。其核心文件约 880 行：`interpreter/{parser,interpreter,pattern-match,types,helpers,foreign-functions}.js`、`typechecker/typechecker.js`、CLI `termlisp.js`、`prelude.tls`、`examples/*.tls`、`tests.js`。

本设计的目标是把该项目**重新设计并实现为 Emacs Lisp**，成为一个**嵌入式库**，并满足以下新增能力：

- **默认惰性求值**（call-by-need，带记忆化/共享，优于 JS 版的 call-by-name）
- **尾调用优化（TCO）**（绕开 elisp 无 TCO 的限制）
- **Monad 能力**：语言层（暴露 monad 与 `do` 记法）与实现层（求值器用 cats 组织）**两者都要**
- **相对强类型 + GC**：静态类型推断，分阶段实现
- 允许参考 `sexp-rewrite.el`、`eprolog.el`、`emacs-cats`，并使用内建 `peg.el` 与 `pcase-defmacro` 作为辅助

## 2. 需求决策记录

以下决策由用户在本轮头脑风暴中确认：

| 议题 | 决策 |
|---|---|
| 移植的保真度 | **完全可重新设计**；term-lisp 仅作灵感，`.tls` 语法与现有 prelude 可重写 |
| 类型系统强度 | **先 B 后 A**：B = Hindley–Milner（无类型类，monad 用显式字典）；A = HM + 类型类（字典传递） |
| 表面语法 | **统一 S-exp**：顶层用 elisp `read`；peg 解析类型/模式/声明等子语法；开放项用 eprolog 式合一处理 |
| 未定义项 | **开放数据类型（extensible variants）** |
| Monad 实例集 | **Maybe + State + List + Reader**（保持最小稳固集） |
| 副作用 / IO | **第一阶段纯语言**；仅顶层由库输出结果；语言内不提供 `print` |
| Emacs 集成 | **仅嵌入式库**；不做 major mode / REPL / org-babel |
| 依赖策略 | **vendor**（把 cats 拷入仓库） |
| 许可证 | 项目由 MIT **改为 GPLv3**，然后 vendor cats（GPLv3） |
| 求值机制 | **方案一：显式抽象机器（CEK/SECD 风格）+ 惰性 thunk** |
| 验收文档 | 用户稍后提供，作为补充验收参考（本设计先行） |

## 3. 架构总览

```
文本 ──reader(read + peg)──▶ 表面 AST ──elaborate/typecheck──▶ 带类型核心 AST
                                                                      │
                                          CEK 机器（State/Maybe/List/Reader, 惰性, TCO）──▶ 值
```

分层原则：

1. **类型检查是独立的编译期 pass**。运行时求值不依赖类型信息（A 阶段类型类经字典传递后，运行时只剩普通值）。`B → A` 的差异仅限这一层。
2. **求值器与类型无关**。它独立处理开放构造子、匹配失败、回溯。
3. **Monad 分两层**：实现层用 cats 组织机器状态；语言层向用户暴露 monad 与 `do`。

## 4. 模块划分

全部为库文件，无 major mode / REPL：

```
termlisp.el            ; 入口：公共 API、autoload、require 汇总、load-path 注入
termlisp-reader.el     ; elisp read 读 S-exp；peg 解析类型/模式/声明子语法
termlisp-syntax.el     ; cl-defstruct 表面 AST 与核心 AST；S-exp <-> struct
termlisp-types.el      ; 类型表示、合一化(eprolog 式)、HM 推断(B)、约束求解(A)、kind 检查
termlisp-elaborate.el  ; 表面 AST -> 带类型核心 AST；模式编译；字典插入(A)
termlisp-machine.el    ; CEK 机器：control/env/kont/store、TCO、force/memo、fuel
termlisp-eval.el       ; 重写规则库、开放构造子分派、clause 选择、回溯
termlisp-pattern.el    ; 模式 AST、模式匹配器、合一内核的项侧封装
termlisp-monad.el      ; 语言层 monad 字典、do 记法宏、return/bind 内建
termlisp-builtins.el   ; 内建构造子/函数；Maybe/State/List/Reader 实例
termlisp-data-reader.el; cats 无 Reader，补一个 Reader monad
termlisp-prelude.tlsp  ; 重写后的 prelude
vendor/cats/           ; vendor 的 emacs-cats（GPLv3）
test/                  ; ERT 测试
```

依赖策略：cats 整体拷入 `vendor/cats/`，由 `termlisp.el` 注入 `load-path` 并 `require`，不依赖包管理器。

## 5. 表面语法（S-exp）

顶层程序是若干 S-exp 形式的序列，由 elisp `read` 逐个读取（文件扩展名 `.tlsp`）。`;;` 行注释由 reader 处理；保留 `read` 的位置信息用于错误定位。

### 5.1 顶层形式

- 封闭数据类型声明：
  ```
  (datatype Bool
    (True)
    (False))
  ```
- 开放数据类型声明：
  ```
  (datatype open Expr
    (Lit Int)
    (Var Symbol))
  ```
- 开放数据类型扩展（可在任意位置追加构造子）：
  ```
  (datatype-extension Expr
    (Add Expr Expr)
    (Mul Expr Expr))
  ```
- 函数/规则子句（同名多子句构成一个函数）：
  ```
  (define (if (True) a b) a)
  (define (if (False) a b) b)
  ```
- 常量/值绑定：
  ```
  (define true (True))
  ```
- 类型签名标注：
  ```
  (: if (Bool -> a -> a -> a))
  ```
  `TYPE` 是 S-exp，由 peg 归一（见 §7）。
- 类型类与实例（阶段 A）：
  ```
  (class Functor (f) (fmap ((-> a b) -> (f a) -> (f b))))
  (instance (Functor Maybe) ...)
  ```
- `do` 记法（见 §11）：
  ```
  (do Maybe
    (x <- (some-expr))
    (return (+ x 1)))
  ```
- lambda：`(lambda (x y) body)`
- 字面量：整数、字符串作为原子；布尔值用 ADT `Bool` 表示，不用内建 `#t/#f`。

### 5.2 模式语法

- `x`：变量模式，绑定且**不 force**
- `_`：通配，匹配任意且不绑定
- `(:literal e)`：字面量模式，归一后比较
- `(:list rest)`：余项模式，绑定剩余实参
- `(:lambda f)`：函数模式，绑定一个函数
- `(Con p1 ... pn)`：构造子模式，force 被匹配项到 WHNF 后逐参递归
- `(guard p e)`：卫式，先匹配 `p`，再用绑定求值 `e`（`e` 必须为 `Bool`）
- `(or p1 p2 ...)`、`(and p1 p2 ...)`：组合模式

## 6. 项与值的表示、开放数据类型

### 6.1 核心项（`termlisp-syntax.el`，`cl-defstruct`）

- `tl-atom`：symbol / number / string
- `tl-app`：head + 实参列表
- `tl-lambda`：形参列表 + body
- `tl-let`、`tl-do` 等语法糖在 elaborate 阶段脱糖，不进入运行时
- 每个核心节点带 `type` 槽（类型检查后填充；B 阶段可为推断结果）

### 6.2 运行时值（WHNF）

- `tl-value-atom`：不可再归约的原子
- `tl-cons-value`：已归约的构造子应用 `(Con v1 ... vn)`，`Con` 为已声明或开放构造子
- `tl-thunk`：闭包 + `forced?` + `memo` 槽（call-by-need 共享；blackhole 检测 `<<loop>>`）

### 6.3 开放数据类型（extensible variants）

- `(datatype ...)` 声明一个**封闭**类型；`(datatype open ...)` 声明**开放**类型；`(datatype-extension ...)` 向开放类型追加构造子。
- 每个构造子携带**名义类型标签**，类型推断仍能区分 `Expr` 与 `Bool`。
- **关键语义**：对开放类型的模式匹配**永不视为穷尽**，匹配失败是**运行时可发生的**，用 `Maybe` / 机器失败表示，而非编译期拒绝。
- 未在任何 `open` 类型中注册、且未声明的符号落入一个**全局开放宇宙**（名义类型 `Dynamic`），类型上表现为不透明多态，运行时作为构造子。
- 封闭类型的匹配若被证明不穷尽，类型检查阶段给出警告/错误（可配置）。

## 7. Reader 与 peg 子语法

- **顶层**：elisp `read` 逐形式读取。括号结构、字符串、数字、注释交由 `read`。
- **peg 职责**（仅符号型迷你语法，不接管顶层括号）：
  1. **类型表达式**：把 `(a -> b -> c)` 归一为 `(-> a (-> b c))`（`->` 右结合、优先级最低）；`(f a b)` 归一为类型应用 `(TApp (TApp f a) b)`；提取 `forall` 量词与 `=>` 约束。
  2. **模式子语法**：校验并归一 §5.2 的模式写法。
  3. **声明字段**：datatype 构造子签名、类方法签名、超类约束。
- 选择理由：顶层保持 S-exp 的简单可靠；peg 专注于算符优先级/约束语法，并提供优于 `read` 的语法错误信息。

## 8. 类型系统（B → A）

### 8.1 类型表示（`termlisp-types.el`）

- `tl-tvar`：合一化变量（带 level 以便泛化）
- `tl-tcon`：名义类型构造子应用，如 `Int`、`(List a)`、`(-> a b)`
- `tl-tscheme`：`forall` 量化类型（含约束列表，A 阶段使用）
- **kind**：最小 kind 系统 `*` 与 `* -> *`，用于检查 `Functor f` 这类高阶参数

### 8.2 阶段 B（HM，无类型类）

- Algorithm W/J：推断时维护替换；在 `define`/`let` 边界**泛化**，使用点**实例化**。
- 合一化复用 §9 内核，加 occurs-check；失败返回错误而非抛异常。
- 构造子类型来自 datatype 声明：`(True : Bool)`、`(Cons : a -> List a -> List a)`。
- 同一函数多个子句必须类型一致；每个子句的模式绑定变量类型；body 推断后统一。
- **递归**：允许一般递归（不做整体性检查）；递归函数类型为一个 fresh tvar，与各子句统一。
- **值限制（value restriction）**：惰性语言中 `let` 无限制泛化不可靠（经典 lazy-let 反例）。**只对语法值**（lambda、构造子、字面量、变量）泛化，非值计算不泛化。

### 8.3 阶段 A（类型类，B 之上增量）

- 类声明 `(class Functor (f) (fmap ...))`、超类 `(class (Monad m) ...)`；实例声明 `(instance (Monad Maybe) ...)`。
- 推断时**收集约束**：`fmap : (Functor f => (-> a b) -> f a -> f b)`。
- 统一后**求解约束**：按实例匹配、递归求解实例上下文；未解析约束报错。
- **字典传递**：elaborate 在调用点插入字典参数；类型擦除后运行时就是普通值。
- `do` 脱糖为 `bind`/`return`；A 阶段由约束求解自动定 monad，B 阶段需显式写 monad 名。
- 实例集：`Maybe`、`State`、`List`、`Reader` 的 `Functor/Applicative/Monad`；`Monoid` 视需要。

## 9. 模式匹配与合一化（eprolog 式）

### 9.1 合一内核

- 替换用 binding alist；`deref`（walk）跟随绑定；occurs-check 由 Reader 配置（类型推断默认开）。
- 结构合一：原子相等、变量绑定、构造子逐参递归；用 **worklist 迭代**实现（借鉴 `eprolog--unify`，不递归爆栈）。
- 类型推断与模式匹配**共用内核**，但使用不同的变量命名空间。

### 9.2 匹配语义

- 匹配是**有向**的（pattern vs value），但开放项引入逻辑变量，可退化为合一。
- 同一函数多子句、开放类型构造子搜索 → **choice point** 存入 kont，配合 `List` monad 回溯。
- **非线性模式**（同一变量出现两次）：先绑定再 deref 比较，不等则失败（对应 sexp-rewrite 的 nonlinear 检查）。
- 匹配失败是**值**（`Maybe`/机器失败），不是异常。

### 9.3 编译策略

- 模式在 elaborate 阶段**编译为闭包匹配器**，比解释式匹配更快，并便于按需 force。

## 10. CEK 机器、惰性、TCO

### 10.1 机器状态（`tl-machine`，`cl-defstruct`）

- `control`：待求值核心 AST 或待返回值
- `env`：词法环境（持久化 alist，name → thunk/value）
- `kont`：显式 continuation 栈（帧的列表）
- `store`：thunk 记忆化表（或 thunk 自带 memo 槽）
- `defs`：全局重写规则库（函数名 → 子句列表）
- `fresh`：gensym 计数器（State）
- `fuel`：步数上限（Reader 配置，防失控）

continuation 帧类型：`eval-args`、`force`、`do-bind`、`if`、`choice`（回溯点）等。

### 10.2 求值循环 `tl-step`

- 原子 → 查 env → force → 值。
- thunk → force（求值一次并回填 memo；blackhole 检测 `<<loop>>`）。
- 应用 `(f a1..an)`：
  - `f` 是 lambda：为实参建 thunk、绑定、`control = body`（**尾调用，不压 kont**）。
  - `f` 是已定义函数：模式匹配选第一条匹配子句（按需 force 实参）、绑定、`control = body`（**TCO**）。
  - `f` 是已声明/开放构造子：压 `eval-args` 帧，逐个求到 WHNF，组装构造子值。
  - 已定义函数但无子句匹配：**机器失败** → `Maybe`。
- **TCO 原理**：kont 显式化后，尾位置子表达式**不压帧**，直接替换 `control`；整个循环是 elisp 的 `while`，递归深度恒定，绕开 elisp 无 TCO 的限制，互递归同样成立。

### 10.3 惰性

- 实参一律先变 thunk（捕获 env），不预先求值。
- 模式匹配**按需** force：构造子模式 force 到 WHNF，字面量模式比较，变量模式**不 force**、直接绑定 thunk。
- 深层结构遍历用显式 worklist，避免 elisp 递归爆栈。

### 10.4 实现层 monad 落点

- 顶层驱动器用 `cats-do` 在 `State`（机器状态）+ `Maybe`（步失败）+ `List`（规则/回溯分支）上串联 `tl-step`；`Reader` 提供静态配置（occurs-check、fuel、严格性开关）。
- 内层热路径 `tl-step` 写成纯函数返回下一状态，cats 负责组合。
- **风险**：cats 抽象在热循环上有开销；后续可用 `cl-defmethod` 特化或局部展开优化，先正确后优化。

## 11. Monad 与 do 记法

### 11.1 实现层

- 直接使用 vendor 的 `cats-data-state`、`cats-data-maybe`、`cats-data-monad`、`cats-data-applicative`、`cats-data-functor`、`cats-data-foldable`、`cats-macros` 的 `cats-do`。
- cats 无 Reader：新增 `termlisp-data-reader.el`（`tl-data-reader`），实现 `fmap`/`pure`/`apply`/`bind`/`ask`/`local`。

### 11.2 语言层

- 每个 monad 实例是一个**字典值**（B 阶段显式传递；A 阶段由类型类求解自动插入），含 `pure`/`bind`/`fmap`/`apply` 字段。
- `do` 形式与脱糖：
  - `(x <- e)` → `(bind m e (lambda (x) ...))`
  - 裸 `e` → `(bind m e (lambda (_) ...))`
  - 末行 `(return v)` 保留
- 暴露 `return`/`pure`、`bind`/`>>=`。
- 实例：`Maybe`、`State`、`List`、`Reader` 的 `Functor/Applicative/Monad`；`Monoid` 视需要。
- B 阶段 `do` 需写 monad 名（elaborator 解析为字典）；A 阶段可省略、由约束推断。
- **monad 三定律**对每个实例用 ERT 验证。

## 12. 库 API

`termlisp.el` 暴露（嵌入式库）：

- `(termlisp-make-env &optional options)` → 新建求值上下文
- `(termlisp-eval STRING &optional env)` → 求值程序串，返回结果值
- `(termlisp-eval-file FILE &optional env)`
- `(termlisp-parse STRING)` → 表面 AST
- `(termlisp-typecheck STRING &optional env)` → 推断类型/错误
- `(termlisp-load-prelude env)` / `(termlisp-load-file FILE env)`
- `(termlisp-value->string v)` / `termlisp-format`
- `options`：`occurs-check`、`fuel`、`type-check`、`phase`（`B`/`A`）、`open-universe`

**错误处理**：内部机器用 `Maybe`；公共 API 用 `define-error 'termlisp-error` 抛出结构化错误（含位置、栈、匹配失败原因），并另提供 `-safe` 变体返回错误对象而非抛出。

## 13. 测试与验收

`test/` 下用 ERT：

- reader/parser、类型推断（B 与 A）、合一化、模式匹配（含开放类型失败）、monad 定律、prelude。
- 求值专项：**惰性**（无限结构、共享只求值一次）、**TCO**（深递归不溢出）、开放类型匹配失败。
- 验收：重写后的 prelude + 示例程序全绿；用户稍后提供的文档作为补充验收参考。

## 14. 许可证变更

项目当前为 MIT。`emacs-cats`、`sexp-rewrite.el`、`eprolog.el`、`peg.el` 均为 GPLv3。为 vendor cats，**项目整体改为 GPLv3**，更新 `LICENSE` 与文件头。

## 15. 风险与非目标

**风险**：

- cats 在热求值循环上的性能开销（缓解：纯函数热路径 + 后续特化）。
- 惰性 + HM 的值限制可能让某些直觉上应泛化的绑定不被泛化（这是正确性代价，需在文档中说明）。
- 开放类型的匹配失败与"相对强类型"的张力（缓解：失败显式建模为 `Maybe`）。
- 阶段 A 的约束求解与字典传递复杂度较高（缓解：B 阶段先落地，A 增量）。

**非目标（本设计不做）**：

- 依赖类型 / 整体性（totality）检查。
- IO monad 与语言内副作用（第一阶段纯）。
- Emacs major mode、REPL、org-babel 集成。
- 与现有 `.tls` 语法或 JS 实现的向后兼容。
