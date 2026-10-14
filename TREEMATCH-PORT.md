# 阶段 3 可行性简报：用 termlisp 移植 `~/treematch`

> **状态：不作为独立分发，降级为压力测试 workload。**
> 移植目标从"产出一个能跑的 treematch"改为"用 treematch 的类型形状压测检查器"，
> workload 的翻译套件**推迟到阶段 3 完成之后**。详见 §7。

> 结论先行：**可行，但瓶颈不在你预期的地方。**
> treematch 需要的类型系统能力，termlisp 现在**已经全部具备**（模式匹配甚至超出需求）。
> 真正的三个阻塞点全在**输出侧**——Camlp4 代码生成、sexplib 派生器、OCaml 美化打印器。
> 而阶段 3 计划中的四项（`Eq`/`Refl`/`sym`/`trans`/`subst`/`rewrite`、dot pattern、穷尽性检查）
> **只有一项**——穷尽性检查 G7——对这个移植有直接贡献。

---

## 1. treematch 实际是什么

**先纠一个会误导估算的前提**：`doc/treematch.org` 描述了一个大语言
（fold/reduce/rewrite/recurse/iter/eval 策略、cut/wide/deep 访问算子、参数化 AST、
include、从重写规则反推 AST 类型推断）。**这些几乎全部没有实现。**
代码实现的只有三件事：

1. `ast` 声明 → 互递归 OCaml variant 类型
2. `map` 重写规则 → OCaml class 访问器方法（一个规则一个方法，编译成 pattern match）
3. 两个 OCaml 代码后端

所以它是**一个约 1,276 行的小型代码生成器**，不是一个语言运行时。
`src/` 下 16 个 `.ml`（1,215 行）+ 2 个 `.mli`（47 行）+ ocamllex（81）+ menhir（88）。

流水线：`.tm` 源文件 → lexer → parser → `Typing.program`（5 道 pass：`Construct |> Vars |> Rename |> Unify |> Default`，`typing.ml:344-349`）→ 两个后端之一 → OCaml 源码。

---

## 2. 特性逐项对照

| treematch 需要 | 出处 | termlisp 现状 | 判定 |
|---|---|---|---|
| **互递归 ADT** | `tree.ml:7-15`、`program.ml:7-27`、`constr.ml:7-13`、`ident.ml:3-6`、`error.ml:1-4` 全是互递归 variant | `datatype` + `datatype-extension`。实测 `A` 的构造子字段提到尚未声明的 `B` **可行** | ✅ |
| **嵌套模式**（深度 ≤3，构造子×元组两侧同时匹配） | `typing.ml:209` `T.Tree (ty,(nm,tree)), T.Tree (ty',(nm',tree'))` | `tl-pattern-parse` 递归展开；实测 `(Pair a (Pair b c))` 通过 | ✅ |
| **guard** | `typing.ml:296` `function P.Ast (name,nodes) when ast_name = name` | `(guard p e)` 模式，`termlisp-pattern.el:40-41` | ✅ |
| **or-pattern**（含字符串字面量 or-pattern） | `constr.ml:33` `List tycon \| Option tycon`；`specialBackend.ml:138` `"string"\|"int"\|...` | `(or p1 p2)` 模式 + `:literal` 模式 | ✅ |
| **通配/兜底子句** | 遍地 `_` 与 `\| x -> x` | `_` → `wild` | ✅ |
| **参数多态** | `'a tree` 分别实例化为 `unit` / `Constr.tycon` | HM + level 泛化（2d）+ 索引族（阶段1/2） | ✅ |
| **幻影类型 + 多态变体行约束** | `ident.ml:4-6` `'a ident = ([< \`U\|\`L] as 'a) t` | HM 表达不了行约束 | ⚠️ 重构为两个名义类型 `UIdent`/`LIdent`，约 30 行，机械 |
| **类型类 / 对象** | OCaml 对象当打印器架构：`class virtual ['a] base_print` + `inherit [unit] base_print` + `method!` 覆写 + `self : 'a`（`program.ml:38-81`、`tree.ml:26-45`、`constr.ml:19-26`） | `class`/`instance` 已有（Functor/Applicative/Monad/Num），或直接用闭包记录 | ⚠️ 重构，机械 |
| **高阶函数 / 闭包 / 柯里化** | 遍地 `List.map/fold_right`、`\|>`、`%`、`%>`、`function`、部分应用 | 齐备 | ✅ |
| **可变状态** | 7 个 CLI `ref`（`options.ml:2-9`）、lexer 行计数（`lexer.mll:5,28`）、fresh-name 计数器（`typing.ml:277-284`）、2 个 `Hashtbl`（`typing.ml:129`、`inline.ml:25`） | 表层无可变状态 | ⚠️ 全部函数化：fresh-name 计数器改成 prelude 里现成的 **State 单子**；两个 `Hashtbl` 只是计数器/集合 |
| **异常** | 1 个自定义异常 + 用 `Not_found` 当控制流（`typing.ml:157-159,314-320`、`inline.ml:30-36`）+ `failwith` + `assert`（`typing.ml:211,213`） | 无用户级异常；`Either`/`Void`/`absurd` 已有 | ⚠️ 改写成 Result 风格。**机械，但要碰 `typing.ml` 全部 349 行** |
| **字符串处理**（大小写归一、`Char.escaped`、format box） | `ident.ml:9-18`、`lexer.mll:79`、`program.ml:39-57` | `string-join`、`string->list`、`list->string`、`format`（仅 `~a`）。**没有拼接、没有 `string-length`、没有 `substring`、没有字符判别** | ❌ 需补 6 个 builtin |
| **I/O** | `open_in` 读文件、stdout 写、代码写死 `/dev/stdout` | 只有 stdout | ⚠️ 需补 1 个写文件 builtin |
| **自己的前端**（ocamllex 81 + menhir 88 = 169 行） | `lexer.mll`、`parser.mly` | 表层语法就是 s-表达式 | 🚫 **不要移植**——见 §5 |
| **Camlp4 引号代码生成**（255 行） | `simpleBackend.ml`、`specialBackend.ml` | 无 | ❌ **真阻塞点之一** |
| **sexplib `with sexp` 派生器**，且是**输出契约的一部分** | `program.ml:22-27`、`tree.ml:15`、`constr.ml:13`；生成代码 `open Sexplib.Conv` + `\| SEXP` 构造子 | 无 | ❌ **真阻塞点之二** |
| **数值** | 只有机器 `int`，运算只有 `+1`（`inline.ml:34`），`int32/int64/bool` 只是字符串魔法名 | Int/Double、`+ - * /` 等 | ✅ |
| **性能** | 无热点。全是对小 AST 的 O(n) 列表 map/fold；无 memoization、无 hash-consing、无 interning | elisp 解释器 | ✅ |
| **并发 / 浮点 / 大整数 / 位运算 / 正则 / 运行时反射 / eval** | 完全没有 | — | ✅ |

**统计**：12 项 ✅、5 项 ⚠️（全部机械重构）、3 项 ❌、1 项 🚫（明确不做）。

---

## 3. 三个真阻塞点（全在输出侧）

### 3.1 Camlp4 引号 + OCaml 美化打印器（`simpleBackend.ml` + `specialBackend.ml`，255 行）

这是最难的一块。它不是"拼字符串"，而是：

- 用**带类型的准引号**构造宿主语言 AST：`<:str_item< >>`、`<:ctyp< >>`、`<:patt< >>`、`<:expr< >>`、`<:match_case< >>`、`<:class_str_item< >>`、`<:module_binding< >>`，配反引号 `$uid:...$`、`$lid:...$`、`$tup:...$`、`$str:...$`、`$int:...$`（`simpleBackend.ml:18-35, 40-65, 68-92`；`specialBackend.ml:10-15, 35-41, 48-93, 110-151`）
- 再交给 Camlp4 的 `Printers.OCaml.print_implem` 打印（`simpleBackend.ml:96-98`、`specialBackend.ml:155-157`）

它必须产出的 OCaml 结构相当刁钻：

- **递归模块 + 手写递归签名**（`module rec List : sig type t = Cons of Integer.t * List.t | Nil | SEXP ... end and Integer : ...`，见 `001-basic_ast.ref:4-35`）
- **对象类当访问器**（`class $lid:nm$ = object (self : 'a) method $lid:node$ = function ...`）
- 硬编码的 `| SEXP` 构造子与 `sexp_of_t`/`t_of_sexp` 命名，必须与 sexplib 的 camlp4 派生器约定一致

> 在 termlisp 上，要么有对 OCaml 语法的**卫生代码生成**，要么接受输出不同、重写 `.ref` 测试。
> 没有第三条路。

### 3.2 sexplib 派生器

`with sexp` 在三个互递归类型上生成序列化器，而且**生成的代码本身依赖 sexplib**（`open Sexplib.Conv`、`sexp_of_t`/`t_of_sexp`、`| SEXP`）。移植要么自带一个派生宏，要么手写约 100 行转换器——注意 `ident.mli:1-4` 把表示藏起来了，手写转换器必须放在 Ident 模块内部。

### 3.3 字符串与文件 I/O 基础设施（**不属于任何阶段**）

这是最"便宜"但完全没被任何 roadmap 覆盖的一块。实测 termlisp 现在：

```
string-join                => (string-join (Cons "a" (Cons "b" Nil)))  ⇒ "ab"
format "~a" 42             ⇒ "42"
eq "a" "a"                 ⇒ True
format "~a" (Cons 1 Nil)   ⇒ "[1]"
string->list / list->string ⇒ 互逆，字符是单字符 String
```

缺口（全部是 builtin，估计合计 **约 50 行 + 10 行**）：

| 缺什么 | 为什么必需 |
|---|---|
| `string-append` / `++`（拼接） | 没有它，任何文本生成都写不了 |
| `string-length`、`substring` | lexer 与 ident 归一化必需 |
| `string<` 或字符判别 | `<` 已被注册为 `Int -> Int -> Bool`，实测 `(< "a" "b")` 报 `Cannot apply`。而 `tl-sort!` 内部已经在用 elisp 的 `string<`，只是没暴露 |
| `string-upcase` / `string-downcase` | `ident.ml:9-18` 的大小写归一 |
| `write-file`（或 `with-output-to-file`） | 现在只有 `princ` 到 stdout |

---

## 4. 阶段 3 与这个移植的真实关系（正交性）

这是本简报最重要的一节，因为它推翻了"阶段 3 做完才能移植"的直觉。

| 阶段 3 计划项 | 对移植 treematch 的贡献 |
|---|---|
| `Eq : (a : *) -> a -> a -> *`、`Refl` | **零**。treematch 不写任何证明 |
| `sym` / `trans` / `subst` / `rewrite` | **零** |
| dot pattern（Idris 2 的 `IMustUnify` → `checkDots`） | **零**。treematch 无 dot pattern |
| **穷尽性检查（G7）** | **直接、关键**——见下 |

**为什么穷尽性检查是关键**：treematch 的 `typing.ml`（349 行，最大的模块）用
OCaml 编译器免费提供的穷尽性保证来兜底，剩下的地方则靠 `assert` 和异常当控制流：

```ocaml
(* typing.ml:211 *)  assert (nm = nm');
(* typing.ml:213 *)  assert (List.length tree = List.length tree');
(* typing.ml:157 *)  try Hashtbl.find collector (nm,nm'), args with Not_found -> c
(* typing.ml:314 *)  try ... with Not_found -> P.Map ...
```

一旦移植，这些 `assert` 变成运行时炸点、`Not_found` 变成静默走错分支。
**只有 G7 能把 OCaml 编译器当初给 treematch 的那份保证，原样搬到 termlisp 里。**

反过来说：阶段 3 的其余三项**服务的是 Curry–Howard 基准，不是这个移植**。
两者应当被当作**两个独立的立项理由**，不要用一个给另一个背书。

---

## 5. 建议的移植形态：两条路线

### 路线 A（推荐）：重新表达，不逐行翻译

`.tm` 源文件**直接用 s-表达式写**，不移植那 169 行 ocamllex/menhir。

treematch 的 `.tm` 语法本质是带类型标注的 S-表达式树：

```
ast Program {
Program:     | Program Definition Program
             | End
Definition:  | Function Function
             | Global Global
Identifer: string
Integer: int
}
```

s-表达式版本是同构的，而且**少一层解析**、可以直接被 termlisp 的 reader 读入、
还顺带让 `.tm` 文件本身可以被类型检查。

然后后端改成**产出 termlisp 源码**（ datatype 声明 + 函数定义），而不是 OCaml 源码。

- 输出是数据（s-表达式），**不需要美化打印器**，`termlisp-value->string` 就够
- §3.1 和 §3.2 **整体消失**
- 移植规模估计 **约 600 行**（`typing.ml` 的 349 行是主体，两个后端被替换成 100 行左右的 sexp 构造）
- 副作用：生成出来的代码是**带索引的类型**，反过来对阶段 1/2 的机制是一次真实压力测试

### 路线 B：保留 OCaml 作为输出目标

那就必须补齐 §3.1 + §3.2 + §3.3 全部三项：

- OCaml 文本生成（用 §3.3 的字符串 builtins 手写，放弃字节级一致）
- sexplib 命名约定
- 递归模块块与 class 访问器的模板

**风险全部集中在这里**，且 `testsuite/treematch/*.ref` 五个文件必然要重写
（因为拿不到 Camlp4 的格式化输出，缩进与 `;;` 位置不会一致）。

**建议**：先做 A（验证移植模型、把 1,276 行跑通、拿到 G7 的价值），
B 作为 A 的后续增量，且只有在确实需要 OCaml 产物时才做。

---

## 6. 风险

| # | 风险 | 影响 | 缓解 |
|---|---|---|---|
| T1 | 互递归 datatype 靠的是 `tl-type-parse` 对未知类型头的**宽松**（`termlisp-types.el:861-866` 的 kind check 是 `condition-case` 吞掉的），不是设计 | 前向引用的构造子字段**跳过了 kind 检查** | ~~阶段 3 前先补：datatype 声明后回填 kind。约 20 行~~ **已核实失效（2026-10-14）**：阶段 2 的 `early` 登记项 + 声明后的 kind 复查已经覆盖了两种声明顺序，见 §7.1 |
| T2 | `Not_found` 当控制流 → 改 Result 后若漏掉一处，错误变成静默分支 | `typing.ml` 349 行逐函数过 | G7 穷尽性检查恰好在此发挥作用 |
| T3 | equirecursive 默认开（`occurs-check` 关，`base:41`），与索引族叠加后类型相等判定变慢 | 大 AST 上可能退化 | treematch 的类型都很小，实测风险低 |
| T4 | elisp 上 NbE 性能未经验证 | 生成大类型时可能慢 | 先在 §5 路线 A 的 600 行上实测 |
| T5 | 路线 B 的 `.ref` 无法字节对齐 | 测试基线重写 | 接受，并在决策文档里写明这是有意的取舍 |

---

## 7. 分步建议

> **决定（2026-10-12）**：本移植**不作为独立分发**，降级为阶段 1/2/3 的**压力测试 workload**；
> 而 workload 的翻译套件**推迟到阶段 3 完成之后**再做。
> 理由：既然是压力测试，就不需要 `.ref` 字节对齐，也就不需要文件输出 builtin
> （§3.3 只剩 6 个字符串 builtin）；而穷尽性检查 G7 是阶段 3 的一部分，
> 它落地之前，压力测试测不到最有价值的那一项。

按此调整后的顺序：

1. **阶段 3**：`Eq`/`Refl`/`sym`/`trans`/`subst`/`rewrite`、dot pattern、**穷尽性检查 G7**
2. **补 6 个字符串 builtins**（§3.3，约 40 行；写文件的那 1 个不再需要）
3. **修互递归 datatype 的 kind 回填**（T1，约 20 行）
4. **treematch → workload 翻译套件**：把 `.tm` 的类型形状译成 termlisp workload
   （互递归 ADT、深嵌套模式、`typing.ml` 那种大量 partial function 的 match），
   挂进 battery，观察 fuel、`occurs-check` 关闭时的表现、elisp 上 NbE 的实际速度
5. （远期，视 4 的结果）路线 A 后端产出 termlisp；再视需要做路线 B 的 OCaml 输出

第 2、3 步在阶段 3 之前独立做也无妨，不改变任何现有语义；但**翻译套件本身（第 4 步）不做**。

---

### 7.1 执行记录与实测数据（2026-10-14）

阶段 3 完成（`9747c9f`），上面那句"第 4 步不做"的前置条件随之解除，
于是按本节开头的决定执行了第 4 步，落地为 **`test/treematch-workload-test.el`（12 条 ERT）**，
挂进 `test/aldor-test.el`。三处审计结论一并记在这里：

- **第 3 步（T1 互递归 kind 回填）不需要做。** 阶段 2 的 `early` 登记项在声明时就把类型头挂进
  环境，声明全部读完后再统一做一次 kind 复查，所以**先用后声明**与**先声明后用**两条顺序都已覆盖。
  逐项核对 `001-basic_ast.tm` 的 12 组互递归，两种顺序均通过（见下表第 1、2 行）。
- **第 2 步（§3.3 的 6 个字符串 builtins）仍未做。** 它们全在输出侧，穷尽性检查与 kind 检查
  一行都不用到；压力测试测不到它们，也没有因此被阻塞。
- **压测顺带挖出一个输出侧缺陷**：`tl-output--format`（`print` / `format` / `string-join` 共用的
  渲染器）没有构造子应用的分支，`(format "~a" (Succ Zero))` 会落到 `(format "%s" value)`，
  把参数 thunk 连同它们闭包的**整个环境**打出来——实测 32,937 字符，`(Pair Zero True)` 是 65,868 字符。
  已修（补 `consp` 分支，按 `(Succ Zero)` 渲染），回归测试 `tl-prelude-format-constructor` 等两条。

#### 实测

每次运行都含 0.26s 的 prelude 装载，所以"边际成本"= 总时间 − 0.26s。
机器：本机 elisp，`make test` 同一进程。

| 形状 | 总耗时 | 边际 | 结果 |
|---|---|---|---|
| 12 组互递归 AST 声明 + 检查 | 0.394s | 0.13s | `ok` |
| 前向引用：`P` 的字段写 `Q`，而 `Q` 在其后才声明 | 0.394s | 0.13s | `ok`，不是自由变量 |
| 同上前向引用，但 `MkQ` 收了 `True` | — | — | 拒绝：`Cannot apply MkQ to True` |
| `size` 穷尽覆盖 `Program` | 0.277s | 0.02s | `ok` |
| `size` 漏掉 `PEnd` | 0.261s | — | `size: match is not exhaustive; no case for PEnd` |
| 3 层嵌套构造子模式 | 0.280s | 0.02s | `ok` |
| 深处漏一例（`DGlobal`） | 0.261s | — | `no case for (PProgram (DGlobal _) _)` |
| `003` 的参数写反（`Cons xs x`） | 0.274s | 0.01s | `Clause of rev does not match its signature` |
| **704 个 datatype**（AST × 64） | 0.431s | 0.17s | `ok` |
| 嵌套深度 1 / 2 / 4 / 8 / 16 / 32 | 0.261–0.286s | ≤0.03s | 全部 `ok`，**对深度平坦** |
| 12 个二元构造子，穷尽 | 0.354s | 0.09s | `ok`（最重的一例） |
| 同上，`tl-exh-fuel 10` | 0.324s | — | `Coverage: fuel exhausted after 10 steps` |

三条值得写下来的结论：

1. **成本对 datatype 数量近线性**：64 倍的 datatype 只让边际成本从 0.13s 涨到 0.17s。
2. **成本对嵌套深度平坦**：深度 1 到 32 全部落在基线噪声里，usefulness 搜索没有随深度翻倍。
3. **fuel 是真的**：把 `tl-exh-fuel` 压到 10，usefulness 搜索会**报错而不是假装通过**——
   一条覆盖检查半途放弃就什么都没证明，这正是 `test/treematch-workload-test.el`
   存在的理由，`typing.ml` 里那些 `assert` 和 `Not_found` 当控制流的写法（T2）
   一旦移植过来就是运行时爆炸或静默错分支。
