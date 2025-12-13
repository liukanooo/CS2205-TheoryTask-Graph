# Coq 图论库 (Graph Theory Library)

[![Coq](https://img.shields.io/badge/Coq-8.20+-blue.svg)](https://coq.inria.fr/)

一个基于 Type Classes 的高度抽象 Coq 图论形式化验证库，将路径（Path）的抽象概念与其具体实现（顶点序列或边序列）完全分离。

## 目录

- [核心设计思想](#核心设计思想)
- [架构概览](#架构概览)
- [归纳与解构原则](#归纳与解构原则)
- [项目结构](#项目结构)

---

## 核心设计思想

本库的核心创新在于**将路径的抽象定义与具体表示解耦**：

- **抽象层面**：用户通过 `Path G V E P` Type Class 操作路径，无需关心路径的底层表示
- **实现层面**：支持两种主要的路径表示方式：
  - **顶点路径 (vpath)**：路径表示为顶点序列 `list V`
  - **边路径 (epath)**：路径表示为边序列 `list E`

这种设计使得相同的图算法逻辑可以无缝切换底层表示，同时保持证明的通用性和复用性。

---

## 架构概览

### Type Class 层次结构

库采用三层架构设计：

```
┌─────────────────────────────────────────────────────────┐
│        抽象接口层 (Abstract Interface)                   │
│  ┌───────────────────────────────────────────────────┐  │
│  │ Graph G V E                                       │  │
│  │   - vvalid: 顶点有效性                            │  │
│  │   - evalid: 边有效性                              │  │
│  │   - step_aux: 边的连接关系                        │  │
│  └───────────────────────────────────────────────────┘  │
│  ┌───────────────────────────────────────────────────┐  │
│  │ Path G V E P                                      │  │
│  │   - path_valid: 路径有效性                        │  │
│  │   - head / tail: 起点/终点                        │  │
│  │   - vertex_in_path: 顶点序列                      │  │
│  │   - edge_in_path: 边序列                          │  │
│  └───────────────────────────────────────────────────┘  │
│  ┌───────────────────────────────────────────────────┐  │
│  │ EmptyPath / SinglePath / ConcatPath               │  │
│  │   - empty_path: 空路径（单点）                    │  │
│  │   - single_path: 单边路径                         │  │
│  │   - concat_path: 路径连接                         │  │
│  └───────────────────────────────────────────────────┘  │
│  ┌───────────────────────────────────────────────────┐  │
│  │ Destruct1nPath / Destructn1Path                   │  │
│  │   - destruct_1n: 从头部分解                       │  │
│  │   - destruct_n1: 从尾部分解                       │  │
│  └───────────────────────────────────────────────────┘  │
│  ┌───────────────────────────────────────────────────┐  │
│  │ PathInd1n / PathIndn1                             │  │
│  │   - path_ind1n: 头部优先归纳                      │  │
│  │   - path_indn1: 尾部优先归纳                      │  │
│  └───────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────┐
│           具体实现层 (Concrete Realizations)            │
│  ┌──────────────────┐       ┌──────────────────┐       │
│  │  Vertex Path     │       │   Edge Path      │       │
│  │  (vpath)         │       │   (epath)        │       │
│  │                  │       │                  │       │
│  │  P = list V      │       │  P = list E      │       │
│  │                  │       │                  │       │
│  │  路径由访问的    │       │  路径由经过的    │       │
│  │  顶点序列表示    │       │  边序列表示      │       │
│  └──────────────────┘       └──────────────────┘       │
└─────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────┐
│              应用层 (Applications)                      │
│  - Dijkstra 最短路径算法                                │
│  - Floyd-Warshall 全源最短路径                          │
│  - Prim 最小生成树                                      │
│  - Kruskal 最小生成树                                   │
└─────────────────────────────────────────────────────────┘
```

### 核心 Type Classes

#### 1. **Graph** - 图的基本定义

```coq
Class Graph (G V E: Type) := {
  vvalid : G -> V -> Prop;          (* 顶点有效性 *)
  evalid : G -> E -> Prop;          (* 边有效性 *)
  step_aux : G -> E -> V -> V -> Prop  (* e 连接 u 到 v *)
}.
```

#### 2. **Path** - 路径的抽象定义

```coq
Class Path (G V E: Type) `{Graph G V E} (P: Type) := {
  path_valid: G -> P -> Prop;       (* 路径有效性 *)
  head: P -> V;                      (* 起点 *)
  tail: P -> V;                      (* 终点 *)
  vertex_in_path: P -> list V;      (* 顶点视图 *)
  edge_in_path: P -> list E;        (* 边视图 *)
  vpath_iff_epath: ...               (* 顶点与边的对应关系 *)
}.
```

#### 3. **路径操作 Type Classes**

```coq
(* 空路径（单点） *)
Class EmptyPath := {
  empty_path: V -> P;
  empty_path_valid: forall g v, path_valid g (empty_path v);
  empty_path_vertex: forall v, vertex_in_path (empty_path v) = [v]
}.

(* 单边路径 *)
Class SinglePath := {
  single_path: V -> V -> E -> P;
  single_path_valid: forall g u v e, 
    step_aux g e u v -> path_valid g (single_path u v e);
  single_path_vertex: forall u v e, 
    vertex_in_path (single_path u v e) = [u; v]
}.

(* 路径连接 *)
Class ConcatPath := {
  concat_path: P -> P -> P;
  concat_path_valid: forall g a1 a2, 
    path_valid g a1 -> path_valid g a2 -> 
    tail a1 = head a2 -> 
    path_valid g (concat_path a1 a2)
}.
```

---

## 归纳与解构原则

本库提供了**两种对称的视角**来处理路径的归纳证明和结构分解，这是库设计的核心特性之一。

### "1n" 视角（头部优先，Head-First）

**概念**：从路径的**起点**开始分解和构造。

#### Destruct1nPath - 头部分解

```coq
Class Destruct1nPath := {
  destruct_1n_path: P -> path_destruct_1n;
  destruct_1n_spec: forall g p, path_valid g p ->
    match destruct_1n_path p with
    | DestructBase1n v => 
        p = empty_path v                    (* 空路径 *)
    | DestructStep1n p' u v e =>
        path_valid g p' /\
        head p' = v /\
        step_aux g e u v /\
        p = concat_path (single_path u v e) p'   (* p = (u→v) ++ p' *)
    end
}.
```

**分解模式**：`p = Empty(v)` 或 `p = Single(u→v) ++ Rest`

**典型应用场景**：
- 前向可达性证明（从起点 `u` 出发证明可以到达 `v`）
- 构造从起点开始的路径
- Dijkstra 算法等单源最短路径算法

#### PathInd1n - 头部归纳

```coq
Class PathInd1n := {
  path_ind1n: forall g (X: P -> Type)
    (H_empty: forall v, X (empty_path v))
    (H_step: forall u v e rest, 
      step_aux g e u v -> 
      path_valid g rest ->
      head rest = v ->
      X rest -> 
      X (concat_path (single_path u v e) rest)),
    forall p, path_valid g p -> X p
}.
```

**归纳策略**：
1. **基础情况**：`empty_path v` 满足性质 `X`
2. **归纳步骤**：如果 `rest` 满足 `X`，那么在前面添加一步 `u→v` 后仍满足 `X`

---

### "n1" 视角（尾部优先，Tail-First）

**概念**：从路径的**终点**开始分解和构造。

#### Destructn1Path - 尾部分解

```coq
Class Destructn1Path := {
  destruct_n1_path: P -> path_destruct_n1;
  destruct_n1_spec: forall g p, path_valid g p ->
    match destruct_n1_path p with
    | DestructBasen1 p' v =>
        p = empty_path v                    (* 空路径 *)
    | DestructStepn1 p' u v e =>
        path_valid g p' /\
        tail p' = u /\
        step_aux g e u v /\
        p = concat_path p' (single_path u v e)   (* p = p' ++ (u→v) *)
    end
}.
```

**分解模式**：`p = Empty(v)` 或 `p = Rest ++ Single(u→v)`

**典型应用场景**：
- 后向可达性证明（证明从某点可以到达终点 `v`）
- 从终点倒推构造路径
- 路径末尾追加操作

#### PathIndn1 - 尾部归纳

```coq
Class PathIndn1 := {
  path_indn1: forall g (X: P -> Type)
    (H_empty: forall v, X (empty_path v))
    (H_step: forall u v e rest, 
      step_aux g e u v -> 
      path_valid g rest ->
      tail rest = u ->
      X rest -> 
      X (concat_path rest (single_path u v e))),
    forall p, path_valid g p -> X p
}.
```

---

### 公理 vs 导出原则

**重要区别**：

1. **PathInd 是公理**：`PathInd1n` 和 `PathIndn1` 是 Type Class 的字段，作为**公理**被声明，针对抽象类型 `P` 工作

2. **具体归纳原则是导出的**：
   - 对于 `valid_vpath g u (l: list V) v`（顶点序列），使用 `PathInd1n` 可以导出针对 `list V` 的归纳原则
   - 对于 `valid_epath g u (l: list E) v`（边序列），同样可以导出针对 `list E` 的归纳原则

**示例**：从抽象到具体

```coq
(* 抽象层：PathInd1n 是公理 *)
Context {PathInd1n_inst: PathInd1n G V E P path emptypath singlepath concatpath}.

(* 具体层：导出 valid_vpath 的列表归纳原则 *)
Lemma valid_vpath_ind1n: forall g u v (X: list V -> Type),
  (X [u]) ->  (* 基础情况：单点 *)
  (forall w rest e, 
    step_aux g e u w -> 
    valid_vpath g w rest v -> 
    X rest -> 
    X (u :: rest)) ->  (* 归纳步骤 *)
  forall l, valid_vpath g u l v -> X l.
Proof.
  (* 使用 path_ind1n 公理和 vpath 到 P 的对应关系来证明 *)
Admitted.
```

---



---

## 项目结构

```
graph_lib/
├── graph_basic.v              # 图的基本定义 (Graph, GValid, ...)
├── Syntax.v                   # 语法糖和记号定义
├── GraphLib.v                 # 库的统一入口
│
├── reachable/                 # 路径与可达性
│   ├── reachable_basic.v      # 可达性定义 (step, reachable)
│   ├── path.v                 # 路径抽象接口 (Path, EmptyPath, ...)
│   ├── path_basic.v           # 路径基本性质
│   ├── vpath.v                # 顶点路径实现
│   ├── epath.v                # 边路径实现
│   ├── Zweight.v              # 整数权重支持
│   └── reachable_restricted.v # 受限可达性
│
├── directed/                  # 有向图
│   └── rootedtree.v           # 有根树
│
├── undirected/                # 无向图
│   ├── undirected_basic.v     # 无向图基础
│   └── tree.v                 # 无向树
│
├── subgraph/                  # 子图
│   └── subgraph.v             # 子图定义与性质
│
└── examples/                  # 示例应用
    ├── dijkstra.v             # Dijkstra 算法示例
    ├── floyd.v                # Floyd-Warshall 示例
    ├── prim.v                 # Prim 算法示例
    └── kruskal.v              # Kruskal 算法示例
```

---

## 编译与安装

### 前置依赖

- **Coq**: 8.20.1
- **SetsClass**: 集合类型类库
- **RecordUpdate**: 记录更新库
- **MonadLib**: 单子库（用于状态证明）
- **ListLib**: 表库

### 编译

```bash
cd graph_lib
make
```

### 在项目中使用

```coq
Require Import GraphLib.
```

或选择性导入：

```coq
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable_basic.
Require Import GraphLib.path.
```

---

## 设计哲学

### 为什么分离抽象和实现？

1. **证明复用**：在抽象层面证明的定理自动适用于所有具体实现
2. **灵活性**：算法可以根据需要选择最适合的路径表示
   - Dijkstra 使用 vpath（关注访问的顶点）
   - 最小生成树算法使用 epath（关注选择的边）
3. **可扩展性**：可以轻松添加新的路径表示（如带权重的路径）
4. **形式化友好**：Type Class 机制提供了良好的推理支持

### 1n vs n1 的设计理由

不同的算法和定理有不同的"自然方向"：

- **前向算法**（BFS, Dijkstra）：从源点出发探索 → 使用 1n 视角
- **后向算法**（最优子结构证明）：从目标倒推 → 使用 n1 视角
- **双向搜索**：两种视角结合使用

提供对称的两种视角避免了繁琐的方向转换。

---


