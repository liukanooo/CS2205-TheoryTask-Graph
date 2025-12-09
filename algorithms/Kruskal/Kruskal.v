Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic examples.kruskal vpath.
From MaxMinLib Require Import MaxMin.
Require Import Algorithms.MapLib.

Import MonadNotation.
Import SetsNotation.

Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope nat.


Section Kruskal.

(** Kruskal算法用于计算无向连通图的最小生成树。
    核心思想是按边权重从小到大排序，贪心地选择不会形成环的边。
    
    算法流程：
    1. 初始化：边集为空，每个顶点自成一个连通分量
    2. 循环：在所有未处理的边中，选择权重最小且不会形成环的边
    3. 将该边加入生成树
    4. 重复直到边数达到 |V|-1 或没有可选边
    
    循环不变量提示：
    - mst_edges 构成一个森林（无环）
    - mst_edges 的权重之和不超过任何其他可行方案
    - 选择的边满足"安全边"性质
*)

Context {V: Type}
        `{eq_dec: EqDec V eq}
        (g: OriginalGraphType V)
        {origin_gvalid: OriginalGraph_gvalid g}.

Record St: Type := mkSt {
  mst_edges: list (V * V);  (** 当前选中的边集 *)
}.

(** 初始状态：边集为空 *)
Definition initSt: St := {| mst_edges := @nil (V * V) |}.

Instance: Settable St := settable! mkSt <mst_edges>.

(** 将边e加入生成树边集 *)
Definition add_edge_to_mst (e: V * V): program St unit :=
  update' (fun s => s <| mst_edges ::= fun es => e :: es |>).


(** ===== 辅助定义 ===== *)

(** 边集构成的图中，从u到v可达（考虑无向边） *)
Definition connected_by_edges (edges: list (V * V)) (u v: V): Prop :=
  u = v \/
  exists p: list V, 
    length p >= 2 /\
    hd_error p = Some u /\ 
    nth_error p (length p - 1) = Some v /\
    (forall i, i < length p - 1 -> 
      In (nth i p u, nth (S i) p u) edges \/ 
      In (nth (S i) p u, nth i p u) edges).

(** 加入边e后是否会形成环：
    即e的两个端点是否已经通过现有边连通 *)
Definition forms_cycle (s: St) (e: V * V): Prop := 
  let (u, v) := e in
  connected_by_edges s.(mst_edges) u v.

(** 边是有效边（在原图中存在） *)
Definition is_valid_edge (e: V * V): Prop :=
  original_weight g e <> None.

(** 从所有有效且不形成环的边中选择权重最小的 *)
Definition get_min_edge (f: St -> (V * V) -> Prop): program St (V * V) :=
  get (fun s e => min_object_of_subset option_le (fun e => f s e) (original_weight g) e).

(** 可选边：有效边且不形成环 *)
Definition selectable_edge (s: St) (e: V * V): Prop :=
  is_valid_edge e /\ ~ forms_cycle s e.

(** Kruskal主算法：循环直到没有可选边 *)
Definition Kruskal: program St unit :=
  while (fun s => exists e, selectable_edge s e)
    (e <- get_min_edge selectable_edge;;  (* 选择最小权重的可选边 *)
      add_edge_to_mst e                    (* 将边加入边集 *)
    ).


(** ===== 更多辅助定义 ===== *)

(** 边集的总权重 *)
Fixpoint total_weight (edges: list (V * V)): nat :=
  match edges with
  | nil => 0
  | e :: es => 
      match original_weight g e with
      | Some w => w + total_weight es
      | None => total_weight es
      end
  end.

(** 边集是无环的（构成森林） *)
Definition is_acyclic (edges: list (V * V)): Prop :=
  forall e, In e edges -> 
    let (u, v) := e in
    ~ connected_by_edges (remove (prod_eqdec eq_dec eq_dec) e edges) u v.

(** 边集连接了给定顶点集合中的所有顶点 *)
Definition spans_vertices (edges: list (V * V)) (vertices: V -> Prop): Prop :=
  forall u v, u ∈ vertices -> v ∈ vertices -> 
    connected_by_edges edges u v.

(** 图中所有顶点的集合 *)
Definition all_vertices: V -> Prop :=
  fun v => In v (original_vlist g).


(** ===== 最小生成树定义 ===== *)

(** 是生成森林：无环 *)
Definition is_forest (s: St): Prop :=
  is_acyclic s.(mst_edges).

(** 是生成树：无环 + 连接所有顶点 *)
Definition is_spanning_tree (s: St): Prop :=
  is_acyclic s.(mst_edges) /\
  spans_vertices s.(mst_edges) all_vertices.

(** 是最小生成树：是生成树 + 边权重之和最小 *)
Definition is_mst (s: St): Prop :=
  (* 1. mst_edges构成生成树 *)
  is_spanning_tree s /\
  (* 2. 边权重之和最小 *)
  (forall edges', 
    is_acyclic edges' -> 
    spans_vertices edges' all_vertices ->
    total_weight s.(mst_edges) <= total_weight edges').


(** ===== 循环不变量定义 ===== *)

(** 不变量1：mst_edges中的边都是有效边 *)
Definition edges_valid (s: St): Prop :=
  forall e, In e s.(mst_edges) -> is_valid_edge e.

(** 不变量2：mst_edges是无环的（构成森林） *)
Definition edges_acyclic (s: St): Prop :=
  is_acyclic s.(mst_edges).

(** 不变量3：mst_edges可以扩展为某个最小生成树
    即存在一个MST包含当前所有边 *)
Definition extendable_to_mst (s: St): Prop :=
  exists mst_edges_full,
    (forall e, In e s.(mst_edges) -> In e mst_edges_full) /\
    is_acyclic mst_edges_full /\
    spans_vertices mst_edges_full all_vertices /\
    (forall edges',
      is_acyclic edges' ->
      spans_vertices edges' all_vertices ->
      total_weight mst_edges_full <= total_weight edges').

(** 完整的循环不变量 *)
Definition loop_invariant (s: St): Prop :=
  edges_valid s /\
  edges_acyclic s /\
  extendable_to_mst s.

(** 安全边性质：选择的边加入后仍能扩展为MST *)
Definition safe_edge (s: St) (e: V * V): Prop :=
  selectable_edge s e ->
  (forall e', selectable_edge s e' -> 
    option_le (original_weight g e) (original_weight g e')) ->
  extendable_to_mst s ->
  extendable_to_mst (mkSt (e :: s.(mst_edges))).


(** ===== 正确性规范 ===== *)

(** ===== 主定理 =====
    
    证明提示：
    1. 使用 while 循环的 Hoare 规则，以 loop_invariant 作为循环不变量
    2. 证明初始状态满足循环不变量：
       - 空边集是无环的
       - 空边集可以扩展为MST（整个MST就是扩展）
    3. 证明每次循环保持循环不变量：
       a. 选择最小权重的可选边e（使用safe_edge性质）
       b. 加入边后仍满足edges_valid
       c. 加入边后仍满足edges_acyclic（因为我们只选择不形成环的边）
       d. 关键：证明extendable_to_mst被保持（需要证明Kruskal安全边引理）
    4. 证明循环终止时（没有可选边），is_mst成立
       - 如果没有可选边但边集未连通所有顶点，则图不连通
       - 如果图连通，则最终边集就是MST
    5. 关键引理：
       - Kruskal安全边引理：最小权重的不形成环的边是安全边
       - 这保证了贪心选择不会破坏最优性
       - 可以用"交换论证"证明
*)
Theorem Kruskal_correct: 
  Hoare (fun s => s = initSt)
        Kruskal
        (fun _ s => is_mst s).
Admitted.

End Kruskal.