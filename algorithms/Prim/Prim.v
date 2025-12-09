Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic examples.prim vpath.
From MaxMinLib Require Import MaxMin. 
Require Import Algorithms.MapLib.

Import SetsNotation.
Import MonadNotation.

Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope nat.

Section Prim.

(** Prim算法用于计算无向连通图的最小生成树。
    核心思想是贪心地选择连接"树内顶点"和"树外顶点"的最小权重边。
    
    算法流程：
    1. 初始化：选择一个起始顶点S，将其加入树中
    2. 循环：在所有"切边"（一端在树内，一端在树外）中选择权重最小的边
    3. 将该边和对应的树外顶点加入生成树
    4. 重复直到所有可达顶点都在树中
    
    循环不变量提示：
    - in_tree 包含的顶点通过 mst_edges 构成一棵树
    - mst_edges 是当前 in_tree 上的最小生成树的边集
    - 每次选择的切边满足"安全边"性质
*)

Context {V: Type}
        `{eq_dec: EqDec V eq}
        (g: OriginalGraphType V)
        {origin_gvalid: OriginalGraph_gvalid g}.

Record St: Type := mkSt_s {
  in_tree: V -> Prop;      (** 当前在生成树中的顶点集合 *)
  mst_edges: list (V * V); (** 当前生成树的边集 *)
}.

Context (Source: V)
        (validSource: vvalid g Source).

(** 初始状态：只有源点S在树中，边集为空 *)
Definition initSt: St := {|
  in_tree := [Source];
  mst_edges := @nil (V * V);
|}.

Instance: Settable St := settable! mkSt_s <in_tree; mst_edges>.

(** 切边定义：一端在树内，一端在树外的边 *)
Definition is_cut_edge (s: St) (e: V * V): Prop :=
  let (u, v) := e in
  step g u v /\
  ((u ∈ s.(in_tree) /\ ~ v ∈ s.(in_tree))).

(** 从所有切边中选择权重最小的边 *)
Definition get_min_cut_edge (f: St -> (V * V) -> Prop): program St (V * V) :=
  get (fun s e => min_object_of_subset option_le (fun e => is_cut_edge s e) (original_weight g) e).

(** 将顶点v加入生成树 *)
Definition add_to_tree (v: V): program St unit :=
  update' (fun s => s <| in_tree ::= fun t => t ∪ [v] |>).

(** 将边e加入生成树边集 *)
Definition add_to_mst_edges (e: V * V): program St unit :=
  update' (fun s => s <| mst_edges ::= fun es => e :: es |>).

(** Prim主算法：循环直到没有切边（所有可达顶点都在树中） *)
Definition Prim: program St unit :=
  while (fun s => exists e, is_cut_edge s e) 
    ( e <- get_min_cut_edge is_cut_edge ;;  (* 选择最小权重的切边 *)
      let (u, v) := e in
        add_to_tree v;;                      (* 将新顶点加入树 *)
        add_to_mst_edges e                   (* 将边加入边集 *)
    ).


(** ===== 辅助定义 ===== *)

(** 边集的总权重 *)
Fixpoint total_weight (edges: list (V * V)): nat :=
  match edges with
  | nil => 0
  | e :: es => 
      match original_weight g e with
      | Some w => w + total_weight es
      | None => total_weight es  (* 不应该发生 *)
      end
  end.

(** 边集构成的图中，从u到v可达 *)
Definition connected_by_edges (edges: list (V * V)) (u v: V): Prop :=
  exists p, 
    (forall i, i < length p - 1 -> 
      In (nth i p u, nth (S i) p v) edges \/ In (nth (S i) p v, nth i p u) edges) /\
    hd_error p = Some u /\ 
    nth_error p (length p - 1) = Some v.

(** 边集是无环的（构成森林） *)
Definition is_acyclic (edges: list (V * V)): Prop :=
  forall e, In e edges -> 
    let (u, v) := e in
    ~ connected_by_edges (remove (prod_eqdec eq_dec eq_dec) e edges) u v.

(** 边集连接了给定顶点集合中的所有顶点 *)
Definition spans_vertices (edges: list (V * V)) (vertices: V -> Prop): Prop :=
  forall u v, u ∈ vertices -> v ∈ vertices -> 
    connected_by_edges edges u v.


(** ===== 最小生成树定义 ===== *)

(** 是生成树：无环 + 连接所有in_tree中的顶点 *)
Definition is_spanning_tree (s: St): Prop :=
  is_acyclic s.(mst_edges) /\
  spans_vertices s.(mst_edges) s.(in_tree) /\
  Source ∈ s.(in_tree).

(** 是最小生成树：是生成树 + 边权重之和最小 *)
Definition is_mst (s: St): Prop :=
  (* 1. 所有从S可达的顶点都在in_tree中 *)
  (forall v, reachable g Source v -> v ∈ s.(in_tree)) /\
  (* 2. mst_edges构成in_tree上的生成树 *)
  is_spanning_tree s /\
  (* 3. 边权重之和最小 *)
  (forall edges', 
    is_acyclic edges' -> 
    spans_vertices edges' s.(in_tree) ->
    total_weight s.(mst_edges) <= total_weight edges').


(** ===== 循环不变量定义 ===== *)

(** 不变量1：mst_edges中的边都是有效边且端点都在in_tree中 *)
Definition edges_valid (s: St): Prop :=
  forall e, In e s.(mst_edges) ->
    let (u, v) := e in
    step g u v /\ u ∈ s.(in_tree) /\ v ∈ s.(in_tree).

(** 不变量2：mst_edges是无环的 *)
Definition edges_acyclic (s: St): Prop :=
  is_acyclic s.(mst_edges).

(** 不变量3：mst_edges连接了in_tree中的所有顶点 *)
Definition edges_connected (s: St): Prop :=
  spans_vertices s.(mst_edges) s.(in_tree).

(** 不变量4：|mst_edges| = |in_tree| - 1（树的性质） *)
Definition edges_count_correct (s: St): Prop :=
  exists n, 
    length s.(mst_edges) = n /\
    (forall l, (forall v, In v l <-> v ∈ s.(in_tree)) -> NoDup l -> length l = S n).

(** 不变量5：mst_edges是in_tree上的最小生成树（关键不变量） *)
Definition partial_mst (s: St): Prop :=
  forall edges',
    is_acyclic edges' ->
    spans_vertices edges' s.(in_tree) ->
    total_weight s.(mst_edges) <= total_weight edges'.

(** 完整的循环不变量 *)
Definition loop_invariant (s: St): Prop :=
  Source ∈ s.(in_tree) /\
  edges_valid s /\
  edges_acyclic s /\
  edges_connected s /\
  partial_mst s.

(** 安全边性质：选择的切边加入后仍能保持最小生成树性质 *)
Definition safe_edge (s: St) (e: V * V): Prop :=
  is_cut_edge s e ->
  (forall e', is_cut_edge s e' -> 
    option_le (original_weight g e) (original_weight g e')) ->
  partial_mst s ->
  let (u, v) := e in
  partial_mst (mkSt_s (s.(in_tree) ∪ [v]) (e :: s.(mst_edges))).


(** ===== 正确性规范 ===== *)

(** ===== 主定理 =====
    
    证明提示：
    1. 使用 while 循环的 Hoare 规则，以 loop_invariant 作为循环不变量
    2. 证明初始状态满足循环不变量
    3. 证明每次循环保持循环不变量：
       a. 选择最小权重的切边e（使用safe_edge性质）
       b. 将新顶点加入in_tree后，仍满足edges_valid
       c. 加入边后，仍满足edges_acyclic（因为v之前不在树中）
       d. 加入边后，仍满足edges_connected
       e. 关键：证明partial_mst被保持（需要证明切边引理）
    4. 证明循环终止时（没有切边），is_mst成立
    5. 关键引理：
       - 切边引理：在任意切割中，最小权重的切边是安全边
       - 这保证了贪心选择不会破坏最优性
*)
Theorem Prim_correct: 
  Hoare (fun s => s = initSt)
        Prim
        (fun _ s => is_mst s).
Admitted.

End Prim.

