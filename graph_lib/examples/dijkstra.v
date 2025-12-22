Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From MaxMinLib Require Import MaxMin Interface.

Import SetsNotation.

Local Open Scope sets.
Local Open Scope Z.

(** 
  Dijkstra 算法证明所需的辅助引理库
  
  本文件提供 Dijkstra 算法正确性证明所需的所有引理，
  使用抽象的 Path Type Class 定义。
  
  核心证明逻辑依赖于以下不变量（Invariant）：
  1. 对于所有已访问集合 S 中的顶点 u，D[u] 是全局最短路径。
  2. 对于所有未访问顶点 v，D[v] 是只经过 S 中的中间顶点的最短路径。
*)

Section dijkstra.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        (g: G).

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

(** 关键假设：Dijkstra 算法仅适用于非负权重的图 *)
Context {src: V}
        (valid_src: vvalid g src).
Context {nonneg_weights: forall e, Z_op_le (Some 0) (weight g e)}.

Notation step := (step g).
Notation reachable := (reachable g).


(** ===== 0. 基础辅助引理 ===== *)

(** 引理1: 路径权重的非负性 (由边权重非负推出) *)
Lemma path_weight_nonneg: forall p,
  path_valid g p ->
  Z_op_le (Some 0) (path_weight g p).
Proof. 
  intros. 
  unfold path_weight. 
  induction (edge_in_path p).
  - simpl. lia. 
  - rewrite map_cons. 
    rewrite Zlist_sum_cons.
    pose proof nonneg_weights a. 
    destruct (weight g a); destruct (Zlist_sum (map (weight g) l)); simpl in *; auto. 
    lia.
Qed.
  
(** 引理2：路径拼接的权重等于两段路径权重之和 *)
Lemma path_concat_weight: 
  forall (p1 p2: P),
    path_valid g p1 ->
    path_valid g p2 ->
    tail p1 = head p2 ->
    path_weight g (concat_path p1 p2) = Z_op_plus (path_weight g p1) (path_weight g p2).
Proof.
  intros.
  unfold path_weight. 
  rewrite concat_path_edge.
  rewrite map_app.
  rewrite Zlist_sum_app.
  reflexivity.
Qed.

(** 引理3: 路径扩展权重单调性 (Dijkstra 核心性质), 即路径的拼接会使路径的权重和增加 *)
Lemma path_weight_monotone_prefix: forall p1 p2,
  path_valid g p1 ->
  path_valid g p2 ->
  tail p1 = head p2 ->
  Z_op_le (path_weight g p1) (path_weight g (concat_path p1 p2)).
Proof.
  intros.
  rewrite path_concat_weight; auto.
  pose proof path_weight_nonneg p1 H.
  pose proof path_weight_nonneg p2 H0.
  destruct (path_weight g p1); destruct (path_weight g p2); simpl in *; auto.
  lia.
Qed.


(** ===== 1. 初始化性质 ===== *)

(** 引理4:
  对于源点 src：
  - dist[src] = 0，且这是真正的最短距离（假设无负环，这由非负权重保证）
*)
Lemma init_dist_source_correct: 
  min_weight_distance g src src (Some 0).
Proof.
  intros.
  unfold min_weight_distance.
  left. split; [|simpl; auto]. 
  assert (Hweight: path_weight g (empty_path src) = Some 0).
  { unfold path_weight. 
    erewrite empty_path_edge; eauto. } 
  exists (empty_path src); split; auto. 
  split. 
  * split; [|split]. 
    + apply empty_path_valid. 
    + apply Some_inversion. 
      erewrite (head_valid g); [|apply empty_path_valid]. 
      rewrite empty_path_vertex. 
      reflexivity. 
    + apply Some_inversion. 
      erewrite (tail_valid g); [|apply empty_path_valid]. 
      rewrite empty_path_vertex. 
      reflexivity. 
  * intros. 
    rewrite Hweight. 
    apply path_weight_nonneg. 
    apply H. 
Qed.

(** 引理5:
  对于其他顶点 v ≠ src，初始状态下通过空集不可达
*)
Lemma init_dist_others_unreachable: forall (v: V),
  v <> src ->
  min_weight_distance_in_vset g src v ∅ None.
Admitted.


(** ===== 2. 路径结构引理 (关键分解) ===== *)

(**
  First-Exit Decomposition (首次离开分解引理)
  
  这是证明 Dijkstra 贪心选择性质最关键的步骤。
  如果一条从 src 到 u 的路径 p (u ∉ visited) 存在，且 src ∈ visited，
  那么 p 可以分解为 p_pre ++ (x, y) ++ p_rem，其中：
  1. p_pre 完全在 visited 内部 (中间节点 ∈ visited，终点 x ∈ visited)
  2. (x, y) 是第一条离开 visited 的边 (x ∈ visited, y ∉ visited)
  3. p_rem 是剩余路径
*)
Lemma path_first_exit_decomposition: 
  forall (u: V) (p: P) (visited: V -> Prop),
    path_valid g p ->
    head p = src ->
    tail p = u ->
    src ∈ visited ->
    ~ u ∈ visited ->
    exists p_pre x y e p_rem,
      (* 结构分解 *)
      p = concat_path (concat_path p_pre (single_path x y e)) p_rem /\
      path_valid g p_pre /\
      path_valid g p_rem /\
      step_aux g e x y /\
      (* 集合性质 *)
      is_path_through_vset g p_pre src x visited /\  (* p_pre 中间点在 visited 中 *)
      x ∈ visited /\
      ~ y ∈ visited. (* y 是第一个未访问点 *)
Admitted.


(** ===== 3. 松弛操作 (Relaxation) ===== *)

(**
  松弛操作保持不变量 2 (Invariant 2 Preservation)
  
  假设：
  - dist[u] 是 src 到 u 的全局最短距离
  - old_dist_v 是只经过 visited 的 src 到 v 的最短距离
  - 考虑边 e: u -> v
  
  则：min(old_dist_v, dist[u] + w_e) 是只经过 visited ∪ {u} 的最短距离
*)
Lemma dijkstra_relax_correct:
  forall (u v: V) (visited: V -> Prop) (e: E) 
         (dist_u old_dist_v w_e: option Z),
    (* 前提 *)
    u ∈ visited ->
    step_aux g e u v ->
    weight g e = w_e ->
    (* 状态假设 *)
    min_weight_distance g src u dist_u ->
    min_weight_distance_in_vset g src v visited old_dist_v ->
    (* 结论 *)
    min_weight_distance_in_vset g src v (visited ∪ [u]) 
      (Z_op_min old_dist_v (Z_op_plus dist_u w_e)).
Admitted.


(** ===== 4. 贪心选择 (Greedy Step) ===== *)

(**
  贪心选择正确性 (Invariant 1 Extension)
  
  假设：
  - Invariant 1: 已访问点 dist 正确
  - Invariant 2: 未访问点 dist 是受限最短距离 (via visited)
  - u 是未访问点中 dist 最小的
  
  则：dist[u] 也是全局最短距离
*)
Lemma greedy_choice_correct:
  forall (u: V) (visited: V -> Prop) (dist: V -> option Z),
    (* 假设：src 已经被访问 (保证 visited 非空，或者 src=u 特判) *)
    src ∈ visited ->
    (* Invariant 1 *)
    (forall v, v ∈ visited -> min_weight_distance g src v (dist v)) ->
    (* Invariant 2 *)
    (forall v, ~ v ∈ visited -> min_weight_distance_in_vset g src v visited (dist v)) ->
    (* u 的选择条件 *)
    ~ u ∈ visited ->
    dist u <> None ->
    (forall v, ~ v ∈ visited -> Z_op_le (dist u) (dist v)) -> (* dist u 最小 *)
    
    (* 结论：dist[u] 是全局最短距离 *)
    min_weight_distance g src u (dist u).
Proof.
  intros.
  (* 
    证明思路草稿：
    1. 设 global_min 为真正的最短距离。显然 global_min <= dist[u] (因为 dist[u] 对应一条具体路径)。
    2. 我们需要证明 dist[u] <= global_min。
    3. 取真正的最短路径 p_opt。
    4. 应用 path_first_exit_decomposition 分解 p_opt。
       找到第一个离开 visited 的点 y (可能 y=u)。
       p_opt = p_pre ++ (x,y) ++ ...
    5. 分析 dist[y]:
       - dist[y] <= weight(p_pre ++ (x,y))   (由 Invariant 2)
       - weight(p_pre ++ (x,y)) <= weight(p_opt) (由非负权重单调性)
    6. 分析 u 和 y 的关系:
       - dist[u] <= dist[y] (由 u 的最小性选择)
    7. 串联不等式:
       dist[u] <= dist[y] <= weight(prefix) <= weight(p_opt) = global_min
    8. 得证 dist[u] = global_min.
  *)
Admitted.


(** ===== 5. 终止与完备性 ===== *)

(**
  当所有有限距离的顶点都被访问后，算法结果正确。
*)
Lemma termination_implies_soundness:
  forall (visited: V -> Prop) (dist: V -> option Z),
    (* 循环不变量保持 *)
    (forall v, v ∈ visited -> min_weight_distance g src v (dist v)) ->
    (forall v, ~ v ∈ visited -> min_weight_distance_in_vset g src v visited (dist v)) ->
    (* 终止状态：未访问的节点都是不可达的 (dist = None) *)
    (forall v, ~ v ∈ visited -> dist v = None) ->
    
    (* 结论：对于任意 v，dist v 是正确的最短距离 *)
    forall v, min_weight_distance g src v (dist v).
Proof.
  (* 
    对于 visited 中的点，由 Invariant 1 直接得证。
    对于未 visited 的点，dist v = None。
    需证明实际上也不可达。
    假设存在路径，必然要离开 visited。
    利用 First-Exit 分解，第一个离开点 y 的 dist[y] 应该是有限的。
    但这与 "未访问点 dist 均为 None" 矛盾。
  *)
Admitted.


(** ===== 6. 辅助工具引理 ===== *)

(** 三角不等式 (用于通用的距离性质推导) *)
Lemma triangle_inequality:
  forall (u v w: V) (d_uw d_uv d_vw: option Z),
    min_weight_distance g u w d_uw ->
    min_weight_distance g u v d_uv ->
    min_weight_distance g v w d_vw ->
    Z_op_le d_uw (Z_op_plus d_uv d_vw).
Admitted.

(** 集合单调性 *)
Lemma min_distance_vset_monotone:
  forall (u v: V) (vset1 vset2: V -> Prop) (d1 d2: option Z),
    min_weight_distance_in_vset g u v vset1 d1 ->
    min_weight_distance_in_vset g u v vset2 d2 ->
    vset1 ⊆ vset2 ->
    Z_op_le d2 d1.
Admitted.

End dijkstra.