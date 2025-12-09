
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic examples.floyd path vpath.
From MaxMinLib Require Import MaxMin.
Require Import Algorithms.MapLib.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope nat.


Section Floyd.

(** Floyd算法用于计算图中所有顶点对之间的最短路径。
    核心思想是通过逐步允许使用更多的顶点作为中间点来优化路径。
    
    循环不变量提示：
    - k-循环不变量：dist[i][j] = shortestPath(i, j, k)
      即 dist[i][j] 是从 i 到 j 只经过前 k 个顶点作为中间点的最短距离
    - i-循环不变量：
      * 对于 i0 < i: dist[i0][j] = shortestPath(i0, j, k)
      * 对于 i0 >= i: dist[i0][j] = shortestPath(i0, j, k-1)
*)

Context {V: Type}
        `{eq_dec: EqDec V eq}
        (g: OriginalGraphType V)
        {origin_gvalid: OriginalGraph_gvalid g}
        {P: Type}
        {path: path.Path (OriginalGraphType V) V (V * V) P}.

Notation step := (step g).
Notation reachable := (reachable g).

Record St: Type := mkSt {
  dist: (V * V) -> option nat;
}.

Definition initSt: St := {|
  dist := original_weight g;
|}.

Instance: Settable St := settable! mkSt <dist>.


(** 松弛操作：dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j]) *)
Definition update_dist (i j k: V): program St unit :=
  update' (fun s => s <| dist ::= fun dist0 =>
    (i, j) !-> (option_min (dist0 (i, j)) (option_plus (dist0 (i, k)) (dist0 (k, j)))); dist0 |>).

(** 对于固定的中间点k，遍历所有顶点对(i,j)进行松弛 *)
Definition Floyd_k (k: V): program St unit :=
    list_iter (original_vlist g) (fun i =>
      list_iter (original_vlist g) (fun j =>
          update_dist i j k)).

(** Floyd主算法：遍历所有可能的中间点k *)
Definition Floyd: program St unit :=
  list_iter (original_vlist g) Floyd_k.


(** ===== 循环不变量定义 ===== *)

(** 辅助定义：前k个顶点构成的集合 *)
Definition first_k_vertices (k: nat): V -> Prop :=
  fun v => In v (firstn k (original_vlist g)).

(** k-循环不变量：
    dist[i][j] 存储的是从 i 到 j 只经过前 k 个顶点作为中间点的最短距离 *)
Definition k_loop_invariant (k: nat) (s: St): Prop :=
  (* 对于可达的顶点对：dist正确记录限制距离 *)
  (forall i j n, 
    s.(dist) (i, j) = Some n -> 
    min_weight_distance_in_vset weight g i j (first_k_vertices k) n) /\
  (* 对于不可达的顶点对：dist为None *)
  (forall i j,
    s.(dist) (i, j) = None ->
    forall p, ~ valid_vpath_in_vset g i p j (first_k_vertices k)).

(** i-循环不变量（外层i循环已处理的部分使用新k，未处理部分使用旧k-1）：
    - 对于 i0 < i（已处理）: dist[i0][j] = shortestPath(i0, j, k)
    - 对于 i0 >= i（未处理）: dist[i0][j] = shortestPath(i0, j, k-1) *)
Definition i_loop_invariant (k: nat) (processed_i: list V) (s: St): Prop :=
  (* 已处理的行：使用前k个顶点 *)
  (forall i j n, 
    In i processed_i ->
    s.(dist) (i, j) = Some n -> 
    min_weight_distance_in_vset weight g i j (first_k_vertices k) n) /\
  (* 未处理的行：使用前k-1个顶点 *)
  (forall i j n, 
    ~ In i processed_i ->
    s.(dist) (i, j) = Some n -> 
    min_weight_distance_in_vset weight g i j (first_k_vertices (k - 1)) n).

(** j-循环不变量（固定i，外层j循环已处理的部分使用新k，未处理部分使用旧k-1） *)
Definition j_loop_invariant (k: nat) (i: V) (processed_j: list V) (s: St): Prop :=
  (* 当前行i中已处理的列：使用前k个顶点 *)
  (forall j n, 
    In j processed_j ->
    s.(dist) (i, j) = Some n -> 
    min_weight_distance_in_vset weight g i j (first_k_vertices k) n) /\
  (* 当前行i中未处理的列：使用前k-1个顶点 *)
  (forall j n, 
    ~ In j processed_j ->
    s.(dist) (i, j) = Some n -> 
    min_weight_distance_in_vset weight g i j (first_k_vertices (k - 1)) n).

(** 初始状态的不变量：dist[i][j] = shortestPath(i, j, 0)
    即只考虑直接边，不经过任何中间点 *)
Definition init_invariant (s: St): Prop :=
  k_loop_invariant 0 s.

(** 终止状态的不变量：dist[i][j] = shortestPath(i, j, |V|)
    即经过所有顶点，等价于真正的最短距离 *)
Definition final_invariant (s: St): Prop :=
  k_loop_invariant (length (original_vlist g)) s.


(** ===== 正确性规范 ===== *)

(** 可达性健全性：如果dist记录了距离n，则n确实是最短距离 *)
Definition distance_reachable_soundness (s: St): Prop :=
  forall u v n, s.(dist) (u, v) = Some n -> min_weight_distance weight g u v n.

(** 可达性完备性：如果存在最短距离n，则dist正确记录 *)
Definition distance_reachable_completeness (s: St): Prop :=
  forall u v n, min_weight_distance weight g u v n -> s.(dist) (u, v) = Some n.

(** 不可达健全性：如果dist为None，则确实不可达 *)
Definition distance_unreachable_soundness  (s: St): Prop :=
  forall u v, s.(dist) (u, v) = None -> ~ reachable u v.

(** 不可达完备性：如果不可达，则dist为None *)
Definition distance_unreachable_completeness (s: St): Prop :=
  forall u v, ~ reachable u v -> s.(dist) (u, v) = None.

Definition distance_sound (s: St): Prop :=
  distance_reachable_soundness s /\ distance_unreachable_soundness s.

Definition distance_complete (s: St): Prop :=
  distance_reachable_completeness s /\ distance_unreachable_completeness s.

Definition distance_correct (s: St): Prop :=
  distance_sound s /\ distance_complete s.

(** ===== 主定理 =====
    
    证明提示：
    1. 使用 list_iter 的 Hoare 规则展开循环
    2. 对k-循环使用不变量：dist[i][j] 表示只经过前k个顶点的最短距离
    3. 关键引理：
       - shortest_path_segment: 最短路径的分割性质
       - shortest_path_triangle_inequality: 三角不等式
       - path_in_vset_mono: 路径集合的单调性
*)
Theorem Floyd_correct: 
  Hoare (fun s => s = initSt)
        Floyd
        (fun _ s => distance_correct s).
Proof. 
Admitted.


End Floyd.