Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic examples.dijkstra vpath.
From MaxMinLib Require Import MaxMin.
Require Import Algorithms.MapLib.
  

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope nat.

Section Dijkstra.

(** Dijkstra算法用于计算单源最短路径。
    核心思想是贪心地选择当前距离最小的未访问顶点，然后松弛其邻居。
    
    算法流程：
    1. 初始化：源点距离为0，其他顶点距离为无穷大（None）
    2. 循环：选择距离最小的未访问顶点u，标记为已访问
    3. 对u的每个邻居v，尝试通过u松弛：dist[v] = min(dist[v], dist[u] + w(u,v))
    4. 重复直到所有可达顶点都被访问
    
    循环不变量提示：
    - 已访问顶点的dist值是最终的最短距离
    - 未访问顶点的dist值是只经过已访问顶点的最短距离
    - 每次选择的顶点u，其dist[u]已经是最短距离
*)

Context {V: Type}
        `{eq_dec: EqDec V eq}
        (g: OriginalGraphType V)
        {origin_gvalid: OriginalGraph_gvalid g}
        {P: Type}
        {path: path.Path (OriginalGraphType V) V (V * V) P}.

Record St: Type := mkSt {
  visited: V -> Prop;  (** 已访问的顶点集合 *)
  dist: V -> option nat;  (** 当前记录的距离，None表示不可达 *)
}.

Context (S: V)
        (validS: vvalid g S).

(** 初始状态：源点距离为0，其他顶点距离为None *)
Definition initSt: St := {|
  visited := ∅;
  dist := fun v => if eq_dec v S then Some 0 else None;
|}.

Instance: Settable St := settable! mkSt <visited; dist>.

(** 将顶点u标记为已访问 *)
Definition visit_u (u: V): program St unit :=
  update' (fun s => s <| visited ::= fun x => x ∪ [u] |>).

(** 从满足条件f的顶点中选择dist值最小的顶点 *)
Definition get_min_dist (f: St -> V -> Prop): program St V :=
  get (fun s u => min_object_of_subset option_le (fun v => f s v) (s.(dist)) u).

(** 未访问且有有限距离的顶点 *)
Definition unvisited_u (S: St) (u: V): Prop :=
  ~ u ∈ S.(visited) /\ S.(dist) u <> None.

(** 松弛操作：dist[v] = min(dist[v], dist[u] + w(u,v)) *)
Definition relax (u v: V): program St unit :=
  update' (fun s => s <| dist ::= fun dist0 =>
    v !-> (option_min (dist0 v) (option_plus (dist0 u) (original_weight g (u, v)))); dist0 |>).

(** Dijkstra主算法：循环直到所有可达顶点都被访问 *)
Definition Dijkstra: program St unit :=
  while (fun s => exists u, unvisited_u s u)
    (
      u <- get_min_dist unvisited_u;;  (* 选择距离最小的未访问顶点 *)
      visit_u u;;                       (* 标记为已访问 *)
      forset (fun v => step g u v)      (* 对u的每个邻居v *)
        (relax u)                       (* 进行松弛 *)
    ).


(** ===== 循环不变量定义 ===== *)

(** 核心不变量1：已访问顶点的dist是最终最短距离 *)
Definition visited_dist_correct (s: St): Prop :=
  forall v n, v ∈ s.(visited) -> s.(dist) v = Some n -> 
    min_weight_distance weight g S v n.

(** 核心不变量2：未访问顶点的dist是只经过已访问顶点的最短距离 *)
Definition unvisited_dist_optimal (s: St): Prop :=
  forall v n, ~ v ∈ s.(visited) -> s.(dist) v = Some n ->
    min_weight_distance_in_vset weight g S v s.(visited) n.

(** 核心不变量3：如果dist为None，则从源点不可达（只经过已访问顶点） *)
Definition none_means_unreachable (s: St): Prop :=
  forall v, s.(dist) v = None ->
    forall p, ~ valid_vpath_in_vset g S p v s.(visited).

(** 核心不变量4：源点始终在visited中或dist[S]=0 *)
Definition source_invariant (s: St): Prop :=
  s.(dist) S = Some 0.

(** 完整的循环不变量 *)
Definition loop_invariant (s: St): Prop :=
  visited_dist_correct s /\
  unvisited_dist_optimal s /\
  none_means_unreachable s /\
  source_invariant s.

(** 贪心选择性质：每次选择的顶点u，其dist[u]已经是最短距离
    这是Dijkstra算法正确性的关键 *)
Definition greedy_choice_correct (s: St) (u: V): Prop :=
  unvisited_u s u ->
  (forall v, unvisited_u s v -> option_le (s.(dist) u) (s.(dist) v)) ->
  forall n, s.(dist) u = Some n -> min_weight_distance weight g S u n.

(** ===== 正确性规范 ===== *)

(** 可达性健全性：如果dist记录了距离n，则n确实是从S到v的最短距离 *)
Definition distance_reachable_soundness (s: St): Prop :=
  forall v n, s.(dist) v = Some n -> min_weight_distance weight g S v n. 

(** 可达性完备性：如果存在从S到v的最短距离n，则dist正确记录 *)
Definition distance_reachable_completeness (s: St): Prop :=
  forall v n, min_weight_distance weight g S v n -> s.(dist) v = Some n.

(** 不可达健全性：如果v从S不可达，则dist[v]=None *)
Definition distance_unreachable_soundness (s: St): Prop :=
  forall v, ~ reachable g S v -> s.(dist) v = None.
  
(** 不可达完备性：如果dist[v]=None，则v从S不可达 *)
Definition distance_unreachable_completeness (s: St): Prop :=
  forall v, s.(dist) v = None -> ~ reachable g S v.
  
Definition distance_sound (s: St): Prop :=
  distance_reachable_soundness s /\ distance_unreachable_soundness s.

Definition distance_complete (s: St): Prop :=
  distance_reachable_completeness s /\ distance_unreachable_completeness s.

Definition distance_correct (s: St): Prop :=
  distance_sound s /\ distance_complete s.

(** ===== 主定理 =====
    
    证明提示：
    1. 使用 while 循环的 Hoare 规则，以 loop_invariant 作为循环不变量
    2. 证明初始状态满足循环不变量（initSt满足loop_invariant）
    3. 证明每次循环保持循环不变量：
       a. 选择最小距离的未访问顶点u（使用greedy_choice_correct）
       b. 将u加入visited后，visited_dist_correct仍成立
       c. 松弛操作后，unvisited_dist_optimal仍成立
    4. 证明循环终止时（无未访问的可达顶点），distance_correct成立
    5. 关键引理：
       - shortest_path_triangle_inequality: 三角不等式
       - shortest_path_prefix_shortest: 最短路径的前缀也是最短路径
       - greedy_choice_correct: 贪心选择的正确性
*)
Theorem Dijkstra_correct:
  Hoare (fun s => s = initSt)
        Dijkstra
        (fun _ s => distance_correct s).
Admitted.
  

End Dijkstra.