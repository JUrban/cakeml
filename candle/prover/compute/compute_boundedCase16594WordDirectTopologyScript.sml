(*****************************************************************************
 * Direct cv implementation of the compact nonlinear topology stack machine. *
 *                                                                           *
 * The ordinary HOL Light call expresses this algorithm as a cexp program.   *
 * These total, fail-closed functions expose the same data traversal without *
 * paying for a generic compute_eval interpreter at executable run time.     *
 *****************************************************************************)
Theory compute_boundedCase16594WordDirectTopology
Ancestors
  compute_exec
Libs
  bossLib preamble

Definition bounded_case16594_direct_cv_list_length_def:
  bounded_case16594_direct_cv_list_length (Num terminal_value) = 0 /\
  bounded_case16594_direct_cv_list_length (Pair item_value remaining_items) =
    SUC (bounded_case16594_direct_cv_list_length remaining_items)
End

Definition bounded_case16594_direct_boxes_join_def:
  bounded_case16594_direct_boxes_join (Num terminal_value) right_boxes_cv =
      Num 0 /\
  bounded_case16594_direct_boxes_join
      (Pair left_interval left_tail) right_boxes_cv =
    case left_interval of
    | Num malformed_left => Num 0
    | Pair left_lower left_upper =>
        (case right_boxes_cv of
         | Num malformed_right => Num 0
         | Pair right_interval right_tail =>
             (case right_interval of
              | Num malformed_interval => Num 0
              | Pair right_lower right_upper =>
                  Pair (Pair left_lower right_upper)
                    (bounded_case16594_direct_boxes_join
                      left_tail right_tail)))
End

Definition bounded_case16594_direct_boxes_split_exact_from_def:
  bounded_case16594_direct_boxes_split_exact_from current_index axis_index
      (Num terminal_value) left_boxes_cv right_boxes_cv =
    (terminal_value = 0 /\ left_boxes_cv = Num 0 /\
     right_boxes_cv = Num 0) /\
  bounded_case16594_direct_boxes_split_exact_from current_index axis_index
      (Pair root_interval root_tail) left_boxes_cv right_boxes_cv =
    case root_interval of
    | Num malformed_root => F
    | Pair root_lower root_upper =>
        (case left_boxes_cv of
         | Num malformed_left => F
         | Pair left_interval left_tail =>
             (case left_interval of
              | Num malformed_interval => F
              | Pair left_lower left_upper =>
                  (case right_boxes_cv of
                   | Num malformed_right => F
                   | Pair right_interval right_tail =>
                       (case right_interval of
                        | Num malformed_right_interval => F
                        | Pair right_lower right_upper =>
                            (if current_index = axis_index
                             then left_lower = root_lower /\
                                  right_upper = root_upper /\
                                  left_upper = right_lower
                             else left_interval = root_interval /\
                                  right_interval = root_interval) /\
                            bounded_case16594_direct_boxes_split_exact_from
                              (SUC current_index) axis_index root_tail
                              left_tail right_tail))))
End

Definition bounded_case16594_direct_topology_transition_def:
  bounded_case16594_direct_topology_transition dimension token_cv
      encoded_jobs_cv active_stack_cv =
    case token_cv of
    | Num leaf_marker =>
        if leaf_marker = 0 then
          (case encoded_jobs_cv of
           | Num malformed_jobs => NONE
           | Pair encoded_job remaining_jobs =>
               (case encoded_job of
                | Num malformed_job => NONE
                | Pair ignored_outer job_tail =>
                    (case job_tail of
                     | Num malformed_tail => NONE
                     | Pair ignored_center source_boxes =>
                         if bounded_case16594_direct_cv_list_length
                              source_boxes = dimension
                         then SOME (remaining_jobs,
                           Pair source_boxes active_stack_cv)
                         else NONE)))
        else NONE
    | Pair axis_cv marker_cv =>
        (case (axis_cv,marker_cv) of
         | (Num axis_index,Num glue_marker) =>
             if glue_marker = 0 then
               (case active_stack_cv of
                | Num malformed_stack => NONE
                | Pair right_boxes after_right =>
                    (case after_right of
                     | Num malformed_after_right => NONE
                     | Pair left_boxes remaining_stack =>
                         let parent_boxes =
                           bounded_case16594_direct_boxes_join
                             left_boxes right_boxes
                         in
                           if bounded_case16594_direct_cv_list_length
                                parent_boxes = dimension /\
                              0 < axis_index /\ axis_index < dimension + 1 /\
                              bounded_case16594_direct_boxes_split_exact_from
                                1 axis_index parent_boxes left_boxes
                                  right_boxes
                           then SOME (encoded_jobs_cv,
                             Pair parent_boxes remaining_stack)
                           else NONE))
             else NONE
         | _ => NONE)
End

Definition bounded_case16594_direct_topology_run_def:
  bounded_case16594_direct_topology_run dimension
      (Num terminal_value) encoded_jobs_cv active_stack_cv =
    (if terminal_value = 0
     then SOME (encoded_jobs_cv,active_stack_cv)
     else NONE) /\
  bounded_case16594_direct_topology_run dimension
      (Pair token_cv remaining_tokens) encoded_jobs_cv active_stack_cv =
    case bounded_case16594_direct_topology_transition dimension token_cv
        encoded_jobs_cv active_stack_cv of
    | NONE => NONE
    | SOME (remaining_jobs,next_stack) =>
        bounded_case16594_direct_topology_run dimension remaining_tokens
          remaining_jobs next_stack
End

Definition bounded_case16594_direct_topology_result_def:
  bounded_case16594_direct_topology_result
      (Pair malformed_dim dim_tail) token_stream_cv encoded_jobs_cv = NONE /\
  bounded_case16594_direct_topology_result
      (Num dimension) token_stream_cv encoded_jobs_cv =
    (case bounded_case16594_direct_topology_run dimension token_stream_cv
        encoded_jobs_cv (Num 0) of
     | NONE => NONE
     | SOME (remaining_jobs,final_stack) =>
         SOME (Pair (Num 1) (Pair remaining_jobs final_stack)))
End

(* Exact root reconstructed by the authenticated 875-leaf case-16594
   subdivision plan.  Keep this separate from the historical cell-0 result:
   cell 0 is the first leaf, not the root of the complete subdivision. *)
Definition bounded_case16594_complete875_root_boxes_def:
  bounded_case16594_complete875_root_boxes =
    Pair
      (Pair (Pair (Pair (Num 6469) (Num 0)) (Num 1249))
        (Pair (Pair (Num 2032128000001) (Num 0))
          (Num 319999999999)))
    (Pair
      (Pair (Pair (Pair (Num 4) (Num 0)) (Num 0))
        (Pair (Pair (Num 1656064000001) (Num 0))
          (Num 319999999999)))
    (Pair
      (Pair (Pair (Pair (Num 6469) (Num 0)) (Num 1249))
        (Pair (Pair (Num 2032128000001) (Num 0))
          (Num 319999999999)))
    (Pair
      (Pair (Pair (Pair (Num 4) (Num 0)) (Num 0))
        (Pair (Pair (Num 1656064000001) (Num 0))
          (Num 319999999999)))
    (Pair
      (Pair (Pair (Pair (Num 423903) (Num 0)) (Num 39999))
        (Pair (Pair (Num 3883216000001) (Num 0))
          (Num 319999999999)))
    (Pair
      (Pair (Pair (Pair (Num 6469) (Num 0)) (Num 1249))
        (Pair (Pair (Num 2032128000001) (Num 0))
          (Num 319999999999)))
      (Num 0))))))
End

Definition bounded_case16594_complete875_topology_result_def:
  bounded_case16594_complete875_topology_result =
    Pair (Num 1)
      (Pair (Num 0)
        (Pair bounded_case16594_complete875_root_boxes (Num 0)))
End

Theorem bounded_case16594_complete875_root_width_six:
  bounded_case16594_direct_cv_list_length
    bounded_case16594_complete875_root_boxes = 6
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_direct_topology_two_leaf_glue_test:
  bounded_case16594_direct_topology_result (Num 1)
    (Pair (Num 0)
      (Pair (Num 0)
        (Pair (Pair (Num 1) (Num 0)) (Num 0))))
    (Pair
      (Pair (Num 7)
        (Pair (Num 8)
          (Pair (Pair (Num 0) (Num 1)) (Num 0))))
      (Pair
        (Pair (Num 9)
          (Pair (Num 10)
            (Pair (Pair (Num 1) (Num 2)) (Num 0))))
        (Num 0))) =
  SOME
    (Pair (Num 1)
      (Pair (Num 0)
        (Pair
          (Pair (Pair (Num 0) (Num 2)) (Num 0))
          (Num 0))))
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_direct_topology_single_leaf_six_test:
  bounded_case16594_direct_topology_result (Num 6)
    (Pair (Num 0) (Num 0))
    (Pair
      (Pair (Num 7)
        (Pair (Num 8)
          (Pair (Num 1)
            (Pair (Num 2)
              (Pair (Num 3)
                (Pair (Num 4)
                  (Pair (Num 5)
                    (Pair (Num 6) (Num 0)))))))))
      (Num 0)) =
  SOME
    (Pair (Num 1)
      (Pair (Num 0)
        (Pair
          (Pair (Num 1)
            (Pair (Num 2)
              (Pair (Num 3)
                (Pair (Num 4)
                  (Pair (Num 5)
                    (Pair (Num 6) (Num 0)))))))
          (Num 0))))
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_direct_topology_rejects_bad_boundary_test:
  bounded_case16594_direct_topology_result (Num 1)
    (Pair (Num 0)
      (Pair (Num 0)
        (Pair (Pair (Num 1) (Num 0)) (Num 0))))
    (Pair
      (Pair (Num 7)
        (Pair (Num 8)
          (Pair (Pair (Num 0) (Num 1)) (Num 0))))
      (Pair
        (Pair (Num 9)
          (Pair (Num 10)
            (Pair (Pair (Num 2) (Num 3)) (Num 0))))
        (Num 0))) = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
