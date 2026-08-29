(*
  Finish translation of the 64-bit version of the compiler.
*)
Theory compiler64Prog[no_sig_docs]
Ancestors
  mipsProg compiler export ml_translator basis_ffi[qualified]
Libs
  preamble ml_translatorLib cfLib basis

open preamble
     mipsProgTheory compilerTheory
     exportTheory
     ml_translatorLib ml_translatorTheory
open cfLib basis

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "mipsProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "compiler64Prog");
val _ = ml_translatorLib.use_sub_check true;

val _ = (ml_translatorLib.trace_timing_to
         := SOME "compiler64Prog_translate_timing.txt")

val () = Globals.max_print_depth := 15;

val () = use_long_names := true;

val spec64 = INST_TYPE[alpha|->``:64``]

val res = translate $ errorLogMonadTheory.return_def;
val res = translate $ errorLogMonadTheory.bind_def;
val res = translate $ errorLogMonadTheory.log_def;
val res = translate $ errorLogMonadTheory.error_def;

val res = translate $ listTheory.OPT_MMAP_def;

Theorem OPT_MMAP_eq_MAP[local]:
  OPT_MMAP f xs = (OPT_MMAP I o MAP f) xs
Proof
  simp [miscTheory.OPT_MMAP_MAP_o]
QED

(* move recursion out of OPT_MMAP to aid the translator *)
val res = panStaticTheory.sh_bd_from_sh_def
  |> REWRITE_RULE [OPT_MMAP_eq_MAP]
  |> SIMP_RULE std_ss [o_DEF]
  |> translate;

val res = translate $ panStaticTheory.sh_bd_from_bd_def;
val res = translate $ panStaticTheory.sh_bd_has_shape_def;
val res = translate $ panStaticTheory.sh_bd_eq_shapes_def;
val res = translate $ panStaticTheory.index_sh_bd_def;
val res = translate $ panStaticTheory.field_sh_bd_def;
val res = translate $ panStaticTheory.based_merge_def;
val res = translate $ panStaticTheory.sh_bd_branch_def;
val res = translate $ panStaticTheory.branch_loc_inf_def;
val res = translate $ panStaticTheory.seq_loc_inf_def;

val res = translate $ panStaticTheory.last_to_str_def;
val res = translate $ panStaticTheory.next_is_reachable_def;
val res = translate $ panStaticTheory.next_now_unreachable_def;
val res = translate $ spec64 $ panStaticTheory.reached_warnable_def;
val res = translate $ panStaticTheory.branch_last_stmt_def;
val res = translate $ panStaticTheory.seq_last_stmt_def;

val res = translate $ panStaticTheory.get_scope_desc_def;
val res = translate $ panStaticTheory.get_scope_msg_def;
val res = translate $ panStaticTheory.get_redec_msg_def;
val res = translate $ panStaticTheory.get_memop_msg_def;
val res = translate $ panStaticTheory.get_oparg_msg_def;
val res = translate $ panStaticTheory.get_unreach_msg_def;
val res = translate $ panStaticTheory.get_rogue_msg_def;
val res = translate $ panStaticTheory.get_non_word_msg_def;
val res = translate $ panStaticTheory.get_shape_mismatch_msg_def;
val res = translate $ panStaticTheory.get_implementation_err_msg_def;

val res = translate $ panStaticTheory.first_repeat_def;
val res = translate $ panStaticTheory.binop_to_str_def;
val res = translate $ panStaticTheory.panop_to_str_def;
val res = translate $ panStaticTheory.primop_to_str_def;
val res = translate $ panStaticTheory.sh_bd_to_str_def;

val res = translate $ alistTheory.ADELKEY_def;

val res = translate $ panStaticTheory.primitive_idents_def;
val res = translate $ panStaticTheory.add_primitive_hint_def;

val res = translate $ panStaticTheory.check_fun_name_def;
val res = translate $ panStaticTheory.check_global_var_def;
val res = translate $ panStaticTheory.check_local_var_def;
val res = translate $ panStaticTheory.check_redec_var_def;
val res = translate $ panStaticTheory.check_export_params_def;
val res = translate $ panStaticTheory.check_operands_def;
val res = translate $ panStaticTheory.check_primitive_args_def;
val res = translate $ panStaticTheory.check_func_args_def;
val res = translate $ panStaticTheory.check_struct_fields_def;
val res = translate $ panStaticTheory.check_shape_def;
val res = translate $ panStaticTheory.check_id_shapes_def;

val res = translate $ spec64 $ panStaticTheory.static_check_exp_def;
val res = translate $ spec64 $ panStaticTheory.static_check_prog_def;
val res = translate $ spec64 $ panStaticTheory.static_check_progs_def;
val res = translate $ spec64 $ panStaticTheory.static_check_decls_def;
val res = translate $ INST_TYPE[alpha|->``:staterr``] $
  INST_TYPE[beta|->``:64``] $ panStaticTheory.static_check_names_def;
val res = translate $ spec64 $ panStaticTheory.static_check_def;

val _ = res |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "panStaticTheory.static_check_def.");

Definition max_heap_limit_64_def:
  max_heap_limit_64 c =
    ^(spec64 data_to_wordTheory.max_heap_limit_def
      |> SPEC_ALL
      |> SIMP_RULE (srw_ss())[backend_commonTheory.word_shift_def]
      |> concl |> rhs)
End

val res = translate max_heap_limit_64_def

Theorem max_heap_limit_64_thm:
  max_heap_limit (:64) = max_heap_limit_64
Proof
  rw[FUN_EQ_THM] \\ EVAL_TAC
QED

val r = translate presLangTheory.default_tap_config_def;

val def = spec64
          (backendTheory.attach_bitmaps_def
             |> Q.GENL[`c'`,`bytes`,`c`]
             |> Q.ISPECL[`lab_conf:lab_to_target$config`,`bytes:word8 list`,`c:backend$config`])

val res = translate def

val def = spec64 backendTheory.compile_def
  |> REWRITE_RULE[max_heap_limit_64_thm]

val res = translate def

val _ = register_type “:64 any_prog”

val r = backend_passesTheory.to_flat_all_def |> spec64 |> translate;
val r = backend_passesTheory.to_clos_all_def |> spec64 |> translate;
val r = backend_passesTheory.to_bvl_all_def |> spec64 |> translate;
val r = backend_passesTheory.to_bvi_all_def |> spec64 |> translate;

Theorem backend_passes_to_bvi_all_side[local]:
  backend_passes_to_bvi_all_side c p
Proof
  fs [fetch "-" "backend_passes_to_bvi_all_side_def"]
  \\ rewrite_tac [GSYM LENGTH_NIL,bvl_inlineTheory.LENGTH_remove_ticks]
  \\ fs []
QED

val _ = update_precondition backend_passes_to_bvi_all_side

val r = backend_passesTheory.to_data_all_def |> spec64 |> translate;

val r = backend_passesTheory.word_internal_all_def |> spec64 |> translate;

val r = backend_passesTheory.to_word_all_def |> spec64
          |> REWRITE_RULE [data_to_wordTheory.stubs_def,APPEND] |> translate;

val r = backend_passesTheory.to_stack_all_def |> spec64
          |> REWRITE_RULE[max_heap_limit_64_thm] |> translate;

val r = backend_passesTheory.to_lab_all_def |> spec64
          |> REWRITE_RULE[max_heap_limit_64_thm] |> translate;

val r = backend_passesTheory.to_target_all_def |> spec64 |> translate;

val r = backend_passesTheory.from_lab_all_def |> spec64 |> translate;

val r = backend_passesTheory.from_stack_all_def |> spec64
          |> REWRITE_RULE[max_heap_limit_64_thm] |> translate;

val r = backend_passesTheory.from_word_all_def |> spec64 |> translate;

val r = backend_passesTheory.from_word_0_all_def |> spec64
          |> REWRITE_RULE[max_heap_limit_64_thm] |> translate;

val r = presLangTheory.word_to_strs_def |> spec64 |> translate
val r = presLangTheory.stack_to_strs_def |> spec64 |> translate
val r = presLangTheory.lab_to_strs_def |> spec64 |> translate

val r = backend_passesTheory.any_prog_pp_def |> spec64 |> translate;
val r = backend_passesTheory.pp_with_title_def |> translate;
val r = backend_passesTheory.compile_tap_def |> spec64 |> translate;

val _ = r |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "backend_passesTheory.compile_tap_def.");

val r = pan_passesTheory.pan_to_target_all_def |> spec64
          |> REWRITE_RULE [NULL_EQ] |> translate;

val r = pan_passesTheory.opsize_to_display_def |> translate;
val r = pan_passesTheory.insert_es_def |> translate;
val r = pan_passesTheory.varkind_to_str_def |> translate;
Theorem lem[local]:
  dimindex(:64) = 64
Proof
  EVAL_TAC
QED
val r = pan_passesTheory.primop_to_display_def |> translate;
val r = pan_passesTheory.pan_exp_to_display_def |> spec64 |> SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] |> translate;
val r = pan_passesTheory.crep_exp_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.loop_exp_to_display_def |> spec64 |> translate;

val r = pan_passesTheory.dest_annot_def |> spec64 |> translate;
val r = pan_passesTheory.pan_seqs_def |> spec64 |> translate;
val r = pan_passesTheory.crep_seqs_def |> spec64 |> translate;
val r = pan_passesTheory.loop_seqs_def |> spec64 |> translate;
val r = pan_passesTheory.pan_prog_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.crep_prog_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.loop_prog_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.pan_fun_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.crep_fun_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.loop_fun_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.pan_to_strs_def |> spec64 |> translate;
val r = pan_passesTheory.crep_to_strs_def |> spec64 |> translate;
val r = pan_passesTheory.loop_to_strs_def |> spec64 |> translate;
val r = pan_passesTheory.any_pan_prog_pp_def |> spec64 |> translate;

val r = pan_passesTheory.pan_compile_tap_def |> spec64 |> translate;

val _ = r |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "pan_passesTheory.pan_compile_tap_def.");

(* exportTheory *)
(* TODO: exportTheory functions that don't depend on the word size
   should probably be moved up to to_dataProg or something*)
val res = translate all_bytes_eq
val res = translate byte_to_string_eq
val res = translate escape_sym_char_def
val res = translate get_sym_label_def
val res = translate get_sym_labels_def
val res = translate emit_symbol_def
val res = translate emit_symbols_def

val export_byte_to_string_side_def = prove(
  ``!b. export_byte_to_string_side b``,
  fs [fetch "-" "export_byte_to_string_side_def"]
  \\ Cases \\ fs [] \\ EVAL_TAC \\ fs [])
                                       |> update_precondition;

val res = translate split16_def;
val res = translate preamble_def;
val res = translate (data_buffer_def |> CONV_RULE (RAND_CONV EVAL));
val res = translate (code_buffer_def |> CONV_RULE (RAND_CONV EVAL));

(* val res = translate space_line_def; *)

(* TODO: maybe do this directly to the definition of data_section *)
fun is_strcat_lits tm =
let val (t1,t2) = stringSyntax.dest_strcat tm in
  stringSyntax.is_string_literal t1 andalso
              stringSyntax.is_string_literal t2
              end handle HOL_ERR _ => false
fun is_strlit_var tm =
is_var (mlstringSyntax.dest_strlit tm)
       handle HOL_ERR _ => false
val res = translate
          ( data_section_def
              |> SIMP_RULE std_ss [MAP]
              |> CONV_RULE(DEPTH_CONV(EVAL o (assert is_strcat_lits)))
              |> SIMP_RULE std_ss [mlstringTheory.implode_STRCAT]
              |> SIMP_RULE std_ss [mlstringTheory.strcat_assoc]
              |> SIMP_RULE std_ss [GSYM mlstringTheory.implode_STRCAT]
              |> CONV_RULE(DEPTH_CONV(EVAL o (assert is_strcat_lits)))
              |> SIMP_RULE std_ss [mlstringTheory.implode_STRCAT])
(* -- *)

val res = translate comm_strlit_def;
val res = translate newl_strlit_def;
val res = translate comma_cat_def;

val res = translate words_line_def;

val res = translate (spec64 word_to_string_def);
(* -- *)

(* compilerTheory *)

val res = translate compilerTheory.find_next_newline_def;

val res = translate compilerTheory.safe_substring_def;

val _ = translate compilerTheory.get_nth_line_def;
val _ = translate compilerTheory.locs_to_string_def;
val _ = translate compilerTheory.parse_cml_input_def;
val _ = translate (compilerTheory.parse_sexp_input_def
                     |> PURE_REWRITE_RULE[fromSexpTheory.sexpdec_alt_intro1]);

val def = spec64 (compilerTheory.compile_def);
val res = translate def;

val res = translate (primTypesTheory.prim_tenv_def
                       |> CONV_RULE (RAND_CONV EVAL));

val res = translate inferTheory.init_config_def;

(* Compiler interface in compilerTheory
  TODO: some of these should be moved up, see comment above on exportScript
 *)
val res = translate error_to_str_def;

val res = translate parse_bool_def;
val res = translate parse_num_def;

val res = translate find_str_def;
val res = translate find_strs_def;
val res = translate find_bool_def;
val res = translate find_num_def;
val res = translate get_err_str_def;

val res = translate parse_num_list_def;

(* comma_tokens treats strings as char lists so we switch modes temporarily *)
val res = translate comma_tokens_def;
val res = translate parse_nums_def;

val res = translate clos_knownTheory.default_inline_factor_def;
val res = translate clos_knownTheory.default_max_body_size_def;
val res = translate clos_knownTheory.mk_config_def;
val res = translate parse_clos_conf_def;
val res = translate parse_bvl_conf_def;
val res = translate parse_wtw_conf_def;
val res = translate parse_gc_def;
val res = translate parse_data_conf_def;
val res = translate parse_stack_conf_def;
val res = translate parse_tap_conf_def;
val res = translate (parse_lab_conf_def |> spec64);

val res = translate (parse_top_config_def |> SIMP_RULE (srw_ss()) []);

(* Translations for each 64-bit target
  Note: ffi_asm is translated multiple times...
 *)

val res = translate backendTheory.prim_src_config_eq;

(* x64 *)
val res = translate x64_configTheory.x64_names_def;
val res = translate export_x64Theory.startup_def;
val res = translate export_x64Theory.ffi_asm_def;
val res = translate export_x64Theory.windows_ffi_asm_def;
val res = translate export_x64Theory.export_func_def;
val res = translate export_x64Theory.export_funcs_def;
val res = translate export_x64Theory.x64_export_def;
val res = translate
          (x64_configTheory.x64_backend_config_def
             |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* riscv *)
val res = translate riscv_configTheory.riscv_names_def;
val res = translate export_riscvTheory.startup_def;
val res = translate export_riscvTheory.ffi_asm_def;
val res = translate export_riscvTheory.export_func_def;
val res = translate export_riscvTheory.export_funcs_def;
val res = translate export_riscvTheory.riscv_export_def;
val res = translate
          (riscv_configTheory.riscv_backend_config_def
             |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* mips *)
val res = translate mips_configTheory.mips_names_def;
val res = translate export_mipsTheory.startup_def;
val res = translate export_mipsTheory.ffi_asm_def;
val res = translate export_mipsTheory.export_func_def;
val res = translate export_mipsTheory.export_funcs_def;
val res = translate export_mipsTheory.mips_export_def;
val res = translate
          (mips_configTheory.mips_backend_config_def
             |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* arm8 *)
val res = translate arm8_configTheory.arm8_names_def;
val res = translate export_arm8Theory.startup_def;
val res = translate export_arm8Theory.ffi_asm_def;
val res = translate export_arm8Theory.export_func_def;
val res = translate export_arm8Theory.export_funcs_def;
val res = translate export_arm8Theory.arm8_export_def;
val res = translate
          (arm8_configTheory.arm8_backend_config_def
             |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* Leave the module now, so that key things are available in the toplevel
   namespace for main. *)
val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

(* Rest of the translation *)
val res = translate (extend_conf_def |> spec64 |> SIMP_RULE (srw_ss()) [MEMBER_INTRO]);
val res = translate parse_target_64_def;
val res = translate add_tap_output_def;

val res = format_compiler_result_def
            |> Q.GENL[`bytes`,`c`]
            |> Q.ISPECL[`bytes:word8 list`,`c:backend$config`]
            |> spec64
            |> translate;

val res = translate backendTheory.ffinames_to_string_list_def;

val res = translate compile_64_def;

val _ = res |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "compile_64_def.");

val res = translate $ spec64 compile_pancake_def;

val res = translate pancake_backend_conf_def;

val res = translate compile_pancake_64_def;

val _ = res |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "compile_pancake_64_def.");

val res = translate (has_version_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])
val res = translate (has_help_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])
val res = translate print_option_def
val res = translate current_build_info_str_def
val res = translate compilerTheory.help_string_def;

Definition nonzero_exit_code_for_error_msg_def:
                                                 nonzero_exit_code_for_error_msg e =
if compiler$is_error_msg e then
  (let a = empty_ffi «nonzero_exit» in
     ml_translator$force_out_of_memory_error ())
else ()
End

val res = translate compilerTheory.is_error_msg_def;
val res = translate nonzero_exit_code_for_error_msg_def;

(* incremental compiler *)

Definition compiler_for_eval_def:
  compiler_for_eval = compile_inc_progs_for_eval x64_config
End

Theorem upper_w2w_eq_I[local]:
  backend_common$upper_w2w = (I:word64 -> word64)
Proof
  fs [backend_commonTheory.upper_w2w_def,FUN_EQ_THM]
QED

val compiler_for_eval_alt =
“compiler_for_eval (id,c,ds)”
  |> SIMP_CONV std_ss [backendTheory.compile_inc_progs_for_eval_eq,
                       compiler_for_eval_def, EVAL “x64_config.reg_count”,
                       backendTheory.ensure_fp_conf_ok_def,
                       EVAL “LENGTH x64_config.avoid_regs”,
                       EVAL “x64_config.fp_reg_count”,
                       EVAL “x64_config.two_reg_arith”,listTheory.MAP_ID,
                       EVAL “x64_config.addr_offset”,upper_w2w_eq_I,
                       EVAL “x64_config.ISA”, EVAL “x86_64 = ARMv7”]

val r = translate (word_to_wordTheory.compile_single_def |> spec64);
val r = translate (word_to_wordTheory.full_compile_single_def |> spec64);
val r = translate (word_to_wordTheory.full_compile_single_for_eval_def |> spec64);
val _ = (next_ml_names := ["compiler_for_eval"]);
val r = translate compiler_for_eval_alt;

(* fun eval_prim env s1 decs s2 bs ws = Eval [env,s1,decs,s2,bs,ws] *)
val _ = append_prog
        “[Dlet (Locs (POSN 1 2) (POSN 2 21)) (Pvar «eval_prim»)
          (Fun «x» (Mat (Var (Short «x»))
                    [(Pcon NONE [Pvar «env»; Pvar «s1»; Pvar «decs»;
                                 Pvar «s2»; Pvar «bs»; Pvar «ws»],
                      App Eval [Var (Short «env»); Var (Short «s1»); Var (Short «decs»);
                                Var (Short «s2»); Var (Short «bs»); Var (Short «ws»)])]))]”;

Datatype:
  eval_res = Compile_error 'a | Eval_result 'b 'c | Eval_exn 'd 'e
End

val _ = register_type “:('a,'b,'c,'d,'e) eval_res”;

Quote add_cakeml:
fun eval ((s1,next_gen), (env,id), decs) =
case compiler_for_eval ((id,0),(s1,decs)) of
  None => Compile_error "ERROR: failed to compile input\n"
| Some (s2,(bs,ws)) =>
    let
val new_env = eval_prim (env,s1,decs,s2,bs,ws)
    in Eval_result (new_env,next_gen) (s2,next_gen+1) end
                   handle e => Eval_exn e (s2,next_gen+1)
End

Quote exn_msg_dec = cakeml:
val _ = (TextIO.print (!Repl.errorMessage);
         print_pp (pp_exn (!Repl.exn));
         print "\n")
End

Definition report_exn_dec_def:
  report_exn_dec = ^exn_msg_dec
End

val _ = (next_ml_names := ["report_exn_dec"]);
val r = translate report_exn_dec_def;

Quote add_cakeml:
fun report_exn e =
(Repl.exn := e;
 Repl.errorMessage := "EXCEPTION: ";
 report_exn_dec)
End

Quote error_msg_dec = cakeml:
val _ = (TextIO.print (!Repl.errorMessage))
End

Definition report_error_dec_def:
  report_error_dec = ^error_msg_dec
End

val _ = (next_ml_names := ["report_error_dec"]);
val r = translate report_error_dec_def;

Quote add_cakeml:
fun report_error msg =
(Repl.errorMessage := msg;
 report_error_dec)
End

val _ = (next_ml_names := ["roll_back"]);
val r = translate repl_check_and_tweakTheory.roll_back_def;

val _ = (next_ml_names := ["check_and_tweak"]);
val r = translate repl_check_and_tweakTheory.check_and_tweak_def;

Quote add_cakeml:
fun repl (parse, types, conf, env, decs, input_str) =
(* input_str is passed in here only for error reporting purposes *)
case check_and_tweak (decs, (types, input_str)) of
  Inl msg => repl (parse, types, conf, env, report_error msg, "")
| Inr (safe_decs, new_types) =>
    (* here safe_decs are guaranteed to not crash;
         the last declaration of safe_decs calls !Repl.readNextString *)
    case eval (conf, env, safe_decs) of
      Compile_error msg => repl (parse, types, conf, env, report_error msg, "")
    | Eval_exn e new_conf =>
        repl (parse, roll_back (types, new_types), new_conf, env, report_exn e, "")
    | Eval_result new_env new_conf =>
        (* check whether the program that ran has loaded in new input *)
        if !Repl.isEOF then () (* exit if there is no new input *) else
          let val new_input = !Repl.nextString in
            (* if there is new input: parse the input and recurse *)
            case parse new_input of
              Inl msg      => repl (parse, new_types, new_conf, new_env, report_error msg, "")
            | Inr new_decs => repl (parse, new_types, new_conf, new_env, new_decs, new_input)
                                   end
End

val _ = (next_ml_names := ["init_types"]);
val r = translate repl_init_typesTheory.repl_init_types_eq;

Definition parse_cakeml_syntax_def:
  parse_cakeml_syntax input =
  case parse_prog (lexer_fun (explode input)) of
  | Success _ x _ => INR x
  | Failure l _ => INL («Parsing failed at » ^ locs_to_string input (SOME l))
End

Definition parse_ocaml_syntax_def:
  parse_ocaml_syntax input =
  case caml_parser$run (explode input) of
  | INR res => INR res
  | INL (l,err) => INL
                   (err ^ «\nParsing failed at » ^ locs_to_string input (SOME l))
End

(*
  This protocol is deliberately recognized by exact argument-list shape.  In
  particular, these predicates must not be replaced by a MEM-style flag test:
  the diagnostic controller treats every other command line as an ordinary
  compiler invocation.
*)
Definition candle_parser_diagnostic_capability_arg_def:
  candle_parser_diagnostic_capability_arg =
    «--candle-parser-diagnostic-capability-v1»
End

Definition candle_parser_diagnostic_run_arg_def:
  candle_parser_diagnostic_run_arg = «--candle-parser-diagnostic-v1»
End

Definition candle_parser_diagnostic_lower_hex_def:
  candle_parser_diagnostic_lower_hex c ⇔ MEM c "0123456789abcdef"
End

Definition candle_parser_diagnostic_nonce_def:
  candle_parser_diagnostic_nonce s ⇔
    strlen s = 64 ∧ EVERY candle_parser_diagnostic_lower_hex (explode s)
End

Definition candle_parser_diagnostic_capability_args_def:
  candle_parser_diagnostic_capability_args cl ⇔
    cl = [candle_parser_diagnostic_capability_arg]
End

Definition candle_parser_diagnostic_run_args_def:
  candle_parser_diagnostic_run_args cl =
    case cl of
    | [arg; nonce] =>
        if arg = candle_parser_diagnostic_run_arg ∧
           candle_parser_diagnostic_nonce nonce
        then SOME nonce
        else NONE
    | _ => NONE
End

Definition has_candle_parser_diagnostic_mode_def:
  has_candle_parser_diagnostic_mode cl ⇔
    candle_parser_diagnostic_capability_args cl ∨
    IS_SOME (candle_parser_diagnostic_run_args cl)
End

val res = translate candle_parser_diagnostic_capability_arg_def;
val res = translate candle_parser_diagnostic_run_arg_def;
val res = translate candle_parser_diagnostic_lower_hex_def;
val res = translate candle_parser_diagnostic_nonce_def;
val res = translate candle_parser_diagnostic_capability_args_def;
val res = translate candle_parser_diagnostic_run_args_def;
val _ = (next_ml_names := ["compiler_has_candle_parser_diagnostic_mode"]);
val res = translate has_candle_parser_diagnostic_mode_def;

(* Pure SHA-256 for binding the exact parser diagnostic written to stderr. *)
Definition candle_sha256_ch_def:
  candle_sha256_ch (x:word32) y z =
    word_xor (word_and x y) (word_and (¬x) z)
End

Definition candle_sha256_maj_def:
  candle_sha256_maj (x:word32) y z =
    word_xor (word_xor (word_and x y) (word_and x z)) (word_and y z)
End

Definition candle_sha256_bigsigma0_def:
  candle_sha256_bigsigma0 (x:word32) =
    word_xor
      (word_xor (word_or (x >>> 2) (x << 30))
                (word_or (x >>> 13) (x << 19)))
      (word_or (x >>> 22) (x << 10))
End

Definition candle_sha256_bigsigma1_def:
  candle_sha256_bigsigma1 (x:word32) =
    word_xor
      (word_xor (word_or (x >>> 6) (x << 26))
                (word_or (x >>> 11) (x << 21)))
      (word_or (x >>> 25) (x << 7))
End

Definition candle_sha256_smallsigma0_def:
  candle_sha256_smallsigma0 (x:word32) =
    word_xor
      (word_xor (word_or (x >>> 7) (x << 25))
                (word_or (x >>> 18) (x << 14)))
      (x >>> 3)
End

Definition candle_sha256_smallsigma1_def:
  candle_sha256_smallsigma1 (x:word32) =
    word_xor
      (word_xor (word_or (x >>> 17) (x << 15))
                (word_or (x >>> 19) (x << 13)))
      (x >>> 10)
End

Definition candle_sha256_nth_def:
  (candle_sha256_nth 0 (x::xs) = (x:word32)) ∧
  (candle_sha256_nth (SUC n) (x::xs) = candle_sha256_nth n xs) ∧
  (candle_sha256_nth n [] = 0w)
End

Definition candle_sha256_schedule_word_def:
  candle_sha256_schedule_word ws =
    candle_sha256_smallsigma1
      (candle_sha256_nth (LENGTH ws - 2) ws) +
    candle_sha256_nth (LENGTH ws - 7) ws +
    candle_sha256_smallsigma0
      (candle_sha256_nth (LENGTH ws - 15) ws) +
    candle_sha256_nth (LENGTH ws - 16) ws
End

Definition candle_sha256_extend_schedule_def:
  (candle_sha256_extend_schedule 0 ws = ws) ∧
  (candle_sha256_extend_schedule (SUC n) ws =
     candle_sha256_extend_schedule n
       (ws ++ [candle_sha256_schedule_word ws]))
End

Definition candle_sha256_pack_word_def:
  candle_sha256_pack_word a b c d =
    (((n2w (ORD a)):word32) << 24) +
    (((n2w (ORD b)):word32) << 16) +
    (((n2w (ORD c)):word32) << 8) +
    ((n2w (ORD d)):word32)
End

Definition candle_sha256_pack_words_def:
  (candle_sha256_pack_words (a::b::c::d::rest) =
     candle_sha256_pack_word a b c d ::
       candle_sha256_pack_words rest) ∧
  (candle_sha256_pack_words _ = [])
End

Definition candle_sha256_constants_def:
  candle_sha256_constants : word32 list =
    [0x428a2f98w; 0x71374491w; 0xb5c0fbcfw; 0xe9b5dba5w;
     0x3956c25bw; 0x59f111f1w; 0x923f82a4w; 0xab1c5ed5w;
     0xd807aa98w; 0x12835b01w; 0x243185bew; 0x550c7dc3w;
     0x72be5d74w; 0x80deb1few; 0x9bdc06a7w; 0xc19bf174w;
     0xe49b69c1w; 0xefbe4786w; 0x0fc19dc6w; 0x240ca1ccw;
     0x2de92c6fw; 0x4a7484aaw; 0x5cb0a9dcw; 0x76f988daw;
     0x983e5152w; 0xa831c66dw; 0xb00327c8w; 0xbf597fc7w;
     0xc6e00bf3w; 0xd5a79147w; 0x06ca6351w; 0x14292967w;
     0x27b70a85w; 0x2e1b2138w; 0x4d2c6dfcw; 0x53380d13w;
     0x650a7354w; 0x766a0abbw; 0x81c2c92ew; 0x92722c85w;
     0xa2bfe8a1w; 0xa81a664bw; 0xc24b8b70w; 0xc76c51a3w;
     0xd192e819w; 0xd6990624w; 0xf40e3585w; 0x106aa070w;
     0x19a4c116w; 0x1e376c08w; 0x2748774cw; 0x34b0bcb5w;
     0x391c0cb3w; 0x4ed8aa4aw; 0x5b9cca4fw; 0x682e6ff3w;
     0x748f82eew; 0x78a5636fw; 0x84c87814w; 0x8cc70208w;
     0x90befffaw; 0xa4506cebw; 0xbef9a3f7w; 0xc67178f2w]
End

Definition candle_sha256_initial_def:
  candle_sha256_initial :
    word32 # word32 # word32 # word32 #
    word32 # word32 # word32 # word32 =
    (0x6a09e667w, 0xbb67ae85w, 0x3c6ef372w, 0xa54ff53aw,
     0x510e527fw, 0x9b05688cw, 0x1f83d9abw, 0x5be0cd19w)
End

Definition candle_sha256_round_def:
  candle_sha256_round (a,b,c,d,e,f,g,h) k w =
    let t1 = h + candle_sha256_bigsigma1 e +
                 candle_sha256_ch e f g + k + w in
    let t2 = candle_sha256_bigsigma0 a + candle_sha256_maj a b c in
      (t1 + t2,a,b,c,d + t1,e,f,g)
End

Definition candle_sha256_rounds_def:
  (candle_sha256_rounds [] ws state = state) ∧
  (candle_sha256_rounds ks [] state = state) ∧
  (candle_sha256_rounds (k::ks) (w::ws) state =
     candle_sha256_rounds ks ws (candle_sha256_round state k w))
End

Definition candle_sha256_compress_def:
  candle_sha256_compress (h0,h1,h2,h3,h4,h5,h6,h7) block =
    let schedule = candle_sha256_extend_schedule 48
                     (candle_sha256_pack_words (TAKE 64 block)) in
    let (a,b,c,d,e,f,g,h) =
      candle_sha256_rounds candle_sha256_constants schedule
        (h0,h1,h2,h3,h4,h5,h6,h7) in
      (h0+a,h1+b,h2+c,h3+d,h4+e,h5+f,h6+g,h7+h)
End

Definition candle_sha256_blocks_def:
  (candle_sha256_blocks 0 bytes state = state) ∧
  (candle_sha256_blocks (SUC n) bytes state =
     candle_sha256_blocks n (DROP 64 bytes)
       (candle_sha256_compress state bytes))
End

Definition candle_sha256_length_suffix_def:
  candle_sha256_length_suffix bytes =
    let n = 8 * LENGTH bytes in
      [CHR ((n DIV 72057594037927936) MOD 256);
       CHR ((n DIV 281474976710656) MOD 256);
       CHR ((n DIV 1099511627776) MOD 256);
       CHR ((n DIV 4294967296) MOD 256);
       CHR ((n DIV 16777216) MOD 256);
       CHR ((n DIV 65536) MOD 256);
       CHR ((n DIV 256) MOD 256);
       CHR (n MOD 256)]
End

Definition candle_sha256_pad_def:
  candle_sha256_pad bytes =
    let r = (LENGTH bytes + 1) MOD 64 in
    let zeros = if r ≤ 56 then 56 - r else 120 - r in
      bytes ++ [CHR 128] ++ REPLICATE zeros (CHR 0) ++
      candle_sha256_length_suffix bytes
End

Definition candle_sha256_digest_def:
  candle_sha256_digest bytes =
    let padded = candle_sha256_pad bytes in
      candle_sha256_blocks (LENGTH padded DIV 64) padded
        candle_sha256_initial
End

Definition candle_sha256_hex_digit_def:
  candle_sha256_hex_digit n =
    let d = n MOD 16 in if d < 10 then CHR (48 + d) else CHR (87 + d)
End

Definition candle_sha256_word_hex_def:
  candle_sha256_word_hex (w:word32) =
    [candle_sha256_hex_digit (w2n (w >>> 28));
     candle_sha256_hex_digit (w2n (w >>> 24));
     candle_sha256_hex_digit (w2n (w >>> 20));
     candle_sha256_hex_digit (w2n (w >>> 16));
     candle_sha256_hex_digit (w2n (w >>> 12));
     candle_sha256_hex_digit (w2n (w >>> 8));
     candle_sha256_hex_digit (w2n (w >>> 4));
     candle_sha256_hex_digit (w2n w)]
End

Definition candle_sha256_hex_def:
  candle_sha256_hex bytes =
    let (h0,h1,h2,h3,h4,h5,h6,h7) = candle_sha256_digest bytes in
      implode (candle_sha256_word_hex h0 ++ candle_sha256_word_hex h1 ++
               candle_sha256_word_hex h2 ++ candle_sha256_word_hex h3 ++
               candle_sha256_word_hex h4 ++ candle_sha256_word_hex h5 ++
               candle_sha256_word_hex h6 ++ candle_sha256_word_hex h7)
End

(* This is the byte/list contract consumed by the wire-protocol proof. *)
Theorem candle_sha256_hex_implements_digest:
  candle_sha256_hex bytes =
    let (h0,h1,h2,h3,h4,h5,h6,h7) = candle_sha256_digest bytes in
      implode (FLAT (MAP candle_sha256_word_hex
        [h0;h1;h2;h3;h4;h5;h6;h7]))
Proof
  simp [candle_sha256_hex_def]
QED

Theorem candle_sha256_known_answers:
  candle_sha256_hex [] =
    «e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855» ∧
  candle_sha256_hex (explode «abc») =
    «ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad»
Proof
  EVAL_TAC
QED

val res = translate candle_sha256_ch_def;
val res = translate candle_sha256_maj_def;
val res = translate candle_sha256_bigsigma0_def;
val res = translate candle_sha256_bigsigma1_def;
val res = translate candle_sha256_smallsigma0_def;
val res = translate candle_sha256_smallsigma1_def;
val res = translate candle_sha256_nth_def;
val res = translate candle_sha256_schedule_word_def;
val res = translate candle_sha256_extend_schedule_def;
val res = translate candle_sha256_pack_word_def;
val res = translate candle_sha256_pack_words_def;
val res = translate candle_sha256_constants_def;
val res = translate candle_sha256_initial_def;
val res = translate candle_sha256_round_def;
val res = translate candle_sha256_rounds_def;
val res = translate candle_sha256_compress_def;
val res = translate candle_sha256_blocks_def;
val res = translate candle_sha256_length_suffix_def;
val res = translate candle_sha256_pad_def;
val res = translate candle_sha256_digest_def;
val res = translate candle_sha256_hex_digit_def;
val res = translate candle_sha256_word_hex_def;
val res = translate candle_sha256_hex_def;

Datatype:
  candle_parser_diagnostic_reply =
    CandleParserDiagnosticOk mlstring
  | CandleParserDiagnosticError mlstring mlstring
End

val _ = register_type “:candle_parser_diagnostic_reply”;

Definition candle_parser_diagnostic_capability_line_def:
  candle_parser_diagnostic_capability_line =
    «CANDLE_CAMLPARSER_DIAGNOSTIC_CAPABILITY_V1\tcaml_parser$run\tstdin-exact-bytes\tparser-only\tno-inference\tno-evaluation\n»
End

Definition candle_parser_diagnostic_result_prefix_def:
  candle_parser_diagnostic_result_prefix =
    «CANDLE_CAMLPARSER_DIAGNOSTIC_V1\t»
End

Definition candle_parser_diagnostic_error_text_def:
  candle_parser_diagnostic_error_text input l err =
    err ^ «\nParsing failed at » ^ locs_to_string input (SOME l)
End

Definition candle_parser_diagnostic_reply_def:
  candle_parser_diagnostic_reply nonce input =
    case caml_parser$run (explode input) of
    | INR res =>
        CandleParserDiagnosticOk
          (candle_parser_diagnostic_result_prefix ^ nonce ^ «\tOK\n»)
    | INL (l,err) =>
        let stderr = candle_parser_diagnostic_error_text input l err in
          CandleParserDiagnosticError
            (candle_parser_diagnostic_result_prefix ^ nonce ^
             «\tPARSE_ERROR\n»)
            stderr
End

Theorem candle_parser_diagnostic_reply_calls_parser_directly:
  candle_parser_diagnostic_reply nonce input =
    case caml_parser$run (explode input) of
    | INR res =>
        CandleParserDiagnosticOk
          (candle_parser_diagnostic_result_prefix ^ nonce ^ «\tOK\n»)
    | INL (l,err) =>
        let stderr = candle_parser_diagnostic_error_text input l err in
          CandleParserDiagnosticError
            (candle_parser_diagnostic_result_prefix ^ nonce ^
             «\tPARSE_ERROR\n»)
            stderr
Proof
  simp [candle_parser_diagnostic_reply_def]
QED

Definition candle_parser_diagnostic_success_fs_def:
  candle_parser_diagnostic_success_fs nonce input fs =
    case candle_parser_diagnostic_reply nonce input of
    | CandleParserDiagnosticOk stdout =>
        add_stdout (fastForwardFD fs 0) stdout
    | CandleParserDiagnosticError stdout stderr =>
        add_stderr (add_stdout (fastForwardFD fs 0) stdout) stderr
End

val res = translate candle_parser_diagnostic_capability_line_def;
val res = translate candle_parser_diagnostic_result_prefix_def;
val res = translate candle_parser_diagnostic_error_text_def;
val res = translate candle_parser_diagnostic_reply_def;

Definition select_parse_def:
  select_parse cl =
  if MEMBER «--candle» cl
  then parse_ocaml_syntax
  else parse_cakeml_syntax
End

val r = translate parse_cakeml_syntax_def;
val r = translate parse_ocaml_syntax_def;
val _ = (next_ml_names := ["select_parse"]);
val r = translate select_parse_def;

Definition init_next_string_def:
  init_next_string cl = if MEM «--candle» cl then «candle» else «»
End

val _ = (next_ml_names := ["init_next_string"]);
val res = translate (init_next_string_def |> REWRITE_RULE [MEMBER_INTRO]);

Quote add_cakeml:
fun start_repl (cl,s1) =
  let
    val parse = select_parse cl
    val types = init_types
    val conf = (s1,1)
    val env = (repl_init_env, 0)
    val decs = []
    val input_str = ""
    val _ = (Repl.nextString := init_next_string cl)
  in
    repl (parse, types, conf, env, decs, input_str)
  end
End

Quote add_cakeml:
fun run_interactive_repl cl =
  let
    val cs = Repl.charsFrom "config_enc_str.txt"
    val s1 = decodeProg.decode_backend_config cs
  in
    start_repl (cl,s1)
  end
End

Definition has_repl_flag_def:
  has_repl_flag cl ⇔ MEM «--repl» cl ∨ MEM «--candle» cl
End

val _ = (next_ml_names := ["compiler_has_repl_flag"]);
val res = translate (has_repl_flag_def |> REWRITE_RULE [MEMBER_INTRO]);

val res = translate (has_pancake_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])

Quote add_cakeml:
  fun main u =
  let
    val cl = CommandLine.arguments ()
  in
    if compiler64prog_candle_parser_diagnostic_capability_args cl then
      print compiler64prog_candle_parser_diagnostic_capability_line
    else case compiler64prog_candle_parser_diagnostic_run_args cl of
      Some nonce =>
        let
          val input = TextIO.inputAll (TextIO.openStdIn ())
        in
          case compiler64prog_candle_parser_diagnostic_reply nonce input of
            CandleParserDiagnosticOk stdout => print stdout
          | CandleParserDiagnosticError stdout stderr =>
              (print stdout; TextIO.output TextIO.stdErr stderr;
               Runtime.exit 65)
        end
    | None => if compiler_has_repl_flag cl then
      run_interactive_repl cl
    else if compiler_has_help_flag cl then
      print compiler_help_string
    else if compiler_has_version_flag cl then
      print compiler_current_build_info_str
    else if compiler_has_pancake_flag cl then
      case compiler_compile_pancake_64 cl (String.explode (TextIO.inputAll (TextIO.openStdIn ())))  of
        (c, e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                   compiler64prog_nonzero_exit_code_for_error_msg e)
    else
      case compiler_compile_64 cl (String.explode (TextIO.inputAll (TextIO.openStdIn ())))  of
        (c, e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                   compiler64prog_nonzero_exit_code_for_error_msg e)
  end
End

val main_v_def = fetch "-" "main_v_def";

Theorem main_spec:
  ¬has_repl_flag (TL cl) ∧ IS_SOME (stdin_content fs) ⇒
  app (p:'ffi ffi_proj) main_v
      [Conv NONE []] (STDIO fs * COMMANDLINE cl)
      (POSTv uv.
       &UNIT_TYPE () uv
       * STDIO (full_compile_64 (TL cl) (get_stdin fs) fs)
       * COMMANDLINE cl)
Proof
  rpt strip_tac
  \\ xcf_with_def main_v_def
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  (* TODO: it would be nice if this followed more directly.
           either (or both):
             - make STD_streams assert "stdin" is in the files
             - make wfFS separate from wfFS, so STDIO fs will imply wfFS fs *)
  \\ reverse(Cases_on`∃inp pos. stdin fs inp pos`)
  >-
   (fs[STDIO_def,IOFS_def] \\ xpull \\ fs[stdin_def]
    \\ `F` suffices_by fs[]
    \\ fs[wfFS_def,STD_streams_def,MEM_MAP,Once EXISTS_PROD,PULL_EXISTS]
    \\ fs[EXISTS_PROD]
    \\ metis_tac[ALOOKUP_FAILS,ALOOKUP_MEM,NOT_SOME_NONE,SOME_11,PAIR_EQ,option_CASES])
  \\ fs[get_stdin_def]
  \\ SELECT_ELIM_TAC
  \\ simp[FORALL_PROD,EXISTS_PROD]
  \\ conj_tac >- metis_tac[] \\ rw[]
  \\ imp_res_tac stdin_11 \\ rw[]
  \\ imp_res_tac stdin_get_file_content
  \\ xlet_auto >- xsimpl
  \\ xif
  \\ first_x_assum $ irule_at $ Pos hd \\ simp []
  \\ xlet_auto >- xsimpl
  \\ xif
  >-
   (simp[full_compile_64_def]
    \\ xapp
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `help_string`
    \\ fs [compilerTheory.help_string_def,
           fetch "-" "compiler_help_string_v_thm"]
    \\ xsimpl
    \\ rename1 `add_stdout _ (strlit string)`
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`fs`
    \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xif
  >-
   (simp[full_compile_64_def]
    \\ xapp
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `current_build_info_str`
    \\ fs [compilerTheory.current_build_info_str_def,
           fetch "-" "compiler_current_build_info_str_v_thm"]
    \\ xsimpl
    \\ rename1 `add_stdout _ (strlit string)`
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`fs`
    \\ xsimpl)
  >> xlet_auto>-xsimpl
  >> xif
  >-
   (xlet_auto >- (xcon \\ xsimpl)
    \\ rename [‘stdin fs inp pos’]
    \\ ‘stdin_content fs = SOME inp ∧ pos = 0’ by
     (gvs [stdin_def,get_file_content_def]
      \\ fs [stdin_content_def,IS_SOME_EXISTS])
    \\ gvs []
    \\ xlet_auto_spec (SOME openStdIn_spec_str) >- xsimpl
    \\ xlet ‘POSTv v.
               &STRING_TYPE (implode inp) v *
               STDIO (fastForwardFD fs 0) * COMMANDLINE cl’
    >-
     (xapp
      \\ qexistsl [‘COMMANDLINE cl’, ‘inp’, ‘fs’, ‘0’]
      \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ fs [full_compile_64_def]
    \\ pairarg_tac
    \\ fs[ml_translatorTheory.PAIR_TYPE_def]
    \\ gvs[CaseEq "bool"]
    \\ xmatch
    \\ xlet_auto >- xsimpl
    \\ qmatch_goalsub_abbrev_tac `STDIO fs'`
    \\ xlet `POSTv uv. &UNIT_TYPE () uv * STDIO (add_stderr fs' err) *
       COMMANDLINE cl`
    THEN1
     (xapp_spec output_stderr_spec \\ xsimpl
      \\ qexists_tac `COMMANDLINE cl`
      \\ asm_exists_tac \\ xsimpl
      \\ qexists_tac `fs'` \\ xsimpl)
    \\ xapp
    \\ asm_exists_tac \\ simp [] \\ xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ rename [‘stdin fs inp pos’]
  \\ ‘stdin_content fs = SOME inp ∧ pos = 0’ by
    (gvs [stdin_def,get_file_content_def]
     \\ fs [stdin_content_def,IS_SOME_EXISTS])
  \\ gvs []
  \\ xlet_auto_spec (SOME openStdIn_spec_str) >- xsimpl
  \\ xlet ‘POSTv v.
             &STRING_TYPE (implode inp) v *
             STDIO (fastForwardFD fs 0) * COMMANDLINE cl’
  >-
   (xapp
    \\ qexistsl [‘COMMANDLINE cl’, ‘inp’, ‘fs’, ‘0’]
    \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ fs [full_compile_64_def]
  \\ pairarg_tac
  \\ fs[ml_translatorTheory.PAIR_TYPE_def]
  \\ gvs[CaseEq "bool"]
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ qmatch_goalsub_abbrev_tac `STDIO fs'`
  \\ xlet `POSTv uv. &UNIT_TYPE () uv * STDIO (add_stderr fs' err) *
     COMMANDLINE cl`
  THEN1
   (xapp_spec output_stderr_spec \\ xsimpl
    \\ qexists_tac `COMMANDLINE cl`
    \\ asm_exists_tac \\ xsimpl
    \\ qexists_tac `fs'` \\ xsimpl)
  \\ xapp
  \\ asm_exists_tac \\ simp [] \\ xsimpl
QED

Theorem main_whole_prog_spec:
  ¬has_repl_flag (TL cl) ∧ IS_SOME (stdin_content fs) ⇒
  whole_prog_spec main_v cl fs NONE
                  ((=) (full_compile_64 (TL cl) (get_stdin fs) fs))
Proof
  strip_tac
  \\ simp[basis_ffiTheory.whole_prog_spec_def,UNCURRY]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ reverse conj_tac >-
   rw[Abbr`fs1`,full_compile_64_def,UNCURRY,
      GSYM fastForwardFD_with_numchars,
      GSYM add_stdo_with_numchars, with_same_numchars]
  \\ simp [SEP_CLAUSES]
  \\ match_mp_tac (MP_CANON(MATCH_MP app_wgframe (UNDISCH main_spec)))
  \\ xsimpl
QED

Theorem dec_sides[local]:
  (peg_v_side ⇔ T) ∧
  (peg_longv_side ⇔ T) ∧
  (peg_uqconstructorname_side ⇔ T) ∧
  (cmlpeg_side ⇔ T)
Proof
  fs[
    parserProgTheory.cmlpeg_side_def,
    parserProgTheory.peg_v_side_def,
    parserProgTheory.peg_longv_side_def,
    parserProgTheory.peg_uqconstructorname_side_def]
QED

val sem_thm = prove_sem_thm "main" "compiler64_prog" main_whole_prog_spec;
val compiler64_prog_def = fetch "-" "compiler64_prog_def";

Theorem semantics_compiler64_prog:
  ¬has_repl_flag (TL cl) ∧ IS_SOME (stdin_content fs) ∧ wfcl cl ∧ wfFS fs ∧
  STD_streams fs ⇒
  ∃io_events.
    semantics_dec_list
      (init_state
        (basis_ffi ext cl fs) with
         eval_state := SOME (EvalDecs (eval_state_var with env_id_counter := (0,0,1))))
      init_env compiler64_prog (Terminate Success io_events) ∧
    extract_fs ext (cl,fs) io_events =
      SOME (full_compile_64 (TL cl) (get_stdin fs) fs)
Proof
  strip_tac
  \\ irule sem_thm
  \\ fs [dec_sides]
QED

(* saving a tidied up final theorem *)

val th = get_ml_prog_state ()
  (* |> ml_progLib.clean_state *)
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]

Theorem BUTLAST_compiler64_prog[local]:
  ^(mk_eq(concl th |> rator |> rator |> rand,“BUTLAST compiler64_prog”))
Proof
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [compiler64_prog_def]))
  \\ CONV_TAC (RAND_CONV (PURE_REWRITE_CONV [listTheory.FRONT_CONS]))
  \\ rewrite_tac []
QED

val th1 = th
            |> CONV_RULE (PATH_CONV "llr" (REWR_CONV BUTLAST_compiler64_prog))
            |> CONV_RULE (RAND_CONV (EVAL THENC REWRITE_CONV
                                          (DB.find "_refs_def" |> map (#1 o #2)) THENC
                                          SIMP_CONV std_ss [APPEND_NIL,APPEND]))
            |> DISCH_ALL |> REWRITE_RULE [dec_sides]

Theorem Decls_FRONT_compiler64_prog = th1

Theorem LAST_compiler64_prog = “LAST compiler64_prog”
  |> (ONCE_REWRITE_CONV [compiler64_prog_def] THENC EVAL);

val _ = ml_translatorLib.reset_translation(); (* because this translation won't be continued *)
