(*****************************************************************************
 * Restartable translator for exact chunks of the authenticated case-16594
 * equation set.
 *
 * Each chunk is a literal sublist of the unchanged HOL definition.  The final
 * assembly proof is required to reconstruct that exact constant from all
 * chunks before the ordinary runtime theories may use it.
 *****************************************************************************)
structure compute_boundedCase16594WordCeqsChunkLib = struct

open HolKernel boolLib bossLib;

fun stage message =
  (print ("CANDLE_CASE16594_WORD_CEQS_CHUNK " ^ message ^ "\n");
   TextIO.flushOut TextIO.stdOut);

fun source_entries original_def =
  let
    val source_rhs = rhs (concl original_def);
    val (entries,entry_type) = listSyntax.dest_list source_rhs;
    val _ =
      if length entries = 175 then ()
      else raise Fail "unexpected case-16594 CEQ source count";
  in
    (entries,entry_type)
  end;

fun translate_chunk {original_def,start,count,name} =
  let
    val (entries,entry_type) = source_entries original_def;
    val _ =
      if 0 <= start andalso 0 < count andalso start + count <= length entries
      then ()
      else raise Fail "invalid case-16594 CEQ chunk bounds";
    val chunk_rhs =
      listSyntax.mk_list
        (List.take (List.drop (entries,start),count),entry_type);
    val chunk_lhs = mk_var (name,type_of chunk_rhs);
    val chunk_def =
      new_definition (name ^ "_def",mk_eq (chunk_lhs,chunk_rhs));
    val translate_start = Time.now ();
    val _ =
      stage
        ("translate-start name=" ^ name ^
         " start=" ^ Int.toString start ^
         " count=" ^ Int.toString count);
    val _ = ml_translatorLib.translate chunk_def;
    val translate_elapsed = Time.- (Time.now (),translate_start);
    val _ =
      stage
        ("translate-done name=" ^ name ^
         " seconds=" ^ Time.toString translate_elapsed);
  in
    chunk_def
  end;

fun translate_assembly {original_def,chunk_defs,theorem_name} =
  let
    val _ =
      if length chunk_defs = 11 then ()
      else raise Fail "unexpected case-16594 CEQ chunk count";
    val chunk_constants = map (lhs o concl) chunk_defs;
    val assembled_rhs = listSyntax.list_mk_append chunk_constants;
    val assembly_goal = mk_eq (lhs (concl original_def),assembled_rhs);
    val _ = stage ("assembly-proof-start chunks=11");
    val assembly_thm =
      prove (assembly_goal,
             SIMP_TAC (srw_ss()) (original_def :: chunk_defs));
    val assembly_thm = save_thm (theorem_name,assembly_thm);
    val _ = stage ("assembly-proof-done chunks=11");
    val translate_start = Time.now ();
    val _ = stage ("assembly-translate-start chunks=11");
    val _ = ml_translatorLib.translate assembly_thm;
    val translate_elapsed = Time.- (Time.now (),translate_start);
    val _ =
      stage
        ("assembly-translate-done chunks=11 seconds=" ^
         Time.toString translate_elapsed);
  in
    assembly_thm
  end;

end
