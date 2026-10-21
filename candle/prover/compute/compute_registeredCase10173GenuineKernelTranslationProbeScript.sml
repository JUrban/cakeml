(*****************************************************************************
 * Development probe for importing the genuine case-10173 fast evaluator
 * into the existing Candle kernel translator state.  Keep this separate
 * from candle_kernelProg until the complete dependency sequence is green.
 *****************************************************************************)
Theory compute_registeredCase10173GenuineKernelTranslationProbe
Ancestors
  candle_kernelProg
  compute_registeredCase10173GenuineCertificateData
Libs
  preamble ml_translatorLib ml_monad_translatorLib ml_progLib

val _ = m_translation_extends "candle_kernelProg";

(* Add the immutable payload as one CakeML literal declaration.  This is the
   program library's proved literal rule, followed by the ordinary translator
   value relation consumed by all later translated definitions.  It avoids
   reprocessing the complete kernel environment once per data chunk. *)
val registered_case10173_genuine_packed_certificate_payload =
  compute_registeredCase10173GenuineCertificateDataTheory.registered_case10173_genuine_packed_certificate_def
  |> concl |> rhs;

val registered_case10173_genuine_packed_certificate_term =
  compute_registeredCase10173GenuineCertificateDataTheory.registered_case10173_genuine_packed_certificate_def
  |> concl |> lhs;

val registered_case10173_genuine_packed_certificate_value_def =
  ml_progLib.define_abbrev false
    "registered_case10173_genuine_packed_certificate_value"
    (semanticPrimitivesSyntax.mk_Litv
      (astSyntax.mk_StrLit
        registered_case10173_genuine_packed_certificate_term));

(* Rewrite the semantic abbreviation to the literal once, before extending
   the program.  The stored environment and all later proofs retain the small
   HOL constant rather than the 4.7-million-character term. *)
val registered_case10173_genuine_packed_certificate_literal_value_def =
  registered_case10173_genuine_packed_certificate_value_def
  |> PURE_REWRITE_RULE
       [compute_registeredCase10173GenuineCertificateDataTheory.registered_case10173_genuine_packed_certificate_def];

val registered_case10173_genuine_packed_certificate_value =
  registered_case10173_genuine_packed_certificate_value_def
  |> concl |> lhs;

val _ =
  ml_prog_update
    (ml_progLib.add_Dlet_lit_abbrev
      (locationTheory.unknown_loc_def |> concl |> dest_eq |> fst)
      (mlstringSyntax.mk_mlstring
        "registered_case10173_genuine_packed_certificate")
      (astSyntax.mk_StrLit
        registered_case10173_genuine_packed_certificate_payload)
      registered_case10173_genuine_packed_certificate_literal_value_def);

Theorem registered_case10173_genuine_packed_certificate_value_relation:
  STRING_TYPE
    registered_case10173_genuine_packed_certificate
    ^registered_case10173_genuine_packed_certificate_value
Proof
  simp [ml_translatorTheory.STRING_TYPE_def,
        registered_case10173_genuine_packed_certificate_value_def]
QED

Theorem registered_case10173_genuine_packed_certificate_v_thm:
  Eval ^(ml_progLib.get_env (ml_translatorLib.get_ml_prog_state ()))
    (Var (Short «registered_case10173_genuine_packed_certificate»))
    (STRING_TYPE registered_case10173_genuine_packed_certificate)
Proof
  simp [ml_translatorTheory.Eval_Var,
        ml_progTheory.lookup_var_def,
        ml_progTheory.nsLookup_merge_env,
        ml_progTheory.option_choice_f_apply,
        GSYM ml_progTheory.nsLookup_Short_def,
        fetch "-"
          "nsLookup_compute_registeredCase10173GenuineKernelTranslationProbe_env_pfun_eqs",
        registered_case10173_genuine_packed_certificate_value_relation]
QED

val _ =
  ml_translatorLib.add_v_thms
    ("registered_case10173_genuine_packed_certificate",
     "registered_case10173_genuine_packed_certificate",
     registered_case10173_genuine_packed_certificate_v_thm,
     TRUTH);

Definition registered_case10173_genuine_packed_certificate_bytes_probe_def:
  registered_case10173_genuine_packed_certificate_bytes_probe =
    mlstring$explode registered_case10173_genuine_packed_certificate
End

val r = translate
  registered_case10173_genuine_packed_certificate_bytes_probe_def;

val _ = export_theory ();
