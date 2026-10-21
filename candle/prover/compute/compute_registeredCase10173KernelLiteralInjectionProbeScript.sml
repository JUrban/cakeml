(*****************************************************************************
 * Focused probe for installing an immutable string literal directly in the
 * existing Candle kernel program, while registering the ordinary translator
 * value theorem for subsequent translated consumers.
 *****************************************************************************)
Theory compute_registeredCase10173KernelLiteralInjectionProbe
Ancestors
  candle_kernelProg
Libs
  preamble ml_translatorLib ml_monad_translatorLib ml_progLib

val _ = m_translation_extends "candle_kernelProg";

Definition kernel_literal_injection_probe_def:
  kernel_literal_injection_probe = «abc»
End

val kernel_literal_injection_probe_payload =
  kernel_literal_injection_probe_def |> concl |> rhs;

val kernel_literal_injection_probe_value_def =
  ml_progLib.define_abbrev false
    "kernel_literal_injection_probe_value"
    (semanticPrimitivesSyntax.mk_Litv
      (astSyntax.mk_StrLit kernel_literal_injection_probe_payload));

val kernel_literal_injection_probe_value =
  kernel_literal_injection_probe_value_def |> concl |> lhs;

val _ =
  ml_prog_update
    (ml_progLib.add_Dlet_lit_abbrev
      (locationTheory.unknown_loc_def |> concl |> dest_eq |> fst)
      (mlstringSyntax.mk_mlstring "kernel_literal_injection_probe")
      (astSyntax.mk_StrLit kernel_literal_injection_probe_payload)
      kernel_literal_injection_probe_value_def);

Theorem kernel_literal_injection_probe_value_relation:
  STRING_TYPE
    kernel_literal_injection_probe
    ^kernel_literal_injection_probe_value
Proof
  simp [ml_translatorTheory.STRING_TYPE_def,
        kernel_literal_injection_probe_def,
        kernel_literal_injection_probe_value_def]
QED

Theorem kernel_literal_injection_probe_v_thm:
  Eval ^(ml_progLib.get_env (ml_translatorLib.get_ml_prog_state ()))
    (Var (Short «kernel_literal_injection_probe»))
    (STRING_TYPE kernel_literal_injection_probe)
Proof
  simp [ml_translatorTheory.Eval_Var,
        ml_progTheory.lookup_var_def,
        ml_progTheory.nsLookup_merge_env,
        ml_progTheory.option_choice_f_apply,
        GSYM ml_progTheory.nsLookup_Short_def,
        fetch "-"
          "nsLookup_compute_registeredCase10173KernelLiteralInjectionProbe_env_pfun_eqs",
        kernel_literal_injection_probe_value_relation]
QED

val _ =
  ml_translatorLib.add_v_thms
    ("kernel_literal_injection_probe",
     "kernel_literal_injection_probe",
     kernel_literal_injection_probe_v_thm,
     TRUTH);

Definition kernel_literal_injection_probe_size_def:
  kernel_literal_injection_probe_size =
    mlstring$strlen kernel_literal_injection_probe
End

val r = translate kernel_literal_injection_probe_size_def;

val _ = export_theory ();
