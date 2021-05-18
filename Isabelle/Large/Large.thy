theory Large
imports "More_Isabelle.More"
begin

subsection \<open>large-theories\<close>

text \<open>HOL sequence \<open>HOL/tools/sequences/large-theories\<close>\<close>

ML \<open>
List.app Load.mark_loaded
  ["prove_real_assumsScript", "prove_real_assumsTheory" (*also in Holmakefile excluded *)]
\<close>
ML \<open>Holmake run make_theories "../../HOL/src/real"\<close>
ML \<open>Holmake run make_theories "../../HOL/src/HolQbf"\<close>
ML \<open>Holmake run make_theories "../../HOL/src/HolSmt"\<close>
ML \<open>Holmake run make_theories "../../HOL/src/Boolify/src"\<close>
ML \<open>Holmake run make_theories "../../HOL/src/float"\<close>


ML \<open>Holmake run make_theories "../../HOL/src/floating-point"\<close>


(* Uncomment if probability library is needed
ML \<open>Holmake run (make_modules []) "../../HOL/src/probability"\<close>
ML \<open>Holmake build_heap (make_modules
  (* see "../HOL/src/probability/Holmakefile" "*)
  ["realTheory", "realLib", "real_sigmaTheory", "seqTheory", "transcTheory",
    "RealArith", "sortingTheory", "pred_setLib", "numpairTheory", "res_quanTools",
    "logrootTheory"]) ""\<close>


ML \<open>Holmake run (make_modules ["util_probTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["iterateTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["productTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["sigma_algebraTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["extrealTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["real_topologyTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["derivativeTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["integrationTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["real_borelTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["real_measureTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["real_lebesgueTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["real_probabilityTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["borelTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["lebesgueTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["martingaleTheory"]) "../../HOL/src/probability"\<close>
ML \<open>Holmake run (make_modules ["probabilityTheory"]) "../../HOL/src/probability"\<close>

ML \<open>Holmake run make_theories "../../HOL/src/probability"\<close>
*)

ML \<open>Context_Var.sorted_allocations (Context.the_generic_context())\<close>
ML \<open>Holmake_Timing.export "large"\<close>

end