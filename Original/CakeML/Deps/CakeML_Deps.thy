theory CakeML_Deps
  imports "More_Original.More"
begin

declare [[ML_environment="HOL4"]]

subsection \<open>misc dependencies\<close>
ML \<open>Context_Var.bind_ref "CakeML_Misc_Deps"\<close>
ML \<open>Holmake run make_theories "../../HOL/examples/fun-op-sem/lprefix_lub"\<close>
ML \<open>Holmake run make_theories "../../HOL/examples/machine-code/hoare-triple"\<close>
ML \<open>Holmake run make_theories "../../HOL/examples/balanced_bst"\<close>
ML \<open>Holmake run make_theories "../../HOL/examples/formal-languages"\<close>
ML \<open>Holmake run make_theories "../../HOL/examples/formal-languages/context-free"\<close>
ML \<open>Holmake run (make_modules ["vec_mapScript"]) "../../HOL/examples/formal-languages/regular"\<close>
ML \<open>Holmake run make_theories "../../HOL/examples/formal-languages/regular"\<close>


subsection \<open>additional dependencies from Large\<close>
ML \<open>Context_Var.bind_ref "CakeML_Large_Deps"\<close>
ML \<open>
List.app Load.mark_loaded
  ["prove_real_assumsScript", "prove_real_assumsTheory" (*also in Holmakefile excluded *)]
\<close>
ML \<open>Holmake run make_theories "../../HOL/src/real"\<close>
ML \<open>Holmake run make_theories "../../HOL/src/floating-point"\<close>


subsection \<open>cakeml dependencies\<close>
ML \<open>Context_Var.bind_ref "CakeML_Deps"\<close>
ML \<open>Holmake run make_theories "../../cakeml/developers"\<close>
ML \<open>Holmake run make_theories "../../cakeml/misc/lem_lib_stub"\<close>
ML \<open>Holmake run make_theories "../../cakeml/misc"\<close>  
ML \<open>Holmake run make_theories "../../cakeml/basis/pure"\<close>

ML \<open>Holmake_Timing.export "CakeML_Deps"\<close>
ML \<open>Context_Var.sorted_allocations (Context.the_generic_context())\<close>
end
