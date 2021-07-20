theory CakeML_Semantics
  imports "CakeML_Deps_Isabelle.CakeML_Deps"
begin

declare [[ML_environment="HOL4"]]

subsection \<open>semantics\<close>

ML \<open>Context_Var.bind_ref "CakeML_Semantics"\<close>
ML \<open>Holmake run make_theories "../../cakeml/semantics/ffi"\<close>
ML \<open>Holmake run make_theories "../../cakeml/semantics"\<close>
ML \<open>Holmake run make_theories "../../cakeml/semantics/proofs"\<close>

end
