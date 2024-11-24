theory Kernel imports Kernel_Sig
begin

declare [[ML_environment = "HOL4"]]
ML \<open>Context_Var.bind_ref "Kernel_Original"\<close>


subsection \<open>0\<close>

ML \<open>Holmake build_heap make_all "../HOL/src/0"\<close>

subsection \<open>thm\<close>
(*
ML \<open>Holmake build_heap make_all "../HOL/src/thm"\<close>*)

ML_file "../HOL/src/thm/Compute.sig"
ML_file "../HOL/src/thm/Compute.sml"
ML_file "../HOL/src/thm/std-thmsig.ML"
ML_file "../HOL/src/thm/std-thm.ML"

ML_file "../HOL/src/thm/Overlay.sml"

end