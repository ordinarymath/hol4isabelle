theory CakeML_Original
  imports "HOL4_Large_Original.HOL4_Large_Original"
begin

declare [[ML_environment="HOL4"]]

subsection \<open>misc dependencies\<close>
ML \<open>Holmake run make_theories "HOL/examples/fun-op-sem/lprefix_lub"\<close>
ML \<open>Holmake run make_theories "cakeml/developers"\<close>
ML \<open>Holmake run make_theories "HOL/examples/machine-code/hoare-triple"\<close>
ML \<open>Holmake run make_theories "HOL/examples/formal-languages/context-free"\<close>
ML \<open>Holmake run make_theories "cakeml/misc/lem_lib_stub"\<close>
ML \<open>Holmake run make_theories "cakeml/misc"\<close>
ML \<open>Holmake run make_theories "HOL/examples/balanced_bst"\<close>
ML \<open>Holmake run make_theories "HOL/examples/formal-languages"\<close>
ML \<open>Holmake run make_theories "HOL/examples/formal-languages/regular"\<close>


ML \<open>Holmake run make_theories "cakeml/basis/pure"\<close>


subsection \<open>semantics\<close>

ML \<open>Holmake run make_theories "cakeml/semantics/ffi"\<close>
ML \<open>Holmake run make_theories "cakeml/semantics"\<close>
ML \<open>Holmake run make_theories "cakeml/semantics/proofs"\<close>

subsection \<open>translator\<close>

ML \<open>Holmake run make_theories "cakeml/translator"\<close>

ML \<open>Holmake run make_theories "cakeml/compiler/parsing"\<close>

ML \<open>Holmake run make_theories "cakeml/characteristic"\<close>

ML \<open>Holmake run make_theories "cakeml/translator/monadic"\<close>


end
