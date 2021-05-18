theory CakeML
  imports "CakeML.CakeML_Semantics"
begin

declare [[ML_environment="HOL4"]]

subsection \<open>translator\<close>

ML \<open>Holmake run make_theories "../cakeml/translator"\<close>

end