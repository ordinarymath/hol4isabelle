theory CakeML_Translator
  imports CakeML_Semantics
begin

declare [[ML_environment="HOL4"]]

subsection \<open>translator\<close>

ML \<open>Holmake run (make_modules [
  "ml_progScript",
  "ml_translatorScript",
  "ml_pmatchScript",
  "ml_optimiseScript"
] ) "../../cakeml/translator"\<close>

ML\<open>Holmake run (make_modules ["std_preludeScript"]) "../../cakeml/translator"\<close> 

end