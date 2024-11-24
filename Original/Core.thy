theory Core
  imports Bool_Kernel
begin

subsection \<open>core-theories\<close>

text \<open>HOL sequence @{file \<open>../HOL/tools/sequences/core-theories\<close>}\<close>


subsection \<open>compute\<close>

declare [[ML_environment="HOL4"]]
ML \<open>Context_Var.bind_ref "HOL4_Core_Isabelle"\<close>
ML \<open>Holmake run make_theories "../HOL/src/compute/src"\<close>

ML \<open>List.app Load.mark_loaded ["fastbuild", "holmakebuild",
    "DiskFiles.lex", "DiskFiles.grm", "AssembleDiskFiles", "DiskThms"]\<close>

subsection \<open>HolSat\<close>

ML \<open>exception Io = IO.Io\<close>
(* Wrapper for minisat, which needs files to be actually written to disk *)
ML \<open>Holmake build_heap (make_modules ["satTools"]) "../HOL/src/HolSat"\<close>
ML \<open>
local
open Lib SatSolvers
in
structure satTools = struct
open satTools
fun invokeSat sat_solver tm vc nr svm sva infile =
 let
   val (name,executable,notime_run,only_true,failure_string,start_string,
        end_string) =
       (getSolverName sat_solver,getSolverExe sat_solver,
        getSolverRun sat_solver, getSolverTrue sat_solver,
        getSolverFail sat_solver, getSolverStart sat_solver,
        getSolverEnd sat_solver)
   val outfile    = infile ^ "." ^ name
   val lines = File_Store.lines_of (Context.the_global_context()) (Path_Isabelle.file_name (Path_Isabelle.explode infile))
   val _ = File.write (Path_Isabelle.explode infile) (String.concat lines)
   val run_cmd    = notime_run executable (infile,outfile)
   val _       = sat_sysl run_cmd
   val ins        = File.read (Path_Isabelle.explode outfile)
   val sat_res_ss = Substring.full ins
   val result     = substringContains failure_string sat_res_ss
 in
  if result
   then NONE
   else
    let val model1 = parseSat (start_string,end_string) sat_res_ss
        val model2 = if only_true then
                       model1 @
                       (map (fn n => 0-n)
                            (subtract
                               (map snd (snd(dimacsTools.showSatVarMap svm)))
                               model1))
                     else model1
    in let val model3 = SOME(map (dimacsTools.intToLiteral sva) model2)
        in model3 end
    end
 end
handle Io _ => NONE

end
end
\<close>



ML \<open>Holmake run make_theories "../HOL/src/taut"\<close>
ML \<open>Holmake run make_theories "../HOL/src/marker"\<close>
ML \<open>Holmake run make_theories "../HOL/src/q"\<close>
ML \<open>Holmake run make_theories "../HOL/src/combin"\<close>
ML \<open>Holmake run make_theories "../HOL/src/lite"\<close>
ML \<open>Holmake run make_theories "../HOL/src/refute"\<close>
ML \<open>Holmake run make_theories "../HOL/src/simp/src"\<close>
ML \<open>Holmake run make_theories "../HOL/src/metis"\<close>
ML \<open>Holmake run make_theories "../HOL/src/meson/src"\<close>
ML \<open>Holmake run make_theories "../HOL/src/IndDef"\<close>
ML \<open>Holmake run make_theories "../HOL/src/basicProof"\<close>
ML \<open>Holmake run make_theories "../HOL/src/relation"\<close>
ML \<open>Holmake run make_theories "../HOL/src/quotient/src"\<close>
ML \<open>Holmake run make_theories "../HOL/src/coretypes"\<close>
ML \<open>Holmake run make_theories "../HOL/src/tfl/src"\<close>
ML \<open>Holmake run make_theories "../HOL/src/num/theories"\<close>
ML \<open>Holmake run make_theories "../HOL/src/num/theories/cv_compute"\<close>
ML \<open>Holmake run make_theories "../HOL/src/num/reduce/conv"\<close>
ML \<open>Holmake run make_theories "../HOL/src/num/reduce/src"\<close>
ML \<open>Holmake run make_theories "../HOL/src/num/arith/src"\<close>

ML \<open>Holmake run make_theories "../HOL/src/num"\<close>
(*
ML \<open>Holmake run make_theories "../HOL/src/num/termination"\<close>*)

text\<open>Look at @{file "../HOL/src/num/termination/Holmakefile"}\<close>

ML \<open>Holmake build_heap
  (* look at src/num/termination/Holmakefile *)
  (make_modules
  ["GenRelNorm"])
  "../HOL/src/num/termination"\<close>

ML \<open>Holmake build_heap
  (* look at src/num/termination/Holmakefile *)
  (make_modules
  ["Arith_cons", "Arith", "Exists_arith","Gen_arith", "Instance", "Norm_arith", "Norm_bool",
   "Norm_ineqs", "numSimps", "Prenex", "Rationals", "RJBConv", "Sol_ranges", "Solve_ineqs", "Solve",
    "Sub_and_cond", "Sup_Inf", "Term_coeffs", "Theorems", "Thm_convs"])
  ""\<close>
ML \<open>Holmake run make_theories "../HOL/src/num/extra_theories"\<close>
ML \<open>Holmake run make_theories "../HOL/src/unwind"\<close>
ML \<open>Holmake run make_theories "../HOL/src/pred_set/src"\<close>
ML \<open>Holmake run make_theories "../HOL/src/datatype/record"\<close>
ML \<open>Holmake run make_theories "../HOL/src/datatype"\<close>
ML \<open>Holmake run make_theories "../HOL/src/monad"\<close>
ML \<open>Holmake run make_theories "../HOL/src/list/src"\<close>
ML \<open>Holmake run make_theories "../HOL/src/quantHeuristics"\<close>
ML \<open>Holmake run make_theories "../HOL/src/pattern_matches"\<close>
ML \<open>Holmake run make_theories "../HOL/src/HolSat/vector_def_CNF"\<close>
ML \<open>Holmake run make_theories "../HOL/src/boss/ml_evaluation"\<close>
ML \<open>Holmake run make_theories "../HOL/src/opentheory/reader"\<close>
ML \<open>Holmake run (make_modules []) "../HOL/src/boss"\<close>
ML \<open>Holmake build_heap (make_modules
  (* see "../HOL/src/boss/Holmakefile" "*)
  ["listTheory", "pred_setTheory", "arithmeticTheory", "numLib", "pred_setLib",
    "pred_setSimps", "numSimps", "optionTheory", "RecordType", "rich_listTheory",
    "bossLib", "lcsymtacs"]) ""\<close>
(*
subsection \<open>Tactictoe\<close>

ML \<open>Holmake run (make_modules []) "../HOL/src/tactictoe/src"\<close>

subsection \<open>holyhammer\<close>

ML \<open>Holmake run (make_modules []) "../HOL/src/holyhammer"\<close>


*)



subsection \<open>Inspecting Variables...\<close>

ML \<open>Context_Var.sorted_allocations (Context.the_generic_context())\<close>
ML \<open>Holmake_Timing.export "core"\<close>

end
