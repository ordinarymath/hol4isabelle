theory Core
  imports Bool_Kernel_Isa
begin
subsection \<open>core-theories\<close>

text \<open>HOL sequence \<open>HOL/tools/sequences/core-theories\<close>\<close>

declare [[ML_environment="HOL4"]]
ML \<open>Context_Var.bind_ref "HOL4_Core_Isabelle"\<close>

ML \<open>List.app Load.mark_loaded ["fastbuild", "holmakebuild",
    "DiskFiles.lex", "DiskFiles.grm", "AssembleDiskFiles", "DiskThms"]\<close>
ML \<open>Holmake build_heap make_all "../HOL/src/1"\<close>
ML \<open>Holmake build_heap make_all "../HOL/src/lite"\<close>

subsection \<open>Proof Manager\<close>

ML \<open>Holmake build_heap make_all "../HOL/src/proofman"\<close> (* HOL4 saves a heap here! *)

text \<open>Installing pretty printers, more or less according to
\<open>ML_file "HOL/tools-poly/prelude.ML"\<close>, but we cannot re-bind ML_system_pp.
\<close>

ML \<open>
local
  fun pp2polypp (ppfn: 'b -> HOLPP.pretty) =
    (fn depth => fn tab => fn x:'b => PrettyImpl.ML_Pretty_of_pretty (ppfn x))
  fun pp2polypp' f =
      (fn depth => fn tab => fn x => PrettyImpl.ML_Pretty_of_pretty (f depth tab x))
  fun gprint g =
    let
      val tyg = Parse.type_grammar ()
      val (_, ppt) = Parse.print_from_grammars (tyg, g)
    in
      smpp.lift ppt
    end
  val ppg = Parse.mlower o term_grammar.prettyprint_grammar gprint
  val ppgrules = Parse.mlower o term_grammar.prettyprint_grammar_rules gprint
  fun locpp l = PP.add_string (locn.toShortString l)
  fun pp_redblackmap (d: ('a,'b) Redblackmap.dict) =
    PP.add_string
      ("<Redblackmap(" ^ Int.toString (Redblackmap.numItems d) ^ ")>")
  fun pp_redblackset (s: 'a Redblackset.set) =
    PP.add_string
      ("<Redblackset(" ^ Int.toString (Redblackset.numItems s) ^ ")>")
in
  val _ =
    (let
        fun pp_db _ _ (c: DB.class) =
          PolyML.PrettyString
            (case c of
               DB.Thm => "Thm"
             | DB.Axm => "Axm"
             | DB.Def => "Def")
        fun pp_delta (depth:FixedInt.int) printArgTypes (d: 'a HolKernel.delta) =
          case d of
            Lib.SAME => PolyML.PrettyString "SAME"
          | Lib.DIFF a =>
              PolyML.PrettyBlock
                (2, false, [],
                 [PolyML.PrettyString "DIFF", PolyML.PrettyBreak (1, 0),
                  printArgTypes (a, depth)])
        fun pp_verdict depth (pra, prb) (v: ('a, 'b) Lib.verdict) =
          case v of
            Lib.PASS (a: 'a) =>
              PolyML.PrettyBlock
                (2, false, [],
                 [PolyML.PrettyString "PASS", PolyML.PrettyBreak (1, 0),
                  pra (a,  depth)])
          | Lib.FAIL (b: 'b) =>
              PolyML.PrettyBlock
                (2, false, [],
                 [PolyML.PrettyString "FAIL", PolyML.PrettyBreak (1, 0),
                  prb (b,  depth)])
        fun pp_frag depth printArgTypes (f: 'a HOLPP.frag) =
          case f of
            HOLPP.QUOTE s =>
              PolyML.PrettyBlock
                (2, false, [],
                 [PolyML.PrettyString "QUOTE", PolyML.PrettyBreak (1, 0),
                    PrettyImpl.pretty_of_ML_Pretty
                      (ML_system_pretty (s, depth))])
          | HOLPP.ANTIQUOTE a =>
              PolyML.PrettyBlock
                (2, false, [],
                 [PolyML.PrettyString "ANTIQUOTE", PolyML.PrettyBreak (1, 0),
                  printArgTypes (a,  depth)])
        fun pp_breakstyle _ _ (b: HOLPP.break_style) =
          PolyML.PrettyString
            (case b of
               HOLPP.CONSISTENT => "CONSISTENT"
             | HOLPP.INCONSISTENT => "INCONSISTENT")
        fun pp_symtab d printArgTypes (t : 'a Symtab.table) =
          Symtab.pp (fn a => printArgTypes(a, d-1)) t
        fun pp_inttab d printArgTypes (t : 'a Inttab.table) =
          Inttab.pp (fn a => printArgTypes(a, d-1)) t
        fun pp_knametab d printArgTypes (t : 'a KNametab.table) =
          KNametab.pp (fn a => printArgTypes(a, d-1)) t
        fun pp_seq _ _ (s:'a seq.seq) = HOLPP.add_string "<seq>"
        fun pp_typebase _ _ (tb:TypeBasePure.typeBase) = HOLPP.add_string "<typeBase>"
        fun pp_sexp _ _ (s : HOLsexp.t) = HOLsexp.printer s
        fun pp_termtab d printArgTypes (t : 'a Termtab.table) = Termtab.pp (fn a => printArgTypes(a,d-1)) t
        fun pp_holset' d printArgTypes (s: 'a HOLset.set) = HOLset.pp_holset d (fn (a,d) => printArgTypes(a,d-1)) s
      in
        ML_system_pp (pp2polypp' pp_holset')
      ; ML_system_pp (pp2polypp' pp_db)
      ; ML_system_pp (pp2polypp' pp_delta)
      ; ML_system_pp (pp2polypp' pp_verdict)
      ; ML_system_pp (pp2polypp' pp_frag)
      ; ML_system_pp (pp2polypp' pp_breakstyle)
      ; ML_system_pp (pp2polypp' pp_symtab)
      ; ML_system_pp (pp2polypp' pp_inttab)
      ; ML_system_pp (pp2polypp' pp_knametab)
      ; ML_system_pp (pp2polypp' pp_termtab)
      ; ML_system_pp (pp2polypp' pp_seq)
      ; ML_system_pp (pp2polypp' pp_sexp)
      ; ML_system_pp (pp2polypp' pp_typebase)
      end
  ; ML_system_pp (pp2polypp HOLPP.pp_pretty)
  ; ML_system_pp (pp2polypp ppg)
  ; ML_system_pp (pp2polypp ppgrules)
  ; ML_system_pp (pp2polypp locpp)
  ; ML_system_pp (pp2polypp pp_redblackmap)
  ; ML_system_pp (pp2polypp pp_redblackset)
  ; ML_system_pp
      (pp2polypp (Parse.term_pp_with_delimiters Hol_pp.pp_term))
  ; ML_system_pp
      (pp2polypp (Parse.type_pp_with_delimiters Hol_pp.pp_type))
  ; ML_system_pp (pp2polypp Pretype.pp_pretype)
  ; ML_system_pp (pp2polypp Hol_pp.pp_thm)
  ; ML_system_pp (pp2polypp Hol_pp.pp_theory)
  ; ML_system_pp (pp2polypp type_grammar.prettyprint_grammar)
  ; ML_system_pp (pp2polypp proofManagerLib.pp_proof)
  ; ML_system_pp (pp2polypp proofManagerLib.pp_proofs)
  ; ML_system_pp (pp2polypp Rewrite.pp_rewrites)
  ; ML_system_pp (pp2polypp TypeBasePure.pp_tyinfo)
  ; ML_system_pp (pp2polypp Arbnum.pp_num)
  ; ML_system_pp (pp2polypp Arbint.pp_int)
  ; ML_system_pp (pp2polypp Arbrat.pp_rat)
  ; ML_system_pp (pp2polypp Tag.pp_tag)
  )
end
\<close>

subsection \<open>Tactictoe\<close>

ML \<open>Holmake run (make_modules []) "../HOL/src/tactictoe/src"\<close>

subsection \<open>holyhammer\<close>

ML \<open>Holmake run (make_modules []) "../HOL/src/holyhammer"\<close>

subsection \<open>compute\<close>

ML \<open>Holmake run make_theories "../HOL/src/compute/src"\<close>

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
ML \<open>Holmake run make_theories "../HOL/src/IndDef"\<close>
ML \<open>Holmake run make_theories "../HOL/src/meson/src"\<close>
ML \<open>Holmake run make_theories "../HOL/src/basicProof"\<close>
ML \<open>Holmake run make_theories "../HOL/src/relation"\<close>
ML \<open>Holmake run make_theories "../HOL/src/coretypes"\<close>
ML \<open>Holmake run make_theories "../HOL/src/tfl/src"\<close>
ML \<open>Holmake run make_theories "../HOL/src/num/theories"\<close>
ML \<open>Holmake run make_theories "../HOL/src/num/reduce/src"\<close>
ML \<open>Holmake run make_theories "../HOL/src/num/arith/src"\<close>
ML \<open>Holmake run make_theories "../HOL/src/num"\<close>
ML \<open>Holmake run make_theories "../HOL/src/num/termination"\<close>

ML \<open>Holmake build_heap
  (* look at src/num/termination/Holmakefile *)
  (make_modules
  ["Arith_cons", "Arith", "Exists_arith", "GenRelNorm", "Gen_arith", "Instance", "Norm_arith", "Norm_bool",
   "Norm_ineqs", "numSimps", "Prenex", "Rationals", "RJBConv", "Sol_ranges", "Solve_ineqs", "Solve",
    "Sub_and_cond", "Sup_Inf", "Term_coeffs", "Theorems", "Thm_convs"])
  ""\<close>


ML \<open>Holmake run make_theories "../HOL/src/num/extra_theories"\<close>
ML \<open>Holmake run make_theories "../HOL/src/pred_set/src"\<close>

subsection \<open>datatype\<close>

ML \<open>Holmake run make_theories "../HOL/src/datatype/record"\<close>
ML \<open>Holmake run make_theories "../HOL/src/datatype"\<close>
ML \<open>Holmake run make_theories "../HOL/src/monad"\<close>
ML \<open>Holmake run make_theories "../HOL/src/list/src"\<close>

ML \<open>Holmake run make_theories "../HOL/src/quantHeuristics"\<close>
ML \<open>Holmake run make_theories "../HOL/src/unwind"\<close>
ML \<open>Holmake run make_theories "../HOL/src/pattern_matches"\<close>

ML \<open>Holmake run make_theories "../HOL/src/HolSat/vector_def_CNF"\<close>
ML \<open>Holmake run make_theories "../HOL/src/boss/ml_evaluation"\<close>

ML \<open>Holmake run make_theories "../HOL/src/opentheory/postbool"\<close>

ML \<open>Holmake run (make_modules []) "../HOL/src/boss"\<close>

ML \<open>Holmake build_heap (make_modules
  (* see "../HOL/src/boss/Holmakefile" "*)
  ["listTheory", "pred_setTheory", "arithmeticTheory", "numLib", "pred_setLib",
    "pred_setSimps", "numSimps", "optionTheory", "RecordType", "rich_listTheory",
    "bossLib"]) ""\<close>


subsection \<open>Inspecting Variables...\<close>

ML \<open>Context_Var.sorted_allocations (Context.the_generic_context())\<close>
ML \<open>Holmake_Timing.export "core"\<close>

end
