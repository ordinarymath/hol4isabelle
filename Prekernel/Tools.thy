theory Tools
  imports ML_Environment
begin

declare [[ML_environment = "HOL4"]]

ML \<open>Context_Var.bind_ref "HOL4_Tools"\<close>

ML_file "../HOL/tools/mlyacc/mlyacclib/MLY_base-sig.sml"
ML_file "../HOL/tools/mlyacc/mlyacclib/MLY_join.sml"
ML_file "../HOL/tools/mlyacc/mlyacclib/MLY_lrtable.sml"
(* Version of MLY_stream with unsychronized refs *)
ML\<open>
structure Stream :> STREAM =
struct
   open Uref
   datatype 'a str = EVAL of 'a * 'a str Uref.t | UNEVAL of (unit->'a)

   type 'a stream = 'a str Uref.t

   fun get s = (case !s of
       EVAL t => t
     | UNEVAL f =>
	    let val t = (f(), Uref.new(UNEVAL f)) in s := EVAL t; t end)

   fun streamify f = Uref.new(UNEVAL f)
   fun cons(a,s) = Uref.new(EVAL(a,s))

end;
\<close>
ML_file "../HOL/tools/mlyacc/mlyacclib/MLY_parser2.sml"

text "poly-init"
ML_file_old "../HOL/tools-poly/poly/Mosml.sml"
ML_file "../HOL/tools-poly/poly/Binarymap.sig"
ML_file "../HOL/tools-poly/poly/Binarymap.sml"
ML_file "../HOL/tools-poly/poly/Binaryset.sig"
ML_file "../HOL/tools-poly/poly/Binaryset.sml"
ML_file "../HOL/tools-poly/poly/Listsort.sig"
ML_file "../HOL/tools-poly/poly/Listsort.sml"

ML_file "../HOL/tools/Holmake/holpathdb.sig"
ML_file "../HOL/tools/Holmake/holpathdb.sml"

ML_file "../HOL/tools/Holmake/FunctionalRecordUpdate.sml"

ML_file "../HOL/tools/Holmake/HM_SimpleBuffer.sig"
ML_file "../HOL/tools/Holmake/HM_SimpleBuffer.sml"

ML_file "../HOL/tools/Holmake/SourcePos.sig"
ML_file "../HOL/tools/Holmake/SourcePos.sml"
ML_file "../HOL/tools/Holmake/tailbuffer.sig"
ML_file "../HOL/tools/Holmake/tailbuffer.sml"

ML_file "../HOL/tools/Holmake/SourceFile.sig"
ML_file "../HOL/tools/Holmake/SourceFile.sml"
ML_file "../HOL/tools/Holmake/Holdep_tokens.sig"
ML_file "../HOL/tools/Holmake/Holdep_tokens.sml"
ML_file "../HOL/tools/Holmake/Holdep.sig"
ML_file "../HOL/tools/Holmake/Holdep.sml"
ML_file "../HOL/tools/Holmake/Holmake_tools_dtype.sml"
ML_file "../HOL/tools/Holmake/Holmake_tools.sig"
ML_file_old "../HOL/tools/Holmake/Holmake_tools.sml"
ML \<open>structure Holmake_tools : Holmake_tools = struct
  open Holmake_tools
  fun getWidth () = 80
end\<close>
ML_file "../HOL/tools/Holmake/GetOpt.sig"
ML_file "../HOL/tools/Holmake/GetOpt.sml"
ML_file "../HOL/tools/Holmake/HM_Core_Cline.sig"
ML_file "../HOL/tools/Holmake/HM_Core_Cline.sml"
ML_file "../HOL/tools/Holmake/HM_DepGraph.sig"
ML_file "../HOL/tools/Holmake/HM_DepGraph.sml"
ML_file "../HOL/tools/Holmake/regexpMatch.sig"
ML_file "../HOL/tools/Holmake/regexpMatch.sml"
ML_file "../HOL/tools/Holmake/parse_glob.sig"
ML_file "../HOL/tools/Holmake/parse_glob.sml"
ML_file_old "../HOL/tools/Holmake/holdeptool.sml"
ML_file "../HOL/tools/Holmake/internal_functions.sig"
ML_file_old "../HOL/tools/Holmake/internal_functions.sml"
ML_file "../HOL/tools/Holmake/Holmake_types.sig"
ML_file "../HOL/tools/Holmake/Holmake_types.sml"
ML_file "../HOL/tools/Holmake/HM_GraphBuildJ1.sig"
ML_file "../HOL/tools/Holmake/HM_GraphBuildJ1.sml"
ML_file "../HOL/tools/Holmake/poly/HM_Cline.sig"
ML_file "../HOL/tools/Holmake/poly/HM_Cline.sml"
ML_file "../HOL/tools/Holmake/poly/HM_BaseEnv.sig"
ML_file "../HOL/tools/Holmake/poly/HM_BaseEnv.sml"
ML_file "../HOL/tools/Holmake/poly/GraphExtra.sig"
ML_file "../HOL/tools/Holmake/poly/GraphExtra.sml"
ML_file "../HOL/tools/Holmake/BuildCommand.sig"
ML_file "../HOL/tools/Holmake/ReadHMF.sig"
ML_file_old "../HOL/tools/Holmake/ReadHMF.sml"

ML \<open>structure CompilerSpecific :>
  sig
    val quietbind : string -> unit
  end =
struct

fun quietbind s =
  ML_Compiler.eval {debug = NONE, environment="HOL4", redirect = false, verbose = false, catch_all = true,
  warning = fn _ => (), writeln = fn _ => ()} Position.none (ML_Lex.tokenize s)
end
\<close> \<comment> \<open>not
ML_file "../HOL/tools-poly/Holmake/CompilerSpecific.ML"
\<close>

end
